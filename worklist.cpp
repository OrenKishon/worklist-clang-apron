#include <iostream>     // std::cout
#include <fstream>      // std::ifstream
#include <string>
#include <unistd.h>     // fork()
#include <stdlib.h>     // atoi()
#include <unordered_map> 
#include <set> 

#include "clang/AST/Decl.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Analysis/AnalysisContext.h"
#include "clang/Analysis/Analyses/DataflowWorklist.h"

// Apron includes
#include "ap_global0.h"
#include "ap_global1.h"
#include "box.h"
#include "oct.h"
#include "pk.h"
#include "pkeq.h"

#define MAX_VAR_NAME_LEN 31

#define DEBUGGG printf("** %d **\n", __LINE__)

static int printCFG;
static const char *funcToAnalyze;
static ap_manager_t* man;
static ap_environment_t *env;

typedef enum { EQUAL, NOT_EQUAL, GREATER_EQUAL, LESS, } compare_t;

static char *strdup_e(const char *s) {
    char *dup = strdup(s);
    if (!dup) {
        perror("strdup");
        exit(1);
    }

    return dup;
}

static const char *toString(clang::Stmt *stmt) {
    static char ret[64];
    clang::LangOptions LangOpts;
    LangOpts.C99 = true;
    clang::PrintingPolicy Policy(LangOpts);
    std::string TypeS;
    llvm::raw_string_ostream s(TypeS);
    stmt->printPretty(s, 0, Policy);
    strcpy(ret, s.str().c_str());
    ret[sizeof(ret) - 1] = '\0';

    return (char *)ret;
}

class Variables {
    clang::DeclContext *dc;
    std::set<char *> numerics;
    // Map array name to its size
    struct cmp_str {
        bool operator()(char const *a, char const *b) const {
            return std::strcmp(a, b) < 0;
        }
    };
    std::map<char *, int, cmp_str> array2size;

public:
  // constructor is actually in init() since this is a singletone static class,
  // but the construction requires dynamic data
  Variables() {
  }

  void init(clang::Decl *D) {
    clang::FunctionDecl *FD = clang::dyn_cast<clang::FunctionDecl>(D);
    for (clang::FunctionDecl::param_iterator P = FD->param_begin();
            P != FD->param_end(); ++P) {
        clang::ParmVarDecl *Parm = *P;
        const char *varName = Parm->getNameAsString().c_str();
        clang::QualType ty = Parm->getType();
        if (ty->isScalarType()) {
            char *s = strdup_e(varName);
            numerics.insert(s);
            printf("Tracking numeric paramater variable %s\n", s);
        }
    }
    
    dc = clang::cast<clang::DeclContext>(D);

    for (clang::DeclContext::specific_decl_iterator<clang::VarDecl>
           I(dc->decls_begin()), E(dc->decls_end()); I != E; ++I) {
        const clang::VarDecl *vd = *I;
  
        if (!isTrackedVar(vd))
            continue;
  
        const char *varName = vd->getNameAsString().c_str();
        clang::QualType ty = vd->getType();
        if (ty->isScalarType()) {
            char *name = strdup_e(varName);
            numerics.insert(name);
            printf("Tracking numeric variable %s\n", name);
        } else if (ty->isArrayType()) {
            const clang::ArrayType *at = ty->getAsArrayTypeUnsafe();
            const clang::ConstantArrayType *cat;
            if (!(cat = clang::dyn_cast<const clang::ConstantArrayType>(at))) {
                printf("Can't handle non-constant arrays (%s). Aborting\n",
                        varName);
                exit(1);
            }
            char *name = strdup_e(varName);
            const unsigned long size = *cat->getSize().getRawData();
            array2size[name] = size;
            printf("Tracking array variable %s\n", name);
        }
    }

    ap_var_t temp_ap_var_array[numerics.size()];
    int i = 0;
    for (std::set<char *>::iterator it = numerics.begin(); it != numerics.end();
            ++it) {
        temp_ap_var_array[i++] = (ap_var_t)(*it);
    }

    // Assuming integers only. The allocation copies the content of
    // temp_ap_var_array so its OK its local
    env = ap_environment_alloc(temp_ap_var_array, numerics.size(), NULL, 0);
  }

  ~Variables() {
      if (env)
        ap_environment_free(env);
  
      for (std::map<char *, int>::iterator it=array2size.begin();
              it != array2size.end(); ++it) {
          if (char *key = it->first)
              free(key);
      }
      for (std::set<char *>::iterator it=numerics.begin(); it != numerics.end();
              ++it) {
          free(*it);
      }
  }

  char *find(const char *varName) {
      for (std::set<char *>::iterator it=numerics.begin(); it != numerics.end();
              ++it) {
          if (!*it)
              continue;
          if (!strcmp(varName, *it))
              return *it;
      }

      printf("Error: Variable %s not found in var list. Aborting\n", varName);
      exit(1);
  }

  int arraySize(const char *array_const) {
      char *array = const_cast<char *>(array_const);

      if (array2size.find(array) == array2size.end()) {
          printf("Error: Array %s not found in array list. Aborting\n", array);
          for (std::map<char *, int>::iterator it=array2size.begin();
                  it != array2size.end(); ++it) {
              if (char *key = it->first)
                  printf("%s ", key);

          }
          printf("\n");
          exit(1);
      }

      return array2size[array];
  }

private:
  bool isTrackedVar(const clang::VarDecl *vd) {
      return vd->isLocalVarDecl() && // local, but could be static
          !vd->hasGlobalStorage() && // Can't be static
          !vd->isExceptionVariable() && // Ignore exception vars
          !vd->isInitCapture() && // Ignore init-capture (?)
          vd->getDeclContext() == dc;
  }
};

static Variables variables;

// This context exists for every block
class BlockApronContext {
  const clang::CFGBlock *block;
  // A reference to the global map
  std::unordered_map<const clang::CFGBlock *, BlockApronContext *>
  *block2Ctx;

  // Abstract values
  std::unordered_map<const clang::CFGBlock *, ap_abstract1_t> pred2Abs;
  ap_abstract1_t abst;

  // Successors
  const clang::CFGBlock *succ[2];
public:
  BlockApronContext(const clang::CFGBlock *block,
                       std::unordered_map<const clang::CFGBlock *,
               BlockApronContext *> *block2Ctx) {
    this->block = block;
    this->block2Ctx = block2Ctx;

    // Chaotic iteration: All abstract values initialized as bottom
    for (clang::CFGBlock::const_pred_iterator I = block->pred_begin(),
           E = block->pred_end(); I != E; ++I) {
      const clang::CFGBlock *Pred = *I;
      if (!Pred)
        continue;

      pred2Abs[Pred] = ap_abstract1_bottom(man, env);
    }
    abst = ap_abstract1_bottom(man, env);

    assert(block->succ_size() <= 2);
    // If has terminator statement => has two successors
    assert(!block->getTerminator() || block->succ_size() == 2);

    succ[0] = NULL;
    succ[1] = NULL;
    if (block->succ_empty())
      return;

    for (clang::CFGBlock::const_succ_iterator I = block->succ_begin(),
           E = block->succ_end(); I != E; ++I) {
      const clang::CFGBlock *s = *I;
      if (!s)
        continue;

      if (!succ[0])
        succ[0] = s;
      else
        succ[1] = s;
    }
  }

  // Returns true if entry value has now changed
  bool updateEntryValue() {
    // Entry block
    if (block->pred_empty()) {
      abst = ap_abstract1_top(man, env);
      return true;
    }
    ap_abstract1_t prev = abst;

    // Merge (join) all predeseccors exit values
    abst = ap_abstract1_bottom(man, env);
    for (auto it = pred2Abs.begin(); it != pred2Abs.end(); ++it) {
      ap_abstract1_t absPred = it->second;
      abst = ap_abstract1_join(man, false, &abst, &absPred);
    }
    printf("Prev value: ");
    ap_abstract1_fprint(stdout, man, &prev);
    printf("Curr value: ");
    ap_abstract1_fprint(stdout, man, &abst);
    return !ap_abstract1_is_eq(man, &abst, &prev);
  }

  // Each successor holds a list of its predecessors exit values. We update
  // the entry for this block in each of its successors' list
    void updateSuccessors() {
        if (block->succ_empty())
          return;
  
        // Single successor (no branch): just pass this block's exit value as
        // the successor's entry value
        if (!block->getTerminator()) {
          ((*block2Ctx)[succ[0]])->pred2Abs[block] = abst;
          return;
        }
  
        // Analyze condition which terminates this block
        const clang::BinaryOperator *BO =
            clang::dyn_cast<clang::BinaryOperator>(
                    block->getTerminatorCondition());
        if (!BO || !BO->isComparisonOp()) {
            printf("Can't handle condition which isn't a binary expression\n");
            exit(1);
        }
  
        clang::Expr *lhs = BO->getLHS()->IgnoreImpCasts();
        clang::DeclRefExpr *DR = clang::dyn_cast<clang::DeclRefExpr>(lhs);
  
        if (!DR) {
            printf("Left side of condition must be a variable\n");
            exit(1);
        }
  
        char *x = variables.find(DR->getDecl()->getNameAsString().c_str());
        char *y = NULL;
        int c = 0;
        // Two successors: first for 'then', second for 'else'
        ap_abstract1_t absThen, absElse;
  
        clang::Expr *rhs = BO->getRHS();
        // RHS is a literal: x < c, x != c, etc
        if (clang::IntegerLiteral *IL =
                clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
            c = (int)*IL->getValue().getRawData();
        // RHS is a variable: x < y, x != y, etc
        } else if (clang::DeclRefExpr *DRright =
                clang::dyn_cast<clang::DeclRefExpr>(rhs->IgnoreImpCasts())) {
            y = variables.find(DRright->getDecl()->getNameAsString().c_str());
        } else {
            printf("Can't analyze a compound right hand side: \n\t%s (%s)\n",
                    toString(rhs), rhs->getStmtClassName());
            exit(1);
        }
  
        switch (BO->getOpcode()) {
        case clang::BO_LT:
          absThen = meet_constraint(x, LESS, y, c);
          absElse = meet_constraint(x, GREATER_EQUAL, y, c);
          break;
        case clang::BO_NE:
          absThen = meet_constraint(x, NOT_EQUAL, y, c);
          absElse = meet_constraint(x, EQUAL, y, c);
          break;
        default:
          printf("Can only handle ops: <, !=\n");
          exit(1);
        }
  
        printf("Then branch:\n");
        ap_abstract1_fprint(stdout, man, &absThen);
        (*block2Ctx)[succ[0]]->pred2Abs[block] = absThen;
  
        printf("Else branch:\n");
        ap_abstract1_fprint(stdout, man, &absElse);
        (*block2Ctx)[succ[1]]->pred2Abs[block] = absElse;
    }

#if 0
    void assignExpr(char* var, std::vector<char *> *exprItems,
                    std::vector<int> *coeffs) {
      abst = ApronHelper::assignExpr(abst, var, exprItems, coeffs);
    }
#endif

    void print() {
        ap_abstract1_fprint(stdout, man, &abst);
    }

    bool isIndexInBound(char *indVar, int size) {
        return satisfies_constraint(indVar, GREATER_EQUAL, 0) &&
            satisfies_constraint(indVar, LESS, size);
    }

    /* x := c */
    void assignConst(char *x, int c) {
        ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
        ap_linexpr1_set_list(&expr,
                             AP_CST_S_INT, c,
                             AP_END);
    
        abst = ap_abstract1_assign_linexpr(man, true, &abst, x, &expr, NULL);
        ap_linexpr1_clear(&expr);
    }

    /* x := a*y + c */ 
    void assignLinearExpression(char *x, int a, char *y, int c) {
      // ap_linexpr1_make() destroys contents of *var 
        ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
        ap_linexpr1_set_list(&expr,
                            AP_COEFF_S_INT, a, y,
                            AP_CST_S_INT, c,
                            AP_END);
   
        abst = ap_abstract1_assign_linexpr(man, true, &abst, x, &expr, NULL);
        ap_linexpr1_clear(&expr);    
    } 
  
private:
#if 0
  /* var1 := expr */ 
  static ap_abstract1_t assignExpr(ap_abstract1_t abst, char *var,
                                   std::vector<char *> *exprItems,
                                   std::vector<int> *coeffs) {
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE,
            exprItems->size() + 2);    
    ap_scalar_t *scalar = ap_scalar_alloc_set_double(1);    
    char *src[strlen(var) + 1];
    ap_linexpr1_set_coeff_scalar(&expr, src, scalar);

    assert(exprItems->size() == coeffs->size());
    for (int i = 0; i < (int)exprItems->size(); ++i) {
      scalar = ap_scalar_alloc_set_double(coeffs->at(i));
      ap_linexpr1_set_coeff_scalar(&expr, exprItems->at(i), scalar);
    }

    abst = ap_abstract1_assign_linexpr(man, true, &abst, var, &expr, NULL);
    ap_scalar_free(scalar);
    ap_linexpr1_clear(&expr);    

    return abst;
  }

  /* a[ind] */
  ap_abstract1_t addArrayIndexConst(char *indVar, int size) {
    ap_lincons1_array_t array = ap_lincons1_array_make(env, 2);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_lincons1_t cons = ap_lincons1_make(AP_CONS_SUPEQ, &expr, NULL);
    ap_linexpr1_set_list(&expr, AP_COEFF_S_INT, 1, indVar, AP_END);
    ap_lincons1_array_set(&array, 0, &cons);
    expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
    cons = ap_lincons1_make(AP_CONS_SUP, &expr, NULL);
    ap_linexpr1_set_list(&expr, AP_COEFF_S_INT, -1, indVar, AP_CST_S_INT,
            size, AP_END);
    ap_lincons1_array_set(&array, 1, &cons);
    abst = ap_abstract1_of_lincons_array(man, env, &array);
    ap_abstract1_fprint(stdout, man, &abst);
    ap_lincons1_array_clear(&array);
    ap_linexpr1_clear(&expr);
    return abst;
  }
#endif

    bool satisfies_constraint(char *var, compare_t op, int c) {
        ap_lincons1_t cons = create_linexp_constraint(var, op, NULL, c);
        return ap_abstract1_sat_lincons(man, &abst, &cons);
    }

    ap_abstract1_t meet_constraint(char *var, compare_t op, char *y, int c) {
        ap_lincons1_t cons;
        ap_abstract1_t a, b;
  
        switch(op) {
        case EQUAL:
        case GREATER_EQUAL:
        case LESS:
            cons = create_linexp_constraint(var, op, y, c);
            break;
        case NOT_EQUAL:
            // Instead of using != we do: join(meet(ABS, x<c), meet(ABS, x>c)).
            // If (x=[c, c]) then the result will be bottom.
            a = meet_constraint(var, LESS, y, c);
            b = meet_constraint(var, GREATER_EQUAL, y, c + 1);
            return ap_abstract1_join(man, false, &a, &b);
        default:
            exit(1);
        }
  
        ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
        ap_lincons1_array_set(&array, 0, &cons);
        ap_abstract1_t temp = ap_abstract1_of_lincons_array(man, env, &array);
        ap_lincons1_array_clear(&array);
  
        return ap_abstract1_meet(man, false, &abst, &temp);
    }

    ap_lincons1_t create_linexp_constraint(char *x, compare_t op, char *y,
            int c) {
        typedef struct {
            int x_sign;
            int rhs_sign;
            ap_constyp_t constyp;
        } constraint_param_t;

        static std::map<compare_t, constraint_param_t> op2params = {
            // constraint x = E (x - E = 0)
            { EQUAL,              { 1, -1, AP_CONS_EQ } },
            // constraint x >= E (x - E >= 0)
            { GREATER_EQUAL,   { 1, -1, AP_CONS_SUPEQ } },
            // constraint x < E (-1*x + E > 0)
            { LESS,               { -1, 1, AP_CONS_SUP } },
        };

        constraint_param_t p = op2params[op];

        ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
        ap_lincons1_t cons = ap_lincons1_make(p.constyp, &expr, NULL);
        if (y) {
            ap_lincons1_set_list(&cons,
                    AP_COEFF_S_INT, p.x_sign, x,
                    AP_COEFF_S_INT, p.rhs_sign, y,
                    AP_CST_S_INT, p.rhs_sign * c,
                    AP_END);
        } else {
            ap_lincons1_set_list(&cons,
                    AP_COEFF_S_INT, p.x_sign, x,
                    AP_CST_S_INT, p.rhs_sign * c,
                    AP_END);
        }

        return cons;
    }
};

class TransferFunctions : public clang::StmtVisitor<TransferFunctions> {
    BlockApronContext *blkApronCtx;
    bool error;

public:
    TransferFunctions(BlockApronContext *blkApronCtx) {
        this->blkApronCtx = blkApronCtx;
        this->error = false;
    }

    void VisitArraySubscriptExpr(clang::ArraySubscriptExpr *AS) {
      // find array name and size
      clang::DeclRefExpr *DR;
      if (!(DR = clang::dyn_cast<clang::DeclRefExpr>(
                      AS->getBase()->IgnoreImpCasts()))) {
          printf("Can't handle complex array expressions:\n\t%s\n",
                  toString(AS));
          exit(1);
      }
  
      const char *arr = DR->getDecl()->getNameAsString().c_str();
      int size = variables.arraySize(arr);
  
      clang::Expr *ind = AS->getIdx();
      // Both size and index are literals. No need for abstraction:
      if (clang::IntegerLiteral *IL =
              clang::dyn_cast<clang::IntegerLiteral>(ind)) {
          int val = (int)*IL->getValue().getRawData();
          if (val < 0 || val >= size) {
              printf("** Index out of bounds error: Array %s, size %d, index "
                      "%d\n", arr, size, val);
              printf("\t%s\n", toString(AS));
              error = true;
          }
      // Size is a literal but the index is an abstract value:
      } else if (clang::DeclRefExpr *DR =
              clang::dyn_cast<clang::DeclRefExpr>(ind->IgnoreImpCasts())) {
          char *varInd = variables.find(
                  DR->getDecl()->getNameAsString().c_str());
          if (!blkApronCtx->isIndexInBound(varInd, size)) {
              printf("** Index out of bounds error: Index %s, Array %s, size "
                      "%d\n", toString(DR), arr, size);
              error = true;
          }
      } else {
          printf("Can't handle compound expressions as array indexes:\n\t%s\n",
                  toString(AS));
          exit(1);
      }
//      else if (clang::ImplicitCastExpr *CE =
//              clang::dyn_cast<clang::ImplicitCastExpr>(ind)) {
//        Visit(CE);
//        char *indVar = variables.getLastVar();
//        analysisCtx->addArrayIndex(indVar, size);
//      }
//      variables.toggleCollectingVars(false);
    }

    void VisitBinaryOperator(clang::BinaryOperator *BO) {
        // handle all arithmetic assignments including compound ('+=', etc)
        clang::BinaryOperator::Opcode opcode = BO->getOpcode();
        if (!(opcode >= clang::BO_Assign && opcode <= clang::BO_SubAssign)) {
//            printf("Can't handle compound operations:\n");
//            BO->dump();
            Visit(BO->getLHS());
            Visit(BO->getRHS());
            return;
        }
  
        clang::Expr *lhs = BO->getLHS();
        clang::DeclRefExpr *DRleft = clang::dyn_cast<clang::DeclRefExpr>(lhs);
        if (!DRleft) {
            printf("Can handle only assignment to non-compound variables:\n\t%s"
                    "\n", toString(BO));
            Visit(lhs);
            return;
        }
  
        char *x = variables.find(DRleft->getDecl()->getNameAsString().c_str());
  
        clang::Expr *rhs = BO->getRHS();
        // RHS is a literal: x=c, x+=c, x-=c, ...
        if (clang::IntegerLiteral *IL =
                clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
            int c = (int)*IL->getValue().getRawData();
            switch(opcode) {
            case clang::BO_Assign: 
                blkApronCtx->assignConst(x, c);
                break;
            case clang::BO_MulAssign:
                // x := c*x + 0
                blkApronCtx->assignLinearExpression(x, c, x, 0);
                break;
                // x := (1/c)*x + 0
            case clang::BO_DivAssign:
                blkApronCtx->assignLinearExpression(x, 1/c, x, 0);
                break;
            case clang::BO_AddAssign:
                // x := 1*x + c
                blkApronCtx->assignLinearExpression(x, 1, x, c);
                break;
            case clang::BO_SubAssign:
                // x := -1*x + c
                blkApronCtx->assignLinearExpression(x, -1, x, c);
                break;
            default:
                printf("Can't handle operation %d\n", opcode);
                exit(1);
            }
            // RHS is a variable: x=y
        } else if (clang::DeclRefExpr *DRright =
                clang::dyn_cast<clang::DeclRefExpr>(rhs->IgnoreImpCasts())) {
            char *y = variables.find(
                    DRright->getDecl()->getNameAsString().c_str());
            switch(opcode) {
            case clang::BO_Assign: 
                // x := 1*y + 0
                blkApronCtx->assignLinearExpression(x, 1, y, 0);
                break;
                // XXX: Hnadle all the cases...
            default:
                printf("Can't handle compound assignment operator \n\t%s\n",
                       toString(BO));
                exit(1);
            }
            // Can't handle more than one expression in RHS
        } else {
            printf("Can't assign a compound right hand side: \n\t%s (%s)\n",
                    toString(rhs), rhs->getStmtClassName());
            Visit(rhs);
            return;
        }
    }
//      } else if (clang::DeclRefExpr *DRE =
//              clang::dyn_cast<clang::DeclRefExpr>(rhs)) {
//          Visit(DRE);
//      } else if (clang::ImplicitCastExpr *CE =
//              clang::dyn_cast<clang::ImplicitCastExpr>(rhs)) {
//          Visit(CE);
//      } else if (clang::BinaryOperator *BO2 =
//              clang::dyn_cast<clang::BinaryOperator>(rhs)) {
//          Visit(BO2);        
//      }
//
//              std::vector<char *> used = variables.getUsedVars();
//              std::vector<int> coeffs = variables.getVarCoeffs();
//              
//              if (used.size() > 0) {
//                analysisCtx->assignExpr(var, &used, &coeffs);
//              }
//              variables.toggleCollectingVars(false);
//      else {
//          printf("Handling opcode %d\n", opcode-clang::BO_PtrMemD);
//          // collect variables and coeffs of expr
//          clang::ImplicitCastExpr *CEL =
//              clang::dyn_cast<clang::ImplicitCastExpr>(BO->getLHS());
//          clang::ImplicitCastExpr *CER =
//              clang::dyn_cast<clang::ImplicitCastExpr>(BO->getRHS());
//          clang::IntegerLiteral *ILL =
//              clang::dyn_cast<clang::IntegerLiteral>(BO->getLHS());
//          clang::IntegerLiteral *ILR =
//              clang::dyn_cast<clang::IntegerLiteral>(BO->getLHS());
//          
//          if (CEL) {
//            Visit(CEL);
//            if (ILR) {
//              int val = (int)*ILR->getValue().getRawData();
//              variables.addVarCoeff(val);
//            } else {
//              variables.addVarCoeff(1);
//            }        
//          }              
//          if (CER) {
//            Visit(CER);
//            if (ILL) {
//              int val = (int)*ILL->getValue().getRawData();
//              if (opcode == clang::BO_Mul || opcode == clang::BO_Div) {
//                variables.addVarCoeff(val);
//              } else {
//                variables.addVarCoeff(1);
//              }
//            }
//          }        

    void VisitUnaryOperator(clang::UnaryOperator *UO) {
        if (UO->isIncrementDecrementOp()) {
            clang::Expr *sub = UO->getSubExpr();
            if (clang::DeclRefExpr *DR = 
                clang::dyn_cast<clang::DeclRefExpr>(sub)) {
                char *x = variables.find(
                        DR->getDecl()->getNameAsString().c_str());
                if (UO->isIncrementOp())
                    // x := 1*x + 1
                    blkApronCtx->assignLinearExpression(x, 1, x, 1);
                else
                    // x := 1*x + -1
                    blkApronCtx->assignLinearExpression(x, 1, x, -1);
            }
        }
    }

    // XXX: ArraySubscriptExpr won't be visited without this. Why?
    void VisitImplicitCastExpr(clang::ImplicitCastExpr *IC) {
        Visit(IC->getSubExpr());
    }
   
    bool foundError() {
        return error;
    }
};

class BlockAnalysis {
    // A container for BlockApronContext objects
    std::unordered_map<const clang::CFGBlock *, BlockApronContext *>
        block2Ctx;
    bool error;

public:
    BlockAnalysis() {
        error = false;
    }

    void add(const clang::CFGBlock *block) {
        block2Ctx[block] = new BlockApronContext(block, &block2Ctx);
    }

    ~BlockAnalysis() {
        for (std::unordered_map<const clang::CFGBlock *,
                BlockApronContext *>::iterator I = block2Ctx.begin(),
                E = block2Ctx.end(); I != E; ++I) {
            BlockApronContext *ctx = (*I).second;
            if (!ctx)
                continue;

            delete ctx;
        }
    }

    bool runOnBlock(const clang::CFGBlock *block) {
        BlockApronContext *blkApronCtx = block2Ctx[block];
        if (!blkApronCtx->updateEntryValue())
            return false;

        printf("Some abstract values changed\n");
        // Apply the transfer function.
        TransferFunctions tf(blkApronCtx);

        for (clang::CFGBlock::const_iterator I = block->begin(),
                E = block->end(); I != E; ++I) {
          if (clang::Optional<clang::CFGStmt> cs = I->getAs<clang::CFGStmt>()) {
                tf.Visit(const_cast<clang::Stmt*>(cs->getStmt()));
                if (tf.foundError()) {
                    error = true;
                    break;
                }
          }
        }
    
        printf("After transfer functions, Before update successors:\n");
        blkApronCtx->print();
        blkApronCtx->updateSuccessors();
    
        return true;
    }

    bool foundError() {
        return error;
    }

    void print() {
        printf("Each block abstract value:\n");
        for (std::unordered_map<const clang::CFGBlock *,
                BlockApronContext *>::iterator I = block2Ctx.begin(),
                E = block2Ctx.end(); I != E; ++I) {
            const clang::CFGBlock *block = (*I).first;
            BlockApronContext *ctx = (*I).second;
            printf("[B%d] ", block->getBlockID());
            ctx->print();
        }
    }
};

static void VisualizeCfg(clang::AnalysisDeclContext *ac, clang::CFG *cfg) {
  switch (printCFG) {
  case 1:
    ac->dumpCFG(false);
    break;
  case 2:
    // Child process, pops up a graphic tool to show the graph
    if (fork() == 0) {
      cfg->viewCFG(clang::LangOptions());
      exit(0);
    }
    break;
  }
}

static void analyze(clang::Decl *D) {
    variables.init(D);

    clang::AnalysisDeclContext ac(/* AnalysisDeclContextManager */ nullptr, D);
    clang::CFG *cfg;
    if (!(cfg = ac.getCFG()))
        exit(1);

    VisualizeCfg(&ac, cfg);

    BlockAnalysis blockAnalysis;
    for (clang::CFG::const_iterator BI = cfg->begin(), BE = cfg->end();
            BI != BE; ++BI) {
        const clang::CFGBlock *block = *BI;

        blockAnalysis.add(block);
    }

    clang::ForwardDataflowWorklist worklist(*cfg, ac);
    worklist.enqueueBlock(&cfg->getEntry());

    while (const clang::CFGBlock *block = worklist.dequeue()) {
        // Did the block change?
        bool changed = blockAnalysis.runOnBlock(block);

        if (blockAnalysis.foundError()) {
            goto Error;
        }
        
        if (changed) {
            worklist.enqueueSuccessors(block);
        }
    }
    printf("Fixed point reached\n");
Error:
    blockAnalysis.print();
}

class ExampleVisitor : public clang::RecursiveASTVisitor<ExampleVisitor> {
private:
    clang::ASTContext *astContext; // used for getting additional AST info

public:
    explicit ExampleVisitor(clang::CompilerInstance *CI) 
      : astContext(&(CI->getASTContext())) // initialize private members
    { }

    virtual bool VisitFunctionDecl(clang::FunctionDecl *func) {
        std::string funcName = func->getNameInfo().getName().getAsString();
        llvm::outs() << funcName << "\n";        
        return true;
    }
};

class ExampleASTConsumer : public clang::ASTConsumer {
private:
    ExampleVisitor *visitor; // doesn't have to be private

public:
    // override the constructor in order to pass CI
    // initialize the visitor
    explicit ExampleASTConsumer(clang::CompilerInstance *CI) : visitor(
            new ExampleVisitor(CI)) {
    }

    // override this to call our ExampleVisitor on each top-level Decl
    virtual bool HandleTopLevelDecl(clang::DeclGroupRef DG) {
        if (!DG.isSingleDecl()) {
           return true;
        }

        clang::Decl *D = DG.getSingleDecl();
        const clang::FunctionDecl *FD = clang::dyn_cast<clang::FunctionDecl>(D);
        // Skip other functions
        if (!FD || FD->getName().str().compare(funcToAnalyze)) {
            return true;
        }

        analyze(D);
        
        // recursively visit each AST node in Decl "D"
//        visitor->TraverseDecl(D); 

        return true;
    }
};

class ExampleFrontendAction : public clang::ASTFrontendAction {
public:
    virtual std::unique_ptr<clang::ASTConsumer>
        CreateASTConsumer(clang::CompilerInstance &CI, clang::StringRef file) {
        // pass CI pointer to ASTConsumer
        return llvm::make_unique<ExampleASTConsumer>(&CI);
    }
};

int main(int argc, const char **argv) {
    if (argc < 2) {
        printf("no file name entered\n");
        return 1;
    }

    if (argc > 2)
        printCFG = atoi(&argv[2][0]);

    if (argc > 3)
        funcToAnalyze = argv[3];
    else
        funcToAnalyze = "main";
    printf("Will analyze function %s\n", funcToAnalyze);

    // Read file contents into a char array
    std::ifstream in(argv[1]);
    std::string contents((std::istreambuf_iterator<char>(in)), 
            std::istreambuf_iterator<char>());

    // Interval package
    man = box_manager_alloc();
    printf("******************************\n");
    printf("Apron: Library %s, version %s\n", man->library, man->version);
    printf("******************************\n");

    int ret = !clang::tooling::runToolOnCode(new ExampleFrontendAction,
            contents.c_str());

    ap_manager_free(man);

    return ret;
}
