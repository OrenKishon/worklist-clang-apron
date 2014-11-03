
#include <iostream>     // std::cout
#include <fstream>      // std::ifstream
#include <string>
#include <unistd.h>     // fork()
#include <stdlib.h>     // atoi()
#include <unordered_map> 

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

#define MAX_NUMBER_VARS 16
#define MAX_VAR_NAME_LEN 31

static int printCFG;
static const char *funcToAnalyze;
static ap_manager_t* man;
static ap_environment_t *env;

class ApronHelper {
public:
  /* var1 := expr (vars + integers) */ 
  static ap_abstract1_t assignExpr(ap_abstract1_t abst, char *var,
				   std::vector<std::string> *exprItems,
				   std::vector<int> *coeffs) {
    // ap_linexpr1_make() destroys contents of *var 
    char dest[strlen(var) + 1];
    strcpy(dest, var);    
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, exprItems->size() + 1);    
    ap_scalar_t *scalar = ap_scalar_alloc_set_double(1);    
    char *src[strlen(var) + 1];
    ap_linexpr1_set_coeff_scalar(&expr, src, scalar);
    assert(exprItems->size() == coeffs->size());
    for(unsigned int i = 0; i < exprItems->size(); ++i) {
      int len = exprItems->at(i).size() + 1;
      char *var = new char[len];
      strcpy(var, exprItems->at(i).c_str()); 
      scalar = ap_scalar_alloc_set_double(coeffs->at(i));
      ap_linexpr1_set_coeff_scalar(&expr, var, scalar);
      delete var;
    }
  
    abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
    ap_scalar_free(scalar);
    ap_linexpr1_clear(&expr);    

    return abst;
  }

  /* var1 := var2 */ 
  static ap_abstract1_t assignVar(ap_abstract1_t abst, char *var1,
				  char *var2) {
    // ap_linexpr1_make() destroys contents of *var 
    char dest[strlen(var1) + 1];
    char src[strlen(var2) + 1];
    strcpy(dest, var1);
    strcpy(src, var2);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
    ap_linexpr1_set_list(&expr,
			AP_COEFF_S_INT,1,src,
			AP_END);
 
    abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
    ap_linexpr1_clear(&expr);    

    return abst;
  } 

  /* var := c */
  static ap_abstract1_t assignConst(ap_abstract1_t abst, char *var,
				    int c) {
    // ap_linexpr1_make() destroys contents of *var
    char dest[strlen(var) + 1];
    strcpy(dest, var);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
    ap_linexpr1_set_list(&expr,
			 AP_CST_S_INT, c,
			 AP_END);
    abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
    ap_linexpr1_clear(&expr);
    return abst;
  }

  // var := x + c
  static ap_abstract1_t assignVarPlusInt(ap_abstract1_t abst, char *var,
					 char *x, int c) {
    // ap_linexpr1_make() destroys contents of *var
    char src[strlen(x) + 1];
    strcpy(src, x);
    char dest[strlen(var) + 1];
    strcpy(dest, var);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_linexpr1_set_list(&expr,
			 AP_COEFF_S_INT, 1, src,
			 AP_CST_S_INT, c,
			 AP_END);
    abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
    ap_linexpr1_clear(&expr);
    return abst;
  }

  // var := x * c
  static ap_abstract1_t assignVarMulInt(ap_abstract1_t abst, char *var,
					 char *x, int c) {
    // ap_linexpr1_make() destroys contents of *var
    char src[strlen(x) + 1];
    strcpy(src, x);
    char dest[strlen(var) + 1];
    strcpy(dest, var);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_linexpr1_set_list(&expr,
			 AP_COEFF_S_INT, c, src,
			 AP_END);
    abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
    ap_linexpr1_clear(&expr);
    return abst;
  }

  // meet (intersect) constraint x < c (-1*x + c > 0)
  static ap_abstract1_t meet_constraint_lt(ap_abstract1_t *abst,
					   char *x, int c) {
    return meet_constraint(abst, x, c, AP_CONS_SUP, -1, 1);
  }

  // meet (intersect) constraint x >= c (x - c >= 0)
  static ap_abstract1_t meet_constraint_ge(ap_abstract1_t *abst,
					   char *x, int c) {
    return meet_constraint(abst, x, c, AP_CONS_SUPEQ, 1, -1);
  }

  // meet (intersect) constraint x != c (x - c != 0)
  static ap_abstract1_t meet_constraint_ne(ap_abstract1_t *abst,
					   char *x, int c) {
    // return meet_constraint(abst, x, c, AP_CONS_DISEQ, 1, -1);
    // Instead of using '!=' we do: join(meet(ABS, x<c), meet(ABS, x>c)).
    // If (x=[c, c]) then the result will be bottom.
    ap_abstract1_t a = meet_constraint_lt(abst, x, c);
    ap_abstract1_t b = meet_constraint_ge(abst, x, c + 1);
    return ap_abstract1_join(man, false, &a, &b);
  }

  // meet (intersect) constraint x = c (x - c = 0)
  static ap_abstract1_t meet_constraint_eq(ap_abstract1_t *abst,
					   char *x, int c) {
    return meet_constraint(abst, x, c, AP_CONS_EQ, 1, -1);
  }

private:
  static ap_abstract1_t meet_constraint(ap_abstract1_t *abst, char *var,
					int c, ap_constyp_t constyp, int coeff, int scallar_sign) {
    // ap_linexpr1_make() destroys contents of *var
    ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
    ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
    ap_lincons1_t cons = ap_lincons1_make(constyp, &expr, NULL);
    ap_lincons1_set_list(&cons,
			 AP_COEFF_S_INT, coeff, var,
			 AP_CST_S_INT, scallar_sign * c,
			 AP_END);
    ap_lincons1_array_set(&array, 0, &cons);
    ap_abstract1_t temp = ap_abstract1_of_lincons_array(man, env, &array);
    ap_lincons1_array_clear(&array);
    ap_abstract1_t res = ap_abstract1_meet(man, false, abst, &temp);
    return res;
  }
};

class Variables {
  clang::DeclContext *dc;
  char name_of_dim[MAX_NUMBER_VARS][MAX_VAR_NAME_LEN + 1];
  int size;
  bool collectVariables;

  // store varoables and corresponding coeeficients in expr
  std::vector<std::string> usedVars;
  std::vector<int> varCoeffs;

public:
  Variables() {
    size = 0;
  }

  void init(clang::Decl *D) {
    dc = clang::cast<clang::DeclContext>(D);
    for (clang::DeclContext::specific_decl_iterator<clang::VarDecl>
	   I(dc->decls_begin()), E(dc->decls_end()); I != E; ++I) {
      const clang::VarDecl *vd = *I;
      if (isTrackedVar(vd))
	++size;
    }
    printf("Will track %d vars\n", size);
    assert(size <= MAX_NUMBER_VARS);
    int ind = 0;
    for (clang::DeclContext::specific_decl_iterator<clang::VarDecl>
	   I(dc->decls_begin()), E(dc->decls_end()); I != E; ++I) {
      const clang::VarDecl *vd = *I;
      if (!isTrackedVar(vd)) {
	continue;
      }
      const char *varName = vd->getNameAsString().c_str();
      assert(strlen(varName) <= MAX_VAR_NAME_LEN);
      strcpy(name_of_dim[ind], varName);
      printf("Added var %s (%d) to analysis\n", name_of_dim[ind], ind);
      ++ind;
    }
    ap_var_t tempCastArray[size];
    for (int i = 0; i < size; ++i)
      tempCastArray[i] = (ap_var_t)name_of_dim[i];
    // Assuming integers only;
    env = ap_environment_alloc(tempCastArray, size, NULL, 0);
  }

  ~Variables() {
    if (env)
      ap_environment_free(env);
  }

  bool isTrackedVar(const clang::VarDecl *vd) {
    if (vd->isLocalVarDecl() && !vd->hasGlobalStorage() &&
	!vd->isExceptionVariable() && !vd->isInitCapture() &&
	vd->getDeclContext() == dc) {
      clang::QualType ty = vd->getType();
      return ty->isScalarType() || ty->isVectorType();
    }
    return false;
  }

  void addUsedVar(char *vd) {        
    if(!collectVariables) {
      return;
    }
    char var[strlen(vd) + 1];
    strcpy(var, vd);    
    usedVars.push_back(var);
  }

  const std::vector<std::string> getUsedVars() {
    return usedVars;
  }

  void toggleCollectingVars(bool enable) {
    usedVars.clear();
    varCoeffs.clear();
    collectVariables = enable;
  }

  void addVarCoeff(int coeff) {
    if(!collectVariables) {
      return;
    }
    varCoeffs.push_back(coeff);
  }

  const std::vector<int> getVarCoeffs() {
    return varCoeffs;
  }  

};

static Variables variables;

// This context exists for every block
class BlockAnalysisContext {
  const clang::CFGBlock *block;
  // A reference to the global map
  std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *>
  *block2Ctx;
  // Abstract values
  std::unordered_map<const clang::CFGBlock *, ap_abstract1_t> pred2Abs;
  ap_abstract1_t abst;
  // Successors
  const clang::CFGBlock *succ[2];
public:
  BlockAnalysisContext(const clang::CFGBlock *block,
		       std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *>
		       *block2Ctx) {
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
    // Single successor: just pass this block's exit value as the
    // successor's entry value
    if (!block->getTerminator()) {
      ((*block2Ctx)[succ[0]])->pred2Abs[block] = abst;
      return;
    }
    // Two successors: first for 'then', second for 'else'
    ap_abstract1_t absThen, absElse;
    const clang::Stmt *cond = block->getTerminatorCondition();
    if (const clang::BinaryOperator *BO =
	clang::dyn_cast<clang::BinaryOperator>(cond)) {
      if (!BO->isComparisonOp())
	return;
      clang::Expr *lhs = BO->getLHS()->IgnoreImpCasts();
      if (clang::DeclRefExpr *DR =
	  clang::dyn_cast<clang::DeclRefExpr>(lhs)) {
	const char *xp = DR->getDecl()->getNameAsString().c_str();
	char x[strlen(xp) + 1];
	strcpy(x, xp);
	clang::Expr *rhs = BO->getRHS();
	if (clang::IntegerLiteral *IL =
	    clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
	  int c = (int)*IL->getValue().getRawData();
	  switch (BO->getOpcode()) {
	  case clang::BO_LT:
	    absThen = ApronHelper::meet_constraint_lt(&abst, x, c);
	    absElse = ApronHelper::meet_constraint_ge(&abst, x, c);
	    break;
	  case clang::BO_NE:
	    absThen = ApronHelper::meet_constraint_ne(&abst, x, c);
	    absElse = ApronHelper::meet_constraint_eq(&abst, x, c);
	    break;
	  default:
	    break;
	  }
	}
      }
    }
    printf("Then branch:\n");
    ap_abstract1_fprint(stdout, man, &absThen);
    printf("Else branch:\n");
    ap_abstract1_fprint(stdout, man, &absElse);
    (*block2Ctx)[succ[0]]->pred2Abs[block] = absThen;
    (*block2Ctx)[succ[1]]->pred2Abs[block] = absElse;
  }

    void assignExpr(char* var, std::vector<std::string> *exprItems,
		    std::vector<int> *coeffs) {
        abst = ApronHelper::assignExpr(abst, var, exprItems, coeffs);
    }

    void assignVar(char* var1, char* var2) {
        abst = ApronHelper::assignVar(abst, var1, var2);
    }

    void assignConst(char *var, int val) {
        abst = ApronHelper::assignConst(abst, var, val);
    }

    void increment(char *var) {
        abst = ApronHelper::assignVarPlusInt(abst, var, var, 1);
    }

    void deccrement(char *var) {
        abst = ApronHelper::assignVarPlusInt(abst, var, var, -1);
    }

    void addConst(char *var, int val) {
        abst = ApronHelper::assignVarPlusInt(abst, var, var, val);
    }

    void subConst(char *var, int val) {
        abst = ApronHelper::assignVarPlusInt(abst, var, var, -val);
    }

    void mulConst(char *var, int val) {
        abst = ApronHelper::assignVarMulInt(abst, var, var, val);
    }

    void divConst(char *var, int val) {
        abst = ApronHelper::assignVarMulInt(abst, var, var, 1/val);
    }

    void print() {
        ap_abstract1_fprint(stdout, man, &abst);
    }
};

class TransferFunctions : public clang::StmtVisitor<TransferFunctions> {
    BlockAnalysisContext *analysisCtx;

public:
  TransferFunctions(BlockAnalysisContext *analysisCtx) {
      this->analysisCtx = analysisCtx;
  }

//  void VisitBlockExpr(BlockExpr *be);
//  void VisitCallExpr(CallExpr *ce);

  void VisitDeclRefExpr(clang::DeclRefExpr *DR) {
    const char *varp = DR->getDecl()->getNameAsString().c_str();        
    char var[strlen(varp) + 1];
    strcpy(var, varp);
    variables.addUsedVar(var);
  }

//  void VisitObjCForCollectionStmt(ObjCForCollectionStmt *FS);
//  void VisitObjCMessageExpr(ObjCMessageExpr *ME);

  void VisitIntegerLiteral(clang::IntegerLiteral *IL) {
  }

  void VisitBinaryOperator(clang::BinaryOperator *BO) {
      /// handle all binary operations, including compound assignments (+= etc)
      clang::BinaryOperator::Opcode opcode = BO->getOpcode();
      if (opcode >= clang::BO_Assign && opcode <= clang::BO_SubAssign) {
            clang::Expr *lhs = BO->getLHS();
            if (clang::DeclRefExpr *DR =
                    clang::dyn_cast<clang::DeclRefExpr>(lhs)) {
                const char *varp = DR->getDecl()->getNameAsString().c_str();
                char var[strlen(varp) + 1];
                strcpy(var, varp);
                clang::Expr *rhs = BO->getRHS();
   	        variables.toggleCollectingVars(true);	
                if (clang::IntegerLiteral *IL =
                        clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
                    int val = (int)*IL->getValue().getRawData();
		    switch(opcode) {
		    case clang::BO_Assign: 
                      analysisCtx->assignConst(var, val);
		      break;
		    case clang::BO_MulAssign:
		      analysisCtx->mulConst(var, val);
		      break;
		    case clang::BO_DivAssign:
		      analysisCtx->divConst(var, val);
		      break;
		    case clang::BO_AddAssign:
		      analysisCtx->addConst(var, val);
		      break;
		    case clang::BO_SubAssign:
		      analysisCtx->subConst(var, val);
		      break;
		    default:
		      /* skip */
		      break;
		    }
		} else if(clang::DeclRefExpr *DRE = clang::dyn_cast<clang::DeclRefExpr>(rhs)) {
		    Visit(DRE);
		    // handle assignment
		    //const char *varp2 = DRE->getDecl()->getNameAsString().c_str();
                    //char var2[strlen(varp) + 1];
                    //strcpy(var2, varp2);
		    //variables.addUsedVar(var2);
		    //analysisCtx->assignVar(var, var2);
		} else if(clang::ImplicitCastExpr *CE = clang::dyn_cast<clang::ImplicitCastExpr>(rhs)) {
 	            Visit(CE);
                 } else if(clang::BinaryOperator *BO2 = clang::dyn_cast<clang::BinaryOperator>(rhs)) {
 	            Visit(BO2);
 		}

  	        std::vector<std::string> used = variables.getUsedVars();
  	        std::vector<int> coeffs = variables.getVarCoeffs();
	        if(used.size() == 1) { 
                  const char *varp2 = used[0].c_str();
                  char var2[strlen(varp) + 1];
                  strcpy(var2, varp2);	        
	          analysisCtx->assignVar(var, var2);
	        } else if(used.size() > 1) {
		  analysisCtx->assignExpr(var, &used, &coeffs);
	        }
	        variables.toggleCollectingVars(false);
	    }
      } else {
	  // collect variables of expr
	  clang::ImplicitCastExpr *CE1 = clang::dyn_cast<clang::ImplicitCastExpr>(BO->getLHS());
	  clang::ImplicitCastExpr *CE2 = clang::dyn_cast<clang::ImplicitCastExpr>(BO->getRHS());
	  clang::IntegerLiteral *IL1 = clang::dyn_cast<clang::IntegerLiteral>(BO->getLHS());
	  clang::IntegerLiteral *IL2 = clang::dyn_cast<clang::IntegerLiteral>(BO->getLHS());
	  if(CE1) {
	    Visit(CE1);
	    if(IL2) {
              int val = (int)*IL2->getValue().getRawData();
	      variables.addVarCoeff(val);
	    } else {
	      variables.addVarCoeff(1);
	    }
          }	      
          if(CE2) {
	    Visit(CE2);
	    if(IL1) {
              int val = (int)*IL1->getValue().getRawData();
	      variables.addVarCoeff(val);
	    } else {
	      variables.addVarCoeff(1);
	    }
          }	
      }
    }

    void VisitUnaryOperator(clang::UnaryOperator *UO) {
        if (UO->isIncrementDecrementOp()) {
            clang::Expr *sub = UO->getSubExpr();
            if (clang::DeclRefExpr *DR = 
                clang::dyn_cast<clang::DeclRefExpr>(sub)) {
                const char *varp = DR->getDecl()->getNameAsString().c_str();
                char var[strlen(varp) + 1];
                strcpy(var, varp);
		if(UO->isIncrementOp()) { 
                    analysisCtx->increment(var);
                } else {
		    analysisCtx->deccrement(var);
        	}
            }
        }
    }
 
    void VisitImplicitCastExpr(clang::ImplicitCastExpr *IC) {
      if(clang::DeclRefExpr *DR = clang::dyn_cast<clang::DeclRefExpr>(IC->getSubExpr())) {
 	 Visit(DR);
      }
    }
   
    void VisitDeclStmt(clang::DeclStmt *DS) {
      for (clang::Decl *DI : DS->decls()) {
        if (clang::VarDecl *VD = clang::dyn_cast<clang::VarDecl>(DI)) {
          const char *varp = VD->getNameAsString().c_str();
          char var[strlen(varp) + 1];
          strcpy(var, varp);
	  if(VD->hasInit()) {
            clang::Expr *init = VD->getInit();
	    if(clang::IntegerLiteral *IL =
	      clang::dyn_cast<clang::IntegerLiteral>(init)) {
              int val = (int)*IL->getValue().getRawData();
              analysisCtx->assignConst(var, val);
	    } else {
	      variables.toggleCollectingVars(true);
              Visit(init);
	      std::vector<std::string> used = variables.getUsedVars();
	      std::vector<int> coeffs = variables.getVarCoeffs();
	      if(used.size() == 1) { 
                const char *varp2 = used[0].c_str();
                char var2[strlen(varp) + 1];
                strcpy(var2, varp2);	        
	        analysisCtx->assignVar(var, var2);
	      } else if(used.size() > 1) {
		analysisCtx->assignExpr(var, &used, &coeffs);
	      }
	      variables.toggleCollectingVars(false);
	    }
	 }
       } 
     }
    }

};

class BlockAnalysis {
    // A container for BlockAnalysisContext objects
    std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *> block2Ctx;

public:
    void add(const clang::CFGBlock *block) {
        block2Ctx[block] = new BlockAnalysisContext(block, &block2Ctx);
    }

    ~BlockAnalysis() {
        for (std::unordered_map<const clang::CFGBlock *,
                BlockAnalysisContext *>::iterator I = block2Ctx.begin(),
                E = block2Ctx.end(); I != E; ++I) {
            BlockAnalysisContext *ctx = (*I).second;
            if (!ctx)
                continue;

            delete ctx;
        }
    }

    bool runOnBlock(const clang::CFGBlock *block) {
        BlockAnalysisContext *analysisCtx = block2Ctx[block];
        if (!analysisCtx->updateEntryValue())
            return false;

        printf("%d changed\n", block->getBlockID());
        // Apply the transfer function.
        TransferFunctions tf(analysisCtx);
    
        for (clang::CFGBlock::const_iterator I = block->begin(),
                E = block->end(); I != E; ++I) {
	  if (clang::Optional<clang::CFGStmt> cs = I->getAs<clang::CFGStmt>()) 
                tf.Visit(const_cast<clang::Stmt*>(cs->getStmt()));
        }
    
        analysisCtx->updateSuccessors();
    
        return true;
    }

    void print() {
        printf("Each block abstract value:\n");
        for (std::unordered_map<const clang::CFGBlock *,
                BlockAnalysisContext *>::iterator I = block2Ctx.begin(),
                E = block2Ctx.end(); I != E; ++I) {
            const clang::CFGBlock *block = (*I).first;
            BlockAnalysisContext *ctx = (*I).second;
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
        printf("\n[B%d]\n", block->getBlockID());
        bool changed = blockAnalysis.runOnBlock(block);
        
        if (changed) {
            printf("Enqueing: ");
            for (clang::CFGBlock::const_succ_iterator I = block->succ_begin(),
                    E = block->succ_end(); I != E; ++I) {
                printf("[B%d] ", (*I)->getBlockID());
            }
            printf("\n");
            worklist.enqueueSuccessors(block);
        }
    }
    printf("Fixed point reached\n");
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
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &CI,
            clang::StringRef file) {
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
