#include <iostream>     // std::cout
#include <fstream>      // std::ifstream
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
    /* var := c */
    static ap_abstract1_t assignConst(ap_abstract1_t abst, const char *var,
            int c) {
        // ap_linexpr1_make() destroys contents of *var 
        char dest[strlen(var) + 1];
        strcpy(dest, var);
        ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 1);
        ap_linexpr1_set_list(&expr,
                   AP_CST_S_INT, c,
                   AP_END);
        fprintf(stdout, "Assignement (side-effect) in abstract value of %s by "
               "expression:\n", dest);
        ap_linexpr1_fprint(stdout, &expr);    

        abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
        fprintf(stdout, "\n");
        ap_abstract1_fprint(stdout, man, &abst);
        ap_linexpr1_clear(&expr);    

        return abst;
    }

    // var := x + c
    static ap_abstract1_t assignVarPlusInt(ap_abstract1_t abst, const char *var,
            const char *x, int c) {
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
        fprintf(stdout, "Assignement (side-effect) in abstract value of %s by "
               "expression:\n", dest);
        ap_linexpr1_fprint(stdout, &expr);    

        abst = ap_abstract1_assign_linexpr(man, true, &abst, dest, &expr, NULL);
        fprintf(stdout, "\n");
        ap_abstract1_fprint(stdout, man, &abst);
        ap_linexpr1_clear(&expr);    

        return abst;
    }

    // meet (intersect) constraint x < c (-1*x + c > 0) 
    static ap_abstract1_t meet_constraint_lt(ap_abstract1_t *abst,
            const char *x, int c) {
        return meet_constraint(abst, x, c, AP_CONS_SUP, -1, 1);
    }    

    // meet (intersect) constraint x >= c (x - c >= 0)
    static ap_abstract1_t meet_constraint_ge(ap_abstract1_t *abst,
            const char *x, int c) {
        printf("1%s, %d\n", x, c);
        return meet_constraint(abst, x, c, AP_CONS_SUPEQ, 1, -1);
    }

    // meet (intersect) constraint x != c (x - c != 0)
    static ap_abstract1_t meet_constraint_ne(ap_abstract1_t *abst,
            const char *x, int c) {
        return meet_constraint(abst, x, c, AP_CONS_DISEQ, 1, -1);
    }

    // meet (intersect) constraint x = c (x - c = 0)
    static ap_abstract1_t meet_constraint_eq(ap_abstract1_t *abst,
            const char *x, int c) {
        return meet_constraint(abst, x, c, AP_CONS_EQ, 1, -1);
    }

private:
    static ap_abstract1_t meet_constraint(ap_abstract1_t *abst, const char *x,
            int c, ap_constyp_t constyp, int coeff, int scallar_sign) {
        // ap_linexpr1_make() destroys contents of *var 
        printf("%s, %d\n", x, c);
        char var[strlen(x) + 1];
        strcpy(var, x);
        printf("%s, %d\n", var, c);
        ap_lincons1_array_t array = ap_lincons1_array_make(env, 1);
        printf("X1%s, %d\n", x, c);
        ap_linexpr1_t expr = ap_linexpr1_make(env, AP_LINEXPR_SPARSE, 0);
        printf("X2%s, %d\n", x, c);
        ap_lincons1_t cons = ap_lincons1_make(constyp, &expr, NULL);
        printf("X3%s, %d\n", x, c);
        ap_lincons1_set_list(&cons, 
                AP_COEFF_S_INT, coeff, var,
                AP_CST_S_INT, scallar_sign * c,
                AP_END);
        printf("X4%s, %d\n", x, c);
        ap_lincons1_fprint(stdout, &cons); printf("\n");
        ap_lincons1_array_set(&array, 0, &cons);
        ap_abstract1_t temp = ap_abstract1_of_lincons_array(man, env, &array);
        printf("Condition abstract value, before meet:\n");
        ap_abstract1_fprint(stdout, man, &temp);
        ap_lincons1_array_clear(&array);

        printf("current abstract value, before meet:\n");
        ap_abstract1_fprint(stdout, man, abst);
        ap_abstract1_t res = ap_abstract1_meet(man, false, abst, &temp);
        printf("meet result:\n");
        ap_abstract1_fprint(stdout, man, &res);
        printf("XX%s, %d\n", x, c);
        return res;
    }
};

class Variables {
    // Maps a variable to an apron 'dimention' (index)
    std::unordered_map<const clang::VarDecl *, int> var2ApronDim;
    clang::DeclContext *dc;
    // If the names are not in static memory, ap_abstract1_fprint() fails
    char name_of_dim[MAX_NUMBER_VARS][MAX_VAR_NAME_LEN + 1];
    int size;
    
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
            var2ApronDim[vd] = ind;
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

//            pred2Abs[Pred] = (ap_abstract1_t *)malloc(sizeof(ap_abstract1_t));
//            *pred2Abs[Pred] = ap_abstract1_bottom(man, env);
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

//    ~BlockAnalysisContext() {
//        for (std::unordered_map<const clang::CFGBlock *, ap_abstract1_t *>::
//                iterator I = pred2Abs.begin(), E = pred2Abs.end();
//                I != E; ++I) {
//            ap_abstract1_t *absp = (*I).second;
//            if (!absp)
//                continue;
//
//            free(absp);
//        }
//    }
//
    void updateEntryValue() {
        // Entry block
        if (block->pred_empty()) {
            abst = ap_abstract1_top(man, env);
            return;
        }

        // Merge (join) all predeseccors exit values
        
        printf("%d) Merging preds' values. old value:", block->getBlockID());
        ap_abstract1_fprint(stdout, man, &abst);

        abst = ap_abstract1_bottom(man, env);
        for (auto it = pred2Abs.begin(); it != pred2Abs.end(); ++it) {
            ap_abstract1_t absPred = it->second;
            abst = ap_abstract1_join(man, false, &abst, &absPred);
        }
        printf("After merge:");
        ap_abstract1_fprint(stdout, man, &abst);
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
        printf("condition: %s\n", cond->getStmtClassName());
        if (const clang::BinaryOperator *BO =
                clang::dyn_cast<clang::BinaryOperator>(cond)) {
            if (!BO->isComparisonOp())
                return;
            clang::Expr *lhs = BO->getLHS()->IgnoreImpCasts();
            if (clang::DeclRefExpr *DR =
                    clang::dyn_cast<clang::DeclRefExpr>(lhs)) {
                const char *x = DR->getDecl()->getNameAsString().c_str();
                clang::Expr *rhs = BO->getRHS();
                if (clang::IntegerLiteral *IL =
                        clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
                    int c = (int)*IL->getValue().getRawData();
                    switch (BO->getOpcode()) {
                    case clang::BO_LT:
                        printf("op: %s < %d\n", x, c);
                        absThen = ApronHelper::meet_constraint_lt(&abst, x, c);
                        absElse = ApronHelper::meet_constraint_ge(&abst, x, c);
                        break;
                    case clang::BO_NE:
                        printf("op: %s != %d\n", x, c);
                        absThen = ApronHelper::meet_constraint_ne(&abst, x, c);
                        absElse = ApronHelper::meet_constraint_eq(&abst, x, c);
                        break;
                    default:
                        break;
                    }
                }
            }
        }
        cond->dump();

        printf("Abs value, 'then': ");
        ap_abstract1_fprint(stdout, man, &absThen);
        printf("Abs value, 'Else': ");
        ap_abstract1_fprint(stdout, man, &absElse);
        // XXX: Do something with cond
        (*block2Ctx)[succ[0]]->pred2Abs[block] = absThen;
        (*block2Ctx)[succ[1]]->pred2Abs[block] = absElse;
    }

    void printAbs() {
        printf("Abs value: ");
        ap_abstract1_fprint(stdout, man, &abst);
    }

    void assignConst(const char *var, int val) {
        abst = ApronHelper::assignConst(abst, var, val);
    }

    void increment(const char *var) {
        abst = ApronHelper::assignVarPlusInt(abst, var, var, 1);
    }
};

class TransferFunctions : public clang::StmtVisitor<TransferFunctions> {
    BlockAnalysisContext *analysisCtx;

public:
  TransferFunctions(BlockAnalysisContext *analysisCtx) {
      this->analysisCtx = analysisCtx;
//      printf("\tAbs value before merge:\n");
//      analysisCtx->printAbs();
//      printf("\tAbs value after merge:\n");
  }

//  void VisitBlockExpr(BlockExpr *be);
//  void VisitCallExpr(CallExpr *ce);
//  void VisitDeclRefExpr(DeclRefExpr *dr);
//  void VisitObjCForCollectionStmt(ObjCForCollectionStmt *FS);
//  void VisitObjCMessageExpr(ObjCMessageExpr *ME);
    void VisitBinaryOperator(clang::BinaryOperator *BO) {
        if (BO->getOpcode() == clang::BO_Assign) {
            printf("Assignment\n");
            clang::Expr *lhs = BO->getLHS();
            if (clang::DeclRefExpr *DR =
                    clang::dyn_cast<clang::DeclRefExpr>(lhs)) {
//                char *var = const_cast<char *>(
//                        DR->getDecl()->getNameAsString().c_str());
                const char *var = DR->getDecl()->getNameAsString().c_str();
                printf("%s = ", var);
                clang::Expr *rhs = BO->getRHS();
                if (clang::IntegerLiteral *IL =
                        clang::dyn_cast<clang::IntegerLiteral>(rhs)) {
                    int val = (int)*IL->getValue().getRawData();
                    printf("%d\n", val);
                    analysisCtx->assignConst(var, val);
                }
            }
        }
    }

    void VisitUnaryOperator(clang::UnaryOperator *UO) {
        if (UO->isIncrementDecrementOp()) {
            if (UO->isIncrementOp()) {
                printf("Increment\n");
                clang::Expr *sub = UO->getSubExpr();
                if (clang::DeclRefExpr *DR =
                        clang::dyn_cast<clang::DeclRefExpr>(sub)) {
                    const char *var = DR->getDecl()->getNameAsString().c_str();
                    printf("%s++\n", var);
                    analysisCtx->increment(var);
                }
            }
        }
    }
    
//    void VisitDeclStmt(clang::DeclStmt *DS) {
//        printf("DeclStmt:\n");
//        DS->getSingleDecl()->dump();
//    
//        for (auto *DI : DS->decls()) {
//            clang::VarDecl *VD = clang::dyn_cast<clang::VarDecl>(DI);
//            VD->dump();
//        }
//    }
};

class BlockAnalysis {
    // A container for BlockAnalysisContext objects
    std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *> block2Ctx;

public:
    void add(const clang::CFGBlock *block) {
        block2Ctx[block] = new BlockAnalysisContext(block, &block2Ctx);
    }

    ~BlockAnalysis() {
        for (std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *>::
                iterator I = block2Ctx.begin(), E = block2Ctx.end();
                I != E; ++I) {
            BlockAnalysisContext *ctx = (*I).second;
            if (!ctx)
                continue;

            delete ctx;
        }
    }

    bool runOnBlock(const clang::CFGBlock *block) {
        printf("Run on block B[%d]\n", block->getBlockID());

        block2Ctx[block]->updateEntryValue();

        // Apply the transfer function.
    //    TransferFunctions tf(vals, cfg, block, ac, classification, handler);
        TransferFunctions tf(block2Ctx[block]);
    
        for (clang::CFGBlock::const_iterator I = block->begin(), E = block->end();
                I != E; ++I) {
            if (clang::Optional<clang::CFGStmt> cs = I->getAs<clang::CFGStmt>())
                tf.Visit(const_cast<clang::Stmt*>(cs->getStmt()));
        }
    
        block2Ctx[block]->updateSuccessors();
    
        return false;
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

    clang::ForwardDataflowWorklist worklist(*cfg, ac);
    worklist.enqueueSuccessors(&cfg->getEntry());

    llvm::BitVector previouslyVisited(cfg->getNumBlockIDs());

    BlockAnalysis blockAnalysis;

    for (clang::CFG::const_iterator BI = cfg->begin(), BE = cfg->end(); BI != BE;
            ++BI) {
        const clang::CFGBlock *block = *BI;

        blockAnalysis.add(block);
    }
    

    blockAnalysis.runOnBlock(&cfg->getEntry());

    while (const clang::CFGBlock *block = worklist.dequeue()) {
        // Did the block change?
        bool changed = blockAnalysis.runOnBlock(block);
        
        if (changed || !previouslyVisited[block->getBlockID()])
            worklist.enqueueSuccessors(block);
        previouslyVisited[block->getBlockID()] = true;
    }     
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

    man = box_manager_alloc();
    printf("******************************\n");
    printf("Apron: Library %s, version %s\n", man->library, man->version);
    printf("******************************\n");

    int ret = !clang::tooling::runToolOnCode(new ExampleFrontendAction,
            contents.c_str());

    ap_manager_free(man);

    return ret;
}
