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
// #include "ap_global0.h"
// #include "ap_global1.h"
// #include "box.h"
// #include "oct.h"
// #include "pk.h"
// #include "pkeq.h"

static int printCFG;
static const char *funcToAnalyze;
// static ap_manager_t* man;
// static ap_environment_t *env;

class Variables {
    // Maps a variable to an apron 'dimention' (index)
    std::unordered_map<const clang::VarDecl *, unsigned> var2Dim;
    clang::DeclContext *dc;
//    ap_var_t *name_of_dim;
    int size;
    
public:
    Variables() {
//        name_of_dim = NULL;
        size = 0;
    }

    void init(clang::Decl *D) {
        dc = clang::cast<clang::DeclContext>(D);
        
        for (clang::DeclContext::specific_decl_iterator<clang::VarDecl> I(dc->decls_begin()),
                E(dc->decls_end()); I != E; ++I) {
            const clang::VarDecl *vd = *I;

            if (isTrackedVar(vd))
                ++size;
        }

//        name_of_dim = new ap_var_t[size];

        int ind = 0;
        for (clang::DeclContext::specific_decl_iterator<clang::VarDecl> I(dc->decls_begin()),
                E(dc->decls_end()); I != E; ++I) {
            const clang::VarDecl *vd = *I;

            if (!isTrackedVar(vd)) {
                continue;
            }

//            name_of_dim[ind] = (ap_var_t)vd->getNameAsString().c_str();
            var2Dim[vd] = ind;
            ++ind;
        }

        // Assuming integers only;
//        env = ap_environment_alloc(name_of_dim, size, NULL, 0);
    }

    ~Variables() {
//        if (env)
//            ap_environment_free(env);
//        if (name_of_dim)
//            delete [] name_of_dim;
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
    std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *> *block2Ctx;

    // Abstract values
//    std::unordered_map<const CFGBlock *, ap_abstract1_t> pred2Abs;
//    ap_abstract1_t abs;

    // Successors
    const clang::CFGBlock *succ[2];
public:
    BlockAnalysisContext(const clang::CFGBlock *block,
            std::unordered_map<const clang::CFGBlock *, BlockAnalysisContext *> *block2Ctx) {
        this->block = block;
        this->block2Ctx = block2Ctx; 

        // Chaotic iteration: All abstract values initialized as bottom
        for (clang::CFGBlock::const_pred_iterator I = block->pred_begin(), E = block->pred_end(); I != E; ++I) {
            const clang::CFGBlock *Pred = *I;
            if (!Pred)
                continue;

//            pred2Abs[Pred] = ap_abstract1_bottom(man, env);
        }

        assert(block->succ_size() <= 2);
        // If has terminator statement => has two successors
        assert(!block->getTerminator() || block->succ_size() == 2);

        succ[0] = NULL;
        succ[1] = NULL;
        if (block->succ_empty())
            return;

        for (clang::CFGBlock::const_succ_iterator I = block->succ_begin(), E = block->succ_end(); I != E; ++I) {
            const clang::CFGBlock *s = *I;
            if (!s)
                continue;

            if (!succ[0])
                succ[0] = s;
            else
                succ[1] = s;
        }
    }

    void updateEntryValue() {
        // Entry block
        if (block->pred_empty()) {
//            abs = ap_abstract1_top(man, env);
            return;
        }

        // Merge (join) all predeseccors exit values
        
        printf("%d) Merging preds' values. old value:", block->getBlockID());
//        ap_abstract1_fprint(stdout, man, &abs);
//        abs = ap_abstract1_bottom(man, env);
//        for (auto it = pred2Abs.begin(); it != pred2Abs.end(); ++it) {
//            ap_abstract1_t absPred = it->second;
//            abs = ap_abstract1_join(man, false, &abs, &absPred);
//        }
//        printf("After merge:");
//        ap_abstract1_fprint(stdout, man, &abs);
    }

    // Each successor holds a list of its predecessors exit values. We update the entry for this block in each
    // of its successors' list
    void updateSuccValues() {
        if (block->succ_empty())
            return;

        // Single successor: just pass this block's exit value as the successor's entry value
        if (!block->getTerminator()) {
//            (*block2Ctx)[succ[0]]->pred2Abs[block] = abs;
            return;
        }

        // Two successors: first for 'then', second for 'else'
        const clang::Stmt *cond = block->getTerminatorCondition();
        printf("\tcondition: %s\n", cond->getStmtClassName());
        cond->dump();

        // XXX: Do something with cond
//        (*block2Ctx)[succ[0]]->pred2Abs[block] = abs;
//        (*block2Ctx)[succ[1]]->pred2Abs[block] = abs;
    }

    void printAbs() {
        printf("Abs value: ");
//        ap_abstract1_fprint(stdout, man, &abs);
    }
};

class TransferFunctions : public clang::StmtVisitor<TransferFunctions> {
    BlockAnalysisContext *analysisCtx;

public:
  TransferFunctions(BlockAnalysisContext *analysisCtx) {
      this->analysisCtx = analysisCtx;
      printf("\tAbs value before merge:\n");
      analysisCtx->printAbs();
      printf("\tAbs value after merge:\n");

  }

//  void VisitBlockExpr(BlockExpr *be);
//  void VisitCallExpr(CallExpr *ce);
//  void VisitDeclRefExpr(DeclRefExpr *dr);
//  void VisitObjCForCollectionStmt(ObjCForCollectionStmt *FS);
//  void VisitObjCMessageExpr(ObjCMessageExpr *ME);
    void VisitBinaryOperator(clang::BinaryOperator *BO) {
        if (BO->getOpcode() == clang::BO_Assign) {
            printf("Assignment\n");
            BO->getLHS()->dump();
            BO->getRHS()->dump();
        }
    }
    
    void VisitDeclStmt(clang::DeclStmt *DS) {
        printf("DeclStmt:\n");
        DS->getSingleDecl()->dump();
    
        for (auto *DI : DS->decls()) {
            clang::VarDecl *VD = clang::dyn_cast<clang::VarDecl>(DI);
            VD->dump();
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
    
        block2Ctx[block]->updateSuccValues();
    
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
        printf("Block ID: %u\n", block->getBlockID());

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

//    man = box_manager_alloc();
    printf("******************************\n");
//    printf("Apron: Library %s, version %s\n", man->library, man->version);
    printf("******************************\n");

    int ret = !clang::tooling::runToolOnCode(new ExampleFrontendAction,
            contents.c_str());

//    ap_manager_free(man);

    return ret;
}
