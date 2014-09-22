#include <iostream>     // std::cout
#include <fstream>      // std::ifstream
#include <unistd.h>     // fork()
#include <stdlib.h>     // atoi()

#include "clang/AST/Decl.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Analysis/AnalysisContext.h"
#include "clang/Analysis/Analyses/DataflowWorklist.h"

#include "ap_global0.h"
#include "ap_global1.h"

#include "box.h"
#include "oct.h"
#include "pk.h"
#include "pkeq.h"

using namespace std;
using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace llvm;

static int printCFG;
static const char *funcToAnalyze;
static ap_manager_t* man;
static ap_environment_t *env;

class BlockAnalysisContext {
    const CFGBlock *block;
    int nIterations;
    // If null then not a control branch. 
    const Stmt *cond;
    int x;

public:
    BlockAnalysisContext(const CFGBlock *block) {
        cond = NULL;
        this->block = block;
        nIterations = 0;

        printf("%d\n", block->getBlockID());
        if (const Stmt *cond = block->getTerminatorCondition()) {
                printf("%s\n",
                        block->getTerminatorCondition()->getStmtClassName());
//            if (block->pred_size() > 1) {
//               printf("Analysis error: block %d has multiple predecessors but "
//                       "is also a control branch\n", block->getBlockID());
//               exit(1);
//            }
            this->cond = cond;
        }
        x = 0;
    }

    // Called by worklist algorithm (chaotic iteration)
    void processPredValues();

    int nIterateions() {
        return nIterations;
    }
};

class BlockAnalysis {
    llvm::DenseMap<const CFGBlock *, BlockAnalysisContext *> block2Ctx;
public:
    BlockAnalysis() {}

    void add(const CFGBlock *block) {
        block2Ctx[block] = new BlockAnalysisContext(block);
    }

    ~BlockAnalysis() {
        for (llvm::DenseMap<const CFGBlock *, BlockAnalysisContext *>::
                iterator I = block2Ctx.begin(), E = block2Ctx.end();
                I != E; ++I) {
            BlockAnalysisContext *ctx = (*I).second;
            if (!ctx)
                continue;

            delete ctx;
        }
    }

    BlockAnalysisContext *get(const CFGBlock *block) {
        return block2Ctx[block];
    }

    void processPredValues(const CFGBlock *block) {
        block2Ctx[block]->processPredValues();
    }
};

static BlockAnalysis blockAnalysis;

void BlockAnalysisContext::processPredValues() {
    ++nIterations;

    for (CFGBlock::const_pred_iterator I = block->pred_begin(),
            E = block->pred_end(); I != E; ++I) {
        const CFGBlock *Pred = *I;
        if (!Pred || Pred->getBlockID()==7)
            continue;

        printf("\tRunning on pred %d\n", Pred->getBlockID());
        BlockAnalysisContext *predCtx = blockAnalysis.get(Pred);
        if (predCtx->cond &&
                predCtx->cond->getStmtClassName()) {
//        if (Pred->getTerminatorCondition()) {
//                printf("%d %s\n", Pred->getBlockID(),
//                        Pred->getTerminatorCondition()->getStmtClassName());
            printf("\tcondition: %s\n", predCtx->cond->getStmtClassName());
            predCtx->cond->dump();
//            // Do something with cond
        }

        x = x >= predCtx->x ? x : predCtx->x;
    }
}

class TransferFunctions : public StmtVisitor<TransferFunctions> {
//  CFGBlockValues &vals;
//  const CFG &cfg;
    const CFGBlock *block;
//  AnalysisDeclContext &ac;
//  const ClassifyRefs &classification;
//  ObjCNoReturn objCNoRet;
//  UninitVariablesHandler &handler;
//
public:
  TransferFunctions(const CFGBlock *block) {
      this->block = block;
  }

  void VisitBinaryOperator(BinaryOperator *bo);
//  void VisitBlockExpr(BlockExpr *be);
//  void VisitCallExpr(CallExpr *ce);
//  void VisitDeclRefExpr(DeclRefExpr *dr);
  void VisitDeclStmt(DeclStmt *ds);
//  void VisitObjCForCollectionStmt(ObjCForCollectionStmt *FS);
//  void VisitObjCMessageExpr(ObjCMessageExpr *ME);
};

void TransferFunctions::VisitBinaryOperator(BinaryOperator *BO) {
  if (BO->getOpcode() == BO_Assign) {
      printf("Assignment\n");
      BO->getLHS()->dump();
  }
}

void TransferFunctions::VisitDeclStmt(DeclStmt *DS) {
    printf("DeclStmt:\n");
    DS->getSingleDecl()->dump();

  for (auto *DI : DS->decls()) {
    VarDecl *VD = dyn_cast<VarDecl>(DI);
    VD->dump();
  }
}

static void VisualizeCfg(AnalysisDeclContext *ac, CFG *cfg) {
    switch (printCFG) {
    case 1:
        ac->dumpCFG(false);
        break;
    case 2:
        // Child process, pops up a graphic tool to show the graph
        if (fork() == 0) {
            cfg->viewCFG(LangOptions());
            exit(0);
        }
        break;
    }
}

static bool runOnBlock(const CFGBlock *block) {
    blockAnalysis.processPredValues(block);

    // Apply the transfer function.
//    TransferFunctions tf(vals, cfg, block, ac, classification, handler);
    TransferFunctions tf(block);
    for (CFGBlock::const_iterator I = block->begin(), E = block->end(); I != E;
            ++I) {
        if (Optional<CFGStmt> cs = I->getAs<CFGStmt>())
            tf.Visit(const_cast<Stmt*>(cs->getStmt()));
    }

    return false;
}

static void analyze(Decl *D) {
    // Construct the analysis context with the specified CFG build options.
    AnalysisDeclContext ac(/* AnalysisDeclContextManager */ nullptr, D);
    CFG *cfg;
    if (!(cfg = ac.getCFG()))
        exit(1);

    VisualizeCfg(&ac, cfg);

    ForwardDataflowWorklist worklist(*cfg, ac);
    worklist.enqueueSuccessors(&cfg->getEntry());

    llvm::BitVector previouslyVisited(cfg->getNumBlockIDs());

    for (CFG::const_iterator BI = cfg->begin(), BE = cfg->end(); BI != BE;
            ++BI) {
        const CFGBlock *block = *BI;

        blockAnalysis.add(block);
    }
    

    while (const CFGBlock *block = worklist.dequeue()) {
        printf("Block ID: %u\n", block->getBlockID());

        // Did the block change?
        bool changed = runOnBlock(block);
        
        if (changed || !previouslyVisited[block->getBlockID()])
            worklist.enqueueSuccessors(block);
        previouslyVisited[block->getBlockID()] = true;
    }     
}

class ExampleVisitor : public RecursiveASTVisitor<ExampleVisitor> {
private:
    ASTContext *astContext; // used for getting additional AST info

public:
    explicit ExampleVisitor(CompilerInstance *CI) 
      : astContext(&(CI->getASTContext())) // initialize private members
    { }

    virtual bool VisitFunctionDecl(FunctionDecl *func) {
        string funcName = func->getNameInfo().getName().getAsString();
        llvm::outs() << funcName << "\n";        
        return true;
    }
};

class ExampleASTConsumer : public ASTConsumer {
private:
    ExampleVisitor *visitor; // doesn't have to be private

public:
    // override the constructor in order to pass CI
    // initialize the visitor
    explicit ExampleASTConsumer(CompilerInstance *CI) : visitor(
            new ExampleVisitor(CI)) {
    }

    // override this to call our ExampleVisitor on each top-level Decl
    virtual bool HandleTopLevelDecl(DeclGroupRef DG) {
        if (!DG.isSingleDecl()) {
           return true;
        }

        Decl *D = DG.getSingleDecl();
        const FunctionDecl *FD = dyn_cast<FunctionDecl>(D);
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

class ExampleFrontendAction : public ASTFrontendAction {
public:
    virtual std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
            StringRef file) {
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

    /* One integer vars, none real */
    ap_var_t name_of_dim[] = { (ap_var_t)"x" };
    env = ap_environment_alloc(&name_of_dim[0], 1, NULL,0);    
    
    int ret = !clang::tooling::runToolOnCode(new ExampleFrontendAction,
            contents.c_str());

    ap_manager_free(man);

    return ret;
}
