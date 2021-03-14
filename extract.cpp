#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/YAMLParser.h" // yaml::escape
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <fcntl.h>  // open
#include <unistd.h> // close
#include <sys/file.h> // flock

using namespace llvm;

namespace llvm {
void initializeDAGExtractorPass(PassRegistry &);
}

namespace {

cl::opt<std::string> OutputFile("dump-dags-to",
                                cl::desc("File to dump the extracted DAGs"));

cl::opt<bool>
    IncludeLiveIns("include-live-ins",
                   "include live-in instructions of a given basic block",
                   cl::init(true));

class LockFile {
  int FD;

public:
  LockFile(std::string FName, bool &Ok) {
    FD = open(FName.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    Ok = FD != -1;
    if (!Ok) {
      perror("failed to open lock file");
      abort();
      return;
    }
    if (flock(FD, LOCK_EX)) {
      perror("failed to flock lock file");
      close(FD);
      FD = -1;
      Ok = false;
    }
  }

  ~LockFile() {
    if (FD != -1) {
      flock(FD, LOCK_UN);
      close(FD);
    }
  }
};

bool isSupported(const Instruction *I) {
  return isa<BinaryOperator>(I) || isa<UnaryOperator>(I) ||
         isa<SelectInst>(I) || isa<CastInst>(I) ||
         isa<CmpInst>(I);
}

void dumpBasicBlock(raw_ostream &OS, ArrayRef<Value *> LiveIns,
                    ArrayRef<Instruction *> Instructions) {
  LLVMContext Ctx;
  Module M("", Ctx);

  std::vector<Type *> ParamTypes;
  for (auto *V : LiveIns)
    ParamTypes.push_back(V->getType());
  auto *VoidTy = Type::getVoidTy(Ctx);
  auto WrapperTy = FunctionType::get(VoidTy, ParamTypes, false /*isVarArg*/);
  auto Wrapper =
      cast<Function>(M.getOrInsertFunction("wrapper", WrapperTy).getCallee());

  // old value -> cloned value
  ValueToValueMapTy VMap;
  for (unsigned i = 0; i < LiveIns.size(); i++)
    VMap[LiveIns[i]] = Wrapper->getArg(i);

  auto *EntryBB = BasicBlock::Create(Ctx, "entry", Wrapper);
  auto *SinkBB = BasicBlock::Create(Ctx, "sink", Wrapper);

  DenseSet<Instruction *> Alive;
  for (auto *I : Instructions) {
    auto *Cloned = I->clone();
    VMap[I] = Cloned;
    EntryBB->getInstList().push_back(Cloned);
    // remap the operands
    RemapInstruction(Cloned, VMap,
                     RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);

    // mark the operands of I as alive
    for (Value *Operand : I->operands())
      if (auto *I2 = dyn_cast<Instruction>(Operand))
        Alive.insert(I2);
  }
  BranchInst::Create(SinkBB, EntryBB /*InsertAtEnd*/);
  auto *Ret = ReturnInst::Create(Ctx, SinkBB);
  // make the dead instructions alive by applying them to a dummy use function
  int i = 0;
  for (auto *I : Instructions) {
    if (Alive.count(I))
      continue;
    FunctionCallee User = M.getOrInsertFunction(Twine("use-").concat(Twine(i++)).str(), VoidTy, I->getType());
    CallInst::Create(User, {VMap[I]}, "", Ret /*InsertBefore*/);
  }

  std::string Buffer;
  raw_string_ostream SS(Buffer);
  SS << M;
  SS.flush();
  OS << Instructions.size() << ',' << yaml::escape(Buffer);
}

void dumpBasicBlock(raw_ostream &OS, BasicBlock &BB) {
  std::vector<Instruction *> Instructions;
  std::vector<Value *> LiveIns;
  DenseSet<Value *> Visited;

  std::function<void(Value *)> Visit = [&](Value *V) {
    if (isa<Constant>(V))
      return;

    bool Inserted = Visited.insert(V).second;
    if (!Inserted)
      return;

    auto *I = dyn_cast<Instruction>(V);
    if (!I || !isSupported(I) || (!IncludeLiveIns && I->getParent() != &BB)) {
      if (!V->getType()->isVoidTy())
        LiveIns.push_back(V);
      return;
    }

    for (Value *Operand : I->operands())
      Visit(Operand);

    Instructions.push_back(I);
  };

  for (auto &I : BB)
    Visit(&I);

  if (Instructions.empty())
    return;

  dumpBasicBlock(OS, LiveIns, Instructions);
  OS << '\n';
}

class DAGExtractor : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid
  DAGExtractor() : FunctionPass(ID) {
    initializeDAGExtractorPass(*PassRegistry::getPassRegistry());
  }
  bool runOnFunction(Function &F) override {
    std::string Buffer;
    raw_string_ostream SS(Buffer);
    for (auto &BB : F) {
      dumpBasicBlock(SS, BB);
    }
    if (!OutputFile.empty()) {
      bool Ok;
      LockFile LF(OutputFile + ".lock", Ok);
      if (!Ok) {
        return false;
      }
      std::error_code EC;
      raw_fd_ostream OS(OutputFile, EC, llvm::sys::fs::OF_Append);
      if (EC) {
        errs() << "Failed to open output file\n";
        return false;
      }
      SS.flush();
      OS << Buffer;
    }
    return false;
  }
};
} // end anonymous namespace

char DAGExtractor::ID = 0;

INITIALIZE_PASS_BEGIN(DAGExtractor, "dag-extract", "dag-extract", false, false)
INITIALIZE_PASS_END(DAGExtractor, "dag-extract", "dag-extract", false, false)

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerExtractor(const PassManagerBuilder &PMB,
                              legacy::PassManagerBase &MPM) {
  MPM.add(createSROAPass());
  MPM.add(new DAGExtractor());
}
// Register this pass to run after all optimization,
// because we want this pass to replace LLVM SLP.
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible, registerExtractor);
