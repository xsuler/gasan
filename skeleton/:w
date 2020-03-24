#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "AddressSanitizer.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/BinaryFormat/MachO.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Comdat.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/MC/MCSectionMachO.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
// #include "llvm/Transforms/Utils/AsanStackFrameLayout.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"


 #include <algorithm>
 #include <cassert>
 #include <cstddef>
 #include <cstdint>
 #include <iomanip>
 #include <limits>
 #include <memory>
 #include <sstream>
 #include <string>
 #include <tuple>
 
 using namespace llvm;

#define DEBUG_TYPE "asant"
static const char *const kAsantRegisterGlobalsName = "__asant_register_globals";
static const char *const kAsantUnregisterGlobalsName =
  "__asant_unregister_globals";
static const char *const kAsantRegisterImageGlobalsName =
  "__asant_register_image_globals";
static const char *const kAsantUnregisterImageGlobalsName =
  "__asant_unregister_image_globals";
static const char *const kAsantRegisterElfGlobalsName =
  "__asant_register_elf_globals";
static const char *const kAsantUnregisterElfGlobalsName =
  "__asant_unregister_elf_globals";
static const char *const kAsantGlobalsRegisteredFlagName =
  "___asant_globals_registered";
static const char *const kAsantPtrSub = "__sanitizer_ptr_sub";
static const char *const kAsantPoisonGlobalsName = "__asant_before_dynamic_init";
static const char *const kAsantUnpoisonGlobalsName = "__asant_after_dynamic_init";
static const uint64_t kAsantCtorAndDtorPriority = 1;
static const char *const kAsantModuleCtorName = "asant.module_ctor";
static const char *const kAsantModuleDtorName = "asant.module_dtor";
static const uint64_t kDefaultShadowScale = 3;
static const uint64_t kDefaultShadowOffset32 = 0x0000000100000000;
static const uint64_t kDefaultShadowOffset64 = 0x0000000100000000;
static const size_t kNumberOfAccessSizes = 5;
static const char *const kAsantGenPrefix = "___asant_gen_";
static const char *const kSanCovGenPrefix = "__sancov_gen_";
static const char *const kAsantSetShadowPrefix = "__asant_set_shadow_";
static const char *const kODRGenPrefix = "__odr_asant_gen_";


static cl::opt<bool> ClRecover(
    "asant-recover",
    cl::desc("Enable recovery mode (continue-after-error)."),
    cl::Hidden, cl::init(false));

// This flag may need to be replaced with -f[no-]asant-reads.
static cl::opt<bool> ClInstrumentReads("asant-instrument-reads",
                                       cl::desc("instrument read instructions"),
                                       cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentWrites(
    "asant-instrument-writes", cl::desc("instrument write instructions"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentAtomics(
    "asant-instrument-atomics",
    cl::desc("instrument atomic instructions (rmw, cmpxchg)"), cl::Hidden,
    cl::init(true));

static cl::opt<bool> ClAlwaysSlowPath(
    "asant-always-slow-path",
    cl::desc("use instrumentation with slow path for all accesses"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClForceDynamicShadow(
    "asant-force-dynamic-shadow",
    cl::desc("Load shadow address into a local variable for each function"),
    cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClWithIfunc("asant-with-ifunc",
                cl::desc("Access dynamic shadow through an ifunc global on "
                         "platforms that support this"),
                cl::Hidden, cl::init(true));

static cl::opt<bool> ClWithIfuncSuppressRemat(
    "asant-with-ifunc-suppress-remat",
    cl::desc("Suppress rematerialization of dynamic shadow address by passing "
             "it through inline asm in prologue."),
    cl::Hidden, cl::init(true));

// This flag limits the number of instructions to be instrumented
// in any given BB. Normally, this should be set to unlimited (INT_MAX),
// but due to http://llvm.org/bugs/show_bug.cgi?id=12652 we temporary
// set it to 10000.
static cl::opt<int> ClMaxInsnsToInstrumentPerBB(
    "asant-max-ins-per-bb", cl::init(10000),
    cl::desc("maximal number of instructions to instrument in any given BB"),
    cl::Hidden);

// This flag may need to be replaced with -f[no]asant-stack.
static cl::opt<bool> ClStack("asant-stack", cl::desc("Handle stack memory"),
                             cl::Hidden, cl::init(true));
static cl::opt<uint32_t> ClMaxInlinePoisoningSize(
    "asant-max-inline-poisoning-size",
    cl::desc(
        "Inline shadow poisoning for blocks up to the given size in bytes."),
    cl::Hidden, cl::init(64));

static cl::opt<bool> ClUseAfterReturn("asant-use-after-return",
                                      cl::desc("Check stack-use-after-return"),
                                      cl::Hidden, cl::init(true));

static cl::opt<bool> ClRedzoneByvalArgs("asant-redzone-byval-args",
                                        cl::desc("Create redzones for byval "
                                                 "arguments (extra copy "
                                                 "required)"), cl::Hidden,
                                        cl::init(true));

static cl::opt<bool> ClUseAfterScope("asant-use-after-scope",
                                     cl::desc("Check stack-use-after-scope"),
                                     cl::Hidden, cl::init(false));

// This flag may need to be replaced with -f[no]asant-globals.
static cl::opt<bool> ClGlobals("asant-globals",
                               cl::desc("Handle global objects"), cl::Hidden,
                               cl::init(true));

static cl::opt<bool> ClInitializers("asant-initialization-order",
                                    cl::desc("Handle C++ initializer order"),
                                    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInvalidPointerPairs(
    "asant-detect-invalid-pointer-pair",
    cl::desc("Instrument <, <=, >, >=, - with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClInvalidPointerCmp(
    "asant-detect-invalid-pointer-cmp",
    cl::desc("Instrument <, <=, >, >= with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClInvalidPointerSub(
    "asant-detect-invalid-pointer-sub",
    cl::desc("Instrument - operations with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<unsigned> ClRealignStack(
    "asant-realign-stack",
    cl::desc("Realign stack to the value of this flag (power of two)"),
    cl::Hidden, cl::init(32));

static cl::opt<int> ClInstrumentationWithCallsThreshold(
    "asant-instrumentation-with-call-threshold",
    cl::desc(
        "If the function being instrumented contains more than "
        "this number of memory accesses, use callbacks instead of "
        "inline checks (-1 means never use callbacks)."),
    cl::Hidden, cl::init(7000));

static cl::opt<std::string> ClMemoryAccessCallbackPrefix(
    "asant-memory-access-callback-prefix",
    cl::desc("Prefix for memory access callbacks"), cl::Hidden,
    cl::init("__asant_"));

static cl::opt<bool>
    ClInstrumentDynamicAllocas("asant-instrument-dynamic-allocas",
                               cl::desc("instrument dynamic allocas"),
                               cl::Hidden, cl::init(true));

static cl::opt<bool> ClSkipPromotableAllocas(
    "asant-skip-promotable-allocas",
    cl::desc("Do not instrument promotable allocas"), cl::Hidden,
    cl::init(true));

// These flags allow to change the shadow mapping.
// The shadow mapping looks like
//    Shadow = (Mem >> scale) + offset

static cl::opt<int> ClMappingScale("asant-mapping-scale",
                                   cl::desc("scale of asant shadow mapping"),
                                   cl::Hidden, cl::init(0));

static cl::opt<uint64_t>
    ClMappingOffset("asant-mapping-offset",
                    cl::desc("offset of asant shadow mapping [EXPERIMENTAL]"),
                    cl::Hidden, cl::init(0));

// Optimization flags. Not user visible, used mostly for testing
// and benchmarking the tool.

static cl::opt<bool> ClOpt("asant-opt", cl::desc("Optimize instrumentation"),
                           cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptSameTemp(
    "asant-opt-same-temp", cl::desc("Instrument the same temp just once"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptGlobals("asant-opt-globals",
                                  cl::desc("Don't instrument scalar globals"),
                                  cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptStack(
    "asant-opt-stack", cl::desc("Don't instrument scalar stack variables"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDynamicAllocaStack(
    "asant-stack-dynamic-alloca",
    cl::desc("Use dynamic alloca to represent stack variables"), cl::Hidden,
    cl::init(true));

static cl::opt<uint32_t> ClForceExperiment(
    "asant-force-experiment",
    cl::desc("Force optimization experiment (for testing)"), cl::Hidden,
    cl::init(0));

static cl::opt<bool>
    ClUsePrivateAlias("asant-use-private-alias",
                      cl::desc("Use private aliases for global variables"),
                      cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClUseOdrIndicator("asant-use-odr-indicator",
                      cl::desc("Use odr indicators to improve ODR reporting"),
                      cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClUseGlobalsGC("asant-globals-live-support",
                   cl::desc("Use linker features to support dead "
                            "code stripping of globals"),
                   cl::Hidden, cl::init(true));

// This is on by default even though there is a bug in gold:
// https://sourceware.org/bugzilla/show_bug.cgi?id=19002
static cl::opt<bool>
    ClWithComdat("asant-with-comdat",
                 cl::desc("Place Asant constructors in comdat sections"),
                 cl::Hidden, cl::init(true));

// Debug flags.

static cl::opt<int> ClDebug("asant-debug", cl::desc("debug"), cl::Hidden,
                            cl::init(0));

static cl::opt<int> ClDebugStack("asant-debug-stack", cl::desc("debug stack"),
                                 cl::Hidden, cl::init(0));

static cl::opt<std::string> ClDebugFunc("asant-debug-func", cl::Hidden,
                                        cl::desc("Debug func"));

static cl::opt<int> ClDebugMin("asant-debug-min", cl::desc("Debug min inst"),
                               cl::Hidden, cl::init(-1));

static cl::opt<int> ClDebugMax("asant-debug-max", cl::desc("Debug max inst"),
                               cl::Hidden, cl::init(-1));

STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumOptimizedAccessesToGlobalVar,
          "Number of optimized accesses to global vars");
STATISTIC(NumOptimizedAccessesToStackVar,
          "Number of optimized accesses to stack vars");






namespace{
 struct ShadowMapping {
   int Scale;
   uint64_t Offset;
   bool OrShadowOffset;
   bool InGlobal;
 };
}
static size_t RedzoneSizeForScale(int MappingScale) {
  // Redzone used for stack and globals is at least 32 bytes.
  // For scales 6 and 7, the redzone has to be 64 and 128 bytes respectively.
  return std::max(32U, 1U << MappingScale);
}

static ShadowMapping getShadowMapping(Triple &TargetTriple, int LongSize) {

   ShadowMapping Mapping;
 
   Mapping.Scale = kDefaultShadowScale;
 
   if (LongSize == 32) {
       Mapping.Offset = kDefaultShadowOffset32;
   } else {  // LongSize == 64
     // Fuchsia is always PIE, which means that the beginning of the address
     Mapping.Offset = kDefaultShadowOffset64;
   }
 
   // OR-ing shadow offset if more efficient (at least on x86) if the offset
   // is a power of two, but on ppc64 we have to use add since the shadow
   // offset is not necessary 1/8-th of the address space.  On SystemZ,
   // we could OR the constant in a single instruction, but it's more
   // efficient to load it once and use indexed addressing.
   Mapping.OrShadowOffset =!(Mapping.Offset & (Mapping.Offset - 1));

   Mapping.InGlobal = 0;
 
   return Mapping;
 }

void initializeAsantGlobalsMetadataWrapperPassPass(PassRegistry &);
namespace{
  /***********************************************************************************************/
  class AsantGlobalsMetadataWrapperPass : public ModulePass {
  public:
    static char ID;

    AsantGlobalsMetadataWrapperPass() : ModulePass(ID) {
      initializeAsantGlobalsMetadataWrapperPassPass(
                                                   *PassRegistry::getPassRegistry());
    }

    bool runOnModule(Module &M) override {
      errs()<<"one\n";
      GlobalsMD = GlobalsMetadata(M);
      return false;
    }

    StringRef getPassName() const override {
      return "AsantGlobalsMetadataWrapperPass";
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }

    GlobalsMetadata &getGlobalsMD() { return GlobalsMD; }

  private:
    GlobalsMetadata GlobalsMD;
  };

  char AsantGlobalsMetadataWrapperPass::ID = 0;


  /***********************************************************************************************/

struct AddressSanitizer {
  AddressSanitizer(Module &M, GlobalsMetadata &GlobalsMD,
                    bool Recover = false,
                   bool UseAfterScope = false)
      : UseAfterScope(UseAfterScope), GlobalsMD(GlobalsMD) {
    this->Recover =  Recover;
    C = &(M.getContext());
    LongSize = M.getDataLayout().getPointerSizeInBits();
    IntptrTy = Type::getIntNTy(*C, LongSize);
    TargetTriple = Triple(M.getTargetTriple());

    Mapping = getShadowMapping(TargetTriple, LongSize);
  }

  uint64_t getAllocaSizeInBytes(const AllocaInst &AI) const {
    uint64_t ArraySize = 1;
    if (AI.isArrayAllocation()) {
      const ConstantInt *CI = dyn_cast<ConstantInt>(AI.getArraySize());
      assert(CI && "non-constant array size");
      ArraySize = CI->getZExtValue();
    }
    Type *Ty = AI.getAllocatedType();
    uint64_t SizeInBytes =
        AI.getModule()->getDataLayout().getTypeAllocSize(Ty);
    return SizeInBytes * ArraySize;
  }

  /// Check if we want (and can) handle this alloca.
  bool isInterestingAlloca(const AllocaInst &AI);

  /// If it is an interesting memory access, return the PointerOperand
  /// and set IsWrite/Alignment. Otherwise return nullptr.
  /// MaybeMask is an output parameter for the mask Value, if we're looking at a
  /// masked load/store.
  Value *isInterestingMemoryAccess(Instruction *I, bool *IsWrite,
                                   uint64_t *TypeSize, unsigned *Alignment,
                                   Value **MaybeMask = nullptr);

  void instrumentMop(ObjectSizeOffsetVisitor &ObjSizeVis, Instruction *I,
                     bool UseCalls, const DataLayout &DL);
  void instrumentPointerComparisonOrSubtraction(Instruction *I);
  void instrumentAddress(Instruction *OrigIns, Instruction *InsertBefore,
                         Value *Addr, uint32_t TypeSize, bool IsWrite,
                         Value *SizeArgument, bool UseCalls, uint32_t Exp);
  void instrumentUnusualSizeOrAlignment(Instruction *I,
                                        Instruction *InsertBefore, Value *Addr,
                                        uint32_t TypeSize, bool IsWrite,
                                        Value *SizeArgument, bool UseCalls,
                                        uint32_t Exp);
  Value *createSlowPathCmp(IRBuilder<> &IRB, Value *AddrLong,
                           Value *ShadowValue, uint32_t TypeSize);
  Instruction *generateCrashCode(Instruction *InsertBefore, Value *Addr,
                                 bool IsWrite, size_t AccessSizeIndex,
                                 Value *SizeArgument, uint32_t Exp);
  void instrumentMemIntrinsic(MemIntrinsic *MI);
  Value *memToShadow(Value *Shadow, IRBuilder<> &IRB);
  bool instrumentFunction(Function &F, const TargetLibraryInfo *TLI);
  bool maybeInsertAsantInitAtFunctionEntry(Function &F);
  void maybeInsertDynamicShadowAtFunctionEntry(Function &F);
  void markEscapedLocalAllocas(Function &F);

private:
  friend struct FunctionStackPoisoner;

  void initializeCallbacks(Module &M);

  bool LooksLikeCodeInBug11395(Instruction *I);
  bool GlobalIsLinkerInitialized(GlobalVariable *G);
  bool isSafeAccess(ObjectSizeOffsetVisitor &ObjSizeVis, Value *Addr,
                    uint64_t TypeSize) const;

  /// Helper to cleanup per-function state.
  struct FunctionStateRAII {
    AddressSanitizer *Pass;

    FunctionStateRAII(AddressSanitizer *Pass) : Pass(Pass) {
      assert(Pass->ProcessedAllocas.empty() &&
             "last pass forgot to clear cache");
      assert(!Pass->LocalDynamicShadow);
    }

    ~FunctionStateRAII() {
      Pass->LocalDynamicShadow = nullptr;
      Pass->ProcessedAllocas.clear();
    }
  };

  LLVMContext *C;
  Triple TargetTriple;
  int LongSize;
  bool CompileKernel;
  bool Recover;
  bool UseAfterScope;
  Type *IntptrTy;
  ShadowMapping Mapping;
  FunctionCallee AsantHandleNoReturnFunc;
  FunctionCallee AsantPtrCmpFunction, AsantPtrSubFunction;
  Constant *AsantShadowGlobal;

  // These arrays is indexed by AccessIsWrite, Experiment and log2(AccessSize).
  FunctionCallee AsantErrorCallback[2][2][kNumberOfAccessSizes];
  FunctionCallee AsantMemoryAccessCallback[2][2][kNumberOfAccessSizes];

  // These arrays is indexed by AccessIsWrite and Experiment.
  FunctionCallee AsantErrorCallbackSized[2][2];
  FunctionCallee AsantMemoryAccessCallbackSized[2][2];

  FunctionCallee AsantMemmove, AsantMemcpy, AsantMemset;
  InlineAsm *EmptyAsm;
  Value *LocalDynamicShadow = nullptr;
  GlobalsMetadata GlobalsMD;
  DenseMap<const AllocaInst *, bool> ProcessedAllocas;
};


 /***********************************************************************************************/

class AddressSanitizerLegacyPass : public FunctionPass {
public:
  static char ID;

  explicit AddressSanitizerLegacyPass(bool CompileKernel = false,
                                      bool Recover = false,
                                      bool UseAfterScope = false)
      : FunctionPass(ID), Recover(Recover),
        UseAfterScope(UseAfterScope) {
    initializeAddressSanitizerLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override {
    return "AddressSanitizerFunctionPass";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AsantGlobalsMetadataWrapperPass>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
  }

  bool runOnFunction(Function &F) override {
    GlobalsMetadata &GlobalsMD =
        getAnalysis<AsantGlobalsMetadataWrapperPass>().getGlobalsMD();
    const TargetLibraryInfo *TLI =
        &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
    AddressSanitizer Asant(*F.getParent(), GlobalsMD, Recover,
                          UseAfterScope);
    return Asant.instrumentFunction(F, TLI);
  }

private:
  bool Recover;
  bool UseAfterScope;
};


/***********************************************************************************************/
class ModuleAddressSanitizer {
public:
  ModuleAddressSanitizer(Module &M, GlobalsMetadata &GlobalsMD,
                         bool CompileKernel = false, bool Recover = false,
                         bool UseGlobalsGC = true, bool UseOdrIndicator = false)
      : GlobalsMD(GlobalsMD), UseGlobalsGC(UseGlobalsGC && ClUseGlobalsGC),
        // Enable aliases as they should have no downside with ODR indicators.
        UsePrivateAlias(UseOdrIndicator || ClUsePrivateAlias),
        UseOdrIndicator(UseOdrIndicator || ClUseOdrIndicator),
        // Not a typo: ClWithComdat is almost completely pointless without
        // ClUseGlobalsGC (because then it only works on modules without
        // globals, which are rare); it is a prerequisite for ClUseGlobalsGC;
        // and both suffer from gold PR19002 for which UseGlobalsGC constructor
        // argument is designed as workaround. Therefore, disable both
        // ClWithComdat and ClUseGlobalsGC unless the frontend says it's ok to
        // do globals-gc.
        UseCtorComdat(UseGlobalsGC && ClWithComdat) {
    this->Recover = ClRecover.getNumOccurrences() > 0 ? ClRecover : Recover;

    C = &(M.getContext());
    int LongSize = M.getDataLayout().getPointerSizeInBits();
    IntptrTy = Type::getIntNTy(*C, LongSize);
    TargetTriple = Triple(M.getTargetTriple());
    Mapping = getShadowMapping(TargetTriple, LongSize);
  }

  bool instrumentModule(Module &);

private:
  void initializeCallbacks(Module &M);

  bool InstrumentGlobals(IRBuilder<> &IRB, Module &M, bool *CtorComdat);
  void InstrumentGlobalsCOFF(IRBuilder<> &IRB, Module &M,
                             ArrayRef<GlobalVariable *> ExtendedGlobals,
                             ArrayRef<Constant *> MetadataInitializers);
  void InstrumentGlobalsELF(IRBuilder<> &IRB, Module &M,
                            ArrayRef<GlobalVariable *> ExtendedGlobals,
                            ArrayRef<Constant *> MetadataInitializers,
                            const std::string &UniqueModuleId);
  void InstrumentGlobalsMachO(IRBuilder<> &IRB, Module &M,
                              ArrayRef<GlobalVariable *> ExtendedGlobals,
                              ArrayRef<Constant *> MetadataInitializers);
  void
  InstrumentGlobalsWithMetadataArray(IRBuilder<> &IRB, Module &M,
                                     ArrayRef<GlobalVariable *> ExtendedGlobals,
                                     ArrayRef<Constant *> MetadataInitializers);

  GlobalVariable *CreateMetadataGlobal(Module &M, Constant *Initializer,
                                       StringRef OriginalName);
  void SetComdatForGlobalMetadata(GlobalVariable *G, GlobalVariable *Metadata,
                                  StringRef InternalSuffix);
  IRBuilder<> CreateAsantModuleDtor(Module &M);

  bool ShouldInstrumentGlobal(GlobalVariable *G);
  bool ShouldUseMachOGlobalsSection() const;
  StringRef getGlobalMetadataSection() const;
  void poisonOneInitializer(Function &GlobalInit, GlobalValue *ModuleName);
  void createInitializerPoisonCalls(Module &M, GlobalValue *ModuleName);
  size_t MinRedzoneSizeForGlobal() const {
    return RedzoneSizeForScale(Mapping.Scale);
  }
  int GetAsantVersion(const Module &M) const;

  GlobalsMetadata GlobalsMD;
  bool CompileKernel;
  bool Recover;
  bool UseGlobalsGC;
  bool UsePrivateAlias;
  bool UseOdrIndicator;
  bool UseCtorComdat;
  Type *IntptrTy;
  LLVMContext *C;
  Triple TargetTriple;
  ShadowMapping Mapping;
  FunctionCallee AsantPoisonGlobals;
  FunctionCallee AsantUnpoisonGlobals;
  FunctionCallee AsantRegisterGlobals;
  FunctionCallee AsantUnregisterGlobals;
  FunctionCallee AsantRegisterImageGlobals;
  FunctionCallee AsantUnregisterImageGlobals;
  FunctionCallee AsantRegisterElfGlobals;
  FunctionCallee AsantUnregisterElfGlobals;

  Function *AsantCtorFunction = nullptr;
  Function *AsantDtorFunction = nullptr;
};
/***********************************************************************************************/

class ModuleAddressSanitizerLegacyPass : public ModulePass {
public:
  static char ID;

  explicit ModuleAddressSanitizerLegacyPass(bool CompileKernel = false,
                                            bool Recover = false,
                                            bool UseGlobalGC = true,
                                            bool UseOdrIndicator = false)
      : ModulePass(ID), CompileKernel(CompileKernel), Recover(Recover),
        UseGlobalGC(UseGlobalGC), UseOdrIndicator(UseOdrIndicator) {
    initializeModuleAddressSanitizerLegacyPassPass(
        *PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override { return "ModuleAddressSanitizer"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AsantGlobalsMetadataWrapperPass>();
  }

  bool runOnModule(Module &M) override {
    errs()<<"one1\n";
    GlobalsMetadata &GlobalsMD =
        getAnalysis<AsantGlobalsMetadataWrapperPass>().getGlobalsMD();
    ModuleAddressSanitizer AsantModule(M, GlobalsMD, CompileKernel, Recover,
                                      UseGlobalGC, UseOdrIndicator);
    return AsantModule.instrumentModule(M);
  }

private:
  bool CompileKernel;
  bool Recover;
  bool UseGlobalGC;
  bool UseOdrIndicator;
};


} // end anonymous namespace

void LocationMetadata::parse(MDNode *MDN) {
  assert(MDN->getNumOperands() == 3);
  MDString *DIFilename = cast<MDString>(MDN->getOperand(0));
  Filename = DIFilename->getString();
  LineNo = mdconst::extract<ConstantInt>(MDN->getOperand(1))->getLimitedValue();
  ColumnNo =
      mdconst::extract<ConstantInt>(MDN->getOperand(2))->getLimitedValue();
}

// FIXME: It would be cleaner to instead attach relevant metadata to the globals
// we want to sanitize instead and reading this metadata on each pass over a
// function instead of reading module level metadata at first.
GlobalsMetadata::GlobalsMetadata(Module &M) {
  NamedMDNode *Globals = M.getNamedMetadata("llvm.asant.globals");
  if (!Globals)
    return;
  for (auto MDN : Globals->operands()) {
    // Metadata node contains the global and the fields of "Entry".
    assert(MDN->getNumOperands() == 5);
    auto *V = mdconst::extract_or_null<Constant>(MDN->getOperand(0));
    // The optimizer may optimize away a global entirely.
    if (!V)
      continue;
    auto *StrippedV = V->stripPointerCasts();
    auto *GV = dyn_cast<GlobalVariable>(StrippedV);
    if (!GV)
      continue;
    // We can already have an entry for GV if it was merged with another
    // global.
    Entry &E = Entries[GV];
    if (auto *Loc = cast_or_null<MDNode>(MDN->getOperand(1)))
      E.SourceLoc.parse(Loc);
    if (auto *Name = cast_or_null<MDString>(MDN->getOperand(2)))
      E.Name = Name->getString();
    ConstantInt *IsDynInit = mdconst::extract<ConstantInt>(MDN->getOperand(3));
    E.IsDynInit |= IsDynInit->isOne();
    ConstantInt *IsBlacklisted =
        mdconst::extract<ConstantInt>(MDN->getOperand(4));
    E.IsBlacklisted |= IsBlacklisted->isOne();
  }
}

AnalysisKey AsantGlobalsMetadataAnalysis::Key;

GlobalsMetadata AsantGlobalsMetadataAnalysis::run(Module &M,
                                                 ModuleAnalysisManager &AM) {
  return GlobalsMetadata(M);
}

AddressSanitizerPass::AddressSanitizerPass(bool CompileKernel, bool Recover,
                                           bool UseAfterScope)
    : CompileKernel(CompileKernel), Recover(Recover),
      UseAfterScope(UseAfterScope) {}

PreservedAnalyses AddressSanitizerPass::run(Function &F,
                                            AnalysisManager<Function> &AM) {
  auto &MAMProxy = AM.getResult<ModuleAnalysisManagerFunctionProxy>(F);
  auto &MAM = MAMProxy.getManager();
  Module &M = *F.getParent();
  if (auto *R = MAM.getCachedResult<AsantGlobalsMetadataAnalysis>(M)) {
    const TargetLibraryInfo *TLI = &AM.getResult<TargetLibraryAnalysis>(F);
    AddressSanitizer Sanitizer(M, *R, Recover, UseAfterScope);
    if (Sanitizer.instrumentFunction(F, TLI))
      return PreservedAnalyses::none();
    return PreservedAnalyses::all();
  }

  report_fatal_error(
      "The AsantGlobalsMetadataAnalysis is required to run before "
      "AddressSanitizer can run");
  return PreservedAnalyses::all();
}

ModuleAddressSanitizerPass::ModuleAddressSanitizerPass(bool CompileKernel,
                                                       bool Recover,
                                                       bool UseGlobalGC,
                                                       bool UseOdrIndicator)
    : CompileKernel(CompileKernel), Recover(Recover), UseGlobalGC(UseGlobalGC),
      UseOdrIndicator(UseOdrIndicator) {}

PreservedAnalyses ModuleAddressSanitizerPass::run(Module &M,
                                                  AnalysisManager<Module> &AM) {
  GlobalsMetadata &GlobalsMD = AM.getResult<AsantGlobalsMetadataAnalysis>(M);
  ModuleAddressSanitizer Sanitizer(M, GlobalsMD, CompileKernel, Recover,
                                   UseGlobalGC, UseOdrIndicator);
  if (Sanitizer.instrumentModule(M))
    return PreservedAnalyses::none();
  return PreservedAnalyses::all();
}

// INITIALIZE_PASS(AsantGlobalsMetadataWrapperPass, "asant-globals-md",
//                 "Read metadata to mark which globals should be instrumented "
//                 "when running Asant.",
//                 false, true)

char AddressSanitizerLegacyPass::ID = 0;

INITIALIZE_PASS_BEGIN(
    AddressSanitizerLegacyPass, "asant",
    "AddressSanitizer: detects use-after-free and out-of-bounds bugs.", false,
    false)
INITIALIZE_PASS_DEPENDENCY(AsantGlobalsMetadataWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_END(
    AddressSanitizerLegacyPass, "asant",
    "AddressSanitizer: detects use-after-free and out-of-bounds bugs.", false,
    false)

FunctionPass *llvm::createAddressSanitizerFunctionPass(bool CompileKernel,
                                                       bool Recover,
                                                       bool UseAfterScope) {
  assert(!CompileKernel || Recover);
  return new AddressSanitizerLegacyPass(CompileKernel, Recover, UseAfterScope);
}

char ModuleAddressSanitizerLegacyPass::ID = 0;

INITIALIZE_PASS(
    ModuleAddressSanitizerLegacyPass, "asant-module",
    "AddressSanitizer: detects use-after-free and out-of-bounds bugs."
    "ModulePass",
    false, false)

ModulePass *llvm::createModuleAddressSanitizerLegacyPassPass(
    bool CompileKernel, bool Recover, bool UseGlobalsGC, bool UseOdrIndicator) {
  assert(!CompileKernel || Recover);
  return new ModuleAddressSanitizerLegacyPass(CompileKernel, Recover,
                                              UseGlobalsGC, UseOdrIndicator);
}

static size_t TypeSizeToSizeIndex(uint32_t TypeSize) {
  size_t Res = countTrailingZeros(TypeSize / 8);
  assert(Res < kNumberOfAccessSizes);
  return Res;
}

/// Create a global describing a source location.
static GlobalVariable *createPrivateGlobalForSourceLoc(Module &M,
                                                       LocationMetadata MD) {
  Constant *LocData[] = {
      createPrivateGlobalForString(M, MD.Filename, true, kAsantGenPrefix),
      ConstantInt::get(Type::getInt32Ty(M.getContext()), MD.LineNo),
      ConstantInt::get(Type::getInt32Ty(M.getContext()), MD.ColumnNo),
  };
  auto LocStruct = ConstantStruct::getAnon(LocData);
  auto GV = new GlobalVariable(M, LocStruct->getType(), true,
                               GlobalValue::PrivateLinkage, LocStruct,
                               kAsantGenPrefix);
  GV->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
  return GV;
}

/// Check if \p G has been created by a trusted compiler pass.
static bool GlobalWasGeneratedByCompiler(GlobalVariable *G) {
  // Do not instrument @llvm.global_ctors, @llvm.used, etc.
  if (G->getName().startswith("llvm."))
    return true;

  // Do not instrument asant globals.
  if (G->getName().startswith(kAsantGenPrefix) ||
      G->getName().startswith(kSanCovGenPrefix) ||
      G->getName().startswith(kODRGenPrefix))
    return true;

  // Do not instrument gcov counter arrays.
  if (G->getName() == "__llvm_gcov_ctr")
    return true;

  return false;
}

Value *AddressSanitizer::memToShadow(Value *Shadow, IRBuilder<> &IRB) {
  // Shadow >> scale
  Shadow = IRB.CreateLShr(Shadow, Mapping.Scale);
  if (Mapping.Offset == 0) return Shadow;
  // (Shadow >> scale) | offset
  Value *ShadowBase;
  if (LocalDynamicShadow)
    ShadowBase = LocalDynamicShadow;
  else
    ShadowBase = ConstantInt::get(IntptrTy, Mapping.Offset);
  if (Mapping.OrShadowOffset)
    return IRB.CreateOr(Shadow, ShadowBase);
  else
    return IRB.CreateAdd(Shadow, ShadowBase);
}

// Instrument memset/memmove/memcpy
void AddressSanitizer::instrumentMemIntrinsic(MemIntrinsic *MI) {
  IRBuilder<> IRB(MI);
  if (isa<MemTransferInst>(MI)) {
    IRB.CreateCall(
        isa<MemMoveInst>(MI) ? AsantMemmove : AsantMemcpy,
        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
         IRB.CreatePointerCast(MI->getOperand(1), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)});
  } else if (isa<MemSetInst>(MI)) {
    IRB.CreateCall(
        AsantMemset,
        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(MI->getOperand(1), IRB.getInt32Ty(), false),
         IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)});
  }
  MI->eraseFromParent();
}

/// Check if we want (and can) handle this alloca.
bool AddressSanitizer::isInterestingAlloca(const AllocaInst &AI) {
  auto PreviouslySeenAllocaInfo = ProcessedAllocas.find(&AI);

  if (PreviouslySeenAllocaInfo != ProcessedAllocas.end())
    return PreviouslySeenAllocaInfo->getSecond();

  bool IsInteresting =
      (AI.getAllocatedType()->isSized() &&
       // alloca() may be called with 0 size, ignore it.
       ((!AI.isStaticAlloca()) || getAllocaSizeInBytes(AI) > 0) &&
       // We are only interested in allocas not promotable to registers.
       // Promotable allocas are common under -O0.
       (!ClSkipPromotableAllocas || !isAllocaPromotable(&AI)) &&
       // inalloca allocas are not treated as static, and we don't want
       // dynamic alloca instrumentation for them as well.
       !AI.isUsedWithInAlloca() &&
       // swifterror allocas are register promoted by ISel
       !AI.isSwiftError());

  ProcessedAllocas[&AI] = IsInteresting;
  return IsInteresting;
}

Value *AddressSanitizer::isInterestingMemoryAccess(Instruction *I,
                                                   bool *IsWrite,
                                                   uint64_t *TypeSize,
                                                   unsigned *Alignment,
                                                   Value **MaybeMask) {
  // Skip memory accesses inserted by another instrumentation.
  if (I->getMetadata("nosanitize")) return nullptr;

  // Do not instrument the load fetching the dynamic shadow address.
  if (LocalDynamicShadow == I)
    return nullptr;

  Value *PtrOperand = nullptr;
  const DataLayout &DL = I->getModule()->getDataLayout();
  if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    if (!ClInstrumentReads) return nullptr;
    *IsWrite = false;
    *TypeSize = DL.getTypeStoreSizeInBits(LI->getType());
    *Alignment = LI->getAlignment();
    PtrOperand = LI->getPointerOperand();
  } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    if (!ClInstrumentWrites) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(SI->getValueOperand()->getType());
    *Alignment = SI->getAlignment();
    PtrOperand = SI->getPointerOperand();
  } else if (AtomicRMWInst *RMW = dyn_cast<AtomicRMWInst>(I)) {
    if (!ClInstrumentAtomics) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(RMW->getValOperand()->getType());
    *Alignment = 0;
    PtrOperand = RMW->getPointerOperand();
  } else if (AtomicCmpXchgInst *XCHG = dyn_cast<AtomicCmpXchgInst>(I)) {
    if (!ClInstrumentAtomics) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(XCHG->getCompareOperand()->getType());
    *Alignment = 0;
    PtrOperand = XCHG->getPointerOperand();
  } else if (auto CI = dyn_cast<CallInst>(I)) {
    auto *F = dyn_cast<Function>(CI->getCalledValue());
    if (F && (F->getName().startswith("llvm.masked.load.") ||
              F->getName().startswith("llvm.masked.store."))) {
      unsigned OpOffset = 0;
      if (F->getName().startswith("llvm.masked.store.")) {
        if (!ClInstrumentWrites)
          return nullptr;
        // Masked store has an initial operand for the value.
        OpOffset = 1;
        *IsWrite = true;
      } else {
        if (!ClInstrumentReads)
          return nullptr;
        *IsWrite = false;
      }

      auto BasePtr = CI->getOperand(0 + OpOffset);
      auto Ty = cast<PointerType>(BasePtr->getType())->getElementType();
      *TypeSize = DL.getTypeStoreSizeInBits(Ty);
      if (auto AlignmentConstant =
              dyn_cast<ConstantInt>(CI->getOperand(1 + OpOffset)))
        *Alignment = (unsigned)AlignmentConstant->getZExtValue();
      else
        *Alignment = 1; // No alignment guarantees. We probably got Undef
      if (MaybeMask)
        *MaybeMask = CI->getOperand(2 + OpOffset);
      PtrOperand = BasePtr;
    }
  }

  if (PtrOperand) {
    // Do not instrument acesses from different address spaces; we cannot deal
    // with them.
    Type *PtrTy = cast<PointerType>(PtrOperand->getType()->getScalarType());
    if (PtrTy->getPointerAddressSpace() != 0)
      return nullptr;

    // Ignore swifterror addresses.
    // swifterror memory addresses are mem2reg promoted by instruction
    // selection. As such they cannot have regular uses like an instrumentation
    // function and it makes no sense to track them as memory.
    if (PtrOperand->isSwiftError())
      return nullptr;
  }

  // Treat memory accesses to promotable allocas as non-interesting since they
  // will not cause memory violations. This greatly speeds up the instrumented
  // executable at -O0.
  if (ClSkipPromotableAllocas)
    if (auto AI = dyn_cast_or_null<AllocaInst>(PtrOperand))
      return isInterestingAlloca(*AI) ? AI : nullptr;

  return PtrOperand;
}

static bool isPointerOperand(Value *V) {
  return V->getType()->isPointerTy() || isa<PtrToIntInst>(V);
}

// This is a rough heuristic; it may cause both false positives and
// false negatives. The proper implementation requires cooperation with
// the frontend.
static bool isInterestingPointerComparison(Instruction *I) {
  if (ICmpInst *Cmp = dyn_cast<ICmpInst>(I)) {
    if (!Cmp->isRelational())
      return false;
  } else {
    return false;
  }
  return isPointerOperand(I->getOperand(0)) &&
         isPointerOperand(I->getOperand(1));
}

// This is a rough heuristic; it may cause both false positives and
// false negatives. The proper implementation requires cooperation with
// the frontend.
static bool isInterestingPointerSubtraction(Instruction *I) {
  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(I)) {
    if (BO->getOpcode() != Instruction::Sub)
      return false;
  } else {
    return false;
  }
  return isPointerOperand(I->getOperand(0)) &&
         isPointerOperand(I->getOperand(1));
}

bool AddressSanitizer::GlobalIsLinkerInitialized(GlobalVariable *G) {
  // If a global variable does not have dynamic initialization we don't
  // have to instrument it.  However, if a global does not have initializer
  // at all, we assume it has dynamic initializer (in other TU).
  //
  // FIXME: Metadata should be attched directly to the global directly instead
  // of being added to llvm.asant.globals.
  return G->hasInitializer() && !GlobalsMD.get(G).IsDynInit;
}

void AddressSanitizer::instrumentPointerComparisonOrSubtraction(
    Instruction *I) {
  IRBuilder<> IRB(I);
  FunctionCallee F = isa<ICmpInst>(I) ? AsantPtrCmpFunction : AsantPtrSubFunction;
  Value *Param[2] = {I->getOperand(0), I->getOperand(1)};
  for (Value *&i : Param) {
    if (i->getType()->isPointerTy())
      i = IRB.CreatePointerCast(i, IntptrTy);
  }
  IRB.CreateCall(F, Param);
}

static void doInstrumentAddress(AddressSanitizer *Pass, Instruction *I,
                                Instruction *InsertBefore, Value *Addr,
                                unsigned Alignment, unsigned Granularity,
                                uint32_t TypeSize, bool IsWrite,
                                Value *SizeArgument, bool UseCalls,
                                uint32_t Exp) {
  // Instrument a 1-, 2-, 4-, 8-, or 16- byte access with one check
  // if the data is properly aligned.
  if ((TypeSize == 8 || TypeSize == 16 || TypeSize == 32 || TypeSize == 64 ||
       TypeSize == 128) &&
      (Alignment >= Granularity || Alignment == 0 || Alignment >= TypeSize / 8))
    return Pass->instrumentAddress(I, InsertBefore, Addr, TypeSize, IsWrite,
                                   nullptr, UseCalls, Exp);
  Pass->instrumentUnusualSizeOrAlignment(I, InsertBefore, Addr, TypeSize,
                                         IsWrite, nullptr, UseCalls, Exp);
}

static void instrumentMaskedLoadOrStore(AddressSanitizer *Pass,
                                        const DataLayout &DL, Type *IntptrTy,
                                        Value *Mask, Instruction *I,
                                        Value *Addr, unsigned Alignment,
                                        unsigned Granularity, uint32_t TypeSize,
                                        bool IsWrite, Value *SizeArgument,
                                        bool UseCalls, uint32_t Exp) {
  auto *VTy = cast<PointerType>(Addr->getType())->getElementType();
  uint64_t ElemTypeSize = DL.getTypeStoreSizeInBits(VTy->getScalarType());
  unsigned Num = VTy->getVectorNumElements();
  auto Zero = ConstantInt::get(IntptrTy, 0);
  for (unsigned Idx = 0; Idx < Num; ++Idx) {
    Value *InstrumentedAddress = nullptr;
    Instruction *InsertBefore = I;
    if (auto *Vector = dyn_cast<ConstantVector>(Mask)) {
      // dyn_cast as we might get UndefValue
      if (auto *Masked = dyn_cast<ConstantInt>(Vector->getOperand(Idx))) {
        if (Masked->isZero())
          // Mask is constant false, so no instrumentation needed.
          continue;
        // If we have a true or undef value, fall through to doInstrumentAddress
        // with InsertBefore == I
      }
    } else {
      IRBuilder<> IRB(I);
      Value *MaskElem = IRB.CreateExtractElement(Mask, Idx);
      Instruction *ThenTerm = SplitBlockAndInsertIfThen(MaskElem, I, false);
      InsertBefore = ThenTerm;
    }

    IRBuilder<> IRB(InsertBefore);
    InstrumentedAddress =
        IRB.CreateGEP(VTy, Addr, {Zero, ConstantInt::get(IntptrTy, Idx)});
    doInstrumentAddress(Pass, I, InsertBefore, InstrumentedAddress, Alignment,
                        Granularity, ElemTypeSize, IsWrite, SizeArgument,
                        UseCalls, Exp);
  }
}

void AddressSanitizer::instrumentMop(ObjectSizeOffsetVisitor &ObjSizeVis,
                                     Instruction *I, bool UseCalls,
                                     const DataLayout &DL) {
  bool IsWrite = false;
  unsigned Alignment = 0;
  uint64_t TypeSize = 0;
  Value *MaybeMask = nullptr;
  Value *Addr =
      isInterestingMemoryAccess(I, &IsWrite, &TypeSize, &Alignment, &MaybeMask);
  assert(Addr);

  // Optimization experiments.
  // The experiments can be used to evaluate potential optimizations that remove
  // instrumentation (assess false negatives). Instead of completely removing
  // some instrumentation, you set Exp to a non-zero value (mask of optimization
  // experiments that want to remove instrumentation of this instruction).
  // If Exp is non-zero, this pass will emit special calls into runtime
  // (e.g. __asant_report_exp_load1 instead of __asant_report_load1). These calls
  // make runtime terminate the program in a special way (with a different
  // exit status). Then you run the new compiler on a buggy corpus, collect
  // the special terminations (ideally, you don't see them at all -- no false
  // negatives) and make the decision on the optimization.
  uint32_t Exp = ClForceExperiment;

  if (ClOpt && ClOptGlobals) {
    // If initialization order checking is disabled, a simple access to a
    // dynamically initialized global is always valid.
    GlobalVariable *G = dyn_cast<GlobalVariable>(GetUnderlyingObject(Addr, DL));
    if (G && (!ClInitializers || GlobalIsLinkerInitialized(G)) &&
        isSafeAccess(ObjSizeVis, Addr, TypeSize)) {
      NumOptimizedAccessesToGlobalVar++;
      return;
    }
  }

  if (ClOpt && ClOptStack) {
    // A direct inbounds access to a stack variable is always valid.
    if (isa<AllocaInst>(GetUnderlyingObject(Addr, DL)) &&
        isSafeAccess(ObjSizeVis, Addr, TypeSize)) {
      NumOptimizedAccessesToStackVar++;
      return;
    }
  }

  if (IsWrite)
    NumInstrumentedWrites++;
  else
    NumInstrumentedReads++;

  unsigned Granularity = 1 << Mapping.Scale;
  if (MaybeMask) {
    instrumentMaskedLoadOrStore(this, DL, IntptrTy, MaybeMask, I, Addr,
                                Alignment, Granularity, TypeSize, IsWrite,
                                nullptr, UseCalls, Exp);
  } else {
    doInstrumentAddress(this, I, I, Addr, Alignment, Granularity, TypeSize,
                        IsWrite, nullptr, UseCalls, Exp);
  }
}

Instruction *AddressSanitizer::generateCrashCode(Instruction *InsertBefore,
                                                 Value *Addr, bool IsWrite,
                                                 size_t AccessSizeIndex,
                                                 Value *SizeArgument,
                                                 uint32_t Exp) {
  IRBuilder<> IRB(InsertBefore);
  Value *ExpVal = Exp == 0 ? nullptr : ConstantInt::get(IRB.getInt32Ty(), Exp);
  CallInst *Call = nullptr;
  if (SizeArgument) {
    if (Exp == 0)
      Call = IRB.CreateCall(AsantErrorCallbackSized[IsWrite][0],
                            {Addr, SizeArgument});
    else
      Call = IRB.CreateCall(AsantErrorCallbackSized[IsWrite][1],
                            {Addr, SizeArgument, ExpVal});
  } else {
    if (Exp == 0)
      Call =
          IRB.CreateCall(AsantErrorCallback[IsWrite][0][AccessSizeIndex], Addr);
    else
      Call = IRB.CreateCall(AsantErrorCallback[IsWrite][1][AccessSizeIndex],
                            {Addr, ExpVal});
  }

  // We don't do Call->setDoesNotReturn() because the BB already has
  // UnreachableInst at the end.
  // This EmptyAsm is required to avoid callback merge.
  IRB.CreateCall(EmptyAsm, {});
  return Call;
}

Value *AddressSanitizer::createSlowPathCmp(IRBuilder<> &IRB, Value *AddrLong,
                                           Value *ShadowValue,
                                           uint32_t TypeSize) {
  size_t Granularity = static_cast<size_t>(1) << Mapping.Scale;
  // Addr & (Granularity - 1)
  Value *LastAccessedByte =
      IRB.CreateAnd(AddrLong, ConstantInt::get(IntptrTy, Granularity - 1));
  // (Addr & (Granularity - 1)) + size - 1
  if (TypeSize / 8 > 1)
    LastAccessedByte = IRB.CreateAdd(
        LastAccessedByte, ConstantInt::get(IntptrTy, TypeSize / 8 - 1));
  // (uint8_t) ((Addr & (Granularity-1)) + size - 1)
  LastAccessedByte =
      IRB.CreateIntCast(LastAccessedByte, ShadowValue->getType(), false);
  // ((uint8_t) ((Addr & (Granularity-1)) + size - 1)) >= ShadowValue
  return IRB.CreateICmpSGE(LastAccessedByte, ShadowValue);
}

void AddressSanitizer::instrumentAddress(Instruction *OrigIns,
                                         Instruction *InsertBefore, Value *Addr,
                                         uint32_t TypeSize, bool IsWrite,
                                         Value *SizeArgument, bool UseCalls,
                                         uint32_t Exp) {

  IRBuilder<> IRB(InsertBefore);
  Value *AddrLong = IRB.CreatePointerCast(Addr, IntptrTy);
  size_t AccessSizeIndex = TypeSizeToSizeIndex(TypeSize);

  if (UseCalls) {
    if (Exp == 0)
      IRB.CreateCall(AsantMemoryAccessCallback[IsWrite][0][AccessSizeIndex],
                     AddrLong);
    else
      IRB.CreateCall(AsantMemoryAccessCallback[IsWrite][1][AccessSizeIndex],
                     {AddrLong, ConstantInt::get(IRB.getInt32Ty(), Exp)});
    return;
  }


  Type *ShadowTy =
      IntegerType::get(*C, std::max(8U, TypeSize >> Mapping.Scale));
  Type *ShadowPtrTy = PointerType::get(ShadowTy, 0);
  Value *ShadowPtr = memToShadow(AddrLong, IRB);
  Value *CmpVal = Constant::getNullValue(ShadowTy);
  Value *ShadowValue =
      IRB.CreateLoad(ShadowTy, IRB.CreateIntToPtr(ShadowPtr, ShadowPtrTy));

  Value *Cmp = IRB.CreateICmpNE(ShadowValue, CmpVal);
  size_t Granularity = 1ULL << Mapping.Scale;
  Instruction *CrashTerm = nullptr;

  if (ClAlwaysSlowPath || (TypeSize < 8 * Granularity)) {
    // We use branch weights for the slow path check, to indicate that the slow
    // path is rarely taken. This seems to be the case for SPEC benchmarks.
    Instruction *CheckTerm = SplitBlockAndInsertIfThen(
        Cmp, InsertBefore, false, MDBuilder(*C).createBranchWeights(1, 100000));
    assert(cast<BranchInst>(CheckTerm)->isUnconditional());
    BasicBlock *NextBB = CheckTerm->getSuccessor(0);
    IRB.SetInsertPoint(CheckTerm);
    Value *Cmp2 = createSlowPathCmp(IRB, AddrLong, ShadowValue, TypeSize);
    if (Recover) {
      CrashTerm = SplitBlockAndInsertIfThen(Cmp2, CheckTerm, false);
    } else {
      BasicBlock *CrashBlock =
        BasicBlock::Create(*C, "", NextBB->getParent(), NextBB);
      CrashTerm = new UnreachableInst(*C, CrashBlock);
      BranchInst *NewTerm = BranchInst::Create(CrashBlock, NextBB, Cmp2);
      ReplaceInstWithInst(CheckTerm, NewTerm);
    }
  } else {
    CrashTerm = SplitBlockAndInsertIfThen(Cmp, InsertBefore, !Recover);
  }

  Instruction *Crash = generateCrashCode(CrashTerm, AddrLong, IsWrite,
                                         AccessSizeIndex, SizeArgument, Exp);
  Crash->setDebugLoc(OrigIns->getDebugLoc());
}

// Instrument unusual size or unusual alignment.
// We can not do it with a single check, so we do 1-byte check for the first
// and the last bytes. We call __asant_report_*_n(addr, real_size) to be able
// to report the actual access size.
void AddressSanitizer::instrumentUnusualSizeOrAlignment(
    Instruction *I, Instruction *InsertBefore, Value *Addr, uint32_t TypeSize,
    bool IsWrite, Value *SizeArgument, bool UseCalls, uint32_t Exp) {
  IRBuilder<> IRB(InsertBefore);
  Value *Size = ConstantInt::get(IntptrTy, TypeSize / 8);
  Value *AddrLong = IRB.CreatePointerCast(Addr, IntptrTy);
  if (UseCalls) {
    if (Exp == 0)
      IRB.CreateCall(AsantMemoryAccessCallbackSized[IsWrite][0],
                     {AddrLong, Size});
    else
      IRB.CreateCall(AsantMemoryAccessCallbackSized[IsWrite][1],
                     {AddrLong, Size, ConstantInt::get(IRB.getInt32Ty(), Exp)});
  } else {
    Value *LastByte = IRB.CreateIntToPtr(
        IRB.CreateAdd(AddrLong, ConstantInt::get(IntptrTy, TypeSize / 8 - 1)),
        Addr->getType());
    instrumentAddress(I, InsertBefore, Addr, 8, IsWrite, Size, false, Exp);
    instrumentAddress(I, InsertBefore, LastByte, 8, IsWrite, Size, false, Exp);
  }
}

void ModuleAddressSanitizer::poisonOneInitializer(Function &GlobalInit,
                                                  GlobalValue *ModuleName) {
  // Set up the arguments to our poison/unpoison functions.
  IRBuilder<> IRB(&GlobalInit.front(),
                  GlobalInit.front().getFirstInsertionPt());

  // Add a call to poison all external globals before the given function starts.
  Value *ModuleNameAddr = ConstantExpr::getPointerCast(ModuleName, IntptrTy);
  IRB.CreateCall(AsantPoisonGlobals, ModuleNameAddr);

  // Add calls to unpoison all globals before each return instruction.
  for (auto &BB : GlobalInit.getBasicBlockList())
    if (ReturnInst *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
      CallInst::Create(AsantUnpoisonGlobals, "", RI);
}

void ModuleAddressSanitizer::createInitializerPoisonCalls(
    Module &M, GlobalValue *ModuleName) {
  GlobalVariable *GV = M.getGlobalVariable("llvm.global_ctors");
  if (!GV)
    return;

  ConstantArray *CA = dyn_cast<ConstantArray>(GV->getInitializer());
  if (!CA)
    return;

  for (Use &OP : CA->operands()) {
    if (isa<ConstantAggregateZero>(OP)) continue;
    ConstantStruct *CS = cast<ConstantStruct>(OP);

    // Must have a function or null ptr.
    if (Function *F = dyn_cast<Function>(CS->getOperand(1))) {
      if (F->getName() == kAsantModuleCtorName) continue;
      ConstantInt *Priority = dyn_cast<ConstantInt>(CS->getOperand(0));
      // Don't instrument CTORs that will run before asant.module_ctor.
      if (Priority->getLimitedValue() <= kAsantCtorAndDtorPriority) continue;
      poisonOneInitializer(*F, ModuleName);
    }
  }
}

bool ModuleAddressSanitizer::ShouldInstrumentGlobal(GlobalVariable *G) {
  Type *Ty = G->getValueType();
  LLVM_DEBUG(dbgs() << "GLOBAL: " << *G << "\n");

  // FIXME: Metadata should be attched directly to the global directly instead
  // of being added to llvm.asant.globals.
  if (GlobalsMD.get(G).IsBlacklisted) return false;
  if (!Ty->isSized()) return false;
  if (!G->hasInitializer()) return false;
  if (GlobalWasGeneratedByCompiler(G)) return false; // Our own globals.
  // Two problems with thread-locals:
  //   - The address of the main thread's copy can't be computed at link-time.
  //   - Need to poison all copies, not just the main thread's one.
  if (G->isThreadLocal()) return false;
  // For now, just ignore this Global if the alignment is large.
  if (G->getAlignment() > MinRedzoneSizeForGlobal()) return false;

  // For non-COFF targets, only instrument globals known to be defined by this
  // TU.
  // FIXME: We can instrument comdat globals on ELF if we are using the
  // GC-friendly metadata scheme.
  if (!TargetTriple.isOSBinFormatCOFF()) {
    if (!G->hasExactDefinition() || G->hasComdat())
      return false;
  } else {
    // On COFF, don't instrument non-ODR linkages.
    if (G->isInterposable())
      return false;
  }

  // If a comdat is present, it must have a selection kind that implies ODR
  // semantics: no duplicates, any, or exact match.
  if (Comdat *C = G->getComdat()) {
    switch (C->getSelectionKind()) {
    case Comdat::Any:
    case Comdat::ExactMatch:
    case Comdat::NoDuplicates:
      break;
    case Comdat::Largest:
    case Comdat::SameSize:
      return false;
    }
  }

  if (G->hasSection()) {
    StringRef Section = G->getSection();

    // Globals from llvm.metadata aren't emitted, do not instrument them.
    if (Section == "llvm.metadata") return false;
    // Do not instrument globals from special LLVM sections.
    if (Section.find("__llvm") != StringRef::npos || Section.find("__LLVM") != StringRef::npos) return false;

    // Do not instrument function pointers to initialization and termination
    // routines: dynamic linker will not properly handle redzones.
    if (Section.startswith(".preinit_array") ||
        Section.startswith(".init_array") ||
        Section.startswith(".fini_array")) {
      return false;
    }

    // On COFF, if the section name contains '$', it is highly likely that the
    // user is using section sorting to create an array of globals similar to
    // the way initialization callbacks are registered in .init_array and
    // .CRT$XCU. The ATL also registers things in .ATL$__[azm]. Adding redzones
    // to such globals is counterproductive, because the intent is that they
    // will form an array, and out-of-bounds accesses are expected.
    // See https://github.com/google/sanitizers/issues/305
    // and http://msdn.microsoft.com/en-US/en-en/library/bb918180(v=vs.120).aspx
    if (TargetTriple.isOSBinFormatCOFF() && Section.contains('$')) {
      LLVM_DEBUG(dbgs() << "Ignoring global in sorted section (contains '$'): "
                        << *G << "\n");
      return false;
    }

    if (TargetTriple.isOSBinFormatMachO()) {
      StringRef ParsedSegment, ParsedSection;
      unsigned TAA = 0, StubSize = 0;
      bool TAAParsed;
      std::string ErrorCode = MCSectionMachO::ParseSectionSpecifier(
          Section, ParsedSegment, ParsedSection, TAA, TAAParsed, StubSize);
      assert(ErrorCode.empty() && "Invalid section specifier.");

      // Ignore the globals from the __OBJC section. The ObjC runtime assumes
      // those conform to /usr/lib/objc/runtime.h, so we can't add redzones to
      // them.
      if (ParsedSegment == "__OBJC" ||
          (ParsedSegment == "__DATA" && ParsedSection.startswith("__objc_"))) {
        LLVM_DEBUG(dbgs() << "Ignoring ObjC runtime global: " << *G << "\n");
        return false;
      }
      // See https://github.com/google/sanitizers/issues/32
      // Constant CFString instances are compiled in the following way:
      //  -- the string buffer is emitted into
      //     __TEXT,__cstring,cstring_literals
      //  -- the constant NSConstantString structure referencing that buffer
      //     is placed into __DATA,__cfstring
      // Therefore there's no point in placing redzones into __DATA,__cfstring.
      // Moreover, it causes the linker to crash on OS X 10.7
      if (ParsedSegment == "__DATA" && ParsedSection == "__cfstring") {
        LLVM_DEBUG(dbgs() << "Ignoring CFString: " << *G << "\n");
        return false;
      }
      // The linker merges the contents of cstring_literals and removes the
      // trailing zeroes.
      if (ParsedSegment == "__TEXT" && (TAA & MachO::S_CSTRING_LITERALS)) {
        LLVM_DEBUG(dbgs() << "Ignoring a cstring literal: " << *G << "\n");
        return false;
      }
    }
  }

  return true;
}

// On Mach-O platforms, we emit global metadata in a separate section of the
// binary in order to allow the linker to properly dead strip. This is only
// supported on recent versions of ld64.
bool ModuleAddressSanitizer::ShouldUseMachOGlobalsSection() const {
  if (!TargetTriple.isOSBinFormatMachO())
    return false;

  if (TargetTriple.isMacOSX() && !TargetTriple.isMacOSXVersionLT(10, 11))
    return true;
  if (TargetTriple.isiOS() /* or tvOS */ && !TargetTriple.isOSVersionLT(9))
    return true;
  if (TargetTriple.isWatchOS() && !TargetTriple.isOSVersionLT(2))
    return true;

  return false;
}

StringRef ModuleAddressSanitizer::getGlobalMetadataSection() const {
  switch (TargetTriple.getObjectFormat()) {
  case Triple::COFF:  return ".ASANT$GL";
  case Triple::ELF:   return "asant_globals";
  case Triple::MachO: return "__DATA,__asant_globals,regular";
  default: break;
  }
  llvm_unreachable("unsupported object format");
}

void ModuleAddressSanitizer::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);

  // Declare our poisoning and unpoisoning functions.
  AsantPoisonGlobals =
      M.getOrInsertFunction(kAsantPoisonGlobalsName, IRB.getVoidTy(), IntptrTy);
  AsantUnpoisonGlobals =
      M.getOrInsertFunction(kAsantUnpoisonGlobalsName, IRB.getVoidTy());

  // Declare functions that register/unregister globals.
  AsantRegisterGlobals = M.getOrInsertFunction(
      kAsantRegisterGlobalsName, IRB.getVoidTy(), IntptrTy, IntptrTy);
  AsantUnregisterGlobals = M.getOrInsertFunction(
      kAsantUnregisterGlobalsName, IRB.getVoidTy(), IntptrTy, IntptrTy);

  // Declare the functions that find globals in a shared object and then invoke
  // the (un)register function on them.
  AsantRegisterImageGlobals = M.getOrInsertFunction(
      kAsantRegisterImageGlobalsName, IRB.getVoidTy(), IntptrTy);
  AsantUnregisterImageGlobals = M.getOrInsertFunction(
      kAsantUnregisterImageGlobalsName, IRB.getVoidTy(), IntptrTy);

  AsantRegisterElfGlobals =
      M.getOrInsertFunction(kAsantRegisterElfGlobalsName, IRB.getVoidTy(),
                            IntptrTy, IntptrTy, IntptrTy);
  AsantUnregisterElfGlobals =
      M.getOrInsertFunction(kAsantUnregisterElfGlobalsName, IRB.getVoidTy(),
                            IntptrTy, IntptrTy, IntptrTy);
}

// Put the metadata and the instrumented global in the same group. This ensures
// that the metadata is discarded if the instrumented global is discarded.
void ModuleAddressSanitizer::SetComdatForGlobalMetadata(
    GlobalVariable *G, GlobalVariable *Metadata, StringRef InternalSuffix) {
  Module &M = *G->getParent();
  Comdat *C = G->getComdat();
  if (!C) {
    if (!G->hasName()) {
      // If G is unnamed, it must be internal. Give it an artificial name
      // so we can put it in a comdat.
      assert(G->hasLocalLinkage());
      G->setName(Twine(kAsantGenPrefix) + "_anon_global");
    }

    if (!InternalSuffix.empty() && G->hasLocalLinkage()) {
      std::string Name = G->getName();
      Name += InternalSuffix;
      C = M.getOrInsertComdat(Name);
    } else {
      C = M.getOrInsertComdat(G->getName());
    }

    // Make this IMAGE_COMDAT_SELECT_NODUPLICATES on COFF. Also upgrade private
    // linkage to internal linkage so that a symbol table entry is emitted. This
    // is necessary in order to create the comdat group.
    if (TargetTriple.isOSBinFormatCOFF()) {
      C->setSelectionKind(Comdat::NoDuplicates);
      if (G->hasPrivateLinkage())
        G->setLinkage(GlobalValue::InternalLinkage);
    }
    G->setComdat(C);
  }

  assert(G->hasComdat());
  Metadata->setComdat(G->getComdat());
}

// Create a separate metadata global and put it in the appropriate Asant
// global registration section.
GlobalVariable *
ModuleAddressSanitizer::CreateMetadataGlobal(Module &M, Constant *Initializer,
                                             StringRef OriginalName) {
  auto Linkage = TargetTriple.isOSBinFormatMachO()
                     ? GlobalVariable::InternalLinkage
                     : GlobalVariable::PrivateLinkage;
  GlobalVariable *Metadata = new GlobalVariable(
      M, Initializer->getType(), false, Linkage, Initializer,
      Twine("__asant_global_") + GlobalValue::dropLLVMManglingEscape(OriginalName));
  Metadata->setSection(getGlobalMetadataSection());
  return Metadata;
}

IRBuilder<> ModuleAddressSanitizer::CreateAsantModuleDtor(Module &M) {
  AsantDtorFunction =
      Function::Create(FunctionType::get(Type::getVoidTy(*C), false),
                       GlobalValue::InternalLinkage, kAsantModuleDtorName, &M);
  BasicBlock *AsantDtorBB = BasicBlock::Create(*C, "", AsantDtorFunction);

  return IRBuilder<>(ReturnInst::Create(*C, AsantDtorBB));
}

void ModuleAddressSanitizer::InstrumentGlobalsCOFF(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());
  auto &DL = M.getDataLayout();

  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    Constant *Initializer = MetadataInitializers[i];
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, Initializer, G->getName());

    // The MSVC linker always inserts padding when linking incrementally. We
    // cope with that by aligning each struct to its size, which must be a power
    // of two.
    unsigned SizeOfGlobalStruct = DL.getTypeAllocSize(Initializer->getType());
    assert(isPowerOf2_32(SizeOfGlobalStruct) &&
           "global metadata will not be padded appropriately");
    Metadata->setAlignment(SizeOfGlobalStruct);

    SetComdatForGlobalMetadata(G, Metadata, "");
  }
}

void ModuleAddressSanitizer::InstrumentGlobalsELF(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers,
    const std::string &UniqueModuleId) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());

  SmallVector<GlobalValue *, 16> MetadataGlobals(ExtendedGlobals.size());
  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, MetadataInitializers[i], G->getName());
    MDNode *MD = MDNode::get(M.getContext(), ValueAsMetadata::get(G));
    Metadata->setMetadata(LLVMContext::MD_associated, MD);
    MetadataGlobals[i] = Metadata;

    SetComdatForGlobalMetadata(G, Metadata, UniqueModuleId);
  }

  // Update llvm.compiler.used, adding the new metadata globals. This is
  // needed so that during LTO these variables stay alive.
  if (!MetadataGlobals.empty())
    appendToCompilerUsed(M, MetadataGlobals);

  // RegisteredFlag serves two purposes. First, we can pass it to dladdr()
  // to look up the loaded image that contains it. Second, we can store in it
  // whether registration has already occurred, to prevent duplicate
  // registration.
  //
  // Common linkage ensures that there is only one global per shared library.
  GlobalVariable *RegisteredFlag = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::CommonLinkage,
      ConstantInt::get(IntptrTy, 0), kAsantGlobalsRegisteredFlagName);
  RegisteredFlag->setVisibility(GlobalVariable::HiddenVisibility);

  // Create start and stop symbols.
  GlobalVariable *StartELFMetadata = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::ExternalWeakLinkage, nullptr,
      "__start_" + getGlobalMetadataSection());
  StartELFMetadata->setVisibility(GlobalVariable::HiddenVisibility);
  GlobalVariable *StopELFMetadata = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::ExternalWeakLinkage, nullptr,
      "__stop_" + getGlobalMetadataSection());
  StopELFMetadata->setVisibility(GlobalVariable::HiddenVisibility);

  // Create a call to register the globals with the runtime.
  IRB.CreateCall(AsantRegisterElfGlobals,
                 {IRB.CreatePointerCast(RegisteredFlag, IntptrTy),
                  IRB.CreatePointerCast(StartELFMetadata, IntptrTy),
                  IRB.CreatePointerCast(StopELFMetadata, IntptrTy)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsantModuleDtor(M);
  IRB_Dtor.CreateCall(AsantUnregisterElfGlobals,
                      {IRB.CreatePointerCast(RegisteredFlag, IntptrTy),
                       IRB.CreatePointerCast(StartELFMetadata, IntptrTy),
                       IRB.CreatePointerCast(StopELFMetadata, IntptrTy)});
}

void ModuleAddressSanitizer::InstrumentGlobalsMachO(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());

  // On recent Mach-O platforms, use a structure which binds the liveness of
  // the global variable to the metadata struct. Keep the list of "Liveness" GV
  // created to be added to llvm.compiler.used
  StructType *LivenessTy = StructType::get(IntptrTy, IntptrTy);
  SmallVector<GlobalValue *, 16> LivenessGlobals(ExtendedGlobals.size());

  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    Constant *Initializer = MetadataInitializers[i];
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, Initializer, G->getName());

    // On recent Mach-O platforms, we emit the global metadata in a way that
    // allows the linker to properly strip dead globals.
    auto LivenessBinder =
        ConstantStruct::get(LivenessTy, Initializer->getAggregateElement(0u),
                            ConstantExpr::getPointerCast(Metadata, IntptrTy));
    GlobalVariable *Liveness = new GlobalVariable(
        M, LivenessTy, false, GlobalVariable::InternalLinkage, LivenessBinder,
        Twine("__asant_binder_") + G->getName());
    Liveness->setSection("__DATA,__asant_liveness,regular,live_support");
    LivenessGlobals[i] = Liveness;
  }

  // Update llvm.compiler.used, adding the new liveness globals. This is
  // needed so that during LTO these variables stay alive. The alternative
  // would be to have the linker handling the LTO symbols, but libLTO
  // current API does not expose access to the section for each symbol.
  if (!LivenessGlobals.empty())
    appendToCompilerUsed(M, LivenessGlobals);

  // RegisteredFlag serves two purposes. First, we can pass it to dladdr()
  // to look up the loaded image that contains it. Second, we can store in it
  // whether registration has already occurred, to prevent duplicate
  // registration.
  //
  // common linkage ensures that there is only one global per shared library.
  GlobalVariable *RegisteredFlag = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::CommonLinkage,
      ConstantInt::get(IntptrTy, 0), kAsantGlobalsRegisteredFlagName);
  RegisteredFlag->setVisibility(GlobalVariable::HiddenVisibility);

  IRB.CreateCall(AsantRegisterImageGlobals,
                 {IRB.CreatePointerCast(RegisteredFlag, IntptrTy)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsantModuleDtor(M);
  IRB_Dtor.CreateCall(AsantUnregisterImageGlobals,
                      {IRB.CreatePointerCast(RegisteredFlag, IntptrTy)});
}

void ModuleAddressSanitizer::InstrumentGlobalsWithMetadataArray(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());
  unsigned N = ExtendedGlobals.size();
  assert(N > 0);

  // On platforms that don't have a custom metadata section, we emit an array
  // of global metadata structures.
  ArrayType *ArrayOfGlobalStructTy =
      ArrayType::get(MetadataInitializers[0]->getType(), N);
  auto AllGlobals = new GlobalVariable(
      M, ArrayOfGlobalStructTy, false, GlobalVariable::InternalLinkage,
      ConstantArray::get(ArrayOfGlobalStructTy, MetadataInitializers), "");
  if (Mapping.Scale > 3)
    AllGlobals->setAlignment(1ULL << Mapping.Scale);

  IRB.CreateCall(AsantRegisterGlobals,
                 {IRB.CreatePointerCast(AllGlobals, IntptrTy),
                  ConstantInt::get(IntptrTy, N)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsantModuleDtor(M);
  IRB_Dtor.CreateCall(AsantUnregisterGlobals,
                      {IRB.CreatePointerCast(AllGlobals, IntptrTy),
                       ConstantInt::get(IntptrTy, N)});
}

// This function replaces all global variables with new variables that have
// trailing redzones. It also creates a function that poisons
// redzones and inserts this function into llvm.global_ctors.
// Sets *CtorComdat to true if the global registration code emitted into the
// asant constructor is comdat-compatible.
bool ModuleAddressSanitizer::InstrumentGlobals(IRBuilder<> &IRB, Module &M,
                                               bool *CtorComdat) {
  *CtorComdat = false;

  errs()<<"instrument globals\n";
  SmallVector<GlobalVariable *, 16> GlobalsToChange;

  for (auto &G : M.globals()) {
    if (ShouldInstrumentGlobal(&G)) GlobalsToChange.push_back(&G);
  }

  size_t n = GlobalsToChange.size();
  if (n == 0) {
    *CtorComdat = true;
    return false;
  }

  auto &DL = M.getDataLayout();

  // A global is described by a structure
  //   size_t beg;
  //   size_t size;
  //   size_t size_with_redzone;
  //   const char *name;
  //   const char *module_name;
  //   size_t has_dynamic_init;
  //   void *source_location;
  //   size_t odr_indicator;
  // We initialize an array of such structures and pass it to a run-time call.
  StructType *GlobalStructTy =
      StructType::get(IntptrTy, IntptrTy, IntptrTy, IntptrTy, IntptrTy,
                      IntptrTy, IntptrTy, IntptrTy);
  SmallVector<GlobalVariable *, 16> NewGlobals(n);
  SmallVector<Constant *, 16> Initializers(n);

  bool HasDynamicallyInitializedGlobals = false;

  // We shouldn't merge same module names, as this string serves as unique
  // module ID in runtime.
  GlobalVariable *ModuleName = createPrivateGlobalForString(
      M, M.getModuleIdentifier(), /*AllowMerging*/ false, kAsantGenPrefix);

  for (size_t i = 0; i < n; i++) {
    static const uint64_t kMaxGlobalRedzone = 1 << 18;
    GlobalVariable *G = GlobalsToChange[i];
    errs()<<"instrument one global\n";

    // FIXME: Metadata should be attched directly to the global directly instead
    // of being added to llvm.asant.globals.
    auto MD = GlobalsMD.get(G);
    StringRef NameForGlobal = G->getName();
    // Create string holding the global name (use global name from metadata
    // if it's available, otherwise just write the name of global variable).
    GlobalVariable *Name = createPrivateGlobalForString(
        M, MD.Name.empty() ? NameForGlobal : MD.Name,
        /*AllowMerging*/ true, kAsantGenPrefix);

    Type *Ty = G->getValueType();
    uint64_t SizeInBytes = DL.getTypeAllocSize(Ty);
    uint64_t MinRZ = MinRedzoneSizeForGlobal();
    // MinRZ <= RZ <= kMaxGlobalRedzone
    // and trying to make RZ to be ~ 1/4 of SizeInBytes.
    uint64_t RZ = std::max(
        MinRZ, std::min(kMaxGlobalRedzone, (SizeInBytes / MinRZ / 4) * MinRZ));
    uint64_t RightRedzoneSize = RZ;
    // Round up to MinRZ
    if (SizeInBytes % MinRZ) RightRedzoneSize += MinRZ - (SizeInBytes % MinRZ);
    assert(((RightRedzoneSize + SizeInBytes) % MinRZ) == 0);
    Type *RightRedZoneTy = ArrayType::get(IRB.getInt8Ty(), RightRedzoneSize);

    StructType *NewTy = StructType::get(Ty, RightRedZoneTy);
    Constant *NewInitializer = ConstantStruct::get(
        NewTy, G->getInitializer(), Constant::getNullValue(RightRedZoneTy));

    // Create a new global variable with enough space for a redzone.
    GlobalValue::LinkageTypes Linkage = G->getLinkage();
    if (G->isConstant() && Linkage == GlobalValue::PrivateLinkage)
      Linkage = GlobalValue::InternalLinkage;
    GlobalVariable *NewGlobal =
        new GlobalVariable(M, NewTy, G->isConstant(), Linkage, NewInitializer,
                           "", G, G->getThreadLocalMode());
    NewGlobal->copyAttributesFrom(G);
    NewGlobal->setComdat(G->getComdat());
    NewGlobal->setAlignment(MinRZ);
    // Don't fold globals with redzones. ODR violation detector and redzone
    // poisoning implicitly creates a dependence on the global's address, so it
    // is no longer valid for it to be marked unnamed_addr.
    NewGlobal->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

    // Move null-terminated C strings to "__asant_cstring" section on Darwin.
    if (TargetTriple.isOSBinFormatMachO() && !G->hasSection() &&
        G->isConstant()) {
      auto Seq = dyn_cast<ConstantDataSequential>(G->getInitializer());
      if (Seq && Seq->isCString())
        NewGlobal->setSection("__TEXT,__asant_cstring,regular");
    }

    // Transfer the debug info.  The payload starts at offset zero so we can
    // copy the debug info over as is.
    SmallVector<DIGlobalVariableExpression *, 1> GVs;
    G->getDebugInfo(GVs);
    for (auto *GV : GVs)
      NewGlobal->addDebugInfo(GV);

    Value *Indices2[2];
    Indices2[0] = IRB.getInt32(0);
    Indices2[1] = IRB.getInt32(0);

    G->replaceAllUsesWith(
        ConstantExpr::getGetElementPtr(NewTy, NewGlobal, Indices2, true));
    NewGlobal->takeName(G);
    G->eraseFromParent();
    NewGlobals[i] = NewGlobal;

    Constant *SourceLoc;
    if (!MD.SourceLoc.empty()) {
      auto SourceLocGlobal = createPrivateGlobalForSourceLoc(M, MD.SourceLoc);
      SourceLoc = ConstantExpr::getPointerCast(SourceLocGlobal, IntptrTy);
    } else {
      SourceLoc = ConstantInt::get(IntptrTy, 0);
    }

    Constant *ODRIndicator = ConstantExpr::getNullValue(IRB.getInt8PtrTy());
    GlobalValue *InstrumentedGlobal = NewGlobal;

    bool CanUsePrivateAliases =
        TargetTriple.isOSBinFormatELF() || TargetTriple.isOSBinFormatMachO() ||
        TargetTriple.isOSBinFormatWasm();
    if (CanUsePrivateAliases && UsePrivateAlias) {
      // Create local alias for NewGlobal to avoid crash on ODR between
      // instrumented and non-instrumented libraries.
      InstrumentedGlobal =
          GlobalAlias::create(GlobalValue::PrivateLinkage, "", NewGlobal);
    }

    // ODR should not happen for local linkage.
    if (NewGlobal->hasLocalLinkage()) {
      ODRIndicator = ConstantExpr::getIntToPtr(ConstantInt::get(IntptrTy, -1),
                                               IRB.getInt8PtrTy());
    } else if (UseOdrIndicator) {
      // With local aliases, we need to provide another externally visible
      // symbol __odr_asant_XXX to detect ODR violation.
      auto *ODRIndicatorSym =
          new GlobalVariable(M, IRB.getInt8Ty(), false, Linkage,
                             Constant::getNullValue(IRB.getInt8Ty()),
                             kODRGenPrefix + NameForGlobal, nullptr,
                             NewGlobal->getThreadLocalMode());

      // Set meaningful attributes for indicator symbol.
      ODRIndicatorSym->setVisibility(NewGlobal->getVisibility());
      ODRIndicatorSym->setDLLStorageClass(NewGlobal->getDLLStorageClass());
      ODRIndicatorSym->setAlignment(1);
      ODRIndicator = ODRIndicatorSym;
    }

    Constant *Initializer = ConstantStruct::get(
        GlobalStructTy,
        ConstantExpr::getPointerCast(InstrumentedGlobal, IntptrTy),
        ConstantInt::get(IntptrTy, SizeInBytes),
        ConstantInt::get(IntptrTy, SizeInBytes + RightRedzoneSize),
        ConstantExpr::getPointerCast(Name, IntptrTy),
        ConstantExpr::getPointerCast(ModuleName, IntptrTy),
        ConstantInt::get(IntptrTy, MD.IsDynInit), SourceLoc,
        ConstantExpr::getPointerCast(ODRIndicator, IntptrTy));

    if (ClInitializers && MD.IsDynInit) HasDynamicallyInitializedGlobals = true;

    LLVM_DEBUG(dbgs() << "NEW GLOBAL: " << *NewGlobal << "\n");

    Initializers[i] = Initializer;
  }

  // Add instrumented globals to llvm.compiler.used list to avoid LTO from
  // ConstantMerge'ing them.
  SmallVector<GlobalValue *, 16> GlobalsToAddToUsedList;
  for (size_t i = 0; i < n; i++) {
    GlobalVariable *G = NewGlobals[i];
    if (G->getName().empty()) continue;
    GlobalsToAddToUsedList.push_back(G);
  }
  appendToCompilerUsed(M, ArrayRef<GlobalValue *>(GlobalsToAddToUsedList));

  std::string ELFUniqueModuleId =
      (UseGlobalsGC && TargetTriple.isOSBinFormatELF()) ? getUniqueModuleId(&M)
                                                        : "";

  if (!ELFUniqueModuleId.empty()) {
    InstrumentGlobalsELF(IRB, M, NewGlobals, Initializers, ELFUniqueModuleId);
    *CtorComdat = true;
  } else if (UseGlobalsGC && TargetTriple.isOSBinFormatCOFF()) {
    InstrumentGlobalsCOFF(IRB, M, NewGlobals, Initializers);
  } else if (UseGlobalsGC && ShouldUseMachOGlobalsSection()) {
    InstrumentGlobalsMachO(IRB, M, NewGlobals, Initializers);
  } else {
    InstrumentGlobalsWithMetadataArray(IRB, M, NewGlobals, Initializers);
  }

  // Create calls for poisoning before initializers run and unpoisoning after.
  if (HasDynamicallyInitializedGlobals)
    createInitializerPoisonCalls(M, ModuleName);

  LLVM_DEBUG(dbgs() << M);
  return true;
}

int ModuleAddressSanitizer::GetAsantVersion(const Module &M) const {
  int LongSize = M.getDataLayout().getPointerSizeInBits();
  bool isAndroid = Triple(M.getTargetTriple()).isAndroid();
  int Version = 8;
  // 32-bit Android is one version ahead because of the switch to dynamic
  // shadow.
  Version += (LongSize == 32 && isAndroid);
  return Version;
}
static const char *const kAsantVersionCheckNamePrefix =
  "__asant_version_mismatch_check_v";
static const char *const kAsantInitName = "__asant_init";
bool ModuleAddressSanitizer::instrumentModule(Module &M) {
  initializeCallbacks(M);

  if (CompileKernel)
    return false;

  // Create a module constructor. A destructor is created lazily because not all
  // platforms, and not all modules need it.
  std::string VersionCheckName =
      kAsantVersionCheckNamePrefix + std::to_string(GetAsantVersion(M));
  std::tie(AsantCtorFunction, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, kAsantModuleCtorName, kAsantInitName, /*InitArgTypes=*/{},
      /*InitArgs=*/{}, VersionCheckName);

  bool CtorComdat = true;
  bool Changed = false;
  // TODO(glider): temporarily disabled globals instrumentation for KAsant.
  errs()<<"pre\n";
  if (ClGlobals) {
    IRBuilder<> IRB(AsantCtorFunction->getEntryBlock().getTerminator());
    Changed |= InstrumentGlobals(IRB, M, &CtorComdat);
  }

  // Put the constructor and destructor in comdat if both
  // (1) global instrumentation is not TU-specific
  // (2) target is ELF.
  if (UseCtorComdat && TargetTriple.isOSBinFormatELF() && CtorComdat) {
    AsantCtorFunction->setComdat(M.getOrInsertComdat(kAsantModuleCtorName));
    appendToGlobalCtors(M, AsantCtorFunction, kAsantCtorAndDtorPriority,
                        AsantCtorFunction);
    if (AsantDtorFunction) {
      AsantDtorFunction->setComdat(M.getOrInsertComdat(kAsantModuleDtorName));
      appendToGlobalDtors(M, AsantDtorFunction, kAsantCtorAndDtorPriority,
                          AsantDtorFunction);
    }
  } else {
    appendToGlobalCtors(M, AsantCtorFunction, kAsantCtorAndDtorPriority);
    if (AsantDtorFunction)
      appendToGlobalDtors(M, AsantDtorFunction, kAsantCtorAndDtorPriority);
  }

  return Changed;
}

static const char *const kAsantReportErrorTemplate = "__asant_report_";

void AddressSanitizer::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);
  // Create __asant_report* callbacks.
  // IsWrite, TypeSize and Exp are encoded in the function name.
  for (int Exp = 0; Exp < 2; Exp++) {
    for (size_t AccessIsWrite = 0; AccessIsWrite <= 1; AccessIsWrite++) {
      const std::string TypeStr = AccessIsWrite ? "store" : "load";
      const std::string ExpStr = Exp ? "exp_" : "";
      const std::string EndingStr = Recover ? "_noabort" : "";

      SmallVector<Type *, 3> Args2 = {IntptrTy, IntptrTy};
      SmallVector<Type *, 2> Args1{1, IntptrTy};
      if (Exp) {
        Type *ExpType = Type::getInt32Ty(*C);
        Args2.push_back(ExpType);
        Args1.push_back(ExpType);
      }
      AsantErrorCallbackSized[AccessIsWrite][Exp] = M.getOrInsertFunction(
          kAsantReportErrorTemplate + ExpStr + TypeStr + "_n" + EndingStr,
          FunctionType::get(IRB.getVoidTy(), Args2, false));

      AsantMemoryAccessCallbackSized[AccessIsWrite][Exp] = M.getOrInsertFunction(
          ClMemoryAccessCallbackPrefix + ExpStr + TypeStr + "N" + EndingStr,
          FunctionType::get(IRB.getVoidTy(), Args2, false));

      for (size_t AccessSizeIndex = 0; AccessSizeIndex < kNumberOfAccessSizes;
           AccessSizeIndex++) {
        const std::string Suffix = TypeStr + itostr(1ULL << AccessSizeIndex);
        AsantErrorCallback[AccessIsWrite][Exp][AccessSizeIndex] =
            M.getOrInsertFunction(
                kAsantReportErrorTemplate + ExpStr + Suffix + EndingStr,
                FunctionType::get(IRB.getVoidTy(), Args1, false));

        AsantMemoryAccessCallback[AccessIsWrite][Exp][AccessSizeIndex] =
            M.getOrInsertFunction(
                ClMemoryAccessCallbackPrefix + ExpStr + Suffix + EndingStr,
                FunctionType::get(IRB.getVoidTy(), Args1, false));
      }
    }
  }
  static const char *const kAsantHandleNoReturnName = "__asant_handle_no_return";
  static const char *const kAsantPtrCmp = "__sanitizer_ptr_cmp";
  const std::string MemIntrinCallbackPrefix =
      CompileKernel ? std::string("") : ClMemoryAccessCallbackPrefix;
  AsantMemmove = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memmove",
                                      IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                      IRB.getInt8PtrTy(), IntptrTy);
  AsantMemcpy = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memcpy",
                                     IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                     IRB.getInt8PtrTy(), IntptrTy);
  AsantMemset = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memset",
                                     IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                     IRB.getInt32Ty(), IntptrTy);

  AsantHandleNoReturnFunc =
      M.getOrInsertFunction(kAsantHandleNoReturnName, IRB.getVoidTy());

  AsantPtrCmpFunction =
      M.getOrInsertFunction(kAsantPtrCmp, IRB.getVoidTy(), IntptrTy, IntptrTy);
  AsantPtrSubFunction =
      M.getOrInsertFunction(kAsantPtrSub, IRB.getVoidTy(), IntptrTy, IntptrTy);
  // We insert an empty inline asm after __asant_report* to avoid callback merge.
  EmptyAsm = InlineAsm::get(FunctionType::get(IRB.getVoidTy(), false),
                            StringRef(""), StringRef(""),
                            /*hasSideEffects=*/true);
  if (Mapping.InGlobal)
    AsantShadowGlobal = M.getOrInsertGlobal("__asant_shadow",
                                           ArrayType::get(IRB.getInt8Ty(), 0));
}

bool AddressSanitizer::maybeInsertAsantInitAtFunctionEntry(Function &F) {
  // For each NSObject descendant having a +load method, this method is invoked
  // by the ObjC runtime before any of the static constructors is called.
  // Therefore we need to instrument such methods with a call to __asant_init
  // at the beginning in order to initialize our runtime before any access to
  // the shadow memory.
  // We cannot just ignore these methods, because they may call other
  // instrumented functions.
  if (F.getName().find(" load]") != std::string::npos) {
    FunctionCallee AsantInitFunction =
        declareSanitizerInitFunction(*F.getParent(), kAsantInitName, {});
    IRBuilder<> IRB(&F.front(), F.front().begin());
    IRB.CreateCall(AsantInitFunction, {});
    return true;
  }
  return false;
}
static const char *const kAsantShadowMemoryDynamicAddress =
  "__asant_shadow_memory_dynamic_address";

static const uint64_t kDynamicShadowSentinel =
  std::numeric_limits<uint64_t>::max();
void AddressSanitizer::maybeInsertDynamicShadowAtFunctionEntry(Function &F) {
  // Generate code only when dynamic addressing is needed.
  if (Mapping.Offset != kDynamicShadowSentinel)
    return;

  IRBuilder<> IRB(&F.front().front());
  if (Mapping.InGlobal) {
    if (ClWithIfuncSuppressRemat) {
      // An empty inline asm with input reg == output reg.
      // An opaque pointer-to-int cast, basically.
      InlineAsm *Asm = InlineAsm::get(
          FunctionType::get(IntptrTy, {AsantShadowGlobal->getType()}, false),
          StringRef(""), StringRef("=r,0"),
          /*hasSideEffects=*/false);
      LocalDynamicShadow =
          IRB.CreateCall(Asm, {AsantShadowGlobal}, ".asant.shadow");
    } else {
      LocalDynamicShadow =
          IRB.CreatePointerCast(AsantShadowGlobal, IntptrTy, ".asant.shadow");
    }
  } else {
    Value *GlobalDynamicAddress = F.getParent()->getOrInsertGlobal(
        kAsantShadowMemoryDynamicAddress, IntptrTy);
    LocalDynamicShadow = IRB.CreateLoad(IntptrTy, GlobalDynamicAddress);
  }
}

void AddressSanitizer::markEscapedLocalAllocas(Function &F) {
  // Find the one possible call to llvm.localescape and pre-mark allocas passed
  // to it as uninteresting. This assumes we haven't started processing allocas
  // yet. This check is done up front because iterating the use list in
  // isInterestingAlloca would be algorithmically slower.
  assert(ProcessedAllocas.empty() && "must process localescape before allocas");

  // Try to get the declaration of llvm.localescape. If it's not in the module,
  // we can exit early.
  if (!F.getParent()->getFunction("llvm.localescape")) return;

  // Look for a call to llvm.localescape call in the entry block. It can't be in
  // any other block.
  for (Instruction &I : F.getEntryBlock()) {
    IntrinsicInst *II = dyn_cast<IntrinsicInst>(&I);
    if (II && II->getIntrinsicID() == Intrinsic::localescape) {
      // We found a call. Mark all the allocas passed in as uninteresting.
      for (Value *Arg : II->arg_operands()) {
        AllocaInst *AI = dyn_cast<AllocaInst>(Arg->stripPointerCasts());
        assert(AI && AI->isStaticAlloca() &&
               "non-static alloca arg to localescape");
        ProcessedAllocas[AI] = false;
      }
      break;
    }
  }
}

bool AddressSanitizer::instrumentFunction(Function &F,
                                          const TargetLibraryInfo *TLI) {
  if (F.getLinkage() == GlobalValue::AvailableExternallyLinkage) return false;
  if (!ClDebugFunc.empty() && ClDebugFunc == F.getName()) return false;
  if (F.getName().startswith("__asant_")) return false;

  bool FunctionModified = false;

  // If needed, insert __asant_init before checking for SanitizeAddress attr.
  // This function needs to be called even if the function body is not
  // instrumented.
  if (maybeInsertAsantInitAtFunctionEntry(F))
    FunctionModified = true;

  // Leave if the function doesn't need instrumentation.
  if (!F.hasFnAttribute(Attribute::SanitizeAddress)) return FunctionModified;

  LLVM_DEBUG(dbgs() << "ASANT instrumenting:\n" << F << "\n");

  initializeCallbacks(*F.getParent());

  FunctionStateRAII CleanupObj(this);

  maybeInsertDynamicShadowAtFunctionEntry(F);

  // We can't instrument allocas used with llvm.localescape. Only static allocas
  // can be passed to that intrinsic.
  markEscapedLocalAllocas(F);

  // We want to instrument every address only once per basic block (unless there
  // are calls between uses).
  SmallPtrSet<Value *, 16> TempsToInstrument;
  SmallVector<Instruction *, 16> ToInstrument;
  SmallVector<Instruction *, 8> NoReturnCalls;
  SmallVector<BasicBlock *, 16> AllBlocks;
  SmallVector<Instruction *, 16> PointerComparisonsOrSubtracts;
  int NumAllocas = 0;
  bool IsWrite;
  unsigned Alignment;
  uint64_t TypeSize;

  // Fill the set of memory operations to instrument.
  for (auto &BB : F) {
    AllBlocks.push_back(&BB);
    TempsToInstrument.clear();
    int NumInsnsPerBB = 0;
    for (auto &Inst : BB) {
      if (LooksLikeCodeInBug11395(&Inst)) return false;
      Value *MaybeMask = nullptr;
      if (Value *Addr = isInterestingMemoryAccess(&Inst, &IsWrite, &TypeSize,
                                                  &Alignment, &MaybeMask)) {
        if (ClOpt && ClOptSameTemp) {
          // If we have a mask, skip instrumentation if we've already
          // instrumented the full object. But don't add to TempsToInstrument
          // because we might get another load/store with a different mask.
          if (MaybeMask) {
            if (TempsToInstrument.count(Addr))
              continue; // We've seen this (whole) temp in the current BB.
          } else {
            if (!TempsToInstrument.insert(Addr).second)
              continue; // We've seen this temp in the current BB.
          }
        }
      } else if (((ClInvalidPointerPairs || ClInvalidPointerCmp) &&
                  isInterestingPointerComparison(&Inst)) ||
                 ((ClInvalidPointerPairs || ClInvalidPointerSub) &&
                  isInterestingPointerSubtraction(&Inst))) {
        PointerComparisonsOrSubtracts.push_back(&Inst);
        continue;
      } else if (isa<MemIntrinsic>(Inst)) {
        // ok, take it.
      } else {
        if (isa<AllocaInst>(Inst)) NumAllocas++;
        CallSite CS(&Inst);
        if (CS) {
          // A call inside BB.
          TempsToInstrument.clear();
          if (CS.doesNotReturn() && !CS->getMetadata("nosanitize"))
            NoReturnCalls.push_back(CS.getInstruction());
        }
        if (CallInst *CI = dyn_cast<CallInst>(&Inst))
          maybeMarkSanitizerLibraryCallNoBuiltin(CI, TLI);
        continue;
      }
      ToInstrument.push_back(&Inst);
      NumInsnsPerBB++;
      if (NumInsnsPerBB >= ClMaxInsnsToInstrumentPerBB) break;
    }
  }

  bool UseCalls =
      (ClInstrumentationWithCallsThreshold >= 0 &&
       ToInstrument.size() > (unsigned)ClInstrumentationWithCallsThreshold);
  const DataLayout &DL = F.getParent()->getDataLayout();
  ObjectSizeOpts ObjSizeOpts;
  ObjSizeOpts.RoundToAlign = true;
  ObjectSizeOffsetVisitor ObjSizeVis(DL, TLI, F.getContext(), ObjSizeOpts);

  // Instrument.
  int NumInstrumented = 0;
  for (auto Inst : ToInstrument) {
    if (ClDebugMin < 0 || ClDebugMax < 0 ||
        (NumInstrumented >= ClDebugMin && NumInstrumented <= ClDebugMax)) {
      if (isInterestingMemoryAccess(Inst, &IsWrite, &TypeSize, &Alignment))
        instrumentMop(ObjSizeVis, Inst, UseCalls,
                      F.getParent()->getDataLayout());
      else
        instrumentMemIntrinsic(cast<MemIntrinsic>(Inst));
    }
    NumInstrumented++;
  }

  //  FunctionStackPoisoner FSP(F, *this);
  bool ChangedStack = false; //FSP.runOnFunction();

  // We must unpoison the stack before NoReturn calls (throw, _exit, etc).
  // See e.g. https://github.com/google/sanitizers/issues/37
  for (auto CI : NoReturnCalls) {
    IRBuilder<> IRB(CI);
    IRB.CreateCall(AsantHandleNoReturnFunc, {});
  }

  for (auto Inst : PointerComparisonsOrSubtracts) {
    instrumentPointerComparisonOrSubtraction(Inst);
    NumInstrumented++;
  }

  if (NumInstrumented > 0 || ChangedStack || !NoReturnCalls.empty())
    FunctionModified = true;

  LLVM_DEBUG(dbgs() << "ASANT done instrumenting: " << FunctionModified << " "
                    << F << "\n");

  return FunctionModified;
}

// Workaround for bug 11395: we don't want to instrument stack in functions
// with large assembly blobs (32-bit only), otherwise reg alloc may crash.
// FIXME: remove once the bug 11395 is fixed.
bool AddressSanitizer::LooksLikeCodeInBug11395(Instruction *I) {
  if (LongSize != 32) return false;
  CallInst *CI = dyn_cast<CallInst>(I);
  if (!CI || !CI->isInlineAsm()) return false;
  if (CI->getNumArgOperands() <= 5) return false;
  // We have inline assembly with quite a few arguments.
  return true;
}




static void registerSkeletonPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  // PM.add((llvm::Pass*)new AddressSanitizerLegacyPass());
  // PM.add((llvm::Pass*)new ModuleAddressSanitizerPass());
  PM.add(new AsantGlobalsMetadataWrapperPass());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
                 registerSkeletonPass);


