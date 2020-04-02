#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
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
#include "llvm/Transforms/Instrumentation/AddressSanitizer.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Instructions.h"
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
#include "llvm/Transforms/Utils/ASanStackFrameLayout.h"
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
#include<vector>


using namespace std;
using namespace llvm;



namespace {

  struct SkeletonPass : public ModulePass {
    static char ID;
    SkeletonPass() : ModulePass(ID) {}
    Triple TargetTriple;
    vector<Instruction*> starts;
    vector<Instruction*> ends;
    vector<GlobalVariable*> to_remove;


    virtual bool runOnModule(Module &M) {
      TargetTriple=Triple(M.getTargetTriple());
      auto &DL = M.getDataLayout();
      LLVMContext &context = M.getContext();

      Type* it = IntegerType::getInt8Ty(context);

      BasicBlock* last;
      for(auto &F : M){
	    auto name=F.getName();
            if(name=="report_xasan"||name=="enter_func"||name=="leave_func"||name=="mark_valid"||name=="mark_invalid")
              continue;

            int first_flag=0;
	    int end_flag=0;
            for(auto &BB: F){
                last=&BB;
              if(first_flag==0){
                first_flag++;
                for(auto &Inst: BB){
                        starts.push_back(&Inst);
			end_flag=1;
                        break;
                }
              }
            }
	    if(end_flag){
            Instruction* term=last->getTerminator();
            ends.push_back(term);
	    }

      }
      errs()<<"start: "<<starts.size()<<" "<<ends.size()<<"\n";


      IRBuilder<> builder(context);
       for(auto &global : M.globals()){
         if(global.isConstant())
           continue;
	 if(global.getName().startswith("llvm."))
		 continue;
	 if(global.getSection().startswith(".bss.percpu"))
		 continue;
	 if(!ShouldInstrumentGlobal(&global)){
		continue;
	 }

         if(global.getMetadata("past")){
           if(cast<MDString>(global.getMetadata("past")->getOperand(0))->getString()=="true"){
             continue;
           }
         }

          Type *Ty=global.getValueType();
          long size=DL.getTypeAllocSize(Ty);
          errs()<<"var name: "<<global.getName()<<"\n";
          errs()<<"var size: "<<size<<"\n";

          ArrayType* arrayTyper = ArrayType::get(it, 16+16-size%16);

          StructType *gTy=StructType::get(global.getValueType(),arrayTyper);
          Constant* initializer;
	  GlobalValue::LinkageTypes Linkage = global.getLinkage();
	  if (global.isConstant() && Linkage == GlobalValue::PrivateLinkage)
	      Linkage = GlobalValue::InternalLinkage;

          initializer = ConstantStruct::get(gTy,global.getInitializer(),Constant::getNullValue(arrayTyper));
          auto gv=new GlobalVariable(M, gTy, global.isConstant(),Linkage,initializer,Twine("__xasan_global")+GlobalValue::dropLLVMManglingEscape(global.getName()));

          MDNode* N = MDNode::get(context, MDString::get(context, "true"));
          gv->setMetadata("past",N);

          global.replaceAllUsesWith(gv);
          gv->takeName(&global);
	  to_remove.push_back(&global);

           gv->copyAttributesFrom(&global);
           gv->setComdat(global.getComdat());
           gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
          
          for(auto inst: starts){
            IRBuilder<> IRB(inst);
            FunctionType *type_rz = FunctionType::get(Type::getVoidTy(context), {Type::getInt8PtrTy(context),Type::getInt64Ty(context),Type::getInt8Ty(context)}, false);
            auto callee_rz = M.getOrInsertFunction("mark_invalid", type_rz);
            ConstantInt *size_rz = builder.getInt64(16+16-size%16);
            ConstantInt *offset =IRB.getInt64(size);
            ConstantInt *er_sz=IRB.getInt8(3);
            Value *rzv=IRB.CreateIntToPtr(
              IRB.CreateAdd(gv,offset),Type::getInt8PtrTy(context));
            CallInst::Create(callee_rz, {rzv,size_rz,er_sz}, "",inst);
          }

          for(auto inst: ends){
            IRBuilder<> IRB(inst);
            FunctionType *type_rz = FunctionType::get(Type::getVoidTy(context), {Type::getInt8PtrTy(context),Type::getInt64Ty(context)}, false);
            auto callee_rz = M.getOrInsertFunction("mark_valid", type_rz);
            ConstantInt *size_rz = builder.getInt64(16+16-size%16);
            ConstantInt *offset =IRB.getInt64(size);
            Value *rzv=IRB.CreateIntToPtr(
              IRB.CreateAdd(gv,offset),Type::getInt8PtrTy(context));
            CallInst::Create(callee_rz, {rzv,size_rz}, "",inst);
          }


       }


       for(auto g:to_remove){
	g->eraseFromParent();
       }


       return false;

    }
    bool ShouldInstrumentGlobal(GlobalVariable *G) {
      Type *Ty = G->getValueType();
    
      if (!Ty->isSized()) return false;
      if (!G->hasInitializer()) return false;
      if (GlobalWasGeneratedByCompiler(G)) return false; // Our own globals.
      // Two problems with thread-locals:
      //   - The address of the main thread's copy can't be computed at link-time.
      //   - Need to poison all copies, not just the main thread's one.
      if (G->isThreadLocal()) return false;
      // For now, just ignore this Global if the alignment is large.
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
            return false;
          }
          // The linker merges the contents of cstring_literals and removes the
          // trailing zeroes.
          if (ParsedSegment == "__TEXT" && (TAA & MachO::S_CSTRING_LITERALS)) {
            return false;
          }
        }
      }
      return true;
    }
    static bool GlobalWasGeneratedByCompiler(GlobalVariable *G) {
      // Do not instrument @llvm.global_ctors, @llvm.used, etc.
      if (G->getName().startswith("llvm."))
        return true;
    
      // Do not instrument gcov counter arrays.
      if (G->getName() == "__llvm_gcov_ctr")
        return true;
    
      return false;
    }
        
      };
    }
    



char SkeletonPass::ID = 0;

static void registerSkeletonPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new SkeletonPass());
}

static RegisterStandardPasses
 RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly, registerSkeletonPass);

static RegisterStandardPasses
RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0, registerSkeletonPass);
