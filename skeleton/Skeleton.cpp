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


    virtual bool runOnModule(Module &M) {
      TargetTriple=Triple(M.getTargetTriple());
      auto &DL = M.getDataLayout();
      LLVMContext &context = M.getContext();

      Type* it = IntegerType::getInt8Ty(context);

      IRBuilder<> builder(context);
       for(auto &global : M.globals()){
         if(global.isConstant())
           continue;

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

          StructType *gTy=StructType::get(global.getType(),arrayTyper);
          Constant* initializer;
          if(global.hasInitializer()){
            initializer = ConstantStruct::get(gTy,global.getInitializer(),Constant::getNullValue(arrayTyper));
          }
          else{
            initializer = ConstantStruct::get(gTy,Constant::getNullValue(global.getType()),Constant::getNullValue(arrayTyper));
          }
          auto gv=new GlobalVariable(M, gTy, global.isConstant(),GlobalValue::CommonLinkage,initializer,Twine("__xasan_global")+GlobalValue::dropLLVMManglingEscape(global.getName()));

          gv->copyAttributesFrom(&global);
          gv->setComdat(global.getComdat());
          gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

          MDNode* N = MDNode::get(context, MDString::get(context, "true"));
          gv->setMetadata("past",N);

          global.replaceAllUsesWith(gv);
          gv->takeName(&global);

          for(auto &F : M){

            if(F.getName()=="mark_invalid"||F.getName()=="mark_valid")
              continue;
            int first_flag=0;
            BasicBlock *last;
            for(auto &BB: F){
              last=&BB;
              if(first_flag==0){
                first_flag=1;
                for(auto &Inst: BB){
                  IRBuilder<> IRB(&Inst);
                  FunctionType *type_rz = FunctionType::get(Type::getVoidTy(context), {Type::getInt8PtrTy(context),Type::getInt64Ty(context)}, false);
                  auto callee_rz = M.getOrInsertFunction("mark_invalid", type_rz);

                  ConstantInt *size_rz = builder.getInt64(16+16-size%16);
                  ConstantInt *offset =IRB.getInt64(size);
                  Value *rzv=IRB.CreateIntToPtr(
                    IRB.CreateAdd(gv,offset),Type::getInt8PtrTy(context));
                  CallInst::Create(callee_rz, {rzv,size_rz}, "",&Inst);
                  break;
                }
              }
            }
            Instruction* term=last->getTerminator();
            IRBuilder<> IRB(term);
            FunctionType *type_rz = FunctionType::get(Type::getVoidTy(context), {Type::getInt8PtrTy(context),Type::getInt64Ty(context)}, false);
            auto callee_rz = M.getOrInsertFunction("mark_valid", type_rz);

            ConstantInt *size_rz = builder.getInt64(16+16-size%16);
            ConstantInt *offset =IRB.getInt64(size);
            Value *rzv=IRB.CreateIntToPtr(
                                          IRB.CreateAdd(gv,offset),Type::getInt8PtrTy(context));
            CallInst::Create(callee_rz, {rzv,size_rz}, "",term);
          }

       }




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
