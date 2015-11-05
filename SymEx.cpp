/* Symbolic Execution
 *
 * Authors: Harshvardhan Sharma (11907299)
 *          Aniruddha Zalani (11907097)
 */

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/Dwarf.h"
#include "llvm/IR/CFG.h"
#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include <set>
#include <vector>

#define INF 1000

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "SymEx"

typedef pair<Value *, bool> branchCondition;

set<Value *> Var;
map<Value *, int> namedVarCounter;

void dumpBinInst (Instruction *I)
{
    errs() << I->getName() << " = ";
    for (int i = 0; i < 2; i++) {
        if (auto c = dyn_cast<ConstantInt>(I->getOperand(i))) errs() << c->getValue();
        else if(I->getOperand(i)->hasName()) errs() << I->getOperand(i)->getName();
        else errs() << I->getOperand(i);
        if(i == 0) {
            int opcode  = I->getOpcode();
            switch(opcode) {
                case (8): {
                              errs() << " + ";
                              break;
                          }
                case (10): {
                               errs() << " - ";
                               break;
                           }
                case (12): {
                               errs() << " * ";
                               break;
                           }
                case (15): {
                               errs() << " / ";
                               break;
                           }
            }
        }
    }
    errs() << "\n";
}

void dumpStoreInst (Instruction *I)
{
    errs() << I->getOperand(1)->getName();;
    if (namedVarCounter.count(I->getOperand(1)))
        errs() << ++namedVarCounter[I->getOperand(1)];
    errs() << " = ";
    if (auto V = dyn_cast<ConstantInt>(I->getOperand(0))) {
        errs() << V->getValue();
    }
    else {
        errs() << I->getOperand(0)->getName();
    }
    errs() << "\n";
}

void dumpLoadInst(Instruction *I)
{
    errs() << I->getName() << " = " << I->getOperand(0)->getName() << namedVarCounter[I->getOperand(0)] << "\n";
}

/* Returns vector of all variables of an instruction */
std::vector<Value *> getUsedVars (Instruction *I)
{
    std::vector<Value *> ret;
    if (isa<AllocaInst>(I));
    else if(isa<StoreInst>(I)) {
        if(!isa<Constant>(I->getOperand(0)))
            ret.push_back(I->getOperand(0));
    }
    else if(isa<CallInst>(I));
    else {
        for(unsigned i=0; i<I->getNumOperands(); i++){
            Value *oper = I->getOperand(i);
            if (! (isa<Constant>(*oper) || isa<Function>(*oper) || oper->getType()->isLabelTy())) {
                ret.push_back(oper);
            }
        }
    }
    return ret;
}

Value * getAssignedVars (Instruction *I)
{
    if (isa<StoreInst>(I)) {
        return I->getOperand(1);
    }
    if( ! (isa<TerminatorInst>(I)
    // void function call
    || (isa<CallInst>(I) && dyn_cast<CallInst>(I)->getCalledFunction()->getReturnType()->getTypeID() == 0) )) {
        return I;
    }
    return NULL;
}

/* Assign names of the form tmpXX to unnamed variables in the IR. */
void assignTempNames ()
{
    int unnamed_count = 0;
    for (auto&v : Var) {
        if (!v->hasName())
            v->setName("tmp" + Twine(unnamed_count++));
        else
            namedVarCounter.insert(make_pair(*&v, 0));
    }
}

/* Construct the set of all named and unnamed variables in a function. */
void findAllVars (Function *F)
{
    for (auto& B : *F) {
        for(auto& I : B) {
            for (auto& v : getUsedVars(&I)) {
                Var.insert(v);
            }
            if (auto v = getAssignedVars(&I)) {
                Var.insert(v);
            }
        }
    }
}

void encodeConstraints (vector<Instruction> constraints)
{
    for (auto& I : constraints) {
        if (isa<AllocaInst>(&I)) {
        }

        if (isa<StoreInst>(&I)) {
            dumpStoreInst(&I);
        }

        if (isa<LoadInst>(&I)) {
            dumpLoadInst(&I);
        }

        if (isa<BinaryOperator>(&I)) {
            dumpBinInst(&I);
        }
    }
}


// takes vector of instruction as input and outputs true/false 
bool taintAnalyse(vector<Instruction *>path)
{
    vector<Instruction *> symList;
    for(vector<Instruction *>::iterator I=path.begin(), e = path.end();I!=e;I++ ){
       if (isa<AllocaInst>(*I)){
           (*I)->dump();
           if ((*I)->getName().substr(0,3)=="sym"){
                symList.push_back(*I);
           }
       }
       if (auto c = dyn_cast<CallInst>(*I)){
           if(c->getCalledFunction()->getName()=="eval"){ //check if the value in eval is symbolic
                I--;
               (*I)->dump();
                //check for load 
                if(isa<LoadInst>(*I)){
                    for (auto& sym:symList){
                        if(sym->getName() == (*I)->getOperand(0)->getName())
                            return true;
                    } 
                }
                I++; 
           }
           if(c->getCalledFunction()->getName()=="write"){ //check if the value in eval is symbolic
                I--;
               (*I)->dump();
                //check for load 
                if(isa<LoadInst>(*I)){
                    for (auto& sym:symList){
                        if(sym->getName() == (*I)->getOperand(0)->getName())
                            return true;
                    } 
                }
                I++; 
           }

               
       }
    }
   return false; 
}

/* Find path constraints of the basic block and add them to constraints found so far.
 * branches specifies the branch conditions on the path. */
void processBB (BasicBlock *b, vector<Instruction *> constraints, map<BranchInst *, branchCondition> branches,  bool verbose)
{
    if (verbose) {
        errs() << "\n---------------\n";
        b->dump();
        errs() << "\n---------------\n";
    }

    for (auto &I : *b) {
        DEBUG(I.dump());
        constraints.push_back(&I);
    }
    if(b->getTerminator()->getNumSuccessors() <= 1) {
        constraints.pop_back();
    }

    if (isa<ReturnInst>(b->getTerminator()))  {
        return;
    }

    if (auto branch = dyn_cast<BranchInst>(b->getTerminator())) {
        if(branch->isConditional()) {
            branches[branch] = make_pair(branch->getCondition(), true);
            processBB(branch->getSuccessor(0), constraints, branches, verbose); // recurse on true branch

            // negate the predicate to get the constraint for the false branch
            branches[branch].second = false;
            processBB(branch->getSuccessor(1), constraints, branches, verbose);
            return;
        }
        else {
            processBB(branch->getSuccessor(0), constraints, branches, verbose);
        }
    }

}
namespace {
    struct SymEx : public FunctionPass {
        static char ID;
        SymEx() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            errs() << "Function Name: " << F.getName() << "\n\n";
            Var.clear();
            findAllVars(&F);
            assignTempNames();
            vector<Instruction *> constraints;
            map<BranchInst *, branchCondition> b;
            processBB(&F.getEntryBlock(), constraints, b, false);
            return false;
        }
    };
}

char SymEx::ID = 0;
static RegisterPass<SymEx> X("symex", "Symbolic Execution Interpretation");
