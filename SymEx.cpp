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

//typedef std::pair<APInt, APInt> Interval;
typedef ConstantRange Interval;
typedef map<const Value *, Interval> State; 
typedef map<BasicBlock *, State> BBState;
#define MP make_pair

set<Value *> Var;
BBState outState; //stores final state for each basic block
map<BasicBlock *, BBState> inState; //stores incoming state from each predecessor
map<Value *, int> namedVarCounter;
//Interval EMPTY = MP(APInt::getMinValue(32), APInt::getMinValue(32));

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

void dumpMap(State * m, bool printUnnamed)
{
    for (auto p : *m) {
        if (p.first->hasName())
            errs() << p.first->getName() << ":[" << p.second.getSignedMin() << "," << p.second.getSignedMax() << "] ";
        else if (printUnnamed)
            errs() << p.first << ":[" << p.second.getSignedMin() << "," << p.second.getSignedMax() << "] ";
    }
    errs() << "\n";
}

void updateMap (State *m, Value * v, Interval i)
{
    if (m->find(v) == m->end())
        m->insert(make_pair(v, i));
    else
        m->find(v)->second = i;
}

Interval getValInterval(Value *v, State *m)
{
    if (auto c = dyn_cast<ConstantInt>(v))
        return Interval(c->getValue());
    return m->find(v)->second;
}

APInt getMin (APInt a, APInt b)
{
    if (a.slt(b))
        return a;
    return b;
}

APInt getMax (APInt a, APInt b)
{
    if (a.sgt(b))
        return a;
    return b;
}

//void normalizeInfinity (State *m)
//{
//    APInt nInf(32, -INF);
//    APInt pInf(32, INF);
//    for (auto p : *m) {
//        if (p.second.first.slt(nInf))
//            p.second.first = nInf;
//        if (p.second.second.slt(nInf))
//            p.second.second = nInf;
//        if (p.second.first.sgt(pInf))
//            p.second.first = pInf;
//        if (p.second.second.sgt(pInf))
//            p.second.second = pInf;
//    }
//}

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
void FindAllVars (Function *F)
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

void InitializeStates (Function *F)
{
    for (auto& B : *F) {
        for (auto &v : Var) {
            outState[&B].insert(make_pair(v, Interval (32, false)));
        }
        for (auto it = pred_begin(&B), et = pred_end(&B); it != et; ++it){
            BasicBlock *bb = *it;
            for (auto &v : Var) {
                inState[&B][bb].insert(make_pair(v, Interval(32, false)));
            }
        }
    }
}

/* Calculate innitial state set by taking union of out sets of all predecessors. */
State findIn (BasicBlock*  b)
{
    State in,s1;
    for (auto it = pred_begin(b), et = pred_end(b); it != et; ++it){
        BasicBlock *bb = *it;
        s1 = outState[bb];
        if (auto* pred_block = dyn_cast<BasicBlock>(*it)) {
            if (auto* pred_term = dyn_cast<BranchInst>(pred_block->getTerminator())) {
                if (pred_term->isConditional())
                    s1 = inState[b][pred_block];
            }
        }
        if (it == pred_begin(b)) {
            in = s1;
        }
        else {
            for(auto& v:Var) {
                if(in.count(v) && s1.count(v)){
                    in.at(v)  = (in.find(v)->second).unionWith(s1.find(v)->second); // in[v] = in[v].unionWith(s1[v])c
                }
            }
        }
    }
    return in;
}

/* Run the interpreter on the basic block to update output state.
 * If verbose is true, print the state at all instructions. */
bool processBB (BasicBlock *b, bool verbose)
{
    State in = findIn(b);
    State *iSet = &in;
    DILocation prevLoc(NULL);
    for (auto& I : *b) {
        DEBUG(I.dump());

        /* Print value intervals if we are at a new line */
        DILocation Loc(I.getMetadata("dbg"));
        //if (verbose && Loc && prevLoc && !Loc.atSameLineAs(prevLoc)) {
        //    errs() << "Line " << prevLoc.getLineNumber() << "\t";
        //    dumpMap(iSet, false);
        //}
        prevLoc = Loc;

        if (isa<AllocaInst>(&I)) {
            if (auto V = dyn_cast<Value>(&I)) {
                (*iSet).insert(make_pair(V, Interval(APInt(32, -1000, true), APInt(32, 1000, true))));
            }
        }

        if (isa<StoreInst>(&I)) {
            dumpStoreInst(&I);
            if (auto V = dyn_cast<ConstantInt>(I.getOperand(0))) {
                (*iSet).find(I.getOperand(1))->second = Interval(V->getValue());
            }
            else {
                (*iSet).find(I.getOperand(1))->second = (*iSet).find(I.getOperand(0))->second;
            }
        }

        if (isa<LoadInst>(&I)) {
            dumpLoadInst(&I);
            if(iSet->find(dyn_cast<Value>(&I)) == iSet->end())
                (*iSet).insert(make_pair(dyn_cast<Value>(&I), (*iSet).at(I.getOperand(0))));
            else
                (*iSet).find(dyn_cast<Value>(&I))->second = (*iSet).at(I.getOperand(0));
        }

        if (isa<BinaryOperator>(&I)) {
            dumpBinInst(&I);
            // addition
            if (I.getOpcode() == 8) {
                Interval i1 = getValInterval(I.getOperand(0), iSet);
                Interval i2 = getValInterval(I.getOperand(1), iSet);
                //(*iSet)[dyn_cast<Value>(&I)] = MP(i1.first + i2.first, i1.second + i2.second);
                //(*iSet).insert(make_pair(dyn_cast<Value>(&I), i1.add(i2)));
                updateMap(iSet, dyn_cast<Value>(&I), i1.add(i2));
            }

            // subtraction
            if (I.getOpcode() == 10) {
                Interval i1 = getValInterval(I.getOperand(0), iSet);
                Interval i2 = getValInterval(I.getOperand(1), iSet);
                //(*iSet)[dyn_cast<Value>(&I)] = MP(i1.first - i2.second, i1.second - i2.first);
                //(*iSet).insert(make_pair(dyn_cast<Value>(&I), i1.sub(i2)));
                updateMap(iSet, dyn_cast<Value>(&I), i1.sub(i2));
            }

            // multiplication
            if (I.getOpcode() == 12) {
                Interval i1 = getValInterval(I.getOperand(0), iSet);
                Interval i2 = getValInterval(I.getOperand(1), iSet);
                //APInt minim = i1.first * i2.first;
                //APInt maxim = i1.first * i2.first;
                //minim = getMin(minim, i1.first * i2.second);
                //maxim = getMax(maxim, i1.first * i2.second);
                //minim = getMin(minim, i1.second * i2.first);
                //maxim = getMax(maxim, i1.second * i2.first);
                //minim = getMin(minim, i1.second * i2.second);
                //maxim = getMax(maxim, i1.second * i2.second);
                //(*iSet).insert(make_pair(dyn_cast<Value>(&I), i1.multiply(i2)));
                updateMap(iSet, dyn_cast<Value>(&I), i1.multiply(i2));
            }

            // division
            if (I.getOpcode() == 15) {
                Interval i1 = getValInterval(I.getOperand(0), iSet);
                Interval i2 = getValInterval(I.getOperand(1), iSet);
                if (i2.contains(APInt(32, 0))) {
                    if (verbose) {
                        errs() << "\n*************WARNING*************\n";
                        errs() << "Possible division by 0 detected";
                        if (Loc) {
                            errs() << " in function '" << Loc.getScope().getName() << "'";
                            errs() << " at line " << Loc.getLineNumber();
                        }
                        errs() << "\n\n";
                    }
                }
                //APInt minim = i1.first.sdiv(i2.first);
                //APInt maxim = i1.first.sdiv(i2.first);
                //minim = getMin(minim, i1.first.sdiv(i2.second));
                //maxim = getMax(maxim, i1.first.sdiv(i2.second));
                //minim = getMin(minim, i1.second.sdiv(i2.first));
                //maxim = getMax(maxim, i1.second.sdiv(i2.first));
                //minim = getMin(minim, i1.second.sdiv(i2.second));
                //maxim = getMax(maxim, i1.second.sdiv(i2.second));
                //(*iSet).insert(make_pair(dyn_cast<Value>(&I), i1.udiv(i2)));
                updateMap(iSet, dyn_cast<Value>(&I), i1.udiv(i2));
            }
        }
    }

    bool changed = false;
    for (auto v : *iSet) {
        if (outState[b].find(v.first) != outState[b].end() && outState[b].find(v.first)->second != (*iSet).find(v.first)->second) {
            changed = true;
            break;
        }
    }
    outState[b] = *iSet;

    /* Update IN sets of all successors corresponding to this basic block */
    auto branch = dyn_cast<BranchInst>(b->getTerminator());
    if (branch && branch->isConditional() ) {
        /* Assuming conditions of the form (Var Op Constant).
         * Op can be >, >=, <, <=, == or !=. */
        ICmpInst * condition = dyn_cast<ICmpInst>(branch->getCondition());

        // iterate backwards to get variable name
        Instruction *unnamedVar = dyn_cast<Instruction>(condition->getOperand(0));
        Value * namedVar = unnamedVar->getOperand(0);
        APInt cons = dyn_cast<ConstantInt>(condition->getOperand(1))->getValue();

        // true branch
        ConstantRange trueRange = condition->makeConstantRange(condition->getPredicate(), cons);
        inState[branch->getSuccessor(0)][b] = *iSet;
        inState.at(branch->getSuccessor(0)).at(b).at(namedVar) = inState.at(branch->getSuccessor(0)).at(b).at(namedVar).intersectWith(trueRange);

        //false branch
        ConstantRange falseRange = trueRange.inverse();
        inState[branch->getSuccessor(1)][b] = *iSet;
        inState.at(branch->getSuccessor(1)).at(b).at(namedVar) = inState.at(branch->getSuccessor(1)).at(b).at(namedVar).intersectWith(falseRange);
    }

    else { // single or no successor
        //assert(b->getTerminator()->getNumSuccessors() == 1);
        if (b->getTerminator()->getNumSuccessors() == 1)
            inState[b->getTerminator()->getSuccessor(0)][b] = outState[b];
    }
    if(verbose) {
        errs() << "---------------\n";
        b->dump();
        dumpMap(&outState[b], false);
        errs() << "---------------\n";
    }

    return changed;
}

/* Do fixed point computation to find in and out sets. */
void computeFP (Function *F)
{
    bool change = true;
    while (change) {
        change = false;
        for (auto& b : *F) {
            processBB(&b, false);
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
            FindAllVars(&F);
            assignTempNames();
            InitializeStates(&F);
            computeFP(&F);

            return false;
        }
    };
}

char SymEx::ID = 0;
static RegisterPass<SymEx> X("symex", "Symbolic Execution Interpretation");
