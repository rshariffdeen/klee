//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"

#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"

#include "klee/Expr.h"

#include "Memory.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <iomanip>
#include <sstream>
#include <cassert>
#include <map>
#include <set>
#include <stdarg.h>

using namespace llvm;
using namespace klee;

namespace { 
  cl::opt<bool>
  DebugLogStateMerge("debug-log-state-merge");
}

/***/

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0), 
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

/***/

ExecutionState::ExecutionState(KFunction *kf) :
    pc(kf->instructions),
    prevPC(pc),

    weight(1),
    depth(0),

    instsSinceCovNew(0),
    coveredNew(false),
    forkDisabled(false),
    ptreeNode(0),
    steppedInstructions(0), functionStateInfo(new FunctionStateInfo()) {
  pushFrame(0, kf);
}

ExecutionState::ExecutionState(const std::vector<ref<Expr> > &assumptions)
    : constraints(assumptions), ptreeNode(0) , functionStateInfo(new FunctionStateInfo())  {}

ExecutionState::~ExecutionState() {
  for (unsigned int i=0; i<symbolics.size(); i++)
  {
    const MemoryObject *mo = symbolics[i].first;
    assert(mo->refCount > 0);
    mo->refCount--;
    if (mo->refCount == 0)
      delete mo;
  }

  for (auto cur_mergehandler: openMergeStack){
    cur_mergehandler->removeOpenState(this);
  }


  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    fnAliases(state.fnAliases),
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),

    addressSpace(state.addressSpace),
    constraints(state.constraints),

    queryCost(state.queryCost),
    weight(state.weight),
    depth(state.depth),

    pathOS(state.pathOS),
    symPathOS(state.symPathOS),

    instsSinceCovNew(state.instsSinceCovNew),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    coveredLines(state.coveredLines),
    ptreeNode(state.ptreeNode),
    symbolics(state.symbolics),
    arrayNames(state.arrayNames),
    openMergeStack(state.openMergeStack),
    steppedInstructions(state.steppedInstructions),
    functionStateInfo(state.functionStateInfo->copy())
{
  for (unsigned int i=0; i<symbolics.size(); i++)
    symbolics[i].first->refCount++;

  for (auto cur_mergehandler: openMergeStack)
    cur_mergehandler->addOpenState(this);
}

ExecutionState *ExecutionState::branch() {
  depth++;

  ExecutionState *falseState = new ExecutionState(*this);
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  weight *= .5;
  falseState->weight -= weight;

  return falseState;
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.push_back(StackFrame(caller,kf));
}

void ExecutionState::popFrame() {
  StackFrame &sf = stack.back();
  for (std::vector<const MemoryObject*>::iterator it = sf.allocas.begin(), 
         ie = sf.allocas.end(); it != ie; ++it)
    addressSpace.unbindObject(*it);
  stack.pop_back();
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) { 
  mo->refCount++;
  symbolics.push_back(std::make_pair(mo, array));
}
///

std::string ExecutionState::getFnAlias(std::string fn) {
  std::map < std::string, std::string >::iterator it = fnAliases.find(fn);
  if (it != fnAliases.end())
    return it->second;
  else return "";
}

void ExecutionState::addFnAlias(std::string old_fn, std::string new_fn) {
  fnAliases[old_fn] = new_fn;
}

void ExecutionState::removeFnAlias(std::string fn) {
  fnAliases.erase(fn);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second;
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second;
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?
  if (symbolics!=b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }

  std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  std::set< ref<Expr> > bConstraints(b.constraints.begin(), 
                                     b.constraints.end());
  std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  std::set_intersection(aConstraints.begin(), aConstraints.end(),
                        bConstraints.begin(), bConstraints.end(),
                        std::inserter(commonConstraints, commonConstraints.begin()));
  std::set_difference(aConstraints.begin(), aConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(aSuffix, aSuffix.end()));
  std::set_difference(bConstraints.begin(), bConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(bSuffix, bSuffix.end()));
  if (DebugLogStateMerge) {
    llvm::errs() << "\tconstraint prefix: [";
    for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
                                        ie = commonConstraints.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tA suffix: [";
    for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
                                        ie = aSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]>";
    llvm::errs() << "\tB suffix: [";
    for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
                                        ie = bSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
  }

  // We cannot merge if addresses would resolve differently in the
  // states. This means:
  // 
  // 1. Any objects created since the branch in either object must
  // have been free'd.
  //
  // 2. We cannot have free'd any pre-existing object in one state
  // and not the other

  if (DebugLogStateMerge) {
    llvm::errs() << "\tchecking object states\n";
    llvm::errs() << "A: " << addressSpace.objects << "\n";
    llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  }
    
  std::set<const MemoryObject*> mutated;
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  for (; ai!=ae && bi!=be; ++ai, ++bi) {
    if (ai->first != bi->first) {
      if (DebugLogStateMerge) {
        if (ai->first < bi->first) {
          llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
        } else {
          llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
        }
      }
      return false;
    }
    if (ai->second != bi->second) {
      if (DebugLogStateMerge)
        llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
      mutated.insert(ai->first);
    }
  }
  if (ai!=ae || bi!=be) {
    if (DebugLogStateMerge)
      llvm::errs() << "\t\tmappings differ\n";
    return false;
  }
  
  // merge stack

  ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  for (std::set< ref<Expr> >::iterator it = aSuffix.begin(), 
         ie = aSuffix.end(); it != ie; ++it)
    inA = AndExpr::create(inA, *it);
  for (std::set< ref<Expr> >::iterator it = bSuffix.begin(), 
         ie = bSuffix.end(); it != ie; ++it)
    inB = AndExpr::create(inB, *it);

  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if (av.isNull() || bv.isNull()) {
        // if one is null then by implication (we are at same pc)
        // we cannot reuse this local, so just ignore
      } else {
        av = SelectExpr::create(inA, av, bv);
      }
    }
  }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(), 
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly && 
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      wos->write(i, SelectExpr::create(inA, av, bv));
    }
  }

  constraints = ConstraintManager();
  for (std::set< ref<Expr> >::iterator it = commonConstraints.begin(), 
         ie = commonConstraints.end(); it != ie; ++it)
    constraints.addConstraint(*it);
  constraints.addConstraint(OrExpr::create(inA, inB));

  return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out,
                               llvm::DataLayout *dataLayout) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line << ":" << ii.column;
    out << "\n";
    target = sf.caller;
  }

  if (!OutputLocalsOnError)
    return;

  if (!dataLayout)
    return;

  out << "Stack Content:\n";

  // Get the deepest application frame outside libc
  target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator it = stack.rbegin(),
               ie = stack.rend();
       it != ie; ++it) {
    std::string buf;
    const StackFrame &sf = *it;
    llvm::raw_string_ostream frameStr(buf);
    dumpFrame(frameStr, *it, target, dataLayout, true);
    dumpFrame(frameStr, sf, target, dataLayout, true);
    frameStr.flush();
    functionStateInfo->addStateInfo(it->kf->function, buf);
    target = it->caller;
  }
  functionStateInfo->print(out);
}

void ExecutionState::dumpFrame(llvm::raw_ostream &out, const StackFrame &sf,
                               const KInstruction *target,
                               llvm::DataLayout *dataLayout, bool onStack) const {
  const InstructionInfo &ii = *(target->info);
  std::size_t found = ii.file.find("libc");
  if (found == std::string::npos) {

    Function *f = sf.kf->function;
    out << f->getName() << ":\n";
    for (std::vector<const MemoryObject *>::const_iterator
                 it1 = sf.allocas.begin(),
                 ie1 = sf.allocas.end();
         it1 != ie1; ++it1) {
      const MemoryObject *mo = *it1;
      ObjectPair op;
      ref <ConstantExpr> address =
              llvm::dyn_cast<ConstantExpr>(mo->getBaseExpr());

      if (!addressSpace.resolveOne(address, op))
        continue;

      const ObjectState *os = op.second;

      const llvm::AllocaInst *ai =
              llvm::dyn_cast<llvm::AllocaInst>(mo->allocSite);

      if (!ai)
        continue;

      out << f->getName();
      mo->allocSite->print(out);
      if (onStack)
        out << " (stack): ";
      else
        out << " (exited): ";

      std::string buf;
      llvm::raw_string_ostream instrString(buf);
      mo->allocSite->print(instrString);
      instrString.flush();

      size_t spacePos;
      if ((spacePos = buf.find(" ", 3)) != std::string::npos) {
        std::string varName = buf.substr(3, spacePos - 3);
        out << varName << " (local):";
      } else {
        out << "(unknown) (local):";
      }
      out << "\n";

      // Next we print more specific information based on the type of the
      // allocation
      dumpHandleType(out, "", os, ai->getAllocatedType(), dataLayout);
    }

    for (std::map<const MemoryObject *,
            std::pair < ref < Expr > , ref < Expr >> > ::const_iterator
            it1 = sf.nonLocalsRead.begin(),
                    ie1 = sf.nonLocalsRead.end();
            it1 != ie1;
    ++it1) {
      const MemoryObject *mo = it1->first;
      ObjectPair op;
      ref <ConstantExpr> address =
              llvm::dyn_cast<ConstantExpr>(mo->getBaseExpr());

      if (!addressSpace.resolveOne(address, op))
        continue;

      const ObjectState *os = op.second;

      const llvm::AllocaInst *ai =
              llvm::dyn_cast<llvm::AllocaInst>(mo->allocSite);

      if (!ai)
        continue;

      out << f->getName();
      if (onStack)
        out << " (stack): ";
      else
        out << " (exited): ";

      std::string buf;
      llvm::raw_string_ostream instrString(buf);
      mo->allocSite->print(instrString);
      instrString.flush();

      size_t spacePos;
      if ((spacePos = buf.find(" ", 3)) != std::string::npos) {
        std::string varName = buf.substr(3, spacePos - 3);
        out << varName << "[";
        it1->second.first->print(out);
        out << "] (non-local, read): ";
      } else {
        out << "(unknown)[";
        it1->second.first->print(out);
        out << "] (non-local, read): ";
      }
      out << "\n";

      // Next we print more specific information based on the type of the
      // allocation
      dumpHandleType(out, "", os, ai->getAllocatedType(), dataLayout);
    }

    for (std::map<const MemoryObject *,
            std::pair < ref < Expr > , ref < Expr >> > ::const_iterator
            it1 = sf.nonLocalsWritten.begin(),
                    ie1 = sf.nonLocalsWritten.end();
            it1 != ie1;
    ++it1) {
      const MemoryObject *mo = it1->first;
      ObjectPair op;
      ref <ConstantExpr> address =
              llvm::dyn_cast<ConstantExpr>(mo->getBaseExpr());

      if (!addressSpace.resolveOne(address, op))
        continue;

      const ObjectState *os = op.second;

      const llvm::AllocaInst *ai =
              llvm::dyn_cast<llvm::AllocaInst>(mo->allocSite);

      if (!ai)
        continue;

      out << f->getName();
      if (onStack)
        out << " (stack): ";
      else
        out << " (exited): ";

      std::string buf;
      llvm::raw_string_ostream instrString(buf);
      mo->allocSite->print(instrString);
      instrString.flush();

      size_t spacePos;
      if ((spacePos = buf.find(" ", 3)) != std::string::npos) {
        std::string varName = buf.substr(3, spacePos - 3);
        out << varName << "[";
        it1->second.first->print(out);
        out << "]: (non-local, written)";
      } else {
        out << "(unknown):";
        out << "(unknown)[";
        it1->second.first->print(out);
        out << "]: (non-local, written)";
      }
      out << "\n";
      out << "\n";

    }
  }
}

void ExecutionState::dumpHandleType(llvm::raw_ostream &out,
                                    const std::string &prefix,
                                    const ObjectState *valueObjectState,
                                    llvm::Type *type,
                                    llvm::DataLayout *dataLayout) const {
  // First we print basic information about the allocation
  ref<Expr> nullPtr = Expr::createPointer(0);
  out << prefix << "\tType: ";
  type->print(out);
  Expr::Width width = dataLayout->getTypeSizeInBits(type);
  ref<Expr> result = valueObjectState->read(nullPtr, width);
  out << "\tExpr: ";
  result->print(out);
  out << "\n";

  if (type->isPointerTy()) {
    llvm::PointerType *pType = llvm::dyn_cast<llvm::PointerType>(type);
    if (llvm::PointerType *ppType =
            llvm::dyn_cast<llvm::PointerType>(pType->getElementType())) {
      if (llvm::IntegerType *baseElementType =
              llvm::dyn_cast<llvm::IntegerType>(ppType->getElementType())) {
        if (baseElementType->getIntegerBitWidth() == Expr::Int8) {
          // We have found a storage address of a char ** structure
          ref<ConstantExpr> address = llvm::dyn_cast<ConstantExpr>(result);
          ObjectPair op;
          ref<Expr> nullPtr = Expr::createPointer(0);

          if (addressSpace.resolveOne(address, op)) {
            unsigned ptrBitWidth = nullPtr->getWidth();
            unsigned ptrByteWidth = (nullPtr->getWidth()) >> 3;
            const MemoryObject *mo = op.first;
            const ObjectState *os = op.second;

            if (mo->size % ptrByteWidth == 0) {
              for (unsigned i = 0; i < mo->size; i += ptrByteWidth) {
                ref<Expr> result =
                        os->read(Expr::createPointer(i), ptrBitWidth);
                out << prefix << "\t\tAddress: ";
                result->print(out);
                out << "\n";
                address = llvm::dyn_cast<ConstantExpr>(result);
                if (!address->isZero()) {
                  if (addressSpace.resolveOne(address, op)) {
                    const MemoryObject *mo1 = op.first;
                    const ObjectState *os1 = op.second;
                    for (unsigned j = 0; j < mo1->size; ++j) {
                      result = os1->read(Expr::createPointer(j), Expr::Int8);
                      out << prefix << "\t\t\t" << j << " -> ";
                      result->print(out);
                      out << "\n";
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  } else if (type->isArrayTy()) {
    llvm::ArrayType *aType = llvm::dyn_cast<llvm::ArrayType>(type);
    uint64_t nElements = aType->getArrayNumElements();
    if (nElements > 0) {
      out << prefix << "\t\tArray Content:\n";
      if (llvm::IntegerType *eType =
              llvm::dyn_cast<llvm::IntegerType>(aType->getArrayElementType())) {
        unsigned elementBitSize = eType->getBitWidth();
        if (elementBitSize == Expr::Int8) {
          for (unsigned i = 0; i < nElements; ++i) {
            result = valueObjectState->read(Expr::createPointer(i), Expr::Int8);
            out << prefix << "\t\t\t" << i << " -> ";
            result->print(out);
            out << "\n";
          }
        }
      } else if (llvm::StructType *eType = llvm::dyn_cast<llvm::StructType>(
              aType->getArrayElementType())) {
        uint64_t offset = 0;
        unsigned elemBitSize = dataLayout->getTypeSizeInBits(eType);
        unsigned elemByteSize = elemBitSize >> 3;
        for (unsigned i = 0; i < nElements; ++i) {
          dumpHandleStructType(out, prefix, valueObjectState, offset, eType,
                               dataLayout);
          offset += elemByteSize;
        }
      }
    }
  } else if (type->isStructTy()) {
    llvm::StructType *cType = llvm::dyn_cast<llvm::StructType>(type);
    dumpHandleStructType(out, prefix, valueObjectState, 0, cType, dataLayout);
  }
}

void ExecutionState::dumpHandleStructType(llvm::raw_ostream &out,
                                          const std::string &prefix,
                                          const ObjectState *valueObjectState,
                                          uint64_t initOffset,
                                          llvm::StructType *type,
                                          llvm::DataLayout *dataLayout) const {
  unsigned nElements = type->getStructNumElements();
  uint64_t offset = initOffset;

  out << prefix << "\t\tStruct Content:\n";
  for (unsigned i = 0; i < nElements; ++i) {
    llvm::Type *eType = type->getStructElementType(i);
    unsigned elemBitSize = dataLayout->getTypeSizeInBits(eType);
    unsigned elemByteSize = elemBitSize >> 3;

    ref<Expr> result =
            valueObjectState->read(Expr::createPointer(offset), elemBitSize);

    out << prefix << "\t\t\t";
    eType->print(out);
    out << ":\t" << i << " -> ";
    result->print(out);
    out << "\n";

    if (eType->isPointerTy()) {
      if (ConstantExpr *address = llvm::dyn_cast<ConstantExpr>(result)) {
        ObjectPair op;
        if (addressSpace.resolveOne(address, op)) {
          const ObjectState *os = op.second;
          if (llvm::PointerType *pType =
                  llvm::dyn_cast<llvm::PointerType>(eType)) {
            llvm::Type *peType = pType->getPointerElementType();
            std::string newPrefix = "\t\t\t" + prefix;
            dumpHandleType(out, newPrefix, os, peType, dataLayout);
          }
        }
      }
    }

    offset += elemByteSize;
  }

}

void ExecutionState::addStateInfoAsReturn(const KInstruction *target,
                                          llvm::DataLayout *dataLayout) {
  llvm::Function *f = target->inst->getParent()->getParent();
  std::string buffer;
  llvm::raw_string_ostream strStream(buffer);
  const StackFrame &sf = stack.back();

  dumpFrame(strStream, sf, target, dataLayout);
  strStream.flush();
  functionStateInfo->addStateInfo(f, buffer);
}
