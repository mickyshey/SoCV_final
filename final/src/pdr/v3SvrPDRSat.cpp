/****************************************************************************
  FileName     [ v3SvrPDRSat.cpp ]
  PackageName  [ v3/src/pdr ]
  Synopsis     [ Define PDR sat sovler interface ]
  Author       [ Cheng-Yin Wu, SillyDuck ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef V3_SVR_PDRSAT_C
#define V3_SVR_PDRSAT_C

#include "v3SvrPDRSat.h"
#include <unistd.h>
#include <cassert>
#include <vector>
#include <map>
#include "reader.h"
#include "v3Msg.h"
#include "v3Ntk.h"

#include <cmath>

/* -------------------------------------------------- *\
 * Class V3SvrPDRSat Implementations
\* -------------------------------------------------- */
inline void buf(SolverV* SS, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push(~a); lits.push( b); SS->addClause(lits); lits.clear();
   lits.push( a); lits.push(~b); SS->addClause(lits); lits.clear();
}

inline void and_2(SolverV* SS, const Lit& y, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push( a); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push( b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push(~b); lits.push( y); SS->addClause(lits); lits.clear();
}

inline void xor_2(SolverV* SS, const Lit& y, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push( a); lits.push( b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push(~b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push( a); lits.push(~b); lits.push( y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push( b); lits.push( y); SS->addClause(lits); lits.clear();
}


// Constructor and Destructor
V3SvrPDRSat::V3SvrPDRSat(V3Ntk* ntk, const bool& freeBound, const bool& proofLog) 
   : _ntk(ntk), _freeBound(freeBound) , _L(_ntk->getLatchSize()) , _I(_ntk->getInputSize()) {
 
   _Solver = new SolverV();
   if(proofLog) _Solver->proof = new Proof(); // MODIFICATION FOR SoCV
   assert (_Solver); assumeRelease(); initRelease();
   _curVar = 0; _Solver->newVar(); ++_curVar;  // 0 for Recycle Literal, if Needed
   _ntkData = new V3SvrMVarData[ntk->getNetSize()];
   for (uint32_t i = 0; i < ntk->getNetSize(); ++i) _ntkData[i].clear();
   _actVars.clear();
}

V3SvrPDRSat::~V3SvrPDRSat() {
   delete _Solver; assumeRelease(); initRelease();
   for (uint32_t i = 0; i < _ntk->getNetSize(); ++i) _ntkData[i].clear(); delete [] _ntkData;
}

// Basic Operation Functions
void
V3SvrPDRSat::reset() {
   delete _Solver; _Solver = new SolverV(); assert (_Solver); assumeRelease(); initRelease();
   _curVar = 0; _Solver->newVar(); ++_curVar;  // 0 for Recycle Literal, if Needed
   for (uint32_t i = 0; i < _ntk->getNetSize(); ++i) _ntkData[i].clear();
}

void
V3SvrPDRSat::assumeInit() {
   for (uint32_t i = 0; i < _init.size(); ++i) _assump.push(_init[i]);
}

void
V3SvrPDRSat::assertInit() {
   for (uint32_t i = 0; i < _init.size(); ++i) _Solver->addUnit(_init[i]);
}

void
V3SvrPDRSat::initRelease() { _init.clear(); }

void
V3SvrPDRSat::assumeRelease() { _assump.clear(); }

void
V3SvrPDRSat::assumeProperty(const size_t& var, const bool& invert) {
   _assump.push(mkLit(getOriVar(var), invert ^ isNegFormula(var)));
}

void
V3SvrPDRSat::assertProperty(const size_t& var, const bool& invert) {
   _Solver->addUnit(mkLit(getOriVar(var), invert ^ isNegFormula(var)));
}

void
V3SvrPDRSat::assumeProperty(const V3NetId& id, const bool& invert, const uint32_t& depth) {
   assert (validNetId(id)); assert (1 == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   _assump.push(mkLit(var, invert ^ isV3NetInverted(id)));
}

void
V3SvrPDRSat::assertProperty(const V3NetId& id, const bool& invert, const uint32_t& depth) {
   assert (validNetId(id)); assert (1 == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   _Solver->addUnit(mkLit(var, invert ^ isV3NetInverted(id)));
}

const bool
V3SvrPDRSat::simplify() { return _Solver->simplifyDB(); }

const bool
V3SvrPDRSat::solve() {
   double ctime = (double)clock() / CLOCKS_PER_SEC;
   _Solver->solve(); ++_solves;
   _runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
   return _Solver->okay();
}

const bool
V3SvrPDRSat::assump_solve() {
   double ctime = (double)clock() / CLOCKS_PER_SEC;
   bool result = _Solver->solve(_assump); ++_solves;
   _runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
   return result;
}

// Manipulation Helper Functions
void
V3SvrPDRSat::setTargetValue(const V3NetId& id, const V3BitVecX& value, const uint32_t& depth, V3SvrDataVec& formula) {
   // Note : This Function will set formula such that AND(formula) represents (id == value)
   uint32_t i, size = value.size(); assert (size == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   if (isV3NetInverted(id)) {
      for (i = 0; i < size; ++i) {
         if ('1' == value[i]) formula.push_back(getNegVar(var + i));
         else if ('0' == value[i]) formula.push_back(getPosVar(var + i));
      }
   }
   else {
      for (i = 0; i < size; ++i) {
         if ('1' == value[i]) formula.push_back(getPosVar(var + i));
         else if ('0' == value[i]) formula.push_back(getNegVar(var + i));
      }
   }
}

void
V3SvrPDRSat::assertImplyUnion(const V3SvrDataVec& vars) {
   // Construct a CNF formula (var1 + var2 + ... + varn) and add to the solver
   if (vars.size() == 0) return; vec<Lit> lits; lits.clear();
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
   }
   _Solver->addClause(lits); lits.clear();
}

const size_t
V3SvrPDRSat::setTargetValue(const V3NetId& id, const V3BitVecX& value, const uint32_t& depth, const size_t& prev) {
   // Construct formula y = b0 & b1' & b3 & ... & bn', and return variable y
   assert (!prev || !isNegFormula(prev));  // Constrain input prev variable should NOT be negative!
   uint32_t i, size = value.size(); assert (size == _ntk->getNetWidth(id));
   const Var _var = getVerifyData(id, depth); assert (_var);
   Lit aLit = (prev) ? mkLit(getOriVar(prev)) : lit_Undef, bLit, yLit;
   vec<Lit> lits; lits.clear();
   for (i = 0; i < size; ++i) {
      if ('1' == value[i]) bLit = mkLit(_var + i, isV3NetInverted(id));
      else if ('0' == value[i]) bLit = ~mkLit(_var + i, isV3NetInverted(id));
      else bLit = lit_Undef;
      if (!(bLit == lit_Undef)) {
         if (!(aLit == lit_Undef)) {
            yLit = mkLit(newVar(1));
            lits.push(aLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
            lits.push(bLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
            lits.push(~aLit); lits.push(~bLit); lits.push(yLit); _Solver->addClause(lits); lits.clear();
            aLit = yLit; assert (!sign(aLit));
         }
         else aLit = bLit;
      }
   }
   if (aLit == lit_Undef) return 0;
   else if (sign(aLit)) {
      yLit = mkLit(newVar(1));
      lits.push(~aLit); lits.push(yLit); _Solver->addClause(lits); lits.clear();
      lits.push(aLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
      aLit = yLit;
   }
   assert (!isNegFormula(getPosVar(var(aLit))));
   return getPosVar(var(aLit));
}

const size_t
V3SvrPDRSat::setImplyUnion(const V3SvrDataVec& vars) {
   // Construct a CNF formula (y' + var1 + var2 + ... + varn), and return variable y
   if (vars.size() == 0) return 0; vec<Lit> lits; lits.clear();
   Lit lit = mkLit(newVar(1), true); lits.push(lit);
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
   }
   _Solver->addClause(lits); lits.clear();
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const size_t
V3SvrPDRSat::setImplyIntersection(const V3SvrDataVec& vars) {
   // Goal : y --> (var1 && var2 && ... && varn)
   // Construct CNF formulas (y' + var1) && (y' + var2) &&  ... (y' + varn), and return variable y
   if (vars.size() == 0) return 0;
   Lit lit = mkLit(newVar(1), true);
   vec<Lit> lits; lits.clear();
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(lit);
      lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
      _Solver->addClause(lits); lits.clear();
   }
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const size_t
V3SvrPDRSat::setImplyInit() {
   Lit lit = mkLit(newVar(1), true);
   vec<Lit> lits; lits.clear();
   for (uint32_t i = 0; i < _init.size(); ++i) {
      lits.push(lit); lits.push(_init[i]); _Solver->addClause(lits); lits.clear();
   }
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const V3BitVecX
V3SvrPDRSat::getDataValue(const V3NetId& id, const uint32_t& depth) const {
   Var var = getVerifyData(id, depth); assert (var);
   uint32_t i, width = _ntk->getNetWidth(id);
   V3BitVecX value(width);
   if (isV3NetInverted(id)) {
      for (i = 0; i < width; ++i)
         if (l_True == _Solver->model[var + i]) value.set0(i);
         else value.set1(i);
   }
   else {
      for (i = 0; i < width; ++i)
         if (l_True == _Solver->model[var + i]) value.set1(i);
         else value.set0(i);
   }
   return value;
}

const bool
V3SvrPDRSat::getDataValue(const size_t& var) const {
   return (isNegFormula(var)) ^ (l_True == _Solver->model[getOriVar(var)]);
}

void
V3SvrPDRSat::getDataConflict(V3SvrDataVec& vars) const {
   for (int i = 0; i < _Solver->conflict.size(); ++i)
      vars.push_back(getPosVar(var(_Solver->conflict[i])));
}

const size_t
V3SvrPDRSat::getFormula(const V3NetId& id, const uint32_t& depth) {
   Var var = getVerifyData(id, depth); assert (var);
   assert (!isNegFormula(getPosVar(var)));
   return (isV3NetInverted(id) ? getNegVar(var) : getPosVar(var));
}

const size_t
V3SvrPDRSat::getFormula(const V3NetId& id, const uint32_t& bit, const uint32_t& depth) {
   Var var = getVerifyData(id, depth); assert (var);
   assert (bit < _ntk->getNetWidth(id)); assert (!isNegFormula(getPosVar(var + bit)));
   return (isV3NetInverted(id) ? getNegVar(var + bit) : getPosVar(var + bit));
}

// Print Data Functions
void
V3SvrPDRSat::printInfo() const {
   Msg(MSG_IFO) << "#Vars = " << _Solver->nVars() << ", #Cls = " << _Solver->nClauses() << ", " 
                << "#SV = " << totalSolves() << ", AccT = " << totalTime();
}

// Gate Formula to Solver Functions
void
V3SvrPDRSat::add_FALSE_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (AIG_FALSE == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   // Set SATVar
   _ntkData[index].push_back(newVar(1)); assert (getVerifyData(out, depth));
   _Solver->addUnit(mkLit(_ntkData[index].back(), true));
}

void
V3SvrPDRSat::add_PI_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (V3_PI == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   // Set SATVar
   _ntkData[index].push_back(newVar(_ntk->getNetWidth(out))); assert (getVerifyData(out, depth));
}

void
V3SvrPDRSat::add_FF_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (V3_FF == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   const uint32_t width = _ntk->getNetWidth(out); assert (width);
   if (_freeBound) {
      // Set SATVar
      _ntkData[index].push_back(newVar(width));
   }
   else if (depth) {
      // Build FF I/O Relation
      const V3NetId in1 = _ntk->getInputNetId(out, 0); assert (validNetId(in1));
      const Var var1 = getVerifyData(in1, depth - 1); assert (var1);
      // Set SATVar
      if (isV3NetInverted(in1)) {
         _ntkData[index].push_back(newVar(width));
         for (uint32_t i = 0; i < width; ++i) 
            buf(_Solver, mkLit(_ntkData[index].back() + i), mkLit(var1 + i, true));
      }
      else _ntkData[index].push_back(var1);
   }
   else {
      // Set SATVar
      _ntkData[index].push_back(newVar(width));
      const Var& var = _ntkData[index].back();
      // Build FF Initial State
      const V3NetId in1 = _ntk->getInputNetId(out, 1); assert (validNetId(in1));
      _init.push_back(mkLit(var, !isV3NetInverted(in1)));
   }
   assert (getVerifyData(out, depth));
}

void
V3SvrPDRSat::add_AND_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (!getVerifyData(out, depth));
   assert ((AIG_NODE == _ntk->getGateType(out)) || (BV_AND == _ntk->getGateType(out)));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   const uint32_t width = _ntk->getNetWidth(out); assert (width);
   // Set SATVar
   _ntkData[index].push_back(newVar(_ntk->getNetWidth(out))); assert (getVerifyData(out, depth));
   const Var& var = _ntkData[index].back();
   // Build AND I/O Relation
   const V3NetId in1 = _ntk->getInputNetId(out, 0); assert (validNetId(in1));
   const V3NetId in2 = _ntk->getInputNetId(out, 1); assert (validNetId(in2));
   const Var var1 = getVerifyData(in1, depth); assert (var1);
   const Var var2 = getVerifyData(in2, depth); assert (var2);
   for (uint32_t i = 0; i < width; ++i) 
      and_2(_Solver, mkLit(var + i), mkLit(var1 + i, isV3NetInverted(in1)), mkLit(var2 + i, isV3NetInverted(in2)));
}


// Network to Solver Functions
void
V3SvrPDRSat::addVerifyData(const V3NetId& id, const uint32_t& depth) {
   V3GateType type = _ntk->getGateType(id); assert (type < V3_XD);
   if (V3_PIO >= type) return add_PI_Formula(id, depth);
   else if (V3_FF == type) return add_FF_Formula(id, depth);
   else {
      if (AIG_FALSE == type) return add_FALSE_Formula(id, depth);  // AIG_FALSE
      return add_AND_Formula(id, depth);  // AIG_NODE
   }
}

void
V3SvrPDRSat::addBoundedVerifyData(const V3NetId& id, const uint32_t& depth) {
   if (existVerifyData(id, depth)) return;
   uint32_t qq = depth;
   addBoundedVerifyDataRecursively(id, qq);
}

void 
V3SvrPDRSat::addBoundedVerifyDataRecursively(const V3NetId& id, uint32_t& depth)
{
    assert( validNetId(id) );
    if( existVerifyData(id,depth) ) return;
    const V3GateType type = _ntk->getGateType(id); assert(type < V3_XD);
    if( V3_PIO >= type ) add_PI_Formula(id,depth);
    else if( V3_FF == type ) {
        if(depth) { --depth; addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,0), depth); ++depth; }
        add_FF_Formula(id, depth);
    }
    else if(AIG_FALSE >= type) {
        if(AIG_NODE == type) {
            addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,0), depth);
            addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,1), depth);
            add_AND_Formula(id,depth);
        }
        else {
            assert(AIG_FALSE == type);
            add_FALSE_Formula(id,depth);
        }
    }
    else {
        assert(0);
    }
}

const bool
V3SvrPDRSat::existVerifyData(const V3NetId& id, const uint32_t& depth) {
   return getVerifyData(id, depth);
}

// MODIFICATION FOR SoCV
void V3SvrPDRSat::resizeNtkData(const uint32_t& num) {
  V3SvrMVarData* ntkData_tmp = new V3SvrMVarData[_ntk->getNetSize()];
  for(uint32_t i = 0, j = (_ntk->getNetSize()-num); i < j; ++i) {
    ntkData_tmp[i] = _ntkData[i];
  }
  delete[] _ntkData;
  _ntkData = ntkData_tmp;
}

// MiniSat Functions
const Var
V3SvrPDRSat::newVar(const uint32_t& width) {
   Var cur_var = _curVar;
   for (uint32_t i = 0; i < width; ++i) _Solver->newVar();
   _curVar += width; return cur_var;
}

const Var
V3SvrPDRSat::getVerifyData(const V3NetId& id, const uint32_t& depth) const {
   assert (validNetId(id));
   if (depth >= _ntkData[getV3NetIndex(id)].size()) return 0;
   else return _ntkData[getV3NetIndex(id)][depth];
}




/*****************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
**********************ABOVE IS NOT RELEVANT TO PDR****************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
*****************************************************************************/


void V3SvrPDRSat::setFrame(vector<vector<Cube*>*>* f) {
  _F = f;
}

void V3SvrPDRSat::setMonitor(const V3NetId& m) {
  _monitor = m;
	// modified by r04943179
	setDFSMonitor();
	// end of modification
}

void V3SvrPDRSat::addInitiateState() {
  if (debug) cerr << "_actVars[0] : " << _actVars[0] << endl;
  for (unsigned i = 0; i < _L; ++i) {
    vec<Lit> lits;
    lits.push(mkLit(getVerifyData(_ntk->getLatch(i), 0), true));
    if (debug) cerr << getVerifyData(_ntk->getLatch(i), 0) << " ";
    lits.push(mkLit(_actVars[0], true));
    _Solver->addClause(lits);
  }
}

void V3SvrPDRSat::dfs(V3NetVec& orderedNets) {
  orderedNets.clear();
  orderedNets.reserve(_ntk->getNetSize());
  _ntk->newMiscData();
  for (unsigned i = 0, n = _ntk->getLatchSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getLatch(i);
    V3NetId tmp = _ntk->getInputNetId(nId, 0);
    _ntk->dfsOrder(tmp,orderedNets);
    _ntk->dfsOrder(nId,orderedNets);
  }
  for (unsigned i = 0, n = _ntk->getOutputSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getOutput(i);
    _ntk->dfsOrder(nId,orderedNets);
  }
}

void V3SvrPDRSat::dfs(V3NetVec& orderedNets, Cube* s) {
  orderedNets.clear();
	orderedNets.reserve(_ntk -> getNetSize());
  _ntk->newMiscData();
	// dfs from all next states
	// No !!! dfs from all non-DC next states
	//if( b ) {
		// no need to traverse all _latchValues, but only _states
		// TODO
		//assert(statesEQ(s));
		const vector<V3NetId>& states = s -> getStates();
		for( unsigned i = 0; i < states.size(); ++i ) {
    		const V3NetId& nId = _ntk -> getInputNetId(states[i], 0);
			_ntk -> dfsOrder(nId, orderedNets);
		}
/*
  		for (unsigned i = 0, n = _L; i < n; ++i) {
			//if( 'X' == s -> _latchValues[i].ternaryValue() ) continue;
			if( s -> _latchValues[i]._dontCare ) continue;
    		//const V3NetId& nId = _ntk -> getInputNetId(tmp, 0);
    		_ntk->dfsOrder(_ntk -> getInputNetId(_ntk -> getLatch(i), 0),orderedNets);
  		}
*/
	//}
	// dfs from monitor
/*
	else {
		_ntk -> dfsOrder(_monitor, orderedNets);
  }
*/
}

void V3SvrPDRSat::v3SimOneGate(V3NetId id) {
  const V3GateType type = _ntk->getGateType(id);
  if (type == AIG_NODE) {
/*
	const V3NetId& in1 = _ntk -> getInputNetId(id, 0);
	const V3NetId& in2 = _ntk -> getInputNetId(id, 1);
	_Value3List[id.id].ternaryAnd(_Value3List[in1.id], in1.cp, _Value3List[in2.id], in2.cp);
*/
    Value3 in1 = _Value3List[(_ntk->getInputNetId(id, 0)).id];
    Value3 in2 = _Value3List[(_ntk->getInputNetId(id, 1)).id];
    if ((_ntk->getInputNetId(id, 0)).cp) in1 = ~in1;
    if ((_ntk->getInputNetId(id, 1)).cp) in2 = ~in2;
    _Value3List[id.id] = in1 & in2;
  }
}

Cube* V3SvrPDRSat::ternarySimulation(Cube* c, bool b, bool* input, Cube* s) {
    //TODO: SAT generalization
		// Note: s = NULL if b = 0
		assert(c -> _L == _L);
		V3NetId nId;
		// assign value from the SAT assignment
		for( unsigned i = 0; i < _L; ++i ) {
			nId = _ntk -> getLatch(i);
			assert(!nId.cp);
			//_Value3List[nId.id] = c -> _latchValues[i];
			_Value3List[nId.id]._bit = c -> _latchValues[i]._bit;
			_Value3List[nId.id]._dontCare = 0;
		}
		for( unsigned i = 0; i < _I; ++i ) {
			nId = _ntk -> getInput(i);
			assert(!nId.cp);
			//if( input[i] ) _Value3List[nId.id].set1();
			//else _Value3List[nId.id].set0();
			_Value3List[nId.id]._bit = input[i];
			_Value3List[nId.id]._dontCare = 0;
		}
		for( unsigned i = 0; i < _ntk -> getConstSize(); ++i ) {
			nId = _ntk -> getConst(i);
			//_Value3List[nId.id].set0();
			_Value3List[nId.id]._bit = 0;
			_Value3List[nId.id]._dontCare = 0;
		}

		// get the COI
		V3NetVec orderedNets;
		if( b ) dfs(orderedNets, s);
		else orderedNets = getDFSMonitor();
		//dfs(orderedNets, b, s);
	
		vector<V3NetId> tmpStates;
		tmpStates.clear();
		// generalization
		for( unsigned i = 0; i < _L; ++i ) {
			nId = _ntk -> getLatch(i);
			assert(!nId.cp);
			assert(c -> _latchValues[i] == _Value3List[nId.id]);
			// set state to 'X'
			//_Value3List[nId.id].setX();
			_Value3List[nId.id]._dontCare = 1;
			
			// maybe you can try to get fanout cone first !?
			for( unsigned j = 0; j < orderedNets.size(); ++j ) 			// many sim values remain unchanged
				v3SimOneGate(orderedNets[j]);				

			if( Value3Changed(b, s) ) {
				// undo the 'X' assignment
				//_Value3List[nId.id] = c -> _latchValues[i];
				_Value3List[nId.id]._dontCare = 0;

				// push back the NetId to tmpStates
				//cp indicates the condition of the state variables (i.e. cp(a) = 1 -> a = 1)
				tmpStates.push_back(V3NetId::makeNetId(nId.id, (c -> _latchValues[i]._bit == 1)));
			}
			//else c -> _latchValues[i].setX();
			else c -> _latchValues[i]._dontCare = 1;
		}
		c -> setStates(tmpStates);

    return c;
}

bool V3SvrPDRSat::Value3ChangedDuringSim(bool b, Cube* s, const vector<V3NetId>& orderedNets)
{
/*
	std::cout << "start checking..." << std::endl;
	if( b ) {
		s -> showStates();
		unsigned idx = 0;
		vector<V3NetId> states = s -> getStates();
		V3NetId nId = _ntk -> getInputNetId(states[idx], 0);
		for( unsigned i = 0; i < orderedNets.size(); ++i ) {
			std::cout << "looking for: " << nId.id << std::endl;
			std::cout << "now: " << orderedNets[i].id << std::endl;
			v3SimOneGate(orderedNets[i]);
			// if simulate to latch input, check value
			if( orderedNets[i].id == nId.id ) {
				if( _Value3List[nId.id]._dontCare ) return true;
				++idx;
				std::cout << "idx: " << idx << ", size: " << states.size() << std::endl;
				if( idx == states.size() ) return false;
				nId = _ntk -> getInputNetId(states[idx], 0);
			}
		}
	}
	else {
		for( unsigned i = 0; i < orderedNets.size(); ++i ) v3SimOneGate(orderedNets[i]);
		return _Value3List[_monitor.id]._dontCare;
		//if( _Value3List[_monitor.id]._dontCare ) return true;
		//else return false;
	}
	assert(0);
	return false;
*/
}

bool V3SvrPDRSat::Value3Changed(bool b, Cube* s)
{
	// solveRelative, look at next state
	if(b) {
		// no need to traverse all _L, but only for states
		// TODO
		V3NetId nId;
		const vector<V3NetId>& states = s -> getStates();
		for( unsigned i = 0; i < states.size(); ++i ) {
			nId = _ntk -> getInputNetId(states[i], 0);
			if( _Value3List[nId.id]._dontCare == 1 ) return true;
		}
/*
		for( unsigned i = 0; i < _L; ++i ) {
			//if( 'X' == s -> _latchValues[i].ternaryValue() ) continue;
			if( s -> _latchValues[i]._dontCare ) continue;
			V3NetId nId = _ntk -> getInputNetId(_ntk -> getLatch(i), 0);
			//if( 'X' == _Value3List[nId.id].ternaryValue() ) return true;
			if( _Value3List[nId.id]._dontCare ) return true;
		}
*/
	}
	// getBadCube, look at PO(just monitor)
	else {
		// we should get a specific value to compare with the SAT assignment
		//if( 'X' == _Value3List[_monitor.id].ternaryValue() ) return true;
		if( _Value3List[_monitor.id]._dontCare == 1 ) return true;
	}
	return false;
}

void V3SvrPDRSat::getSATAssignmentToCube(Cube* cube) {
  // get SAT assignment from sovler if the cube is reachable from previous frame
  for (unsigned i = 0; i < _L; ++i) {
    Var tv = getVerifyData(_ntk->getLatch(i), 0);
/*	
		if( tv ) {
			if( getValue(tv) ) cube -> _latchValues[i].set1();
			else cube -> _latchValues[i].set0();
		}
*/
    if (tv)
      cube->_latchValues[i]._bit = getValue(tv);
    cube->_latchValues[i]._dontCare = 0;

  }
}

bool* V3SvrPDRSat::ternarySimInit(Cube* c) {
  // for latch
  getSATAssignmentToCube(c);
  //for inputs
  bool* ii = new bool[_I];
  for (unsigned i = 0; i < _I; ++i) {
    Var tv = getVerifyData(_ntk->getInput(i), 0);
    if (tv)
      ii[i] = getValue(tv);
  }
  return ii;
}

Cube* V3SvrPDRSat::getBadCube(unsigned depth) {
  // 0 -> init
  // SAT ? [R_k and !P]
  assumeRelease();
  assumeProperty(_monitor, false, 0);
  if (debug) cerr << "Get bad cube, _actVars.size() : " << _actVars.size() <<" depth : "<< depth << endl;
  if (debug) cerr << "added actVars from " << depth << " to " << _actVars.size() - 1 << endl;
  // add R_k
  for (unsigned i = depth; i < _actVars.size(); ++i) {
    _assump.push(Lit(_actVars[i]));
  }
  
  if (debug) {
    cerr << "_assump : ";
    for (int i = 0; i < _assump.size(); ++i) {
      cerr << _assump[i].x << " ";
    }
    cerr << endl;
  }

  Cube* c = new Cube();
  if (assump_solve()) {
    if (debug) cerr << "result : SAT" << endl;
    bool* ii = ternarySimInit(c);				// ii is the input assignment, c is the latch output assignment
    if (debug) {
      cerr << "cube before 3-sim : " << endl;
      c->show();
    }
    //TODO: uncomment the following line to evoke SAT generalization
    c = ternarySimulation(c, 0, ii, NULL);
    if (debug) {
      cerr << "cube after 3-sim : " << endl;
      c->show();
    }
	// modified by r04943179
	//_Cex.push_back(ii);
	_Cex.insert({c, {NULL, ii}});
    //delete[] ii;
	// end of modification
    return c;
  } else {
    if (debug) cerr << "result : UNSAT" << endl;
    delete [] c->_latchValues;
    c->_latchValues = NULL;
    return c;
  }
}

void V3SvrPDRSat::newActVar() {
    Var v = newVar(1);
    _actVars.push_back(v);
}

void V3SvrPDRSat::initValue3Data() {
   _Value3List.clear();
   for (unsigned i = 0; i < _ntk->getNetSize(); ++i) {
      _Value3List.push_back(Value3(0, 1));			// all values are don't-cares !!
   }
}

int V3SvrPDRSat::getValue(Var v) const {
  if (_Solver->model[v]==l_True) return 1;
  if (_Solver->model[v]==l_False) return 0;
  assert(0);
  return -1;
}

bool V3SvrPDRSat::isBlocked(TCube c) {
  // Currently do not use SAT solver to check, always return false
  // To enable SAT checking, uncomment following 3 lines
  /*
  TCube t = solveRelative(c, c._frame);
  if (t._frame == -1) return false;
  else return true;
  */
  return false;
}

bool V3SvrPDRSat::isInitial(Cube* c) {
  // check if a cube subsumes R0
  for (unsigned i = 0; i < _L; ++i) {
	 //if ( c->_latchValues[i]._data1 ) return false;
	 //if ( '1' == c->_latchValues[i].ternaryValue() ) return false;
    if (c->_latchValues[i]._bit == 1 && c->_latchValues[i]._dontCare == 0)
      return false;
  }
  return true;
}

void V3SvrPDRSat::blockCubeInSolver(TCube s) {
  if (debug) {
    cerr<<"blocked cube in solver in frame : " << s._frame << " cube is : ";
    s._cube->show();
  }
  assert(s._frame != 0);
  vec<Lit> lits;
  Lit l;
	// no need to traverse all _L
	// TODO

	const vector<V3NetId>& states = s._cube -> getStates();
	for( unsigned i = 0; i < states.size(); ++i ) {
		l = states[i].cp ? mkLit(getVerifyData(states[i], 0), true) : mkLit(getVerifyData(states[i], 0), false);
		lits.push(l);
	}

/*
	//std::cout << "_latchValues: " << std::endl;
	//assert(statesEQ(s._cube));
  for (unsigned i = 0; i < _L; ++i) {
    //if ( 'X' == s._cube->_latchValues[i].ternaryValue() ) continue;
    if ((s._cube->_latchValues[i]._dontCare)) continue;
		//std::cout << _ntk -> getLatch(i).id << ", cp: " << s._cube -> _latchValues[i]._bit << std::endl;
      //l = s._cube->_latchValues[i]._data1 ?
      l = s._cube->_latchValues[i]._bit ?
        mkLit(getVerifyData(_ntk->getLatch(i), 0), true) :
        mkLit(getVerifyData(_ntk->getLatch(i), 0), false);
      lits.push(l);
  }
*/
  if (s._frame != INT_MAX) {
    assert((unsigned)s._frame < _actVars.size());
    lits.push(mkLit(_actVars[s._frame], true));
  }
  if (debug) {
    for (int i = 0; i < lits.size(); ++i) cout << lits[i].x << " + ";
    cout << endl;
  }
  _Solver->addClause(lits);
}

Var V3SvrPDRSat::addNotSToSolver(Cube* c) {
  // !s
  Var tmpActVar = newVar(1);
  vec<Lit> lits;
  Lit l;
	// no need to traverse all _L
	// TODO

	vector<V3NetId> states = c -> getStates();
	for( unsigned i = 0; i < states.size(); ++i ) {
		l = states[i].cp ? mkLit(getVerifyData(states[i], 0), true) : mkLit(getVerifyData(states[i], 0), false);
		lits.push(l);
	}
/*
	//std::cout << "_latchValues: " << std::endl;
  for (unsigned i = 0; i < _L; ++i) {
    //if ( 'X' == c->_latchValues[i].ternaryValue() ) continue;
    if ((c->_latchValues[i]._dontCare)) continue;
		//std::cout << _ntk -> getLatch(i).id << "[" << c -> _latchValues[i]._bit << "]" << std::endl;
		//std::cout << "var: " << getVerifyData(_ntk -> getLatch(i), 0) << std::endl;
      //l = c->_latchValues[i]._data1 ?
      l = c->_latchValues[i]._bit ?
        mkLit(getVerifyData(_ntk->getLatch(i), 0), true) : 
        mkLit(getVerifyData(_ntk->getLatch(i), 0), false);
      lits.push(l);
  }
*/
  lits.push(mkLit(tmpActVar, true));
  _Solver->addClause(lits);
  if (debug) {
    cout << "!s : ";
    for (int i = 0; i < lits.size(); ++i) {
       cout << lits[i].x << " ";
    }
    cout  << endl;
  }
  _assump.push(mkLit(tmpActVar, false)); // actVar of !s
  return tmpActVar;
}

void V3SvrPDRSat::addNextStateSToSolver(Cube* c, vector<Lit>& Lit_vec_origin) {
/*
	cerr << "Var of s" << endl;
	for( unsigned i = 0; i < _L; ++i ) {
		if( c -> _latchValues[i]._dontCare == 1 ) cerr << "x ";
		else cerr << c -> _latchValues[i]._bit << " ";
	}
	cerr << endl;
*/
  if (debug) cerr << "Var of s'" << endl;
  for (unsigned i = 0; i < _L; ++i) { // s'
    V3NetId id = _ntk->getInputNetId(_ntk->getLatch(i), 0); // get input of Latch(i)
    Var tmp = getVerifyData(id, 0); // get Var of it
    assert(tmp); // make sure it's valid
    //if ( 'X' != c->_latchValues[i].ternaryValue() ) {
    if (c->_latchValues[i]._dontCare == 0) {
		//bool p = (c -> _latchValues[i]._data0 ? id.cp : !id.cp);		// if value is 0, then p = id.cp, else p = ~id.cp
      bool p = (c->_latchValues[i]._bit ^ id.cp );
      _assump.push(p ? mkLit(tmp, false) : mkLit(tmp, true));
      Lit_vec_origin.push_back(p ? mkLit(tmp, false) : mkLit(tmp, true));
    }
    else Lit_vec_origin.push_back(Lit(0)); // use Lit(0) to represent NULL
  }

  if (debug) {
    cout << "Lit_vec_origin : ";
    for (unsigned i = 0; i < _L; ++i) {
      cout << Lit_vec_origin[i].x << "(" << sign(Lit_vec_origin[i]) << ") ";
    }
    cout << endl;
  }
}

Cube* V3SvrPDRSat::UNSATGeneralizationWithUNSATCore(Cube* c, vector<Lit>& Lit_vec_origin) {
  vector<Lit> Lit_vec_new;
  Lit_vec_new.resize(_L);
  for (unsigned i = 0; i < _L; ++i) {
    Lit_vec_new[i] = Lit(0);
  }
  if (debug) {
    cerr <<  "conflict core : ";
    for (int j = 0; j < _Solver -> conflict.size(); ++j) {
      cerr << (_Solver -> conflict[j]).x << " ";
    }
    cerr  << endl;
  }
  // find which lit is in unsat core and generalize the cube
  for (unsigned i = 0; i < Lit_vec_origin.size(); ++i) {
		// change from inner loop to outer loop
      if (Lit_vec_origin[i] != Lit(0)) {
    for (int j = 0; j < _Solver -> conflict.size(); ++j) {
        if (~(Lit_vec_origin[i]) == _Solver -> conflict[j]) {
          Lit_vec_new[i] = Lit_vec_origin[i];
          break;
        } else if (Lit_vec_origin[i] == _Solver -> conflict[j]) {
          Lit_vec_new[i] = Lit_vec_origin[i];
          break;
        }
      }
    }
  }

	unsigned idx = 0;
  Cube* tmpCube = new Cube(c);
  for (unsigned i = 0; i < _L; ++i) {
		assert(tmpCube -> _latchValues[i] == c -> _latchValues[i]);
    	if (Lit_vec_new[i] == Lit(0)) {
      	//tmpCube->_latchValues[i].setX();
      	tmpCube->_latchValues[i]._dontCare = 1;
			// modified by r04943179
			//if( c -> _latchValues[i]._data1 ) idx = i;
			if( c -> _latchValues[i]._bit == 1 ) idx = i;
			// end of modification
		}
  }
  // record the last 1's when changing _dontCare to 1
  // check at last , not in for loop , TODO

  // if tmpCube intersect with initial, use original c
	// change the last "1"'s _dontCare back to 0
  if (isInitial(tmpCube)) {
    assert(c->_latchValues);
	//tmpCube -> _latchValues[idx] = c -> _latchValues[idx];
	tmpCube -> _latchValues[idx]._dontCare = 0;
  }
	// update states
	// There must be a better way
	// TODO
	tmpCube -> setUpStates(_ntk);
/*
	vector<V3NetId> states = tmpCube -> getStates();
	states.clear();
	for( unsigned i = 0; i < _L; ++i ) {
		if( tmpCube -> _latchValues[i]._dontCare ) continue;
		states.push_back(V3NetId::makeNetId(_ntk -> getLatch(i).id, (tmpCube -> _latchValues[i]._bit == 1)));
	}
	tmpCube -> setStates(states);
*/
  return tmpCube;
}
void V3SvrPDRSat::assertCubeUNSAT(Cube*c, uint d) {
  // This is just a debug function
  assert(d);
  assumeRelease();
  vector<Lit> Lit_vec_origin;
  addNextStateSToSolver(c, Lit_vec_origin);
  Var tmpActVar = addNotSToSolver(c);
  int k = d - 1;
  unsigned idx = k;
  if (idx < _actVars.size()) {
    for ( ; idx < _actVars.size(); ++idx) { // actVars, here is to represent R_k
      _assump.push(Lit(_actVars[idx]));
    }
  }
  if (assump_solve()) {
    _Solver->addUnit(mkLit(tmpActVar, true));
    assert(0);
  } else {
    _Solver->addUnit(mkLit(tmpActVar, true));
    return;
  }
}

TCube V3SvrPDRSat::solveRelative(TCube s, size_t param) {
  // important preliminary
  // class Var == int
  // class Lit.x == (2*var) + (int)sign

  // param = 0 : if the query satisfiable, just return (CUBE NULL, FRAME NULL).
  // param = 1 : "EXTRACTMODEL", SAT ? [ Rk-1 and !s and T and s' ]
  // param = 2 : "NOIND"       , SAT ? [ Rk-1 and T and s' ]
  if (debug) {
    cerr << "Solve Relative in frame : "<< s._frame << " param : " << param;
    cerr << ", cube is : ";
    s._cube->show();
  }
  assert(s._frame != 0);
	//assert(statesEQ(s._cube));

  assumeRelease();
  vector<Lit> Lit_vec_origin;
  addNextStateSToSolver(s._cube, Lit_vec_origin);  // s' , s._cube can be useful in ternarySimulation !!

  Var tmpActVar = 0;
  if (param == 1) {
    tmpActVar = addNotSToSolver(s._cube);  // !s
	}

  // R_k
  int k = s._frame - 1;
  if (debug) cerr << "added actVars from " << k << " to " << _actVars.size()-1 << endl;

  unsigned idx = k;
  if (idx < _actVars.size()) {
    for ( ; idx < _actVars.size(); ++idx) { // actVars, here is to represent R_k
      _assump.push(Lit(_actVars[idx]));
    }
  }

  if (debug) {
    cerr << "_assump : ";
    for (int i = 0; i < _assump.size(); ++i) {
      cerr << _assump[i].x << " ";
    }
    cerr << endl;
  }

  // SAT solve here
  if (assump_solve()) { //SAT
    if (debug) cerr << "result: SAT" << endl;
    if (param == 1) _Solver->addUnit(mkLit(tmpActVar, true)); // unvalid this tmp actVar forever
    if (param == 0) { // param == 0, return Cube_NULL,Frame_NULL
      return TCube();
    } else {
      Cube* tmpCube = new Cube();
      bool* ii = ternarySimInit(tmpCube);
      if (debug) {
        cerr << "cube before 3-sim:" << endl;
        tmpCube->show();
      }
      //TODO: uncomment the following line to evoke SAT generalization
      tmpCube = ternarySimulation(tmpCube,1,ii, s._cube);
      if (debug) {
        cerr << "returned cube after 3-sim:";
        tmpCube->show();
      }
      delete [] ii;
      TCube r(tmpCube, -1);
      return r;
    }
  } else { //UNSAT
    if (param == 1) _Solver->addUnit(mkLit(tmpActVar, true)); // make this tmp actVar invalid forever
    Cube* tmpCube = UNSATGeneralizationWithUNSATCore(s._cube,Lit_vec_origin);
    // find the lowest act used
    for (unsigned i = k; i < _actVars.size(); ++i) {
      for (int j = 0; j < _Solver -> conflict.size(); ++j) {
        if (~Lit(_actVars[i]) == _Solver->conflict[j]) {
          if (debug) {
            cerr << "result: UNSAT" << endl;
            cerr << "return:";
            tmpCube->show();
            cerr << "in frame:"<< i+1 << endl;
          }
          TCube r(tmpCube, i+1);
          // assertCubeUNSAT(tmpCube,i+1);
          return r;
        }
      }
    }
    // UNSAT core has no actvars, mean it's will always UNSAT in any Frame (so put in Frame_INF)
    if (debug) {
      cerr << "result: UNSAT" << endl;
      cerr << "return:";
      tmpCube->show();
      cerr << "in frame: INT_MAX"<< endl;
    }
    TCube r(tmpCube, INT_MAX);
    // assertCubeUNSAT(tmpCube,INT_MAX);
    return r;
  }
}

bool V3SvrPDRSat::statesEQ(Cube* c) 
{
	for( unsigned i = 0; i < _L; ++i ) {
		if( c -> _latchValues[i]._dontCare == 1 ) continue;
		bool found = false;
		const vector<V3NetId>& states = c -> getStates();
		for(unsigned j = 0; j < states.size(); ++j ) {
			if( states[j].id == _ntk -> getLatch(i).id && states[j].cp == c -> _latchValues[i]._bit ) { found = true; break; }
		}
		if( !found ) return false;
	}
	return true;
}


void V3SvrPDRSat::getCex(Cube* s, Cube* z) {
	bool* inputs = new bool[_I];
	for( unsigned i = 0; i < _I; ++i ) {
		Var tv = getVerifyData(_ntk->getInput(i), 0);
		assert(tv);
      inputs[i] = getValue(tv);
	}
	//_Cex.push_back(inputs);
	_Cex.insert({z, {s, inputs}});
}

void V3SvrPDRSat::freeCex() {
/*
	for( unsigned i = 0; i < _Cex.size(); ++i ) {
		delete[] _Cex[i];
	}
	_Cex.clear();
*/
	unordered_map<Cube*, Cube_inputs>::iterator it;
	for( it = _Cex.begin(); it!= _Cex.end(); ++it ) {
			delete[] ((*it).second).second;
	}
	_Cex.clear();
}

void V3SvrPDRSat::reportCex(Cube* s) {
/*
	unsigned size = _Cex.size();
	for( unsigned i = 0; i < size; ++i ) {
		unsigned idx = size - i - 1;
		std::cout << "[" << i << "]: ";
		for( unsigned j = _I - 1; j != 0; --j ) {
		//for( unsigned j = 0; j < _I; ++j ) {
			std::cout << _Cex[idx][j];
		}
		std::cout << _Cex[idx][0];
		std::cout << std::endl;
	}
*/
	unsigned count = 0;
	unordered_map<Cube*, Cube_inputs>::iterator it;
	Cube* idx = s;
	while( 1 ) {
		it = _Cex.find(idx);
		if( it == _Cex.end() ) break;
		bool* inputs = ((*it).second).second;
		std::cout << count << ": ";
		for( unsigned i = _I - 1; i != 0; --i ) std::cout << inputs[i];
		std::cout << inputs[0];
		std::cout << std::endl;
		++count;
		idx = ((*it).second).first;
	}
}

#endif
