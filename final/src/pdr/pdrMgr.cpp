/****************************************************************************
  FileName     [ pdrMgr.cpp ]
  PackageName  [ pdr ]
  Synopsis     [ Define PDR main functions ]
  Author       [ SillyDuck ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/
#define showinfo 0

#include <fstream>
#include <iostream>
#include <iomanip>
#include <string>
#include <cstdio>
#include <stdlib.h>
#include <cassert>
#include <climits>
#include <cmath>
#include <unistd.h>
#include <queue>
#include <vector>
#include <algorithm>

#include "v3Msg.h"
#include "v3NtkUtil.h"
#include "v3SvrPDRSat.h"
#include "v3NtkHandler.h" // MODIFICATION FOR SoCV BDD
#include "v3Ntk.h"
#include "PDRDef.h"
#include "reader.h"
#include "pdrMgr.h"

using namespace std;

unsigned Cube::_L = 0;

// Compare class for priority_queue
class TCubeCmp {
 public:
  bool operator() (const TCube lhs, const TCube rhs) const {
    return lhs._frame > rhs._frame;
  }
};

class NetIdCmp {
	public:
	bool operator() (const V3NetId& a, const V3NetId& b) const {
		return a.id < b.id;
	}
};

// Main verification starts here
void PDRMgr::verifyProperty(const string& name, const V3NetId& monitor) {
  _ntk = new V3Ntk();
  *_ntk = *(v3Handler.getCurHandler()->getNtk());
  SatProofRes pRes;

  V3SvrPDRSat* satSolver = new V3SvrPDRSat(_ntk, false, false);

  // monitor is a V3NetId,
  // Please figure out how V3 present a circuit
  // by V3Ntk and V3NetId in src/ntk/V3Ntk.h and V3Type.h
  satSolver->setMonitor(monitor);

  pRes.setMaxDepth(100);
  pRes.setSatSolver(satSolver);
  double runTime = 0;
  double ctime = (double)clock() / CLOCKS_PER_SEC;

  PDR(monitor, pRes);

  runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
  pRes.reportResult(name);
  cerr << "runtime: " << runTime << endl;
  delete satSolver; delete _ntk;
  reset();
}

void PDRMgr::reset() {
  _ntk = NULL;
}

void PDRMgr::buildAllNtkVerifyData(const V3NetId& monitor) {
  // Added all circuit constraint to SAT solver here.

  for (uint32_t i = 0; i < _ntk->getLatchSize(); ++i)
     Z->addBoundedVerifyData(_ntk->getLatch(i), 0);
  for (uint32_t i = 0; i < _ntk->getLatchSize(); ++i)
     Z->addBoundedVerifyData(_ntk->getLatch(i), 1);
  Z->addBoundedVerifyData(monitor, 0);
  Z->initValue3Data();
}

bool PDRMgr::PDR(const V3NetId& monitor, SatProofRes& pRes) {
  // assume no inout
  if (_ntk->getInoutSize()) { assert(0); }
  Z = pRes.getSatSolver();
  L = _ntk->getLatchSize();
  Cube::_L = L;

  F = new vector<vector<Cube*>*>();
  Z->setFrame(F);
  buildAllNtkVerifyData(monitor);
  // this is F_inf
  // which means the cube that will never be reached
  // in any time frame
  // watch out that _frame of cube in this Frame will be INT_MAX
  F->push_back(new vector<Cube*>());

  depth = 0;
  newFrame(); // F[0]

  Z->addInitiateState();
  Z->setMonitor(monitor);

  // PDR Main function
  while (true) {
    // find bad cube, check SAT? (!P & R_k)
    Cube* cube = Z->getBadCube(depth);
	if( cube -> _latchValues != NULL ) {
	//std::cout << "after getBadCube: " << std::endl;
	//cube -> show();
	//cube -> showStates();
	}
    if (debug) {
      if (cube->_latchValues) { 
        cerr<<"bad cube in frame:" << depth << endl;
        cube->show();
      } else {
        cerr << "bad cube is NULL\n";
      }
    }

    if (cube->_latchValues != NULL) {
      TCube t(cube, depth);
      // Counter example found
      if (!recursiveBlockCube(t)) {
        pRes.setFired(0);
        if (showinfo) {
          system("clear");
          cerr << "Number of Cubes:" << endl;
          for (unsigned i = 0; i < F->size() - 1; ++i)
            cerr << "Frame "<< i << " : " << (*F)[i]->size() << endl;
          cerr << "Frame INF :" << (*F)[F->size()-1]->size() << endl;
        }
			// modified by r04943179
			Z -> reportCex();
			// end of modification
        return true;
      }
    } else {
      // depth will only be increased here
      depth++;
      newFrame();
      // Fixed point
      if (propagateBlockedCubes(pRes)) {
        if (showinfo) {
          system("clear");
          cerr << "Number of Cubes:" << endl;
          for (unsigned i = 0; i < F->size() - 1; ++i)
            cerr << "Frame "<< i << " : " << (*F)[i]->size() << endl;
          cerr << "Frame INF :" << (*F)[F->size()-1]->size() << endl;
        }
        return false;
      }
    }
  }
}

bool PDRMgr::recursiveBlockCube(TCube s0){
	//std::cout << "in recursiveBlockCube: " << std::endl;
	//s0._cube -> show();
	//s0._cube -> showStates();
	//assert(Z -> statesEQ(s0._cube));
	//PASS
  if (debug) cerr << "recursiveBlockCube" << endl;
  priority_queue<TCube, vector<TCube>, TCubeCmp> Q;
  Q.push(s0);
  if (debug) {
    cerr << "pushed : " << s0._cube << ", ";
    s0._cube->show();
  }
  while (!Q.empty()) {
    TCube s = Q.top();
    Q.pop();
	//std::cout << "pop from queue: " << std::endl;
	//s._cube -> show();
	//s._cube -> showStates();
    if (debug) {
      cerr << "poped : " << s._cube << ", ";
      s._cube->show();
    }
    // reach R0, counter example found
    if (s._frame == 0) return false;
    // block s
    if (!isBlocked(s)) {
		//std::cout << "before assert !isInitial: " << std::endl;
		//s._cube -> show();
      assert(!(Z->isInitial(s._cube)));
		//std::cout << "in recursiveBlockCube, before solveRelative 183: " << std::endl;
		//s._cube -> show();
		//s._cube -> showStates();
		//assert(Z -> statesEQ(s._cube));
      TCube z = Z->solveRelative(s, 1);
		//if( Z -> statesEQ(s._cube) ) assert(Z -> statesEQ(z._cube));
		//std::cout << "in recursiveBlockCube, after solveRelative 183: " << std::endl;
		//z._cube -> show();
		//z._cube -> showStates();
		//std::cout << "frame: " << z._frame << std::endl;

      if (z._frame != -1) {
        // UNSAT, s is blocked
			//std::cout << "before going into generalize: " << std::endl;
			//z._cube -> show();
			//z._cube -> showStates();
        z = generalize(z);  // UNSAT generalization
		//assert(Z -> statesEQ(z._cube));
		//PASS
			//std::cout << "in recursiveBlockCube, after generalize: " << std::endl;
			//z._cube -> show();
			//z._cube -> showStates();
        if (debug) {
          cerr << "cube after generalized :";
          z._cube->show();
          cerr << " frame : " << z._frame << endl;
        }
        // push to higher frame
        while (z._frame < (int)(depth - 1)) {
          // condAssign
          TCube t = Z->solveRelative(next(z), 1);
			//assert(Z -> statesEQ(t._cube));
			//std::cout << "in recursiveBlockCube, after solveRelative 202: " << std::endl;
			//t._cube -> show();
			//t._cube -> showStates();
          if (t._frame != -1) z = t;
          else break;
        }
        addBlockedCube(z);
        if((s._frame < (int)depth) && (z._frame != INT_MAX)) {
          TCube a = next(s);
          Q.push(a);
          if (debug) {
            cerr << "pushed : " << s._cube << ", ";
            s._cube->show();
          }
        }
      } else {
        // SAT, s is not blocked
        // TODO: to generate counterexample trace for unsafe property,
        //       you need to record the SAT pattern here
			//std::cout << "push z to queue: " << std::endl;
			//z._cube -> show();
			//z._cube -> showStates();
			//std::cout << "push s to queue: " << std::endl;
			//s._cube -> show();
			//s._cube -> showStates();
        z._frame = s._frame - 1;
        Q.push(z);
        if (debug) {
          cerr << "pushed : " << z._cube << ", ";
          z._cube->show();
        }
        Q.push(s); // put it in queue again
        if (debug) {
          cerr << "pushed : " << s._cube << ", ";
          s._cube->show();
        }
			// modified by r04943179
			Z -> getCex();
			// end of modification
      }
    }
  }
	// modified by r04943179
	Z -> freeCex();
	// end of modification
  return true;
}

bool PDRMgr::isBlocked(TCube s) {
  // check if a cube is already blocked in solver
  // first check if it is subsumes by that frame
  // then check by solver (more time-consuming)
	//assert(Z -> statesEQ(s._cube));
	//PASS
  for (unsigned d = s._frame; d < F->size(); ++d) {
    for (unsigned i = 0; i < (*F)[d]->size(); ++i) {
		// better way to check subsume, check V3 Qsignature
      if ((*((*F)[d]))[i]->subsumes(s._cube)) {
        if (debug) {
          cerr << "F->size():" << F->size() << endl;
          cerr << "already blocked in frame:" << d << endl;
          (*((*F)[d]))[i]->show();
        }
        return true;
      }
    }
  }
  return Z->isBlocked(s);
}

TCube PDRMgr::generalize(TCube s) {
	//std::cout << "in generalize: " << std::endl;
	//s._cube -> show();
	//s._cube -> showStates();
  // UNSAT generalization
  if (debug) cerr << "UNSAT generalization" << endl;
	// no need to traverse all _L, but only states
	// TODO
	//assert(Z -> statesEQ(s._cube));

	//vector<V3NetId> states = s._cube -> getStates();
	//for( unsigned i = 0; i < states.size(); ++i ) {
	for( unsigned i = 0; i < L; ++i ) {
		//vector<V3NetId> currStates = s._cube -> getStates();
		//s._cube -> show();
		//s._cube -> showStates();
		//unsigned idx = states[i].id - _ntk -> getLatch(0).id;
		//if( s._cube -> _latchValues[i].isX() ) continue;
		if( s._cube -> _latchValues[i]._dontCare == 1 ) continue;
		//if( s._cube -> _latchValues[idx]._dontCare ) continue;
		
		//std::cout << "checking idx: " << idx << std::endl;

		//Value3 record = s._cube -> _latchValues[i];
		//s._cube -> _latchValues[i].setX();
		s._cube -> _latchValues[i]._dontCare = 1;
		//s._cube -> _latchValues[idx]._dontCare = 1;
		//std::cout << "after assign X at idx: ";
		//s._cube -> show();
		//if( (Z -> isInitial(s._cube)) ) { s._cube -> _latchValues[i] = record; continue; }
		//assert(Z -> valueEQ(s._cube));
		if( (Z -> isInitial(s._cube)) ) { s._cube -> _latchValues[i]._dontCare = 0; continue; }
		//if( (Z -> isInitial(s._cube)) ) { s._cube -> _latchValues[idx]._dontCare = 0; continue; }
/*
		for( unsigned j = 0; j < currStates.size(); ++j ) {
			if( currStates[j].id == states[i].id ) {
				currStates[j] = currStates.back(); currStates.pop_back();
				break;
			}
		}
*/
		//s._cube -> setStates(currStates);
		//std::cout << "going into solveRelative, idx: " << idx << std::endl;
		s._cube -> setUpStates(_ntk);
		TCube t = Z -> solveRelative(TCube(s._cube, s._frame), 1);
		//if( Z -> statesEQ(s._cube) ) assert(Z -> statesEQ(t._cube));
		//PASS
		//assert(Z -> statesEQ(s._cube)); assert(Z -> statesEQ(t._cube));
		//std::cout << "frame of t: " << t._frame << std::endl;
		if( t._frame != -1 ) {
			// if UNSAT, 'X' would be performed on s._cube, no problem !!!
			//std::cout << "good result, keep the X ..." << std::endl;
			//std::cout << "changing from: " << std::endl;
			//s._cube -> show();
			//s._cube -> showStates();
			s = t;
			//std::cout << "to : " << std::endl;
			//s._cube -> show();
			//s._cube -> showStates();
		}
		// recover 
		else {
			//std::cout << "bad result, recover ..." << std::endl;
			//s._cube -> _latchValues[i] = record;
			s._cube -> _latchValues[i]._dontCare = 0;
			//s._cube -> _latchValues[idx]._dontCare = 0;
			//s._cube -> pushBackStates(V3NetId::makeNetId(_ntk -> getLatch(i).id, s._cube -> _latchValues[i]._data1 == 1));
			s._cube -> pushBackStates(V3NetId::makeNetId(_ntk -> getLatch(i).id, s._cube -> _latchValues[i]._bit == 1));
			//assert(Z -> statesEQ(s._cube));
			//currStates.push_back(V3NetId::makeNetId(states[i].id, s._cube -> _latchValues[idx]._bit == 1));
			//s._cube -> setStates(currStates);
			//s._cube -> setStates(oriStates);
			//std::cout << "after recover: " << std::endl;
			//s._cube -> show();
			//s._cube -> showStates();
		}
	}
	//states = s._cube -> getStates();
	//std::sort(states.begin(), states.end(), NetIdCmp());
	//s._cube -> setStates(states);


	//std::cout << "before generalize: " << std::endl;
	//s._cube -> show();
	//s._cube -> showStates();
/*
  for (unsigned i = 0; i < L; ++i) {
    Cube* tc = new Cube(s._cube);
    if (tc->_latchValues[i]._dontCare == 1) continue;
    else tc->_latchValues[i]._dontCare = 1;

    if (!(Z->isInitial(tc))) {
		// the order of states is not important here
*/
// modified by r04943179
/*
		vector<V3NetId> states = tc -> getStates();
		for( unsigned j = 0; j < states.size(); ++j ) {
			if( states[j].id == _ntk -> getLatch(0).id + i ) {
				states[j] = states.back(); states.pop_back();
				break;
			}
		}
		tc -> setStates(states);
		std::cout << "now: " << std::endl;
		tc -> show();
		tc -> showStates();
*/
// end of modification
/*
      TCube t = Z->solveRelative(TCube(tc, s._frame), 1);
		//std::cout << "after solverRelative: " << std::endl;
		//t._cube -> show();
		//t._cube -> showStates();
      if (t._frame != -1) {
			//std::cout << "good result, keep the X ..." << std::endl;
			delete s._cube;
			s = t;
		}
		else { 
			//std::cout << "bad result, recover ..." << std::endl;
			//s._cube -> show();
			//s._cube -> showStates();
			delete tc; delete t._cube;
		}
    }
	 else delete tc;
  }
*/
  return s;
}

bool PDRMgr::propagateBlockedCubes(SatProofRes& pRes) {
  if (debug) cerr << "propagateBlockedCubes" << endl;
  for (unsigned k = 1; k < depth; ++k) {
    for (unsigned i = 0; i < (*F)[k]->size(); ++i) {
      TCube s = Z->solveRelative(TCube((*((*F)[k]))[i], k+1), 2);
      if (s._frame != -1) addBlockedCube(s);
    }
    if ((*F)[k]->size() == 0){
      pRes.setProved(k);
      return true;
    }
  }
  return false;
}

void PDRMgr::newFrame(bool force) {
  if (force || depth >= F->size() - 1) {
    unsigned n = F -> size();
    F->push_back(new vector<Cube*>());
    (*F)[n]->swap(*((*F)[n-1]));
    Z->newActVar();
    assert(Z->_actVars.size() == F->size() - 1); // Frame_inf doesn't need ActVar
    if (debug) {
      cerr << endl;
      cerr << "Newed frame:" << F->size() << endl;
      cerr << "actVar:" << Z->_actVars[Z->_actVars.size() - 1] << endl;
    }
  }
  assert ( depth <= F->size()-2 ) ;
}

void PDRMgr::addBlockedCube(TCube s) {
  assert(s._frame != -1);
	//assert(Z -> statesEQ(s._cube));
  //addBlockedCube (To Frame Structure)
  if (debug) {
    cerr << "addBlockCube in frame : " << s._frame << ", cube is : ";
    s._cube->show();
    cerr << "frame size now is " << F->size() << endl;
  }
  if((unsigned)s._frame == F->size() - 1){
    newFrame(true);
  }
  int l = s._frame;
  int r = F->size()-1;
  unsigned k = (unsigned)(l > r ? r : l);
  for (unsigned d = 1; d <= k; ++d) {
    for (unsigned i = 0; i < (*F)[d]->size(); ) {
      if (s._cube->subsumes((*((*F)[d]))[i])) {
        (*((*F)[d]))[i] = (*F)[d]->back();
        (*F)[d] -> pop_back();
      } else {
        i++;
      }
    }
  }
  (*F)[k]->push_back(s._cube);
	//std::cout << "before blockCubeInSolver: " << std::endl;
	//s._cube -> show();
	//s._cube -> showStates();
  Z->blockCubeInSolver(s);
}

TCube PDRMgr::next(const TCube& s){
  return TCube(s._cube, s._frame + 1);
}
