/****************************************************************************
  FileName     [ PDRDef.h ]
  PackageName  [ pdr ]
  Synopsis     [ Define pdr basic classes ]
  Author       [ ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/

#define show_address 0

#include <iostream>
#include <vector>
#include <bitset>
#include "v3Ntk.h"

#ifndef PDRDEF_H
#define PDRDEF_H

using namespace std;

class Value3 {
  // This is not dual rail encoding,
  // If the _dontCare is one it means it's X,
  // Otherwise it's decided by _bit
 public:
  //Value3() : _data0(0), _data1(0) {}
  Value3() : _bit(0), _dontCare(1) {}
  //Value3(bool d0, bool d1): _data0(d0), _data1(d1) {}
  Value3(bool b, bool d): _bit(b), _dontCare(d) {}
  Value3(const Value3& a) {
	//_data0 = a._data0;
	//_data1 = a._data1;
    _bit = a._bit;
    _dontCare = a._dontCare;
  }
  Value3 operator & (Value3 a) const {
	//std::cout << "&" << std::endl;
	//return Value3(0 ,0);

    if ((_bit == 0 && _dontCare == 0) || a == Value3(0, 0)) return Value3(0, 0);
    else if (a._dontCare || _dontCare) return Value3(0, 1);
    else return Value3(1, 0);

  }
  Value3 operator & (bool a) const {
	std::cout << "&" << std::endl;
	return Value3(0, 0);
/*
    if (a == 0) return Value3(0, 0);
    else if (_dontCare) return Value3(0, 1);
    else return Value3(1, 0);
*/
  }
  Value3 operator | (Value3 a) const {
	std::cout << "|" << std::endl;
	return Value3(0, 0);
/*
    if ((_bit == 1 && _dontCare == 0) || a == Value3(1,0)) return Value3(1, 0);
    else if (a._dontCare || _dontCare) return Value3(0, 1);
    else return Value3(0, 0);
*/
  }
  Value3 operator | (bool a) const {
	std::cout << "|" << std::endl;
	return Value3(0, 0);
/*
    if (a) return Value3(1, 0);
    else if (_dontCare) return Value3(0, 1);
    else return Value3(0, 0);
*/
  }
  Value3 operator ~ () const {
	//std::cout << "~" << std::endl;
	//return Value3(0, 0);
    if (_dontCare) return Value3(0, 1);
    else return Value3(!_bit, 0);
  }
  bool operator == (const Value3& a) const {
	//return ternaryValue() == a.ternaryValue();

    if (_dontCare ^ a._dontCare) return false;
    else if (_dontCare && a._dontCare) return true;
    else if (_bit == a._bit) return true;
    else return false;

  }
  bool operator != (const Value3& a) const {
    return !((*this) == a);
  }
	// modified by r04943179
/*
	void set0() { _data0 = 1; _data1 = 0; }
	void set1() { _data0 = 0; _data1 = 1; }
	void setX() { _data0 = 0; _data1 = 0; }
	bool isX()	{ return (!_data0 && !_data1); }
	void ternaryAnd(const Value3& v1, const bool& inv1, const Value3& v2, const bool& inv2) {
		if( inv1 ) {
			if( inv2 ) { _data0 = v1._data1 | v2._data1; _data1 = v1._data0 & v2._data0; }
			else { _data0 = v1._data1 | v2._data0; _data1 = v1._data0 & v2._data1; }
		}
		else {
			if( inv2 ) { _data0 = v1._data0 | v2._data1; _data1 = v1._data1 & v2._data0; }
			else { _data0 = v1._data0 | v2._data0; _data1 = v1._data1 & v2._data1; }
		}
	}
	const char ternaryValue() const {
		return (_data0 ? '0' : _data1 ? '1' : 'X');
	}
*/
	// end of modification
  //bool _data0;
  //bool _data1;
  bool _bit;
  bool _dontCare;
};

class Cube {
 public:
  Cube(){
    // cube is all zeros for default constructor
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i) {
      _latchValues[i]._bit = 0;
      _latchValues[i]._dontCare = 0;
		//_latchValues[i].set0();
    }
	// modified by r04943179
	_states.clear();
	_signature = 0;
	// end of modification
  }
/*
  Cube(bool* b) {
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i){
      _latchValues[i]._bit = b[i];
    }
  }
  Cube(bool* b, bool* d) {
    _latchValues = new Value3[_L];
    for (unsigned i = 0; i < _L; ++i) {
      _latchValues[i]._bit = b[i];
      _latchValues[i]._dontCare = d[i];
    }
  }
*/
  Cube(Cube* c) {
    if (c->_latchValues) {
      _latchValues = new Value3[_L];
      for (unsigned i = 0; i < _L; ++i) {
        _latchValues[i] = c->_latchValues[i];
      }
    } else {
      _latchValues = NULL;
    }
	// modified by r04943179
	setStates(c -> getStates());
	// end of modification
  }
  Cube(const Cube& c) {
    if (c._latchValues) {
      _latchValues = new Value3[_L];
      for (unsigned i = 0; i < _L; ++i) {
        _latchValues[i] = c._latchValues[i];
      }
    } else {
      _latchValues = NULL;
    }
	// modified by r04943179
	setStates(c.getStates());
	// end of modification
  }
  ~Cube() {
    if (_latchValues) {
      delete [] _latchValues;
    }
    _latchValues = NULL;
  }
	// better approach using sigature-based algorithm
	// TODO
  bool subsumes(Cube* s) const {
	//std::cout << "checking subsumes: " << std::endl;
	//std::cout << "this: " << std::endl;
	//showStates();
	//std::cout << "sig: " << std::bitset<64>(_signature) << std::endl;
	//std::cout << "cube: " << std::endl;
	//s -> showStates();
	//std::cout << "sig: " << std::bitset<64>(s -> getSignature()) << std::endl;


	vector<V3NetId> cubeStates = s -> getStates();
	unsigned cubeSignature = s -> getSignature();
	if( _states.size() > cubeStates.size() ) { return false; }//std::cout << "subsume false 1" << std::endl; return false; }
	if( _signature & ~cubeSignature ) { return false; }//std::cout << "subsume false 2" << std::endl; return false; }
	// check all
/*
	unsigned i = 0, j = 0;
	while( i < _states.size() && j < _states.size() ) {
		assert(!i || _states[i].id > _states[i - 1].id); assert(!j || cubeStates[j].id > cubeStates[j - 1].id);
		if( _states[i].id < cubeStates[j].id ) { return false; }//std::cout << "subsume false 3" << std::endl; return false; }
		else if( _states[i].id > cubeStates[j].id ) ++j;
		else{
			if( _states[i].cp == cubeStates[j].cp ) { ++i; ++j; }
			else { return false; }//std::cout << "subsume false 4" << std::endl; return false; }
		}
	}
	return i == _states.size();
	//if( i == _states.size() ) { std::cout << "subsume true" << std::endl; return true; }
	//else { std::cout << "subsume false 5 " << std::endl; return false; }
*/
/*
	for( unsigned i = 0; i < _L; ++i ) {
		if( 'X' == _latchValues[i].ternaryValue() ) continue;
		if( 'X' == s -> _latchValues[i].ternaryValue() ) return false;
		if( s -> _latchValues[i] != _latchValues[i] ) return false;
	}
	return true;
*/

    for (unsigned i = 0; i < _L; ++i) {
      if (!_latchValues[i]._dontCare) {
        if (s->_latchValues[i]._dontCare) return false;
        if (s->_latchValues[i]._bit != _latchValues[i]._bit) return false;
      }
    }
    return true;

  }
  void show() {
    // debug fuction
    for (unsigned i = _L - 1; i != 0; --i) {
		//std::cout << _latchValues[i].ternaryValue();
      if (_latchValues[i]._dontCare) cout << "X";
      else cout << ((_latchValues[i]._bit) ? "1" : "0");
    }
	//std::cout << _latchValues[0].ternaryValue();
    if (_latchValues[0]._dontCare) cout << "X";
    else cout << ((_latchValues[0]._bit) ? "1" : "0");
    cout << endl;
  }

	// modified by r04943179
	const vector<V3NetId>& getStates() const { return _states; }
	const uint64_t& getSignature() const { return _signature; }
	void setStates(const vector<V3NetId>& v);
	void setUpStates(V3Ntk* ntk);
	void setUpSignature();
	void pushBackStates(const V3NetId& id);
	void showStates() const;
	vector<V3NetId>		_states;
	uint64_t					_signature;
	// end of modification
  static unsigned _L;               // latch size
  Value3*         _latchValues;     // latch values
};

inline void Cube::showStates() const {

	for( unsigned i = 0; i < _states.size(); ++i ) {
		std::cout << _states[i].id << "[" << _states[i].cp << "] ";
	}
	std::cout << std::endl;

}

inline void Cube::setStates(const vector<V3NetId>& v) {

	_states = v; _signature = 0;
	// change the signature according to states
	// TODO
	for( unsigned i = 0; i < _states.size(); ++i ) {
		_signature |= (1ul << (_states[i].id % 64));
	}

}

inline void Cube::setUpStates(V3Ntk* ntk) {
	_states.clear(); _signature = 0;
	for( unsigned i = 0; i < _L; ++i ) {
		if( _latchValues[i]._dontCare ) continue;
		const V3NetId& nId = ntk -> getLatch(i);
		_states.push_back(V3NetId::makeNetId(nId.id, _latchValues[i]._bit == 1));
		// update signature
		_signature |= (1ul << (nId.id % 64));
	}
}

inline void Cube::pushBackStates(const V3NetId& id) {
	_states.push_back(id);
	_signature |= (1ul << (id.id % 64));
}

class TCube
{
 public:
  TCube(): _cube(NULL), _frame(-1) {
    cerr << "NULL constructor" << endl;
  }
  TCube(Cube* c, unsigned d): _cube(c), _frame((int)d) {
    if (show_address) {
      cerr << "default constructor" << endl;
      cerr << c << endl;
    }
  }
  TCube(const TCube& t) {
    if (show_address) {
      cerr << "copy constructor" << endl;
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    _cube = t._cube;
    _frame = t._frame;
  }
  ~TCube(){
    if (show_address) cerr << "destructor" << endl;
  }
  TCube& operator = (const TCube& t){
    if (show_address) {
      cerr << "= constructor" << endl;
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    _cube = t._cube;
    _frame = t._frame;
    return (*this);
  }
  friend bool operator > (const TCube& l, const TCube& r) { return l._frame > r._frame; }

  Cube* _cube;
  int   _frame; // -1 = frame_null, INT_MAX = INF
};

#endif
