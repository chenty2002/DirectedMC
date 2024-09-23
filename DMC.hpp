#include <iostream>
#include <string>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include "assert.h"
#include "aig.hpp"
#include "sat_solver.hpp"
using namespace std;


unsigned long long state_count = 0;

class State{
public:
    vector<int> latches, inputs;
    State * next = nullptr;
    unsigned long long index;
    int failed;
    int failed_depth;
    State(){
        state_count++;
        index =  state_count;
        failed = 0;
        failed_depth = 0;
    }
    State(vector<int> l, vector<int> i):latches(l),inputs(i){
        state_count++;
        index =  state_count;
        failed = 0;
        failed_depth = 0;
    }
    void clear(){latches.clear(); inputs.clear(); next = nullptr;}
};

class Variable{ 
public:
    int dimacs_var; // the index in variables set;
    string name;    // the name of this variable
    Variable(int dimacs_index, string name){
        this->dimacs_var = dimacs_index;
        this->name = name;
    }
    Variable(int dimacs_index, char type, int type_index, bool prime){
        this->dimacs_var = dimacs_index;
        assert(type=='i' || type=='o' || type=='l' || type == 'a');
        stringstream ss;
        ss << type;
        ss << type_index;
        if(prime)
            ss << "'";
        ss >> name;
    }
};


class And{
public:
    int o, i1, i2;
    And(int o, int i1, int i2):o(o),i1(i1),i2(i2){}
};


class DMC {
    Aiger *aiger;
    
    // the interal data structure for Aiger (in CNF dimacs format).
    int nInputs, nLatches, nAnds;
    vector<Variable> variables;
    vector<And> ands;
    vector<int> nexts;
    vector<int> constraints, constraints_prime;
    vector<int> state_I; 
    set<int> set_state_I;
    int bad, bad_prime;
    const int unprimed_first_dimacs = 2;
    int primed_first_dimacs;
    int property_index;
    bool use_acc, use_pc;
    map<int, int> map_to_prime, map_to_unprime;

    minisatSimp *satelite = nullptr;
public:

    bool find_cex = false;
    vector<State *> states, cex_states;

    SATSolver *state_B_solver = nullptr;
    SATSolver *state_I_solver = nullptr;

    int nQuery;

    bool check();
    void aig2Dimacs();
    void initialize();

    void encode_state_I(SATSolver *s);   // I
    void encode_state_B(SATSolver *s);        // Bad cone, used for test SAT?[I/\-B]
    void encode_transition(SATSolver *s);

    void extract_state_from_sat(SATSolver *sat, State *s, State *succ);

    bool check_one_step();

    bool get_pre_B(State *s);
    bool get_suc_I(State *s);

    void expand_I();
    void expand_B();

    int prime_var(int var);
    int prime_lit(int lit);
};