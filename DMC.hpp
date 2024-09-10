#include <iostream>
#include <string>
#include <fstream>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include "assert.h"
#include "aig.hpp"
using namespace std;


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
    vector<int> init_state; set<int> set_init_state;
    int bad, bad_prime;
    const int unprimed_first_dimacs = 2;
    int primed_first_dimacs;
    int property_index;
    bool use_acc, use_pc;
    map<int, int> map_to_prime, map_to_unprime;

public:
    bool check();
    void aig2Dimacs();
    void initialize();

    bool check_one_step();
    void expand_I();
    void expand_B();

    int prime_var(int var);
    int prime_lit(int lit);
};