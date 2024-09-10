#include "DMC.hpp"
#include "basic.hpp"

bool DMC::check() {
    initialize();
    
    while(true) {
        if(check_one_step()) {
            return false;
        }

        expand_I();
        expand_B();
    }

    return true;
}

bool DMC::check_one_step() {
    SATSolver *sat0 = new CaDiCaL();
    encode_init_condition(sat0);
    encode_bad_state(sat0);
    sat0->assume(bad);
    int res = sat0->solve();
    if(res == SAT) {
        find_cex = true;
        delete sat0;
        return false;
    }
    delete sat0;
    // push F0
    new_frame();
    encode_init_condition(frames[0].solver);
    return true;
}

void DMC::aig2Dimacs(){
    variables.clear();
    ands.clear();
    nexts.clear();
    init_state.clear();
    constraints.clear();
    constraints_prime.clear();
    map_to_prime.clear();
    map_to_unprime.clear();

    variables.push_back(Variable(0, string("NULL")));
    variables.push_back(Variable(1, string("False")));
    
    // load inputs
    nInputs = aiger->num_inputs;
    for(int i=1; i<=nInputs; ++i){
        assert((i)*2 == aiger->inputs[i-1]);
        variables.push_back(Variable(1 + i, 'i', i-1, false));
    }

    // load latches
    nLatches = aiger->num_latches;
    for(int i=1; i<=nLatches; ++i){
        assert((nInputs+i)*2 == aiger->latches[i-1].l);
        variables.push_back(Variable(1 + nInputs + i, 'l', i-1, false));
    }
    
    // load ands
    nAnds = aiger->num_ands;
    for(int i=1; i<=nAnds; ++i){
        assert(2*(nInputs+nLatches+i) == aiger->ands[i-1].o);
        int o = 1+nInputs+nLatches+i;
        int i1 = aiger_to_dimacs(aiger->ands[i-1].i1);
        int i2 = aiger_to_dimacs(aiger->ands[i-1].i2);
        variables.push_back(Variable(o, 'a', i-1, false));
        ands.push_back(And(o, i1, i2));
    }

    // deal with initial states
    for(int i=1; i<=nLatches; ++i){
        int l = 1 + nInputs + i;
        assert((l-1)*2 == aiger->latches[i-1].l);
        Aiger_latches & al = aiger->latches[i-1];
        nexts.push_back(aiger_to_dimacs(al.next));
        if(al.default_val==0){
            init_state.push_back(-l);
        }else if(al.default_val==1){
            init_state.push_back(l);
        }
    }

    // deal with constraints
    for(int i=0; i<aiger->num_constraints; ++i){
        int cst = aiger->constraints[i];
        constraints.push_back(aiger_to_dimacs(cst));
    }

    // load bad states
    if(aiger->num_bads > 0 && aiger->num_bads > property_index){
        int b = aiger->bads[property_index];
        bad = aiger_to_dimacs(b);
    }else if(aiger->num_outputs > 0 && aiger->num_outputs > property_index){
        int output = aiger->outputs[property_index];
        bad = aiger_to_dimacs(output);
    }else{
        assert(false);
    }
    assert(abs(bad) <= variables.size());

    // load inputs prime
    primed_first_dimacs = variables.size();
    assert(primed_first_dimacs == 1 + nInputs + nLatches + nAnds + 1);
    for(int i=0; i<nInputs; ++i){
        variables.push_back(
            Variable(primed_first_dimacs + i, 'i', i, true));
    }

    // load latches prime
    for(int i=0; i<nLatches; ++i){
        variables.push_back(
            Variable(primed_first_dimacs + nInputs + i, 'l', i, true));
    }
    
    // load bad prime
    bad_prime = prime_lit(bad);

    // load constraint prime
    for(int i=0; i<constraints.size(); ++i){
        int pl = prime_lit(constraints[i]);
        constraints_prime.push_back(pl);
    }
    
    // show_aag();

}

int DMC::prime_var(int var){
    assert(var >= 1);
    if(var > 1){
        if(var <= 1 + nInputs + nLatches){
            return primed_first_dimacs + var - 2; 
        }else{
            if(map_to_prime.find(var) == map_to_prime.end()){
                int unprimed_var = var;
                int primed_var = variables.size();
                map_to_prime[unprimed_var] = primed_var;
                map_to_unprime[primed_var] = unprimed_var;
                string new_name = variables[unprimed_var].name + string("'");
                variables.push_back(Variable(primed_var, new_name));
                return primed_var;
            }else{
                return map_to_prime[var];
            }
        }
    }else{
        // use const True/False
        return var;
    }
}

int DMC::prime_lit(int lit){
    if(lit >= 0){
        return prime_var(lit);
    }else{
        return -prime_var(-lit);
    }
}

void DMC::initialize(){
    aig2Dimacs();
}
