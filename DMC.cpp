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

void DMC::expand_I() {
    State *s = new State();
    bool flag = get_suc_I(s);

}

void DMC::expand_B() {
    State *s = new State();
    bool flag = get_pre_B(s);

}

// Lifts the pre-state on a given frame
// If SAT?[Fk /\ -succ /\ T /\ succ'] return SAT and extract a pre-state pre \in [Fk /\ -succ]
// Then call SAT?[pre /\ T /\ -succ']
// pre must meet constraints. 
int ext_ct = 0;
void DMC::extract_state_from_sat(SATSolver *sat, State *s, State *succ){
    s->clear();
    if(lift == nullptr){
        lift = new CaDiCaL();
        // lift = new minisatCore();
        encode_transition(lift);
    }

    set<int> successor;
    if(succ != nullptr) for(int l: succ->latches) successor.insert(l);
    
    lift->clear_act();
    vector<int> assumptions, latches, successor_assumption, input_asumption;
    int distance = primed_first_dimacs - (nInputs+nLatches+2);
    // inputs /\ inputs' /\ pre
    for(int i=0; i<nInputs; ++i){
        int ipt = sat->val(unprimed_first_dimacs + i);
        int pipt = sat->val(primed_first_dimacs + i);
        if(ipt != 0){
            s->inputs.push_back(ipt);
            assumptions.push_back(ipt);
        }
        if(pipt > 0){
            pipt = (pipt-distance);
            assumptions.push_back(pipt);
        }
        else if (pipt < 0){
            pipt = -(-pipt-distance);
            assumptions.push_back(pipt);
        }
    }

    //int sz = assumptions.size();

    for(int i=0; i<nLatches; ++i){
        int l = sat->val(unprimed_first_dimacs + nInputs + i);
        if(l!=0){
            latches.push_back(l);
            assumptions.push_back(l);   
        }   
    }

    // encoding -(constraints' /\ pre') <-> -constraints' \/ -pre'
    int act_var = lift->max_var() + 1;
    lift->add(-act_var);
    for(int l : constraints_prime)
        lift->add(-l);

    if(succ == nullptr)
        lift->add(-bad_prime);
    else{
        for(int l: succ->latches)
            lift->add(prime_lit(-l));        
    }
    lift->add(0);

    stable_sort(assumptions.begin(), assumptions.end(), Lit_CMP());

    stable_sort(successor_assumption.begin(), successor_assumption.end(), *heuristic_lit_cmp);
    reverse(successor_assumption.begin(), successor_assumption.end()); 

    lift->assume(act_var);  
    for(int l : assumptions)
        lift->assume(l);
    int res = lift->solve();
    ++nQuery;
    assert(res == UNSAT);

    if(output_stats_for_extract){
        cout << "assumptions ";
        for(int l : assumptions){
            if(abs(l) < primed_first_dimacs)
                cout << variables[abs(l)].name << " "<< heuristic_lit_cmp->counts[abs(l)] << " ";
            else
                cout << variables[abs(l)].name << " "<< heuristic_lit_cmp->counts[abs(l)-distance] << " ";
        }
        cout << endl;

        cout << "lift ";
        for(int l : assumptions){
            if(lift->failed(l))
                cout << variables[abs(l)].name << " ";
        }
        cout << endl;
    }

    int last_index = 0, corelen = 0;
    if(use_acc){
        int core_literal = 0;
        for(int i=0; i<assumptions.size(); i++){
            int l = assumptions[i];
            if(abs(l) >= nInputs+2 and abs(l) <= nInputs+nLatches+1) corelen++;
            if(lift->failed(l)){
                double score = (i-core_literal)/20.0;
                if(score > 1.0) score = 1.05;
                if(abs(l) < primed_first_dimacs)
                    heuristic_lit_cmp->counts[abs(l)] += score; //score
                else 
                    heuristic_lit_cmp->counts[abs(l)-distance] += score;
                core_literal = i;
                last_index = corelen;
            }
        }
    }
    else{
        for(int i=0; i<assumptions.size(); i++){
            int l = assumptions[i];
            if(abs(l) >= nInputs+2 and abs(l) <= nInputs+nLatches+1) 
                corelen++;
            if(lift->failed(l))
                last_index = corelen;
        }           
    }
    nCore++;
    nCorelen += last_index;

    for(int l : latches){
        if(lift->failed(l))
            s->latches.push_back(l);
    }

    s->next = succ;
    lift->set_clear_act();
}


bool DMC::get_pre_B(State *s){
    s->clear();
    state_B_solver->assume(bad_prime);
    int res = state_B_solver->solve();
    ++nQuery;
    
    if(res == SAT){
        extract_state_from_sat(state_B_solver, s, nullptr);
        return true;
    }else{
        return false;
    }
}

bool DMC::check_one_step() {
    SATSolver *sat0 = new CaDiCaL();
    encode_state_I(sat0);
    encode_state_B(sat0);
    sat0->assume(bad);
    int res = sat0->solve();
    if(res == SAT) {
        find_cex = true;
        delete sat0;
        return false;
    }
    delete sat0;
    // push F0
    // new_frame();
    // encode_init_condition(frames[0].solver);
    return true;
}

void DMC::aig2Dimacs(){
    variables.clear();
    ands.clear();
    nexts.clear();
    state_I.clear();
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
            state_I.push_back(-l);
        }else if(al.default_val==1){
            state_I.push_back(l);
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
    state_I_solver = new CaDiCaL();
    state_B_solver = new CaDiCaL();
    nQuery = 0;
}


void DMC::encode_state_I(SATSolver *s){
    s->add(-1); s->add(0); 
    for(int l : state_I){
        s->add(l); s->add(0);
    }

    if(constraints.size() >= 0){
        for(int l : constraints){
            s->add(l); s->add(0);}

        set<int> lit_set;
        for(int l : constraints)
            lit_set.insert(abs(l));

        for(auto i = ands.rbegin(); i != ands.rend(); ++i){
            And & a = *i;
            if(lit_set.find(a.o) == lit_set.end())
                continue;
            lit_set.insert(a.i1);
            lit_set.insert(a.i2);
            
            s->add(-a.o); s->add(a.i1);  s->add(0);
            s->add(-a.o); s->add(a.i2);  s->add(0);
            s->add(a.o);  s->add(-a.i1); s->add(-a.i2); s->add(0);
        }
    }
    if(aig_veb > 2)
        cout<<"c add_cls finish load init"<<endl;
}

void DMC::encode_state_B(SATSolver *s){
    set<int> lit_set;
    lit_set.insert(abs(bad));
    for(auto i = ands.rbegin(); i != ands.rend(); ++i){
        And & a = *i;
        assert(a.o > 0);
        if(lit_set.find(a.o) == lit_set.end())
            continue;
        lit_set.insert(abs(a.i1));
        lit_set.insert(abs(a.i2));
        s->add(-a.o); s->add(a.i1);  s->add(0);
        s->add(-a.o); s->add(a.i2);  s->add(0);
        s->add(a.o);  s->add(-a.i1); s->add(-a.i2); s->add(0);
    }
    if(aig_veb > 2)
        cout<<"c add_cls finish load bad"<<endl;
}

void DMC::encode_transition(SATSolver *s){
    if(satelite == nullptr){
        satelite = new minisatSimp();
        satelite->var_enlarge_to(variables.size()-1);

        for(int i=1; i<= nInputs+nLatches; ++i){
            satelite->set_frozen(1 + i);
            satelite->set_frozen(prime_var(1 + i));
        }
        satelite->set_frozen(abs(bad));
        satelite->set_frozen(abs(bad_prime));
        for(int i=0; i<constraints.size(); ++i){
            satelite->set_frozen(abs(constraints[i]));
            satelite->set_frozen(abs(constraints_prime[i]));
        }
        
        set<int> prime_lit_set;
        prime_lit_set.insert(abs(bad));
        for(int l : constraints)
            prime_lit_set.insert(abs(l));

        set<int> lit_set(prime_lit_set.begin(), prime_lit_set.end());
        for(int l : nexts)
            lit_set.insert(abs(l));
        

        satelite->add(-1); satelite->add(0);    // literal 1 is const 'T'
        satelite->add(-bad); satelite->add(0);  // -bad must hold !
        for(int l : constraints){satelite->add(l);satelite->add(0);}
        // for(int l : constraints_prime){satelite->add(l); satelite->add(0);}
        for(int i=0; i<nLatches; ++i){
            int l = 1 + nInputs + i + 1;
            int pl = prime_lit(l);
            int next = nexts[i];
            satelite->add(-pl);satelite->add(next); satelite->add(0);
            satelite->add(-next); satelite->add(pl); satelite->add(0);
        }


        for(auto i = ands.rbegin(); i != ands.rend(); ++i){
            And &a = *i;
            assert(a.o > 0);

            if(lit_set.find(a.o) != lit_set.end()){
                lit_set.insert(abs(a.i1));
                lit_set.insert(abs(a.i2));
                
                satelite->add(-a.o); satelite->add(a.i1);  satelite->add(0);
                satelite->add(-a.o); satelite->add(a.i2);  satelite->add(0);
                satelite->add(a.o);  satelite->add(-a.i1); satelite->add(-a.i2); satelite->add(0);
                

                if(prime_lit_set.find(a.o) != prime_lit_set.end()){
                    int po  = prime_lit(a.o);
                    int pi1 = prime_lit(a.i1);
                    int pi2 = prime_lit(a.i2);

                    prime_lit_set.insert(abs(a.i1));
                    prime_lit_set.insert(abs(a.i2));
                    satelite->add(-po); satelite->add(pi1);  satelite->add(0);
                    satelite->add(-po); satelite->add(pi2);  satelite->add(0);
                    satelite->add(po);  satelite->add(-pi1); satelite->add(-pi2); satelite->add(0);

                }
            }
        }
        satelite->simplify();
    }
    
    for(int l : satelite->simplified_cnf)
        s->add(l);
    if(aig_veb > 2)
        cout<<"c add_cls finish load translation"<<endl;
}
