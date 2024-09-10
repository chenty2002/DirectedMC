#include "aig.hpp"
#include "DMC.hpp"
#include <iostream>
#include <string>
#include <chrono>
using namespace std;
using namespace std::chrono;

int main(int argc, char **argv){
    auto t_begin = system_clock::now();

    cout<<"c USAGE: ./modelchecker <aig-file>"<<endl;
    Aiger *aiger = load_aiger_from_file(string(argv[1]));
    DMC dmc;
    bool res = dmc.check();
    cout << res << endl;
   
    delete aiger;
    auto t_end = system_clock::now();
    auto duration = duration_cast<microseconds>(t_end - t_begin);
    double time_in_sec = double(duration.count()) * microseconds::period::num / microseconds::period::den;
    cout<<"c time = "<<time_in_sec<<endl;
    return 1;
}