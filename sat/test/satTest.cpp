#include <iostream>
#include <vector>
#include <fstream>
#include "sat.h"

using namespace std;

struct Node
{
    bool traversed;
};



// void reportResult(const SatSolver& solver, bool result, unsigned number_of_node)
// {
//     solver.printStats();
//     cout << (result? "SAT" : "UNSAT") << endl;
//     if (result) {
//         for (size_t i = 0; i < number_of_node; ++i){
//             for (size_t j = 0; j < number_of_node; ++j){
//                 cout << solver.getValue(_e[i][j]->getVar()) << endl;
//             }
//         }
//     }
// }

int main(int argc, char* argv[])
{
    SatSolver solver;
    solver.initialize();
    solver.assumeRelease();  // Clear assumptions
    //read in the info of the graph
    char buffer[200];
    char kind_of_graph;
    int _number_of_node,_number_of_edge;
    int w,s,e;
    
    fstream fin(argv[1]);
    if (!fin){
        cout<<"error"<<endl;
    }
    fstream fout;
    fout.open(argv[2],ios::out);
    fin>>kind_of_graph;
    fin>>_number_of_node;
    fin>>_number_of_edge;
    const int number_of_node = _number_of_node;
    const int number_of_edge = _number_of_edge;
    bool edge[number_of_node][number_of_node];
    vector <unsigned> start[number_of_node];
    vector <unsigned> end[number_of_node];
    for (unsigned i = 0; i < number_of_node; i++){
       for (unsigned j = 0; j < number_of_node; j++){
           edge[i][j] = false;
       }
   }
    while (fin >> s >> e >> w){
        edge[s][e] = true;
        edge[e][s] = true;
        start[s].push_back(e);
        start[e].push_back(s);
        end[e].push_back(s);
        end[s].push_back(e);
    }
    

   //make the relation of the nodes
   //for (unsigned i = 0; i < number_of_node; i++){
   //   assert(start[i].size() >= 2);
   //   for (unsigned j = 0; j < start[i].size(); j++){
   //      cout<<start[i][j]<<" ";
   //   }
   //   cout<<"\n";
  // }
      
   cout<<"file read"<<endl;

   //generate vars for the new directed graph
   Var _e[number_of_node][number_of_node];
   unsigned counter = 0;

   for (unsigned i = 0; i < number_of_node; i++){
       for (unsigned j = 0; j < number_of_node; j++){
           _e[i][j] = solver.newVar();
           if (edge[i][j] == false){
               solver.assumeProperty(_e[i][j],false);
               counter ++;
           }
       }
   }
   cout<<"var generated"<<endl;
   // 1.add constraint that the bidirectional edges cannot be chosen simultaneously
   vector <Var> constraint;
   vector <Var> newV;
//    for(unsigned i = 0; i < 2000 * number_of_node;i++){
//        newV[i] = solver.newVar();
//    }
//    unsigned counter = 0;
   for (unsigned i = 0; i < number_of_node; i++){
        for (unsigned j = 0; j < start[i].size(); j++){
            newV.push_back(solver.newVar());
            solver.addCNF(newV[newV.size() - 1],_e[i][start[i][j]],true, _e[start[i][j]][i], true);
            solver.assumeProperty(newV[newV.size() - 1],true);
            counter ++;
        }
    }
   cout<<"constraint 1 finished"<<endl;
   //2.add the constraint that only one outward and one inward edge would be true 
   //
   //(2.1) this part is for C(n,2)
    for (unsigned i = 0; i < number_of_node; i++){
        for (unsigned j = 0; j < start[i].size(); j++){
            for ( unsigned k = j+1; k < start[i].size(); k++){
                newV.push_back(solver.newVar());
                solver.addCNF(newV[newV.size() - 1],_e[i][start[i][j]],true, _e[i][start[i][k]], true);
                solver.assumeProperty(newV[newV.size() - 1],true);
                counter ++;
            }
        }
    }
cout<<"finished 2.1.1"<<endl;
   for (unsigned i = 0; i < number_of_node; i++){
       for (unsigned j = 0; j < start[i].size(); j++){
            for ( unsigned k = j+1; k < start[i].size(); k++){
                newV.push_back(solver.newVar());
                solver.addCNF(newV[newV.size() - 1],_e[start[i][j]][i],true, _e[start[i][k]][i], true);
                solver.assumeProperty(newV[newV.size() - 1],true);
                counter ++;
            }
       }
   }
//    cout<<"constraint 2.1 finished"<<endl;
   //(2.2) this part is for or all of the literals
    for (unsigned i = 0; i < number_of_node; i++){
        assert(start[i].size() >= 2);
        newV.push_back(solver.newVar());
        solver.addCNF(newV[newV.size() - 1],_e[i][start[i][0]],false, _e[i][start[i][1]], false);
        counter++;
        for (unsigned j = 2; j < start[i].size(); j++){
            newV.push_back(solver.newVar());
            solver.addCNF(newV[newV.size() - 1],newV[newV.size() - 2],false, _e[i][start[i][j]], false);
            counter++;
        }
        solver.assumeProperty(newV[newV.size() - 1],true);
    }
    cout<<"constraint 2.2 finished"<<endl;
    
   
   
   
 
   
   // solver.assumeProperty(newV, true);  // k = 1
    bool result, all_traversed = false,flag = false,sat = false,unsat = false;
    unsigned next_node, start_node,count = 0,number_of_conflicts = 0;
    vector <unsigned> path;
    Node nodes[number_of_node];
    while(sat == false && unsat == false){
        // cout<<"bello!!!"<<endl;
        result = solver.assumpSolve();
        // solver.printStats();
        flag = false;
        all_traversed = false;
        for(unsigned i = 0; i < number_of_node; i++){
            nodes[i].traversed = false;
        }
        // for(unsigned i = 0; i < number_of_node; i++){
        //     for(unsigned j = 0; j < number_of_node; j++){
        //             cout<<_e[i][j];
        //         }
        //         cout<<"\n";
        //     }
        if (!result){
            unsat = true;
            break;
        }
        else if(result){
            while(!all_traversed){
                path.clear();
                count = 0;
                for(unsigned i = 0; i < number_of_node; i++){
                    if(!nodes[i].traversed){
                        start_node = i;
                        nodes[start_node].traversed = true;
                        next_node = start_node;
                        path.push_back(next_node);
                        count ++;
                        break;
                    }
                }
                for(unsigned i = 0; i < number_of_node; i++){
                    for(unsigned j = 0; j < number_of_node; j++){
                        // cout<<solver.getValue(_e[0][0])<<endl;
                        // assert(sat == false);
                        if(solver.getValue(_e[next_node][j])){
                            next_node = j;
                            path.push_back(next_node);
                            count ++;
                            // assert(path.size()<number_of_node+3);
                            nodes[j].traversed = true;
                            if(count < number_of_node + 1 && next_node == start_node && flag == false){
                                // cout<<next_node<<" "<<start_node<<endl;
                                newV.push_back(solver.newVar());
                                solver.addCNF(newV[newV.size() - 1],_e[path[0]][path[1]],true, _e[path[1]][path[2]], true);
                                for(unsigned k = 2; k < path.size()-1; k++){
                                    newV.push_back(solver.newVar());
                                    solver.addCNF(newV[newV.size() - 1],newV[newV.size() - 2],false, _e[path[k]][path[k + 1]], true);
                                }
                                solver.assumeProperty(newV[newV.size() - 1],true);
                                flag = true;
                                count = 0;
                                path.clear();
                                assert(path.empty());
                                break;
                            }
                            
                            if(count == number_of_node + 1){
                                sat = true;
                                flag = true;
                                break;
                            }
                        }
                    }
                    if(flag){
                        break;
                    }
                }
                
                for(unsigned i = 0; i < number_of_node; i++){
                    if(!nodes[i].traversed){
                        break;
                    }
                    if(i == number_of_node - 1){
                        all_traversed = true;
                    }
                }
            }
        }
        if(!sat && !unsat){
            number_of_conflicts ++;
            cout<<number_of_conflicts<<endl;
        }
    }
   
    
   if (result) {
    //    for (size_t i = 0; i < number_of_node; ++i){
    //       cout<<i<<'|';
    //        for (size_t j = 0; j < number_of_node; ++j){
    //            cout << solver.getValue(_e[i][j]);
    //        }
    //        cout << "\n";
    //    }
    //    cout<<"=========================="<<endl;
       for (size_t i = 0; i < number_of_node; ++i){
           for (size_t j = 0; j < number_of_node; ++j){
               if(solver.getValue(_e[i][j])){
                   cout<< i << " " << j<<" ";
               }
           }
           cout<<"\n";
       }
       cout<<"=========================="<<endl;
   }
//    reportResult(solver, result);
    cout<<"counter = "<<counter<<endl;
   cout << endl << endl << "======================" << endl;
   solver.printStats();
   if(sat){
        cout<<"SAT!!!"<<endl;
    }
    else if(unsat){
        cout<<"UNSAT!!!"<<endl;
    }
    cout<<"number of conflicts = " << number_of_conflicts<< endl;

   // // k = Solve(Gate(3) & !Gate(7))
   // newV = solver.newVar();
   // solver.addAigCNF(newV, gates[3]->getVar(), false, gates[7]->getVar(), true);
   // solver.assumeRelease();  // Clear assumptions
   // solver.assumeProperty(newV, true);  // k = 1
   // result = solver.assumpSolve();
   // reportResult(solver, result);
}









