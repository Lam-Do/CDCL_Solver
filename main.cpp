#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <chrono>
#include <filesystem>
#include "SATSolver.h"

using namespace std;
namespace fs = std::filesystem;

// Declare static variable
// Literal:
int Literal::count = 0;
unordered_map<int, Literal*> Literal::id2Lit = {};
unordered_set<int> Literal::id_list = {};
queue<Literal*> Literal::unit_queue= {};
std::unordered_map<int, Literal*> Literal::bd2BranLit;
std::priority_queue<Literal*, std::vector<Literal*>, Literal::Compare> Literal::pq;
// Clause:
int Clause::count = 1;
bool Clause::CONFLICT = false;
Clause* Clause::conflict_clause = nullptr;
vector<Clause*> Clause::list = {};
std::vector<LearnedClause*> LearnedClause::learned_list = {};
int Clause::learned_clause_assertion_level = 0;
// Assignment:
stack<Assignment*> Assignment::stack = {};
vector<stack<Assignment*>> Assignment::assignment_history = {};
int Assignment::bd = 0;
bool Assignment::enablePrintAll = true;
string Assignment::branching_heuristic = "VSIDS";

// Formula
bool Formula::isSAT = false;
bool Formula::isUNSAT = false;
int Formula::var_count = 0;
int Formula::clause_count = 0;
int Formula::branching_count = 0;

// Declare function
vector<vector<int>> readDIMACS(const string& path);
void parse(const vector<vector<int>>& formula);
void simplify();
void removeSATClauses();
void pureLiteralsEliminate();
void removeInitialUnitClauses();
void reset();
//DPLL
void runDPLL(const std::string&);
//CDCL
void runCDCL(const std::string&);

// Global definition
int MAX_RUN_TIME = 300000; // Determine max runtime for solver, in milisecond.
std::chrono::duration<double, std::milli> run_time = std::chrono::high_resolution_clock::duration::zero();

// variables controlling output to terminal
bool Printer::print_parsing_result = false;
bool Printer::print_formula = false;
bool Printer::print_process = false;
bool Printer::print_CDCL_process = false;
bool Printer::print_assignment = false;
bool Printer::print_learned_clause = false;
bool Printer::print_max_depth_literal = false;


int main() {
    string path;
    string select;
    cout << R"(Solve multiple SAT instances ("y" to run on a folder or "n" to run on a single file)?: )" << "\n";
    getline(cin, select);
    if (select == "y") {
        cout << "Please enter the full directory to the folder: " << "\n";
        getline(cin, path);
//        cout << R"(Do you want to disable printing all assignments history("y" to disable)?: )" << endl;
//        getline(cin, select);
//        if (select == "y") Assignment::enablePrintAll = false;
        for (const auto & entry : fs::directory_iterator(path)) {
            std::cout << entry.path().string() << std::endl;
            runCDCL(entry.path().string());
            std::cout << "-------------------------" << endl;
        }
    } else if (select == "n") {
        cout << "Please enter the full directory to the file: " << "\n";
        getline(cin, path);
        runCDCL(path);
    } else {
        cerr << "Invalid input!" << endl;
    }
    return 0;
}

///**
// * run DPLL solver on a file with DIMACS format in CNF form
// *
// * @param path  Directory of DIMACS file, require a full directory, could be plattform sensitive.
//*/
//void runDPLL(const std::string& path) {
//    auto start_time = std::chrono::high_resolution_clock::now();
//
//    //read DIMACS file, return formula in vector<vector<int>>
//    vector<vector<int>> formula = readDIMACS(path);
//
//    if (!formula.empty()) {
//        // parse formula into data structures
//        parse(formula);
//        simplify();
//        while (!Formula::isSAT && !Formula::isUNSAT && run_time.count() < MAX_RUN_TIME && !Clause::CONFLICT) {
//            Clause::unitPropagationDPLL();
//            if (Literal::unit_queue.empty() && !Clause::CONFLICT) {
//                pureLiteralsEliminate();
//            }
//            if (!Formula::isSAT && !Formula::isUNSAT && Literal::unit_queue.empty() && !Clause::CONFLICT) {
//                Assignment::branchingDPLL();
//            }
//            if (Clause::CONFLICT) {
//                Assignment::backtrackingDPLL();
//            }
//            Formula::isSAT = Clause::checkAllClausesSAT();
//            run_time = std::chrono::high_resolution_clock::now() - start_time; // update runtime
//        }
//
//        // Output result
//        if (Formula::isSAT) {
//            cout << "The problem is satisfiable!" << "\n";
//            Printer::printAssignmentStack();
//            //Assignment::printAssignmentHistory();
//        } else if (Formula::isUNSAT) {
//            cout << "The problem is unsatisfiable!" << "\n";
//            Printer::printAssignmentStack();
//            //Assignment::printAssignmentHistory();
//        } else {
//            cout << "Time run out!" << "\n";
//            Printer::printAssignmentStack();
//        }
//    } else if (formula.empty()) {
//        cerr << "File at " << path << " is empty or error opening!" << endl;
//    }
//
//    auto end_time = std::chrono::high_resolution_clock::now();
//    run_time = end_time - start_time;
//    std::cout << "Runtime: " << run_time.count() << "ms" << endl;
//    reset();
//}

/**
 * run CDCL solver on a file with DIMACS format in CNF form
 *
 * @param path  Directory of DIMACS file, require a full directory, could be plattform sensitive.
*/
void runCDCL(const std::string& path) {
    auto start_time = std::chrono::high_resolution_clock::now();
    vector<vector<int>> formula = readDIMACS(path);
    if (!formula.empty()) {
        parse(formula);
        Formula::preprocessing();
        // TODO: CDCL implement
        while (!Formula::isSAT && !Formula::isUNSAT && run_time.count() < MAX_RUN_TIME) {
            Clause::unitPropagationCDCL();
            if (!Formula::isSAT && !Formula::isUNSAT && Literal::unit_queue.empty() && !Clause::CONFLICT) {
                Assignment::branchingCDCL();
            }
            if (!Formula::isSAT && !Formula::isUNSAT && Clause::CONFLICT) {
                Clause::conflictAnalyze();
                if (!Formula::isUNSAT) {
                    Assignment::backtrackingCDCL();
                }
            }
            Formula::isSAT = Clause::checkAllClausesSAT();
            run_time = std::chrono::high_resolution_clock::now() - start_time;
        }
        // Output result
        if (Formula::isSAT) {
            cout << "The problem is satisfiable!" << "\n";
            Printer::printResult();
        } else if (Formula::isUNSAT) {
            cout << "The problem is unsatisfiable!" << "\n";
            Printer::printResult();
        } else {
            cout << "Time run out!" << "\n";
            Printer::printResult();
        }
    } else if (formula.empty()) {
        cerr << "File at " << path << " is empty or error opening!" << endl;
    }
    auto end_time = std::chrono::high_resolution_clock::now();
    run_time = end_time - start_time;
    std::cout << "Runtime: " << run_time.count() << "ms" << endl;
    reset();
}

/**
 * Reset all static and global variable, necessary for solving multiple instances in a single project run.
*/
void reset() {
    if (Printer::print_process) cout << "Data reseted" << endl;

    Literal::count = 0;
//    for (auto [id, l] : Literal::id2Lit) {
//        delete l;
//    }
    Literal::id_list.clear();
    Literal::id2Lit.clear();
    while (!Literal::unit_queue.empty()){Literal::unit_queue.pop();}
    Literal::bd2BranLit.clear();
    while (!Literal::pq.empty()) {Literal::pq.pop();}

    Clause::count = 0;
//    for (auto c : Clause::list) {
//        delete c;
//    }
    Clause::list.clear();
    Clause::CONFLICT = false;
    Clause::conflict_clause = nullptr;
    Clause::learned_clause_assertion_level = 0;
    LearnedClause::learned_list.clear();

    while (!Assignment::stack.empty()) {Assignment::stack.pop();}
    Assignment::assignment_history.clear();
    Assignment::bd = 0;

    Formula::isSAT = false;
    Formula::isUNSAT = false;
    Formula::clause_count = 0;
    Formula::var_count = 0;
    Formula::branching_count = 0;

    run_time = std::chrono::high_resolution_clock::duration::zero();
}

/**
 * Read DIMACS file and parse to vector of vector form
 * @param path file's name or path to the file
 * @return SAT instance type vector<vector<int>>
 */
vector<vector<int>> readDIMACS(const string& path) {
    std::ifstream infile(path);

    if (!infile.is_open()) {
        std::cerr << "Error opening file " << path << std::endl;
        return {};
    } else if (infile.is_open() && Printer::print_CDCL_process) {
        cout << "File opened" << endl;
    }

    vector<vector<int>> formula;

    std::string line;
    while (std::getline(infile, line)) {
        std::istringstream iss(line);
        std::string token;
        iss >> token; // first word/number of the line;

        if (token == "c") { // comments will be ignored
            continue;
        } else if (token == "p") {
            iss >> token; // "cnf"
            if (!(token == "cnf")) { // only read CNF form
                std::cerr << "Error reading cnf format" << std::endl;
                return {};
            } else {
                // parse number of variables and clauses
                iss >> token;
                Formula::var_count = std::stoi(token);
                iss >> token;
                Formula::clause_count = std::stoi(token);
            }
        } else if (token == "0") { // if the line start with 0, will also be ignored
            continue;
        } else { // not c or p or 0, if file in correct format, this should be a number presenting variable or literal
            int variable = std::stoi(token);
            formula.emplace_back(vector<int> {}); // new empty clause
            formula.back().emplace_back(variable); // add first variable
            while (iss >> token) { // if not end of the line
                if (token == "0") {
                    break;
                }
                variable = std::stoi(token);
                formula.back().emplace_back(variable);
            }
        }
    }
    if (Printer::print_CDCL_process) {
        cout << "Finished read file " << path << endl;
    }
    if (Printer::print_formula) {
        cout << "Solving SAT instance: " << "\n";
        for (const auto& c : formula) {
            for (auto v : c) {
                cout << v << " ";
            }
            cout << "\n";
        }
    }
    return formula;
}

/**
 * parse all clauses and literals from the SAT instance to data structures
 * @param formula SAT instance
 */
void parse(const vector<vector<int>>& formula) {
    if (Printer::print_CDCL_process) cout << "Start parsing..." << "\n";
    for (auto c : formula){
        Clause::setNewClause(c);
    }

    // Print out all parsed data
    if (Printer::print_parsing_result) {
        cout << "Number of literals: " << Literal::id2Lit.size() << "\n";
        cout << "Number of clauses: " << Clause::list.size() << "\n";
        Printer::printAllData();
        cout<<"Finish parsing"<<"\n";
    }
}

/**
 * Assign value to all pure literals, which have at the moment of calling function only positive or negative occurrences in UNSAT clauses, with forced assignment.
 * Pure literals can appear during process after remove SAT clauses are SAT from consideration.
 */
void pureLiteralsEliminate() {
    if (Printer::print_process) cout << "Pure literal eliminating..." << "\n";
    for (const auto& id2ad : Literal::id2Lit) {
        Literal* l = id2ad.second;
        if (l->isFree) {
            if (l->getActualPosOcc(INT_MAX) == 0) {
                l->assignValueDPLL(false, Assignment::IsForced);
            } else if (l->getActualNegOcc(INT_MAX) == 0) {
                l->assignValueDPLL(true, Assignment::IsForced);
            }
        }
    }
}

/**
 * Find intersection between two unordered set of type T
 * @tparam T Any type
 * @param s1 First set
 * @param s2 Second set
 * @return Unordered set of elements which both inputted sets contain.
 */
template<typename T>
unordered_set<T> findIntersection(const unordered_set<T>& s1, const unordered_set<T>& s2) {
    unordered_set<T> intersection;

    for (const T& e : s1) {
        if (s2.count(e)) {
            intersection.insert(e);
        }
    }
    return intersection;
}

///**
// * Implement some techniques to simplify SAT instance.
// */
//void simplify() {
//    if (Printer::print_process) cout << "Start simplifying" << "\n";
//    removeSATClauses();
//    removeInitialUnitClauses();
//    if (Printer::print_process) cout << "Finish simplifying" << endl;
//}

/**
 * Clauses having at least literal occur in both positive and negative are SAT by default and will be removed
 */
void removeSATClauses(){
    // check basic SAT condition
    // check a clause contain a literal both pos and neg
    if (Printer::print_process) cout << "Finding SAT clauses..." << "\n";
    for (const auto& id2ad : Literal::id2Lit) {
        Literal* literal = id2ad.second;
        // a literal appear both pos and neg in a clause, that clause is alway SAT, can remove from the process.
        unordered_set<Clause*> intersect = findIntersection(literal->pos_occ, literal->neg_occ);
        if (!intersect.empty()) {
            for (auto c : intersect) {
                if (Printer::print_process) cout << "Clause " << c->id << " is SAT." << "\n";
                Clause::list.erase(Clause::list.begin() + c->id - 1);
                // erase in all connected literals
                for (auto l : c->pos_literals_list) {
                    l->pos_occ.erase(c);
                }
                for (auto l : c->neg_literals_list) {
                    l->neg_occ.erase(c);
                }
            }
        }
    }
}

