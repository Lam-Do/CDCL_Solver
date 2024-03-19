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
// Clause:
int Clause::count = 1; // clauses uses this for id
bool Clause::CONFLICT = false;
Clause* Clause::conflict_clause = nullptr;
vector<Clause*> Clause::list = {};
int Clause::learned_clause_assertion_level = 0;
// Assignment:
stack<Assignment*> Assignment::stack = {};
vector<stack<Assignment*>> Assignment::assignment_history = {};
int Assignment::bd = 0;
bool Assignment::enablePrintAll = true;
string Assignment::branching_heuristic;

// Formula
bool Formula::isSAT = false;
bool Formula::isUNSAT = false;
int Formula::var_count = 0;
int Formula::clause_count = 0;
int Formula::branching_count = 0;

// Declare function
vector<vector<int>> readDIMACS(const string& path);
void parse(vector<vector<int>> formula);
void simplify();
void removeSATClauses();
void pureLiteralsEliminate();
void removeInitialUnitClauses();
void reset();
void printAllData();
//DPLL
void runDPLL(const std::string&);
//CDCL
void runCDCL(const std::string&);

// Global definition
int MAX_RUN_TIME = 60000; // Determine max runtime for solver, in milisecond.
std::chrono::duration<double, std::milli> run_time = std::chrono::high_resolution_clock::duration::zero();

// variables controlling output to terminal
bool print_parsing_result = false;
bool print_formula = false;
bool Printer::print_process = false;
bool printCDCLProcess = false;


/**
 CDCL implement log:
    void runCDCL(const std::string&);
    string Assignment::branching_heuristic; // keeping branching_heuristic's name
    setWatchedLiterals()
    refactor clause pos/neg_literals_list to unordered set
 */

int main() {
    string path;
    string select;
    cout << R"(Solve multiple SAT instances ("y" to run on a folder or "n" to run on a single file)?: )" << "\n";
    getline(cin, select);
    if (select == "y") {
        cout << "Please enter the full directory to the folder: " << "\n";
        getline(cin, path);
        cout << R"(Do you want to disable printing all assignments history("y" to disable)?: )" << endl;
        getline(cin, select);
        if (select == "y") Assignment::enablePrintAll = false;
        for (const auto & entry : fs::directory_iterator(path)) {
            std::cout << entry.path().string() << std::endl;
            runDPLL(entry.path().string());
            std::cout << "-------------------------" << endl;
        }
    } else if (select == "n") {
        cout << "Please enter the full directory to the file: " << "\n";
        getline(cin, path);
        runDPLL(path);
    } else {
        cerr << "Invalid input!" << endl;
    }
    return 0;
}

/**
 * run DPLL solver on a file with DIMACS format in CNF form
 *
 * @param path  Directory of DIMACS file, require a full directory, could be plattform sensitive.
*/
void runDPLL(const std::string& path) {
    auto start_time = std::chrono::high_resolution_clock::now();

    //read DIMACS file, return formula in vector<vector<int>>
    vector<vector<int>> formula = readDIMACS(path);

    if (!formula.empty()) {
        // parse formula into data structures
        parse(formula);
        simplify();
        while (!Formula::isSAT && !Formula::isUNSAT && run_time.count() < MAX_RUN_TIME && !Clause::CONFLICT) {
            Clause::unitPropagationDPLL();
            if (Literal::unit_queue.empty() && !Clause::CONFLICT) {
                pureLiteralsEliminate();
            }
            if (!Formula::isSAT && !Formula::isUNSAT && Literal::unit_queue.empty() && !Clause::CONFLICT) {
                Assignment::branchingDPLL();
            }
            if (Clause::CONFLICT) {
                Assignment::backtrackingDPLL();
            }
            Formula::isSAT = Clause::checkAllClausesSAT();
            run_time = std::chrono::high_resolution_clock::now() - start_time; // update runtime
        }

        // Output result
        if (Formula::isSAT) {
            cout << "The problem is satisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else if (Formula::isUNSAT) {
            cout << "The problem is unsatisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else {
            cout << "Time run out!" << "\n";
            Assignment::printAll();
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
 * run DPLL solver on a file with DIMACS format in CNF form
 *
 * @param path  Directory of DIMACS file, require a full directory, could be plattform sensitive.
*/
void runCDCL(const std::string& path) {
    auto start_time = std::chrono::high_resolution_clock::now();
    vector<vector<int>> formula = readDIMACS(path);
    if (!formula.empty()) {
        parse(formula);
        simplify();
        Clause::setWatchedLiterals();
        // TODO: CDCL implement
        while (!Formula::isSAT && !Formula::isUNSAT && run_time.count() < MAX_RUN_TIME && !Clause::CONFLICT) {

        }
        // Output result
        if (Formula::isSAT) {
            cout << "The problem is satisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else if (Formula::isUNSAT) {
            cout << "The problem is unsatisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else {
            cout << "Time run out!" << "\n";
            Assignment::printAll();
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
 * Reset all static and global variable, this only necessary in case solver is used multiple times in a single project run.
*/
void reset() {
    if (Printer::print_process) cout << "Data reseted" << endl;

    Literal::count = 0;
    Literal::id_list.clear();
    Literal::id2Lit.clear();
    while (!Literal::unit_queue.empty()){Literal::unit_queue.pop();}
    Literal::bd2BranLit.clear();

    Clause::count = 0;
    Clause::list.clear();
    Clause::CONFLICT = false;
    Clause::conflict_clause = nullptr;
    Clause::learned_clause_assertion_level = 0;

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
 * @param file_name file's name or path to the file
 * @return SAT instance type vector<vector<int>>
 */
vector<vector<int>> readDIMACS(const string& file_name) {
    std::ifstream infile(file_name);

    if (!infile.is_open()) {
        std::cerr << "Error opening file " << file_name << std::endl;
        return {};
    } else if (infile.is_open() && Printer::print_process) {
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
    if (Printer::print_process) {
        cout << "Finished read file " << file_name << endl;
    }
    if (print_formula) {
        cout << "Solving SAT instance: " << "\n";
        for (auto c : formula) {
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
void parse(vector<vector<int>> formula) {
    if (Printer::print_process) cout << "Start parsing..." << "\n";
    for (auto c : formula){
        Clause::setNewClause(c);
    }

    // Print out all parsed data
    if (print_parsing_result) {
        cout << "Number of literals: " << Literal::id2Lit.size() << "\n";
        cout << "Number of clauses: " << Clause::list.size() << "\n";
        printAllData();
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

/**
 * Implement some techniques to simplify SAT instance.
 */
void simplify() {
    if (Printer::print_process) cout << "Start simplifying" << "\n";
    removeSATClauses();
    removeInitialUnitClauses();
    if (Printer::print_process) cout << "Finish simplifying" << endl;
}

/**
 * Any unit clause with one literal will have that literal assign value by force
 */
void removeInitialUnitClauses() {
    if (Printer::print_process) cout << "Finding initial unit clauses ..." << "\n";
    for (auto c : Clause::list) {
        int literal_count = c->pos_literals_list.size() + c->neg_literals_list.size();
        if (literal_count == 1) {
            Literal* l = *(c->free_literals.begin());
            if (c->pos_literals_list.empty()) { // Only use this condition to finding suitable value in this case with initial unit clauses
                l->assignValueDPLL(false, Assignment::IsForced);
            }
            else {
                l->assignValueDPLL(true, Assignment::IsForced);
            }
        }
    }
    if (Clause::CONFLICT) {
        Formula::isUNSAT = true;
    } // Conflict by initial unit clauses (all forced assignment) means unsatisfiable
}

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

/**
 * Print all data saving in data structure Literal and Clause.
 * Function is not use if variable print_process is not set to "true";
 */
void printAllData() {
    for (auto t : Literal::id2Lit) {
        t.second->printData();
    }
    for (auto c : Clause::list) {
        c->printData();
    }
}