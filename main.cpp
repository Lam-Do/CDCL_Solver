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
std::unordered_set<Clause*> Clause::list = {};
std::unordered_set<LearnedClause*> LearnedClause::learned_list = {};
int Clause::learned_clause_assertion_level = 0;
// Learned CLause:
int LearnedClause::k_bounded_learning = 15;
int LearnedClause::m_size_relevance_based_learning = 5;
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
int Formula::conflict_count = 0;
int Formula::conflict_count_limit = 100;

// Declare function
vector<vector<int>> readDIMACS(const string& path);
void parse(const vector<vector<int>>& formula);
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
bool Printer::check_delete_process = false;
bool Printer::check_restart_process = false;
bool Printer::check_NiVER = false;
std::unordered_set<Literal*> Printer::flipped_literals = {};

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
        std::cout << "Start solving with TIMEOUT fixed to " << MAX_RUN_TIME/1000 << "s"<< "\n";
        parse(formula);
        Formula::preprocessing();
        while (!Formula::isSAT && !Formula::isUNSAT && run_time.count() < MAX_RUN_TIME) {
            Clause::unitPropagationCDCL();
            if (!Formula::isSAT && !Formula::isUNSAT && Literal::unit_queue.empty() && !Clause::CONFLICT) {
                Assignment::branchingCDCL();
            }
            if (!Formula::isSAT && !Formula::isUNSAT && Clause::CONFLICT) {
                if (Formula::conflict_count == Formula::conflict_count_limit) {
                    Formula::restart();
                } else {
                    Clause::conflictAnalyze();
                    if (!Formula::isUNSAT) {
                        Assignment::backtrackingCDCL();
                        LearnedClause::checkDeletion();
                    }
                }
            }
            Formula::isSAT = Clause::checkAllClausesSAT();
            run_time = std::chrono::high_resolution_clock::now() - start_time;
        }

        // Output result
        if (Formula::isSAT) {
            cout << "s SATISFIABLE" << "\n";
            Printer::printResult();
        } else if (Formula::isUNSAT) {
            cout << "s UNSATISFIABLE" << "\n";
        } else {
            cout << "s UNKNOWN - TIMEOUT" << "\n";
        }
    } else if (formula.empty()) {
        cerr << "File at " << path << " is empty or there are errors when opening!" << endl;
    }
    auto end_time = std::chrono::high_resolution_clock::now();
    run_time = end_time - start_time;
    std::cout << "c Done (runtime is " << run_time.count() << "ms)" << std::endl;
    reset();
}

/**
 * Reset all static and global variable, necessary for solving multiple instances in a single project run.
*/
void reset() {
    if (Printer::print_process) cout << "Data reseted" << endl;

    Literal::count = 0;
    for (auto [id, l] : Literal::id2Lit) {
        delete l;
    }
    Literal::id_list.clear();
    Literal::id2Lit.clear();
    while (!Literal::unit_queue.empty()){Literal::unit_queue.pop();}
    Literal::bd2BranLit.clear();
    while (!Literal::pq.empty()) {Literal::pq.pop();}

    Clause::count = 0;
    for (auto c : Clause::list) {
        delete c;
    }
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
    Formula::conflict_count = 0;
    Formula::conflict_count_limit = 100;

    Printer::flipped_literals.clear();
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
    vector<int> clause_holder;

    std::string line;
    while (std::getline(infile, line)) {
        std::istringstream iss(line);
        if (line.empty()) continue;
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
            formula.emplace_back(clause_holder); // add clause to formula
            clause_holder.clear(); // reset holder
            continue;
        } else { // not c or p or 0, if file in correct format, this should be a number presenting variable or literal
            int variable = std::stoi(token);
            clause_holder.emplace_back(variable); // add first variable to holder
            while (iss >> token) { // if not end of the line
                if (token == "0") {
                    formula.emplace_back(clause_holder); // when meet 0 as token, add finished clause to formula
                    clause_holder.clear(); // reset holder
                    break;
                }
                variable = std::stoi(token);
                clause_holder.emplace_back(variable);
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

///**
// * Implement some techniques to simplify SAT instance.
// */
//void simplify() {
//    if (Printer::print_process) cout << "Start simplifying" << "\n";
//    removeSATClauses();
//    removeInitialUnitClauses();
//    if (Printer::print_process) cout << "Finish simplifying" << endl;
//}

