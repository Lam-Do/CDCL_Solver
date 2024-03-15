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
unordered_map<int, Literal*> Literal::unorderedMap = {};
unordered_set<int> Literal::id_list = {};
queue<Literal*> Literal::unit_queue= {};
// Clause:
int Clause::count = 1; // clauses uses this for id
bool Clause::conflict = false;
vector<Clause*> Clause::list = {};
// Assignment:
stack<Assignment*> Assignment::stack = {};
vector<stack<Assignment*>> Assignment::assignment_history = {};
bool Assignment::enablePrintAll = true;
string Assignment::branching_heuristic;

// Declare function
vector<vector<int>> readDIMACS(const string& path);
void parse(vector<vector<int>> formula);
void unitPropagation();
void backtracking();
void branching();
void simplify();
void removeSATClauses();
void pureLiteralsEliminate();
tuple<Literal *, bool> heuristicMOM();
void removeInitialUnitClauses();
void reset();
void printAllData();
//DPLL
void runDPLL(const std::string&);
//CDCL
void runCDCL(const std::string&);
void setWatchedLiterals();

// Global definition
const bool isForced = true;
bool isSAT = false;
bool isUNSAT = false;
int num_Clause = 0;
int num_Variable= 0;
int MAX_RUN_TIME = 60000; // Determine max runtime for solver, in milisecond.
std::chrono::duration<double, std::milli> run_time = std::chrono::high_resolution_clock::duration::zero();

// variables controlling output to terminal
bool print_parsing_result = false;
bool print_formula = false;
bool print_process = false;
bool printCDCLProcess = true;


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
        while (!isSAT && !isUNSAT && run_time.count() < MAX_RUN_TIME && !Clause::conflict) {
            unitPropagation();
            if (Literal::unit_queue.empty() && !Clause::conflict) {
                pureLiteralsEliminate();
            }
            if (!isSAT && !isUNSAT && Literal::unit_queue.empty() && !Clause::conflict) {
                branching();
            }
            if (Clause::conflict) {
                backtracking();
            }
            isSAT = Clause::checkSAT();
            run_time = std::chrono::high_resolution_clock::now() - start_time; // update runtime
        }

        // Output result
        if (isSAT) {
            cout << "The problem is satisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else if (isUNSAT) {
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
        setWatchedLiterals();
        // TODO: CDCL implement
        while (!isSAT && !isUNSAT && run_time.count() < MAX_RUN_TIME && !Clause::conflict) {

        }
        // Output result
        if (isSAT) {
            cout << "The problem is satisfiable!" << "\n";
            Assignment::printAll();
            //Assignment::printHistory();
        } else if (isUNSAT) {
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
 * Set up 2 watched literals for clauses
 */
void setWatchedLiterals() {
    for (auto* c : Clause::list) {
        // Choose 2 watched literals for each clauses
        int clause_size = c->pos_literals_list.size() + c->neg_literals_list.size();
        if (!c->SAT && clause_size >= 2) { // Only SAT by simplify(),
            c->watched_literal_1 = *(c->unset_literals.begin()); // randomly access due to unordered
            std::unordered_set<Literal*> s = c->unset_literals;
            s.erase(c->watched_literal_1);
            c->watched_literal_2 = *(s.begin());
        }
        // Add clause address to pos/neg_watched_occ of watched literals
        if (c->pos_literals_list.count(c->watched_literal_1) == 1) {
            c->watched_literal_1->pos_watched_occ.insert(c);
        } else {
            c->watched_literal_1->neg_watched_occ.insert(c);
        }
        if (c->pos_literals_list.count(c->watched_literal_2) == 1) {
            c->watched_literal_2->pos_watched_occ.insert(c);
        } else {
            c->watched_literal_2->neg_watched_occ.insert(c);
        }
    }
}

/**
 * Reset all static and global variable, this only necessary in case solver is used multiple times in a single project run.
*/
void reset() {
    if (print_process) cout << "Data reseted" << endl;
    Literal::count = 0;
    Literal::id_list.clear();
    Literal::unorderedMap.clear();
    while (!Literal::unit_queue.empty()){Literal::unit_queue.pop();}
    Clause::count = 0;
    Clause::list.clear();
    Clause::conflict = false;
    while (!Assignment::stack.empty()) {Assignment::stack.pop();}
    Assignment::assignment_history.clear();

    isSAT = false;
    isUNSAT = false;
    num_Clause = 0;
    num_Variable= 0;
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
    } else if (infile.is_open() && print_process) {
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
                num_Variable = std::stoi(token);
                iss >> token;
                num_Clause = std::stoi(token);
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
    if (print_process) {
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
    if (print_process) cout << "Start parsing..." << "\n";
    for (auto c : formula){
        Clause::setNewClause(c);
    }

    // Print out all parsed data
    if (print_parsing_result) {
        cout << "Number of literals: " << Literal::unorderedMap.size() << "\n";
        cout << "Number of clauses: " << Clause::list.size() << "\n";
        printAllData();
        cout<<"Finish parsing"<<"\n";
    }
}
/**
 * find and propagate all literal in unit_queue and assign value to these literal by force
 */
void unitPropagation() {
    if (print_process) cout << "Unit propagating..." << "\n";
    while (!(Literal::unit_queue.empty()) && !Clause::conflict) {
        Literal* next_literal = Literal::unit_queue.front();
        Literal::unit_queue.pop();
        Clause* unit_clause = next_literal->reason;
        // check if the literal is positive or negative in the unit clause to assign fitting value
        if (unit_clause->pos_literals_list.count(next_literal) == 1) {
            next_literal->assignValue(true, isForced);
        } else {
            next_literal->assignValue(false, isForced);
        }
    }
}

/**
 * Backtracking in case conflict flag is raised.
 * Print all assigned literals.
 * The stack which use to store assigning data will be pop until found an assignment by branching, else raise UNSAT flag that signal ending process
 * Literals will be unassigned its value in process.
 */
void backtracking() {
    // Some outputs to console, don't effect solving process
    if (Assignment::enablePrintAll) {
        std::cout << "\n";
        std::cout << "----------------" << "\n";
    }
    Assignment::printAll();

    // pop all forced assignment, stop at last branching assignment or stack empty
    while (!Assignment::stack.empty() && Assignment::stack.top()->isForced) {
        Assignment::stack.top()->assigned_literal->unassignValue();
        Assignment::stack.pop();
    }

    // branching -> forced
    if (!Assignment::stack.empty()) {
        // Save value of the top assignment before assigning new one which push a new assignment to top of stack
        Literal* top_literal = Assignment::stack.top()->assigned_literal;
        bool old_value = top_literal->value;

        top_literal->unassignValue();
        Assignment::stack.pop();
        //empty unit clause queue
        while (!Literal::unit_queue.empty()) {
            Literal::unit_queue.pop();
        }
        // assign opposite value
        top_literal->assignValue(!old_value, isForced); // no need to push new assignment here since assignValue() does it.
        Clause::conflict = false; // remove conflict flag
    } else {
        isUNSAT = true; // flag UNSAT in case stack is empty meaning all assignments is forced and there isn't any another branch
        if (print_process) std::cout << "UNSAT" << "\n";
    }
    if (print_process) cout << "Finished backtracking" << endl;
}

/**
 * Assign value to all pure literals, which have at the moment of calling function only positive or negative occurrences in UNSAT clauses, with forced assignment.
 * Pure literals can appear during process after remove SAT clauses are SAT from consideration.
 */
void pureLiteralsEliminate() {
    if (print_process) cout << "Pure literal eliminating..." << "\n";
    for (const auto& id2ad : Literal::unorderedMap) {
        Literal* l = id2ad.second;
        if (l->isFree) {
            if (l->getActualPosOcc(INT_MAX) == 0) {
                l->assignValue(false, isForced);
            } else if (l->getActualNegOcc(INT_MAX) == 0) {
                l->assignValue(true, isForced);
            }
        }
    }
}
/**
 * Branching in case unit_queue is empty (no unit clause), no conflict, no SAT or UNSAT flag.
 * Function using heuristics to choose a literal then assign value.
 */
void branching() {
    if (print_process) cout << "Start branching " << "\n";
    tuple<Literal*, bool> t = heuristicMOM(); // use MOM heuristic to choose branching literal
    if (std::get<0>(t) != nullptr) std::get<0>(t)->assignValue(std::get<1>(t), !isForced); // only assign if find a literal
    if (print_process) cout << "Finished branching " << endl;
}

/**
 * This heuristic choose clause with the smallest number of unassigned literals.
 * Value is chosen base on number of positive or negative occurrences.
 * @return A tuple of (pointer to chosen literal, value)
 */
std::tuple<Literal*, bool> heuristicMOM() {
    if (print_process) cout << "Using heuristic MOM" << "\n";

    Assignment::branching_heuristic = "MOM";
    // check all clauses for the shortest
    Clause* shortest_clause = nullptr;
    int shortest_width = INT_MAX;
    for (auto c : Clause::list) {
        int clause_actual_width = c->unset_literals.size();
        if (!c->SAT && clause_actual_width < shortest_width) {
            shortest_width = clause_actual_width;
            shortest_clause = c;
        }
    }

    Literal* chosen_literal = nullptr;
    int n = INT_MIN;
    bool value = true;
    if (shortest_clause != nullptr) {
        //choose literal using MOM formula with alpha = 1
        for (auto l : shortest_clause->unset_literals) {
            int actual_pos_occ = l->getActualPosOcc(shortest_width); // get number occ of literal in clauses with the exact shortest_width
            int actual_neg_occ = l->getActualNegOcc(shortest_width);
            int v = (actual_pos_occ + actual_neg_occ) * 2 ^ 1 + actual_pos_occ * actual_neg_occ;
            if (v > n) {
                n = v;
                chosen_literal = l;
                value = (actual_pos_occ >= actual_neg_occ) ? true : false;
            }
        }
    }
    return std::make_tuple(chosen_literal, value);
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
    if (print_process) cout << "Start simplifying" << "\n";
    removeSATClauses();
    removeInitialUnitClauses();
    if (print_process) cout << "Finish simplifying" << endl;
}

/**
 * Any unit clause with one literal will have that literal assign value by force
 */
void removeInitialUnitClauses() {
    if (print_process) cout << "Finding initial unit clauses ..." << "\n";
    for (const auto& c : Clause::list) {
        int literal_count = c->pos_literals_list.size() + c->neg_literals_list.size();
        if (literal_count == 1) {
            Literal* l = *(c->unset_literals.begin());
            if (c->pos_literals_list.empty()) { // Only use this condition to finding suitable value in this case with initial unit clauses
                l->assignValue(false, isForced);
            }
            else {
                l->assignValue(true, isForced);
            }
        }
    }
    if (Clause::conflict) isUNSAT = true; // Conflict by initial unit clauses (all forced assignment) means unsatisfiable
}

/**
 * Clauses having at least literal occur in both positive and negative are SAT by default and will be removed
 */
void removeSATClauses(){
    // check basic SAT condition
    // check a clause contain a literal both pos and neg
    if (print_process) cout << "Finding SAT clauses..." << "\n";
    for (const auto& id2ad : Literal::unorderedMap) {
        Literal* literal = id2ad.second;
        // a literal appear both pos and neg in a clause, that clause is alway SAT, can remove from the process.
        unordered_set<Clause*> intersect = findIntersection(literal->pos_occ, literal->neg_occ);
        if (!intersect.empty()) {
            for (auto c : intersect) {
                if (print_process) cout << "Clause " << c->id << " is SAT." << "\n";
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
    for (auto t : Literal::unorderedMap) {
        t.second->printData();
    }
    for (auto c : Clause::list) {
        c->printData();
    }
}