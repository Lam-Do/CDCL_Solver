#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <chrono>
#include <filesystem>
#include "SolverClass.h"

using namespace std;
namespace fs = std::filesystem;

// Declare static variable
int Literal::count = 0;
unordered_map<int, Literal*> Literal::unorderedMap = {};
unordered_set<int> Literal::id_list = {};
queue<Literal*> Literal::unit_queue= {};
int Clause::count = 1; // clauses uses this for id
bool Clause::conflict = false;
vector<Clause*> Clause::list = {};
stack<Assignment*> Assignment::stack = {};
vector<stack<Assignment*>> Assignment::assignment_history = {};
bool Assignment::enablePrintAll = true;

// Declare function
vector<vector<int>> readDIMACS(const string& path);
void parse(const vector<vector<int>>& formula);
void unitPropagation();
void backtracking();
void pureLiteralsEliminate();
void branching();
void simplify();
void removeSATClauses();
tuple<Literal *, bool> heuristicMOM();
void removeUnitClauses();
void runDPLL(const std::string&);
void reset();
void printAllData();

// Global definition
const int MAX_RUN_TIME = 60000; // Determine max runtime for solver, in milisecond.
const bool printProcess = false; // variable enable output data to console for monitoring solving process

const bool isForced = true;
bool isSAT = false;
bool isUNSAT = false;
int num_Clause = 0;
int num_Variable= 0;
std::chrono::duration<double, std::milli> run_time = std::chrono::high_resolution_clock::duration::zero();

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
        // parse formula into data structure
        parse(formula);
        simplify();
        while (!isSAT && !isUNSAT && run_time.count() < MAX_RUN_TIME) {
            unitPropagation();
            if (Literal::unit_queue.empty()) {
                pureLiteralsEliminate();
            }
            if (Clause::conflict) {
                backtracking();
            }
            if (!isSAT && !isUNSAT && Literal::unit_queue.empty() && !Clause::conflict) {
                branching();
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
        //cerr << "File at " << path << " is empty or error opening!" << endl;
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
    if (printProcess) cout << "Data reseted" << endl;
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
    } else if (infile.is_open() && printProcess) {
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
    if (printProcess) {
        cout << "Finished read file " << file_name << endl;
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
void parse(const vector<vector<int>>& formula) {
    if (printProcess) cout << "Start parsing..."<<"\n";
    for (const auto& c : formula){
        auto* new_clause = new Clause(Clause::count);
        new_clause->updateStaticData();
        for (auto l : c) {
            if (Literal::id_list.count(abs(l)) == 0) { // new literal
                if (l >= 0) {
                    auto* new_literal = new Literal(abs(l));
                    new_literal->updateStaticData();
                    // connecting literals and clauses
                    new_literal->pos_occ.insert(new_clause);
                    new_clause->appendLiteral(new_literal, true);
                } else {
                    auto* new_literal = new Literal(abs(l));
                    new_literal->updateStaticData();
                    // connecting literals and clauses
                    new_literal->neg_occ.insert(new_clause);
                    new_clause->appendLiteral(new_literal, false);
                }
            } else {
                auto* current_literal = Literal::unorderedMap[abs(l)];
                if (l >= 0) {
                    current_literal->pos_occ.insert(new_clause);
                    new_clause->appendLiteral(current_literal, true);
                } else {
                    current_literal->neg_occ.insert(new_clause);
                    new_clause->appendLiteral(current_literal, false);
                }
            }
        }
    }

    // Print out all parsed data
    if (printProcess) {
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
    if (printProcess) cout << "Unit propagating..." << "\n";
    while (!(Literal::unit_queue.empty())) {
        Literal* next_literal = Literal::unit_queue.front();
        Literal::unit_queue.pop();
        Clause* unit_clause = next_literal->reason;
        // check if the literal is positive or negative in the unit clause to assign fitting value
        if (find(unit_clause->pos_literals_list.begin(), unit_clause->pos_literals_list.end(), next_literal) != unit_clause->pos_literals_list.end()) {
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
    if (Assignment::enablePrintAll) {
        std::cout << "\n";
        std::cout << "----------------" << "\n";
    }
    Assignment::printAll();
    while (!Assignment::stack.empty() && Assignment::stack.top()->isForced) {
        Assignment::stack.top()->assigned_literal->unassignValue();
        Assignment::stack.pop();
    }
    if (!Assignment::stack.empty()) {
        // Save value of the top assignment before assigning new one which push a new assignment to top of stack
        Literal* top_literal = Assignment::stack.top()->assigned_literal;
        bool old_value = top_literal->value;

        top_literal->unassignValue();
        Assignment::stack.pop();

        while (!Literal::unit_queue.empty()) {
            Literal::unit_queue.pop();
        }

        top_literal->assignValue(!old_value, isForced); // no need to push new assignment here since assignValue() does it.
        Clause::conflict = false; // remove conflict flag
    } else {
        isUNSAT = true; // flag UNSAT in case stack is empty meaning all assignments is forced and there isn't any another branch
    }
    if (printProcess) cout << "Finished backtracking" << endl;
}

/**
 * Assign value to all pure literals, which have at the moment of calling function only positive or negative occurrences in UNSAT clauses, with forced assignment.
 * Pure literals can appear during process after remove SAT clauses are SAT from consideration.
 */
void pureLiteralsEliminate() {
    if (printProcess) cout << "Pure literal eliminating..." << "\n";
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
    if (printProcess) cout << "Start branching " << "\n";
    tuple<Literal*, bool> t = heuristicMOM(); // use MOM heuristic to choose branching literal
    if (std::get<0>(t) != nullptr) std::get<0>(t)->assignValue(std::get<1>(t), !isForced); // only assign if find a literal
    if (printProcess) cout << "Finished branching " << endl;
}

/**
 * This heuristic choose clause with the smallest number of unassigned literals.
 * Value is chosen base on number of positive or negative occurrences.
 * @return A tuple of (pointer to chosen literal, value)
 */
std::tuple<Literal*, bool> heuristicMOM() {
    // check all clauses for the shortest
    if (printProcess) cout << "Using heuristic MOM" << "\n";
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
    if (printProcess) cout << "Start simplifying" << "\n";
    removeSATClauses();
    removeUnitClauses();
    if (printProcess) cout << "Finish simplifying" << endl;
}

/**
 * Any unit clause with one literal will have that literal assign value by force
 */
void removeUnitClauses() {
    if (printProcess) cout << "Finding initial unit clauses ..." << "\n";
    for (const auto& c : Clause::list) {
        if (c->unset_literals.size() == 1) {
            Literal* l = *(c->unset_literals.begin());
            if (c->pos_literals_list.empty()) {l->assignValue(false, isForced);}
            else {l->assignValue(true, isForced);}
        }
    }
}

/**
 * Clauses having at least literal occur in both positive and negative are SAT by default and will be removed
 */
void removeSATClauses(){
    // check basic SAT condition
    // check a clause contain a literal both pos and neg
    if (printProcess) cout << "Finding SAT clauses..." << "\n";
    for (const auto& id2ad : Literal::unorderedMap) {
        Literal* literal = id2ad.second;
        // a literal appear both pos and neg in a clause, that clause is alway SAT, can remove from the process.
        unordered_set<Clause*> intersect = findIntersection(literal->pos_occ, literal->neg_occ);
        if (!intersect.empty()) {
            for (auto c : intersect) {
                if (printProcess) cout << "Clause " << c->id << " is SAT."<< "\n";
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
 * Function is not use if variable printProcess is not set to "true";
 */
void printAllData() {
    for (auto t : Literal::unorderedMap) {
        t.second->printData();
    }
    for (auto c : Clause::list) {
        c->printData();
    }
}