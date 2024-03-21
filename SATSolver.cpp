#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"

/**
 * Find intersection between two unordered set of type T
 * @tparam T Any type
 * @param s1 First set
 * @param s2 Second set
 * @return Unordered set of elements which both inputted sets contain.
 */
template<typename T>
std::unordered_set<T> findIntersection(const std::unordered_set<T>& s1, const std::unordered_set<T>& s2) {
    std::unordered_set<T> intersection;

    for (const T& e : s1) {
        if (s2.contains(e)) {
            intersection.insert(e);
        }
    }
    return intersection;
}

void Literal::setFree() {
    this->isFree = true;
}

/**
 * Counting all positive occurrence in UNSAT clauses with number of free literal less or equal w, by the time called.
 * Occurrences in SAT clauses will not be counted.
 * @param w  Maximal number of free literals of clauses in pos_occ. If bigger than actual number of clause's size. Simply count all.
 * @return  Number of occurrence
 */
int Literal::getActualPosOcc(int w) {
    int occ = 0;
    for (auto c : this->pos_occ) {
        if (!c->SAT && c->free_literals.size() <= w) {
            occ++;
        }
    }
    return occ;
}
/**
 * Counting all negtive occurrence in UNSAT clauses with number of free literal less or equal w, by the time called.
 * Occurrences in SAT clauses will not be counted.
 * @param w Maximal number of free literals of clauses in neg_occ. If bigger than actual number of clause's size. Simply count all.
 * @return Number of occurrence
 */
int Literal::getActualNegOcc(int w) {
    int occ = 0;
    for (auto c : this->neg_occ) {
        if (!c->SAT && c->free_literals.size() <= w) {
            occ++;
        }
    }
    return occ;
}

/**
 * Print all data saved by this instances of class Literal.
 */
void Literal::printData() {
    std::cout << "Literal " << this->id << " at " << this <<" -";
    if (this->isFree) std::cout << " free";
    else std::cout << " assigned";
    std::cout << " - pos_occ:";
    for (auto c : this->pos_occ) {
        std::cout << " " << c->id << ",";
    }
    std::cout << " - neg_occ:";
    for (auto c : this->neg_occ) {
        std::cout << " " << c->id << ",";
    }
    if (this->reason == nullptr) std::cout << " - satisfy no clause " << std::endl;
    else std::cout << " - satisfy clause " << this->reason->id << std::endl;
}


/**
 * Save literal to clause's positive and negative literal list accordingly, and also all to free literals list.
 *
 * @param literal Pointer to literal
 * @param is_pos_occ "true" if positive literal, "false" otherwise
 */
void Clause::appendLiteral(Literal* literal, bool is_pos_occ) {
    if (is_pos_occ) {
        this->pos_literals_list.insert(literal);
    } else {
        this->neg_literals_list.insert(literal);
    }
    // literal is free when initial parse, unless when parsing to new learned clause
    if (literal->isFree) this->free_literals.insert(literal);
    else {
        if (literal->value == true && is_pos_occ) this->sat_by.insert(literal);
        if (literal->value == false && !is_pos_occ) this->sat_by.insert(literal);
    }
}

/**
 * Check if all clauses are SAT
 * @return true if all clauses are SAT, false otherwise.
 */
bool Clause::checkAllClausesSAT() {
    for (const auto& c : Clause::list) {
        if (!c->SAT) {return false;}
    }
    return true;
}

/**
 * Get number of free literals in the clause.
 * @return Number of free literals
 */
int Clause::getUnsetLiteralsCount() const {return this->free_literals.size();}

int Clause::getWidth() const {return this->pos_literals_list.size() + this->neg_literals_list.size();}
/**
 * Print all data saved by this instances of class Clause.
 */
void Clause::printData() {
    std::cout << "Clause " << this->id << " at " << this <<" -";
    std::cout << " pos_literals:";
    for (auto l : this->pos_literals_list) {
        std::cout << " " << l->id << ",";
    }
    std::cout << " - neg_literals:";
    for (auto l : this->neg_literals_list) {
        std::cout << " -" << l->id << ",";
    }
    std::cout << " - current unassigned literals:";
    for (auto l : this->free_literals) {
        std::cout << " " << l->id << ",";
    }
    if (this->SAT) {
        std::cout << " - satisfy by:";
        for (auto l : this->sat_by) {
            std::cout << " " << l->id << ",";
        }
    } else std::cout << " - UNSAT" << std::endl;
}

/**
 * Update number of literals, unordered map literal's id to adress and list of id.
 */
void Literal::updateStaticData() {
    Literal::count++;
    Literal::id2Lit[this->id] = this;
    Literal::id_list.insert(id);
}

/**
 * Update number of clauses and list of clauses.
 */
void Clause::updateStaticData() {
    Clause::count++;
    Clause::list.insert(this);
}

void Assignment::updateStaticData() {
    stack.push(this);
}

/**
 * Print all assignment in the stack without changing the stack.
 */
void Printer::printAssignmentStack() {
    if (Assignment::enablePrintAll) {
        std::stack<Assignment*> s = Assignment::stack;
        std::stack<Assignment*> reversed_stack;
        while (!s.empty()) {
            reversed_stack.push(s.top());
            s.pop();
        }
        Assignment::assignment_history.emplace_back(reversed_stack);
        while (!reversed_stack.empty()) {
            Literal* l = reversed_stack.top()->assigned_literal;
            std::cout << "[" << l->id << "|" << l->value << "|";
            if (reversed_stack.top()->status) {std::cout << "f]";}
            else {std::cout << "b]";}
            std::cout << "-";
            reversed_stack.pop();
        }
        std::cout<<std::endl;
    }
}

/**
 * Print all assignments include removed ones by backtracking in graph form.
 */
void Printer::printAssignmentHistory() {
    std::unordered_set<std::string> printed_list;
    for (auto& s : Assignment::assignment_history) {
        bool print_rest = false;
        while (!s.empty()) {
            // get first assignment
            Literal* l = s.top()->assigned_literal;
            std::string a = "[" + std::to_string(l->id) + "|" + std::to_string(l->value) + "|";
            if (s.top()->status) { a += "f]";}
            else {a += "b]";}

            if (print_rest || printed_list.count(a) == 0 ) {
                if (print_rest && printed_list.count(a) != 0) {
                    printed_list.erase(a);
                } else printed_list.insert(a);
                std::cout << a << "-";
                print_rest = true; // the first change in assignment history (backtracking), signal print the rest
            } else if (printed_list.count(a) >= 1) {
                std::cout << "        ";
            }
            s.pop();
        }
        std::cout << std::endl;
    }
}
/**
 * creat new variable or update data structure when creating a new clause with old variable
 * Both data structure Clause and Literal, the connection between both, are updated here
 * @param l id of the literal
 * @param new_clause point to the clause contain the literal
 */
void Literal::setLiteral(int l, Clause* new_clause) {
    if (Literal::id_list.count(abs(l)) == 0) { // id is not in the list (count = 0) meaning new Literal
        auto* new_literal = new Literal(abs(l));
        new_literal->updateStaticData();
        if (l >= 0) {
            // connecting literals and clauses
            new_literal->pos_occ.insert(new_clause);
            new_clause->appendLiteral(new_literal, true);
        } else {
            // connecting literals and clauses
            new_literal->neg_occ.insert(new_clause);
            new_clause->appendLiteral(new_literal, false);
        }
        // push to priority queue
        Literal::pq.push(new_literal);
    } else {
        auto* updating_literal = Literal::id2Lit[abs(l)];
        if (l >= 0) {
            updating_literal->pos_occ.insert(new_clause);
            new_clause->appendLiteral(updating_literal, true);
        } else {
            updating_literal->neg_occ.insert(new_clause);
            new_clause->appendLiteral(updating_literal, false);
        }
    }
}

/**
 * creat a new clause
 * update all data structures
 * @param c a new clause in form of vector of literal_id
 */
void Clause::setNewClause(std::vector<int>& c) {
    auto* new_clause = new Clause(Clause::count);
    new_clause->updateStaticData();
    for (auto l : c) {
        Literal::setLiteral(l, new_clause);
    }
    new_clause->setWatchedLiterals();
}

/**
 * This heuristic choose clause with the smallest number of unassigned literals.
 * Value is chosen base on number of positive or negative occurrences.
 * @return A tuple of (pointer to chosen literal, value)
 */
std::tuple<Literal*, bool> Heuristic::MOM() {
    if (Printer::print_process) std::cout << "Using heuristic MOM" << "\n";

    Assignment::branching_heuristic = "MOM";
    // check all clauses for the shortest
    Clause* shortest_clause = nullptr;
    int shortest_width = INT_MAX;
    for (auto c : Clause::list) {
        int clause_actual_width = c->free_literals.size();
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
        for (auto l : shortest_clause->free_literals) {
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
* Return address of all literals in the clause
*/
std::unordered_set<Literal*> Clause::getAllLiterals() {
    std::unordered_set<Literal*> s;
    for (Literal* l : this->pos_literals_list) {
        s.insert(l);
    }
    for (Literal* l : this->neg_literals_list) {
        s.insert(l);
    }
    return s;
}

/**
 * Print all data saving in data structure Literal and Clause.
 * Function is not use if variable print_process is not set to "true";
 */
void Printer::printAllData() {
    for (auto t : Literal::id2Lit) {
        t.second->printData();
    }
    for (auto c : Clause::list) {
        c->printData();
    }
}

/**
 * Print assign values when SAT, branching variables or variables got flipped after backtracking.
 */
void Printer::printResult() {
    std::cout << "v ";
    int variable_per_line_count = 0;
    for (auto [bd, literal]: Literal::bd2BranLit) {
        if (variable_per_line_count == 5) {
            std::cout << "\n" << "v ";
            variable_per_line_count = 0;
        }
        if (literal->value == true) std::cout << literal->id << " ";
        else std::cout << -abs(literal->id) << " ";
        variable_per_line_count++;
    }
    std::cout << "\n" << "c" << "\n" << "v ";
    variable_per_line_count = 0;
    for (Literal* literal : Printer::flipped_literals) {
        if (variable_per_line_count == 5) {
            std::cout << "\n" << "v ";
            variable_per_line_count = 0;
        }
        if (literal->value == true) std::cout << literal->id << " ";
        else std::cout << -abs(literal->id) << " ";
        variable_per_line_count++;
    }
    std::cout << std::endl;
}


void Formula::preprocessing() {
    Formula::removeInitialUnitClauses();
    Formula::removeSATClauses();
}

/**
 * Any unit clause with one literal will have that literal assign value by force
 */
void Formula::removeInitialUnitClauses() {
    if (Printer::print_CDCL_process) std::cout << "Finding initial unit clauses ..." << "\n";
    for (auto c : Clause::list) {
        int literal_count = c->pos_literals_list.size() + c->neg_literals_list.size();
        if (literal_count == 1 && !c->free_literals.empty()) {
            Literal* l = *(c->free_literals.begin()); // Error if free_literals is empty by previous loops
            if (c->pos_literals_list.empty()) { // Only use this condition to finding suitable value in this case with initial unit clauses
                l->assignValueCDCL(false, Assignment::IsForced);
            }
            else {
                l->assignValueCDCL(true, Assignment::IsForced);
            }
        }
    }
    if (Clause::CONFLICT) {
        Formula::isUNSAT = true; // Conflict by initial unit clauses (all forced assignment) means unsatisfiable
    }
}

/**
 * Clauses having at least literal occur in both positive and negative are SAT by default and will be removed
 */
void Formula::removeSATClauses(){
    // check basic SAT condition
    // check a clause contain a literal both pos and neg
    if (Printer::print_CDCL_process) std::cout << "Finding initial SAT clauses..." << "\n";
    for (const auto& id2ad : Literal::id2Lit) {
        Literal* literal = id2ad.second;
        // a literal appear both pos and neg in a clause, that clause is alway SAT, can remove from the process.
        std::unordered_set<Clause*> intersect = findIntersection(literal->pos_occ, literal->neg_occ);
        if (!intersect.empty()) {
            for (Clause* c : intersect) {
                if (Printer::print_CDCL_process) std::cout << "Clause " << c->id << " is SAT." << "\n";
                c->deleteClause();
            }
        }
    }
}

/**
 * Set CONFLICT flag. Save the conflict clause.
 */
void Clause::reportConflict() {
    Clause::CONFLICT = true;
    Clause::conflict_clause = this;
    Formula::conflict_count++;
}
