#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"

/**
 * Assign a value to the literal base on 2 watched literals structure of clauses.
 * All associated data structures will be updated accordingly.
 * Does not creating a new assignment object.
 * If the last free literal is another watched literal of the clause, the clause is unit clause and gets push to unit_queue
 * No free literal left but clause still is UNSAT, report conflict and break from loop
 * @param value Value assign to the literal
 */
void Literal::assignValueCDCL(bool value) {
    if (this->isFree) { // avoid redundant when same literal got appended to unit_queue twice and is getting assigned twice
        this->isFree = false;
        this->value = value;
        this->branching_level = Assignment::bd;

        if (value == true) {
            // Firstly remove this literal from free_literals list of clauses, then modify related data.
            for (auto clause : this->pos_occ) {
                clause->free_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->neg_occ) {
                clause->free_literals.erase(this);
                // this literal is in neg_occ and is watched
                if (this == clause->watched_literal_1 || this == clause->watched_literal_2) {
                    // if the clause is SAT by previously assigned literal, skip this clause
                    if (clause->SAT) continue;
                    // if there are no free literals and clause UNSAT, report CONFLICT
                    if (clause->free_literals.empty()) {
                        clause->reportConflict();
                        break;
                    }
                    // Find another free literal b if two conditions above are not satisfied
                    if (clause->free_literals.size() == 1) { // only free literal left is the other watched literal
                        Literal::unit_queue.push((*clause->free_literals.begin()));
                        (*clause->free_literals.begin())->reason = clause;
                    } else { // >=2 free literals left
                        for (auto l : clause->free_literals) {
                            if (l != clause->watched_literal_1 && l != clause->watched_literal_2) { // l is not watched
                                Literal* new_watched_literal_b = l;
                                // set a new watched literal of the clause
                                if (this == clause->watched_literal_1) clause->watched_literal_1 = new_watched_literal_b;
                                else clause->watched_literal_2 = new_watched_literal_b;
                                // remove/add the clause from/to watched clause list of old/new literal
                                this->neg_watched_occ.erase(clause);
                                if (clause->pos_literals_list.contains(new_watched_literal_b)) new_watched_literal_b->pos_watched_occ.insert(clause);
                                else new_watched_literal_b->neg_watched_occ.insert(clause);
                            }
                        }
                    }
                }
            }

        } else { // Same as above with opposite occur list, changes are highlight with //***
            for (auto clause : this->neg_occ) { //***
                clause->free_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->pos_occ) { //***
                clause->free_literals.erase(this);
                if (this == clause->watched_literal_1 || this == clause->watched_literal_2) {
                    if (clause->SAT) continue;
                    if (clause->free_literals.empty()) {
                        clause->reportConflict();
                        break;
                    }
                    if (clause->free_literals.size() == 1) {
                        Literal::unit_queue.push((*clause->free_literals.begin()));
                        (*clause->free_literals.begin())->reason = clause;
                    } else {
                        for (auto l : clause->free_literals) {
                            if (l != clause->watched_literal_1 && l != clause->watched_literal_2) {
                                Literal* new_watched_literal_b = l;
                                if (this == clause->watched_literal_1) clause->watched_literal_1 = new_watched_literal_b;
                                else clause->watched_literal_2 = new_watched_literal_b;
                                this->pos_watched_occ.erase(clause);
                                if (clause->pos_literals_list.contains(new_watched_literal_b)) new_watched_literal_b->pos_watched_occ.insert(clause);
                                else new_watched_literal_b->neg_watched_occ.insert(clause);
                            }
                        }
                    }
                }
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
}

/**
 * Unassigning value the literal.
 * Data of related clauses with be updated. Clauses will not be set to UNSAT as long as there is a literal in sat_by list.
 * branching_level and reason field got reset.
 */
void Literal::unassignValueCDCL() {
    // No different from DPLL
    this->unassignValueDPLL();
    this->branching_level = -1;
    this->reason = nullptr;
}

/**
 * Analyze the conflict by finding a fitting 1UIP scheme cut in the assignment graph, the graph represented by "value", "branching_depth" and "reason" field of Literal class.
 * No branching assignment will set up UNSAT flag.
 * The cut is represented by list of variable, positive or negative literals is determined when learning.
 * Learn the cut by add clause with flipped value of literals.
 */
void Clause::conflictAnalyze() {
    if (Literal::bd2BranLit.empty()) {
        Formula::isUNSAT = true; // CONFLICT when there are no branching (all forced assignments) means formula unsatisfiable
    } else {
        std::unordered_set<Literal*> current_cut = Clause::conflict_clause->getAllLiterals(); // initial cut is the conflicted clause
        std::stack<Assignment*> stack = Assignment::stack; // making a copy to modify, keeping original assignments history for later unassignValue in backtracking
        while (!Clause::isAsserting(current_cut)) {
            // Redundant case, cut should be asserting before reach here
            // break out of loop if reach the source branching
            if (stack.top()->status == Assignment::IsBranching) {
                current_cut.insert(stack.top()->assigned_literal);
                break;
            } else {
                // Go up the graph through edges (reason)
                std::unordered_set<Literal*> parent_vertexes = stack.top()->assigned_literal->reason->getAllLiterals();
                parent_vertexes.erase(stack.top()->assigned_literal);
                stack.pop();// remove top assignment for next loop

                // Resolving current_cut with new parent_vertexes
                for (Literal* vertex : parent_vertexes) {
                    current_cut.insert(vertex);
                }
            }
        }
        // learn asserting clause
        Clause::learnCut(current_cut);
    }
}

void Clause::learnCut(const std::unordered_set<Literal *>& cut) {
    //empty unit clause queue
    while (!Literal::unit_queue.empty()) {
        Literal::unit_queue.pop();
    }

    auto* new_clause = new LearnedClause(Clause::count);
    new_clause->updateLearnedStaticData();

    // the second-largest branching depth of literals in cut
    Clause::learned_clause_assertion_level = 0;
    for (Literal* l : cut) {
        // update assertion level
        if (l->branching_level < Assignment::bd && l->branching_level > Clause::learned_clause_assertion_level) {
            Clause::learned_clause_assertion_level = l->branching_level;
        } else if (l->branching_level == Assignment::bd) {
            // enqueue new learn clause as unit clause, literal with the highest depth (the old branching literal) is push to unit_queue
            Literal::unit_queue.push(l);
            l->reason = new_clause;
        }
        // learn flipped value of literal and add to new_clause. Ex: Old value is "true" -> set variable in new_clause as negative literal
        if (l->value == true) {
            Literal::setLiteral(-abs(l->id), new_clause);
        } else {
            Literal::setLiteral(abs(l->id), new_clause);
        }
    }
    // TODO: update learned clause fields

}

/**
 * Should be called immediately after analyzing conflict. Could be skipped if UNSAT flag is raised by conflictAnalyze()
 * Assignment stack will be pop all assignment with depth > asserting level d of the learn clause (non-chronological backtracking)
 * Literals will be unassigned accordingly.
 */

void Assignment::backtrackingCDCL() {
    // pop all forced assignment, stop at last branchingDPLL assignment or stack empty
    while (!Assignment::stack.empty() && Assignment::stack.top()->assigned_literal->branching_level > Clause::learned_clause_assertion_level) {
        Assignment::stack.top()->assigned_literal->unassignValueCDCL();
        Assignment::stack.pop();
    }
    if (Assignment::stack.empty()) { // redundant case since stack is empty only when there are no branching, this should be checked by conflictAnalyze()
        Formula::isUNSAT = true;
    } else {
        /**
         * branching literal has highest depth bd which always > asserting level, is popped in while loop
         * Tracking old value branching literal and empty unit_queue are done by learnCut()
         * assigning flipped value is done by unitPropagation
         */

        // backtracking successfully
        if (Printer::print_process) std::cout << "Backtracking successfully" << "\n";
        Assignment::bd = Clause::learned_clause_assertion_level;
        Clause::CONFLICT = false;
        Clause::conflict_clause = nullptr;
    }
}

void Clause::unitPropagationCDCL() {
    // TODO: unitPropagating, add new assignment here instead of in assignValue()

}

/**
 * Set up 2 watched literals for all clauses
 */
void Clause::setWatchedLiterals() {
    for (auto* c : Clause::list) {
        // Choose 2 watched literals for each clause
        int clause_size = c->pos_literals_list.size() + c->neg_literals_list.size();
        if (!c->SAT && clause_size >= 2) { // Only SATable by simplify(),
            c->watched_literal_1 = *(c->free_literals.begin()); // randomly access due to unordered
            std::unordered_set<Literal*> unwatched_free_literals = c->free_literals;
            unwatched_free_literals.erase(c->watched_literal_1);
            c->watched_literal_2 = *(unwatched_free_literals.begin());
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

void Assignment::branchingCDCL() {
    if (Printer::print_process) std::cout << "Start branchingCDCL " << "\n";
    Assignment::bd++;
    Formula::branching_count++;
    std::tuple<Literal*, bool> t;
    if (Assignment::branching_heuristic == "VSIDS") t = Heuristic::VSIDS();
    if (Assignment::branching_heuristic == "BerkMin") t = Heuristic::BerkMin();
    if (Assignment::branching_heuristic == "VMTF") t = Heuristic::VMTF();
    Literal* branching_literal = std::get<0>(t);
    bool assigning_value = std::get<1>(t);
    if (std::get<0>(t) != nullptr) branching_literal->assignValueCDCL(assigning_value); // only assign if find a literal
    // some update for literal
    branching_literal->reason = nullptr; // default reason should be already nullptr if not be pushed to unit_queue.
    Literal::bd2BranLit[Assignment::bd] = branching_literal;
    // new assignment
    auto* new_assignment = new Assignment(Assignment::IsBranching, branching_literal);
    new_assignment->updateStaticData();

    if (Printer::print_process) std::cout << "Finished branchingCDCL " << std::endl;
}

/**
 * Test if the cut the highest possible in the graph,
 * meaning all vertexes in branching side (B side) are source vertexes with edges to cutting side (C side).
 * This is the chosen learning cut for decision scheme, but worst-case for RelSAT and 1UIP scheme
 * @param cut A cut represent by a set of literal
 * @return true if all literals in cut are branching, false otherwise
 */
bool Clause::isDecisionCut(const std::unordered_set<Literal *>& cut) {
    for (Literal* l : cut) {
        // If l is branching literal, l is in bd2BranLit dict as a branching literal
        bool l_is_branching_source = Literal::bd2BranLit[l->branching_level] == l;
        if (!l_is_branching_source) {
            return false;
        }
    }
    return true;
}

bool Clause::isAsserting(const std::unordered_set<Literal *>& cut) {
    int maximal_bd_literal_count = 0;
    for (Literal* l : cut) {
        if (l->branching_level == Assignment::bd) maximal_bd_literal_count++;
        if (maximal_bd_literal_count > 1) return false;
    }
    return true;
}

std::tuple<Literal*, bool> Heuristic::VSIDS() {
    std::tuple<Literal*, bool> t;
    // TODO
    return t;
}

std::tuple<Literal*, bool> Heuristic::BerkMin() {
    std::tuple<Literal*, bool> t;
    // TODO
    return t;
}

std::tuple<Literal*, bool> Heuristic::VMTF() {
    std::tuple<Literal*, bool> t;
    // TODO
    return t;
}

void LearnedClause::updateLearnedStaticData() {
    Clause::count++;
    Clause::list.emplace_back(this);
    LearnedClause::learned_list.emplace_back(this);
    // TODO: further update static data if necessary
}