#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"


void Literal::assignValueCDCL(bool value, bool status) {
    if (this->isFree == true) { // avoid redundant when same literal got appended to unit_queue twice and is getting assigned twice
        this->isFree = false;
        this->value = value;
        this->branching_level = Assignment::bd;
        if (status != Assignment::isForced) {
            this->reason = nullptr; // default reason is nullptr if not be pushed to unit_queue.
        }

        auto* new_assignment = new Assignment(status, this);
        new_assignment->updateStaticData();

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
                    // if there are no free literals and clause UNSAT, report conflict
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

void Literal::unassignValueCDCL() {
    // No different from DPLL
    this->unassignValueDPLL();
    this->branching_level = -1;
}

/**
 * Set conflict flag
 */
void Clause::reportConflict() {
    Clause::conflict = true;
    Clause::conflict_clause = this;
}

void Clause::conflictAnalyze() {
    std::unordered_set<Literal*> current_cut = Clause::conflict_clause->getAllLiterals();

    // Find literals with the lowest depth in the cut for later tracking up
    int max_depth_in_cut = -1;
    std::unordered_set<Literal*> max_depth_literals_in_cut;
    for (Literal* l : current_cut) {
        if (l->branching_level >= max_depth_in_cut) {
            max_depth_in_cut = l->branching_level;
            max_depth_literals_in_cut.insert(l);
        }
    }
    // Follow the deepest literals through their edges to parent vertexes then creating new cut
    for (Literal* C_literal : max_depth_literals_in_cut) {
        std::unordered_set<Literal*> edges_of_C_literal = C_literal->reason->getAllLiterals();
        for (Literal* B_literal : edges_of_C_literal) {
            current_cut.insert(B_literal);
        }
        current_cut.erase(C_literal); // remove the literal that is used for tracking up the graph
    }
    // With current_cut is updated to new one, check for asserting property
    int deepest_literal_count = 0;
    for (Literal* l : current_cut) {
        if (l->branching_level == Assignment::bd) deepest_literal_count++;
    }
    if (deepest_literal_count == 1) {
        Clause::learnCut(current_cut);
    }
}

void Assignment::backtrackingCDCL() {
    // TODO: backtracking

    Clause::conflict = false;
    Clause::conflict_clause = nullptr;
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
    Assignment::branching_heuristic = "";
    Assignment::bd++;
    // TODO: branching here

    if (Printer::print_process) std::cout << "Finished branchingCDCL " << std::endl;
}

void Clause::unitPropagationCDCL() {
    // TODO: unitPropagating

}

void Clause::learnCut(std::unordered_set<Literal *> cut) {

}