#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"


void Literal::assignValueCDCL(bool value, bool status) {
    if (this->isFree == true) { // avoid redundant when same literal got appended to unit_queue twice and is getting assigned twice
        this->isFree = false;
        this->value = value;

        auto* new_assignment = new Assignment(status, this);
        new_assignment->updateStaticData();

        if (value == true) {
            // Firstly remove this literal from unset_literals list of clauses, then modify related data.
            for (auto clause : this->pos_occ) {
                clause->unset_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->neg_occ) {
                clause->unset_literals.erase(this);
                // this literal is in neg_occ and is watched
                if (this == clause->watched_literal_1 || this == clause->watched_literal_2) {
                    // if the clause is SAT by previously assigned literal, skip this clause
                    if (clause->SAT) continue;
                    // if there are no free literals and clause UNSAT, report conflict
                    if (clause->unset_literals.empty()) {
                        clause->reportConflict();
                        break;
                    }
                    // Find another free literal b if two conditions above are not satisfied
                    if (clause->unset_literals.size() == 1) { // only free literal left is the other watched literal
                        Literal::unit_queue.push((*clause->unset_literals.begin()));
                        (*clause->unset_literals.begin())->reason = clause;
                    } else { // >=2 free literals left
                        for (auto l : clause->unset_literals) {
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
                clause->unset_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->pos_occ) { //***
                clause->unset_literals.erase(this);
                if (this == clause->watched_literal_1 || this == clause->watched_literal_2) {
                    if (clause->SAT) continue;
                    if (clause->unset_literals.empty()) {
                        clause->reportConflict();
                        break;
                    }
                    if (clause->unset_literals.size() == 1) {
                        Literal::unit_queue.push((*clause->unset_literals.begin()));
                        (*clause->unset_literals.begin())->reason = clause;
                    } else {
                        for (auto l : clause->unset_literals) {
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
}

void Assignment::backtrackingCDCL() {

}
void Clause::reportConflict() {
    Clause::conflict = true;
}

/**
 * Set up 2 watched literals for clauses
 */
void Clause::setWatchedLiterals() {
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