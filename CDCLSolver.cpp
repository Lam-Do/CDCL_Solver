#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"


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

void Literal::unassignValueCDCL() {
    // No different from DPLL
    this->unassignValueDPLL();
    this->branching_level = -1;
    //TODO more unassign
    //this->reason = nullptr;

}

/**
 * Set CONFLICT flag
 */
void Clause::reportConflict() {
    Clause::CONFLICT = true;
    Clause::conflict_clause = this;
}

void Clause::conflictAnalyze() {
    std::unordered_set<Literal*> current_cut = Clause::conflict_clause->getAllLiterals(); // initial cut is the conflicted clause
    int tracking_bd = Assignment::bd; // bd level for pushing up the cut in the graph, initial value is bd of CONFLICT, which should be actual bd
    if (Literal::bd2BranLit.empty()) {
        Formula::isUNSAT = true; // CONFLICT when there are no branching (all forced assignments) means formula unsatisfiable
    } else {
        while (!Clause::isBranchingCut(current_cut) && tracking_bd > 0) {
            // Find vertexes with the tracking bd level in the cut
            std::unordered_set<Literal*> tracking_vertexes_in_cut;
            for (Literal* l : current_cut) {
                if (l->branching_level == tracking_bd) {
                    tracking_vertexes_in_cut.insert(l);
                }
            }
            if (tracking_vertexes_in_cut.empty()) {
                // Find the next biggest bd for tracking up the graph
                int new_tracking_bd = 0;
                for ( Literal* l : current_cut) {
                    if (l->branching_level < tracking_bd && l->branching_level > new_tracking_bd) {
                        new_tracking_bd = l->branching_level;
                    }
                }
                // update tracking bd and go to the next loop
                tracking_bd = new_tracking_bd;
            } else {
                // Follow the vertexes which are being tracked through their edges to parent vertexes then creating new cut
                for (Literal* C_vertex : tracking_vertexes_in_cut) {
                    std::unordered_set<Literal*> B_vertexes = C_vertex->reason->getAllLiterals(); // get to B side vertexes through edges represented by "reason" field
                    B_vertexes.erase(C_vertex); // remove the vertex that is used for tracking up the graph since "reason" clause also include C_vertex
                    for (Literal* vertex : B_vertexes) {
                        current_cut.insert(vertex);
                    }
                }
                // With current_cut is updated to new one, check for asserting property
                int maximal_bd_literal_count = 0;
                for (Literal* l : current_cut) {
                    if (l->branching_level == Assignment::bd) maximal_bd_literal_count++;
                    if (maximal_bd_literal_count > 1) break;
                }
                // learn asserting clause
                if (maximal_bd_literal_count == 1) {
                    Clause::learnCut(current_cut);
                }
            }

        }
    }
}

void Assignment::backtrackingCDCL() {
    // TODO: backtracking

    Clause::CONFLICT = false;
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
    // TODO: branching here
    Assignment::bd++;
    Formula::branching_count++;
    std::tuple<Literal*, bool> t;
    if (Assignment::branching_heuristic == "VSIDS") t = Heuristic::VSIDS();
    if (Assignment::branching_heuristic == "BerkMin") t = Heuristic::BerkMin();
    if (Assignment::branching_heuristic == "VMTF") t = Heuristic::VMTF();
    Literal* branching_literal = std::get<0>(t);
    bool assigning_value = std::get<1>(t);
    if (std::get<0>(t) != nullptr) branching_literal->assignValueCDCL(assigning_value); // only assign if find a literal
    // update literal
    branching_literal->reason = nullptr; // default reason should be already nullptr if not be pushed to unit_queue.
    Literal::bd2BranLit[Assignment::bd] = branching_literal;
    // new assignment
    auto* new_assignment = new Assignment(Assignment::IsBranching, branching_literal);
    new_assignment->updateStaticData();

    if (Printer::print_process) std::cout << "Finished branchingCDCL " << std::endl;
}

void Clause::unitPropagationCDCL() {
    // TODO: unitPropagating

}

void Clause::learnCut(std::unordered_set<Literal *> cut) {
    // TODO: cut to new learn clause
}
/**
 * Test if the cut the highest possible in the graph, meaning all vertexes in branching side (B side) are source vertexes with edges to cutting side (C side)
 * @param cut A cut represent by a set of literal
 * @return true if all literals in cut are branching, false otherwise
 */
bool Clause::isBranchingCut(const std::unordered_set<Literal *>& cut) {
    for (Literal* l : cut) {
        bool l_is_branching_source = Literal::bd2BranLit[l->branching_level] == l; // If l is branching literal, l is in bd2BranLit dict as a branching literal
        if (!l_is_branching_source) {
            return false;
        }
    }
    return true;
}

std::tuple<Literal*, bool> Heuristic::VSIDS() {
    std::tuple<Literal*, bool> t;

    return t;
}

std::tuple<Literal*, bool> Heuristic::BerkMin() {
    std::tuple<Literal*, bool> t;

    return t;
}

std::tuple<Literal*, bool> Heuristic::VMTF() {
    std::tuple<Literal*, bool> t;

    return t;
}