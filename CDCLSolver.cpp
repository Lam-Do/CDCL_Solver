#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"

/**
 * Assign a assigning_value to the literal base on 2 watched literals structure of clauses.
 * All associated data structures will be updated accordingly.
 * Does not creating a new assignment object.
 * If the last free literal is another watched literal of the clause, the clause is unit clause and gets push to unit_queue
 * No free literal left but clause still is UNSAT, report conflict and break from loop
 * @param assigning_value Value assign to the literal
 */
void Literal::assignValueCDCL(bool assigning_value, bool status) {
    if (this->isFree) {
        this->isFree = false;
        this->value = assigning_value;
        this->branching_level = Assignment::bd;
        auto* new_assignment = new Assignment(status, this);
        new_assignment->updateStaticData();

        // Avoid duplicate literal in unit_queue by push to unordered_set
        std::unordered_set<Literal*> unit_queue_literals;
        if (assigning_value == true) {
            // Firstly remove this literal from free_literals list of clauses, then modify related data.
            for (auto clause : this->pos_occ) {
                clause->free_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->neg_occ) {
                clause->free_literals.erase(this);
                // if the clause is SAT by previously assigned literal, skip this clause
                if (clause->SAT) continue;
                // if there are no free literals and clause UNSAT, report CONFLICT
                if (clause->free_literals.empty()) {
                    clause->reportConflict();
                }
                // this literal is in neg_occ and is watched, meaning the clause is in neg_watched
                if (this->neg_watched_occ.contains(clause)) {
                    // Find another free literal b if two conditions above are not satisfied
                    if (clause->free_literals.size() == 1) { // only free literal left is the other watched literal
                        unit_queue_literals.insert((*clause->free_literals.begin()));
                        (*clause->free_literals.begin())->reason = clause;
                    } else { // >=2 free literals left
                        for (auto l : clause->free_literals) {
                            // find new watched literal
                            if (l != clause->watched_literal_1 && l != clause->watched_literal_2) { // l is not watched
                                Literal* new_watched_literal_b = l;
                                // set a new watched literal of the clause
                                if (this == clause->watched_literal_1) clause->watched_literal_1 = new_watched_literal_b;
                                else clause->watched_literal_2 = new_watched_literal_b;
                                // remove/add the clause from/to watched clause list of old/new literal
                                this->neg_watched_occ.erase(clause);
                                if (clause->pos_literals_list.contains(new_watched_literal_b)) new_watched_literal_b->pos_watched_occ.insert(clause);
                                else new_watched_literal_b->neg_watched_occ.insert(clause);
                                break;
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
                if (clause->SAT) continue;
                if (clause->free_literals.empty()) {
                    clause->reportConflict();
                }
                if (this->pos_watched_occ.contains(clause)) {
                    if (clause->free_literals.size() == 1) {
                        unit_queue_literals.insert((*clause->free_literals.begin()));
                        (*clause->free_literals.begin())->reason = clause;
                    } else {
                        for (auto l : clause->free_literals) {
                            if (l != clause->watched_literal_1 && l != clause->watched_literal_2) {
                                Literal* new_watched_literal_b = l;
                                if (this == clause->watched_literal_1) clause->watched_literal_1 = new_watched_literal_b;
                                else clause->watched_literal_2 = new_watched_literal_b;
                                this->pos_watched_occ.erase(clause); //***
                                if (clause->pos_literals_list.contains(new_watched_literal_b)) new_watched_literal_b->pos_watched_occ.insert(clause);
                                else new_watched_literal_b->neg_watched_occ.insert(clause);
                                break;
                            }
                        }
                    }
                }
            }
        }

        for (Literal* l : unit_queue_literals) {
            Literal::unit_queue.push(l);
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
 * branching_level got reset.
 * Choose the second watched literal for learned clauses
 */
void Literal::unassignValueCDCL() {
    this->setFree();

    // "reason" field is not reassigned to null
    // since it can remove the learned clause as "reason" from the source branching literal when learning cut
//    this->reason = nullptr;

    if (this->value == true) {
        for (auto clause : this->pos_occ) {
            clause->sat_by.erase(this);
            if (clause->sat_by.empty()) {
                clause->SAT = false;
            }
            clause->free_literals.insert(this);
            // Only learned clauses don't have second watched literal when reaching here.
            // Avoid mark the first watched literal second time.
            if (clause->watched_literal_1 != this && clause->watched_literal_2 == nullptr) {
                clause->watched_literal_2 = this;
            }
        }
        for (auto clause : this->neg_occ) {
            clause->free_literals.insert(this);
            if (clause->watched_literal_1 != this && clause->watched_literal_2 == nullptr) clause->watched_literal_2 = this;
        }
    } else {
        for (auto clause : this->neg_occ) {
            clause->sat_by.erase(this);
            if (clause->sat_by.empty()) {
                clause->SAT = false;
            }
            clause->free_literals.insert(this);
            if (clause->watched_literal_1 != this && clause->watched_literal_2 == nullptr) clause->watched_literal_2 = this;

        }
        for (auto clause : this->pos_occ) {
            clause->free_literals.insert(this);
            if (clause->watched_literal_1 != this && clause->watched_literal_2 == nullptr) clause->watched_literal_2 = this;
        }
    }
    this->branching_level = -1;
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
            // break out of loop if reach the source branching assignment
            if (stack.top()->status == Assignment::IsBranching) {
                current_cut.insert(stack.top()->assigned_literal);
                break;
            } else {
                // Go up the graph through edges (reason)
                std::unordered_set<Literal*> parent_vertexes = stack.top()->assigned_literal->reason->getAllLiterals();
                parent_vertexes.erase(stack.top()->assigned_literal);
                current_cut.erase(stack.top()->assigned_literal);
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
/**
 * Cut will be parsed to data structure. New clause is created with watched literals, but without calling setNewClause().
 * Literal with max depth will be pushed to unit_queue
 * Update asserting_level for backtracking use.
 * @param cut
 */
void Clause::learnCut(const std::unordered_set<Literal *>& cut) {
    //empty unit clause queue
    while (!Literal::unit_queue.empty()) {
        Literal::unit_queue.pop();
    }
    // Creat new learned Clause
    auto* new_clause = new LearnedClause(Clause::count);
    new_clause->updateLearnedStaticData();

    // the second-largest branching depth of literals in cut
    Clause::learned_clause_assertion_level = 0;
    for (Literal* l : cut) {
        // learn flipped value of literal and add to new_clause. Ex: Old value is "true" -> set variable in new_clause as negative literal
        if (l->value == true) {
            Literal::setLiteral(-abs(l->id), new_clause);
        } else {
            Literal::setLiteral(abs(l->id), new_clause);
        }
        // update assertion level
        if (l->branching_level < Assignment::bd && l->branching_level > Clause::learned_clause_assertion_level) {
            Clause::learned_clause_assertion_level = l->branching_level;
        } else if (l->branching_level == Assignment::bd) {
            // enqueue new learn clause as unit clause, literal with the highest depth (the old branching literal) is push to unit_queue
            Literal::unit_queue.push(l);
            l->reason = new_clause;
            new_clause->watched_literal_1 = l; // mark first watched literal, second one is assigned later by first time unassigned
            if (Printer::print_max_depth_literal) {
                l->printData();
                std::cout<< "has depth " << l->branching_level << "\n";
                std::cout << "Max depth " << Assignment::bd << "\n";
                std::cout << "Assertion level" << Clause::learned_clause_assertion_level << "\n";
            }
        }
        l->learned_count++;
    }
    if (Printer::print_learned_clause) {
        new_clause->printData();
        std::cout << new_clause->getAllLiterals().size() << "\n";
    }
}

/**
 * Should be called immediately after analyzing conflict. Could be skipped if UNSAT flag is raised by conflictAnalyze()
 * Assignment stack will be pop all assignment with depth > asserting level d of the learn clause (non-chronological backtracking)
 * Literals will be unassigned accordingly.
 */

void Assignment::backtrackingCDCL() {
    // pop all forced assignment, stop at last branchingDPLL assignment or stack empty
    while (!Assignment::stack.empty() && Assignment::stack.top()->assigned_literal->branching_level > Clause::learned_clause_assertion_level) {
        Assignment* top_assignment = Assignment::stack.top();
        if (top_assignment->status == Assignment::IsBranching) {
            Literal::bd2BranLit.erase(top_assignment->assigned_literal->branching_level);
        }
        top_assignment->assigned_literal->unassignValueCDCL();
        Assignment::stack.pop();
//        delete top_assignment;
    }
    /**
     * branching literal has highest depth bd which always > asserting level, is popped in while loop
     * Tracking old value of branching literal and emptying unit_queue are done by learnCut()
     * assigning flipped value is done by unitPropagation
     */

    // backtracking successfully
    Assignment::bd = Clause::learned_clause_assertion_level;
    Clause::CONFLICT = false;
    Clause::conflict_clause = nullptr;
    if (Printer::print_process) std::cout << "Backtracking successfully" << "\n";
}

void Clause::unitPropagationCDCL() {
    if (Printer::print_CDCL_process) std::cout << "Unit propagating..." << "\n";
    while (!(Literal::unit_queue.empty()) && !Clause::CONFLICT) {
        Literal* next_literal = Literal::unit_queue.front();
        Literal::unit_queue.pop();
        Clause* unit_clause = next_literal->reason;
        // check literal is positive or negative in the unit clause to assign fitting value
        if (unit_clause->pos_literals_list.count(next_literal) >= 1) {
            next_literal->assignValueCDCL(true, Assignment::IsForced);
        } else {
            next_literal->assignValueCDCL(false, Assignment::IsForced);
        }
        if (Printer::print_assignment) std::cout << "Literal " << next_literal->id << " forcing " << next_literal->value << "\n";
    }
}

/**
 * Set up 2 watched literals for clause. If it's unit clause, push to unit_queue.
 * Also remove clause with 2 literals of the same variable
 */
void Clause::setWatchedLiterals() {
    int clause_size = this->pos_literals_list.size() + this->neg_literals_list.size();
    if (clause_size >= 2) {
        if (this->free_literals.size() >= 2) {
            // Choose 2 random watched literals for the clause
            if (!this->SAT && clause_size >= 2) { // Only SATable by prepocessing(),
                this->watched_literal_1 = *(this->free_literals.begin()); // randomly access due to unordered
                std::unordered_set<Literal*> unwatched_free_literals = this->free_literals;
                unwatched_free_literals.erase(this->watched_literal_1);
                this->watched_literal_2 = *(unwatched_free_literals.begin());
            }
            // Add clause address to pos/neg_watched_occ of watched literals
            if (this->pos_literals_list.contains(this->watched_literal_1)) {
                this->watched_literal_1->pos_watched_occ.insert(this);
            } else {
                this->watched_literal_1->neg_watched_occ.insert(this);
            }
            if (this->pos_literals_list.contains(this->watched_literal_2)) {
                this->watched_literal_2->pos_watched_occ.insert(this);
            } else {
                this->watched_literal_2->neg_watched_occ.insert(this);
            }
        } else if (this->free_literals.size() == 1) { // Clause's width = 2 with 1 free_literal: a v -a
            this->deleteClause();
        }
    }
}

void Assignment::branchingCDCL() {
    if (Printer::print_process) std::cout << "Start branchingCDCL " << "\n";

    Assignment::bd++;
    Formula::branching_count++;
    // VSIDS heuristic
    if (Formula::branching_count == 250) {
        Literal::updatePriorities();
        Formula::branching_count = 0;
    }
    std::tuple<Literal*, bool> t = Heuristic::VSIDS();
//    if (Assignment::branching_heuristic == "BerkMin") t = Heuristic::BerkMin();
//    if (Assignment::branching_heuristic == "VMTF") t = Heuristic::VMTF();
    Literal* branching_literal = std::get<0>(t);
    bool assigning_value = std::get<1>(t);
    if (std::get<0>(t) != nullptr) {
        branching_literal->assignValueCDCL(assigning_value, Assignment::IsBranching);
        // some update for literal
        branching_literal->reason = nullptr; // branching literal has no parent vertexes
        Literal::bd2BranLit[Assignment::bd] = branching_literal;
        if (Printer::print_assignment) std::cout << "Literal " << branching_literal->id << " branching" << branching_literal->value << "\n";
        if (Printer::print_process) std::cout << "Finished branchingCDCL " << std::endl;
    }
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
    if (maximal_bd_literal_count == 1) return true;
    else {
        std::cerr << "Cut contain no literal with max bd" << std::endl;
        return true;
    }
}

std::tuple<Literal*, bool> Heuristic::VSIDS() {
    Literal *chosen_literal = nullptr;
    bool value = false;
    std::priority_queue<Literal *, std::vector<Literal *>, Literal::Compare> queue = Literal::pq;
    // Find the most prioritized free literal
    while (!queue.top()->isFree && !queue.empty()) {
        queue.pop();
    }
    if (!queue.empty()) {
        chosen_literal = queue.top();

    // Choose value with more actual occur
        if (chosen_literal->getActualPosOcc(INT_MAX) >= chosen_literal->getActualNegOcc(INT_MAX)) value = true;
        else value = false;
    } else {
        if (Printer::print_CDCL_process) {
            std::cout << "Can't branching, all literals are assigned." << "\n";
            Printer::printAssignmentStack();
        }
    }
    return std::make_tuple(chosen_literal, value);
}

//std::tuple<Literal*, bool> Heuristic::BerkMin() {
//    std::tuple<Literal*, bool> t;
//    // TODO
//    return t;
//}
//
//std::tuple<Literal*, bool> Heuristic::VMTF() {
//    std::tuple<Literal*, bool> t;
//    // TODO
//    return t;
//}

void LearnedClause::updateLearnedStaticData() {
    Clause::count++;
    Clause::list.insert(this);
    LearnedClause::learned_list.insert(this);
}

void LearnedClause::setWatchedLiteral(Literal * l) {
    if (this->watched_literal_1 == nullptr) this->watched_literal_1 = l;
    if (this->watched_literal_2 == nullptr && this->watched_literal_1 != l) this->watched_literal_2 = l;
}

void Literal::updatePriorities() {
    // Empty priority queue
    while (!Literal::pq.empty()) {
        Literal::pq.pop();
    }
    for (auto [id, literal] : Literal::id2Lit) {
        // Update
        literal->prioty_level = literal->prioty_level / 2 + literal->learned_count;
        literal->learned_count = 0;
        // Push back to queue for re-sorting base on literals' new priority
        Literal::pq.push(literal);
    }
}

void Literal::deleteLiteral() {
    // TODO
}


void Clause::deleteClause() {
    // Update literals
    for (Literal* l : this->pos_literals_list) {
        l->pos_occ.erase(this);
        if (this->watched_literal_1 == l || this->watched_literal_2 == l) {
            l->pos_watched_occ.erase(this);
        }
        if (this == l->reason) l->reason = nullptr;
    }
    for (Literal* l : this->neg_literals_list) {
        l->neg_occ.erase(this);
        if (this->watched_literal_1 == l || this->watched_literal_2 == l) {
            l->neg_watched_occ.erase(this);
        }
        if (this == l->reason) l->reason = nullptr;
    }
    this->SAT = true;
    if (Clause::conflict_clause == this) Clause::conflict_clause = nullptr;
    Clause::list.erase(this);
}

void LearnedClause::deleteLearnedClause() {
    this->deleteClause();
    LearnedClause::learned_list.erase(this);
}

void Formula::restart() {

}