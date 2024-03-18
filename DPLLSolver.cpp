#include <iostream>
#include <ostream>
#include <algorithm>
#include "SATSolver.h"

/**
 * Assign a value to the literal.
 * A New object of assignment class will also be creat here.
 * All associated data will be update accordingly.
 * After data updated, new appear unit UNSAT clauses will have the last literal push to unit_queue.
 * Clauses with no free literal left but still UNSAT will trigger CONFLICT flag.
 * @param value Value assign to the literal
 * @param status "true" if by force or "false" if branchingDPLL
 */
void Literal::assignValueDPLL(bool value, bool status) {
    // assign value and free status
    // literals could be pushed to unit_queue more than once when they are the last unset literal of more than one clauses.
    // do nothing, skip assigning value process if the literal is not free
    if (this->isFree == true) {
        this->isFree = false;
        this->value = value;
        auto* new_assignment = new Assignment(status, this);
        new_assignment->updateStaticData();

        // change data in related clauses accordingly to occurrence
        if (value == true) {
            for (auto clause : this->pos_occ) {
                clause->free_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->neg_occ) {
                clause->free_literals.erase(this);
                if (clause->getUnsetLiteralsCount() == 1 && !clause->SAT) {
                    auto free_literal = *(clause->free_literals.begin()); // Last unset literal of this clause after assign this literal
                    Literal::unit_queue.push(free_literal);
                    free_literal->reason = clause;
                }
                if (clause->getUnsetLiteralsCount() == 0 && !clause->SAT) {
                    //report CONFLICT when a clause has no free literal but still UNSAT
                    Clause::CONFLICT = true;
                }
            }
        } else {
            for (auto clause : this->neg_occ) {
                clause->free_literals.erase(this);
                clause->SAT = true;
                clause->sat_by.insert(this);
            }
            for (auto clause : this->pos_occ) {
                clause->free_literals.erase(this);
                if (clause->getUnsetLiteralsCount() == 1 && !clause->SAT) {
                    auto free_literal = *(clause->free_literals.begin());
                    Literal::unit_queue.push(free_literal); //
                    free_literal->reason = clause;
                }
                if (clause->getUnsetLiteralsCount() == 0 && !clause->SAT) {
                    // check SAT status, if unSAT report CONFLICT
                    Clause::CONFLICT = true;
                }
            }
        }
    }
}

/**
 * Unassigning value the literal.
 * Data of related clauses with be updated. Clauses will not be set to UNSAT as long as there is a literal in sat_by list.
 */
void Literal::unassignValueDPLL() {
    this->setFree();
    this->reason = nullptr;
    if (this->value == true) {
        for (auto clause : this->pos_occ) {
            clause->sat_by.erase(this);
            if (clause->sat_by.empty()) {
                clause->SAT = false;
            }
            clause->free_literals.insert(this);
        }
        for (auto clause : this->neg_occ) {
            clause->free_literals.insert(this);
        }
    } else {
        for (auto clause : this->neg_occ) {
            clause->sat_by.erase(this);
            if (clause->sat_by.empty()) {
                clause->SAT = false;
            }
            clause->free_literals.insert(this);
        }
        for (auto clause : this->pos_occ) {
            clause->free_literals.insert(this);
        }
    }
}

/**
 * Backtracking in case CONFLICT flag is raised.
 * Print all assigned literals.
 * The stack which use to store assigning data will be pop until found an assignment by branchingDPLL, else raise UNSAT flag that signal ending process
 * Literals will be unassigned its value in process.
 */
void Assignment::backtrackingDPLL() {
    // Some outputs to console, don't have effect upon solving process
    if (Assignment::enablePrintAll) {
        std::cout << "\n";
        std::cout << "----------------" << "\n";
    }
    Assignment::printAll();

    // pop all forced assignment, stop at last branchingDPLL assignment or stack empty
    while (!Assignment::stack.empty() && Assignment::stack.top()->status) {
        Assignment::stack.top()->assigned_literal->unassignValueDPLL();
        Assignment::stack.pop();
    }

    // branching -> forced
    if (!Assignment::stack.empty()) {
        // Save value of the top assignment before assigning new one which push a new assignment to top of stack
        Literal* top_literal = Assignment::stack.top()->assigned_literal;
        bool old_value = top_literal->value;

        top_literal->unassignValueDPLL();
        Assignment::stack.pop();
        //empty unit clause queue
        while (!Literal::unit_queue.empty()) {
            Literal::unit_queue.pop();
        }
        // assign opposite value
        top_literal->assignValueDPLL(!old_value, Assignment::IsForced); // no need to push new assignment here since assignValueDPLL() does it.
        Clause::CONFLICT = false; // remove CONFLICT flag
    } else {
        Formula::isUNSAT = true; // flag UNSAT in case stack is empty meaning all assignments is forced and there isn't any another branch
    }

}

/**
 * Branching in case unit_queue is empty (no unit clause), no CONFLICT, no SAT or UNSAT flag.
 * Function using heuristics to choose a literal then assign value.
 */
void Assignment::branchingDPLL() {
    if (Printer::print_process) std::cout << "Start branchingDPLL " << "\n";
    Assignment::branching_heuristic = "MOM";
    std::tuple<Literal*, bool> t = Heuristic::MOM(); // use MOM heuristic to choose branchingDPLL literal
    if (std::get<0>(t) != nullptr) std::get<0>(t)->assignValueDPLL(std::get<1>(t), Assignment::IsBranching); // only assign if find a literal
    if (Printer::print_process) std::cout << "Finished branchingDPLL " << std::endl;
}

/**
 * find and propagate all literal in unit_queue and assign value to these literal by force
 */
void Clause::unitPropagationDPLL() {
    if (Printer::print_process) std::cout << "Unit propagating..." << "\n";
    while (!(Literal::unit_queue.empty()) && !Clause::CONFLICT) {
        Literal* next_literal = Literal::unit_queue.front();
        Literal::unit_queue.pop();
        Clause* unit_clause = next_literal->reason;
        // check if the literal is positive or negative in the unit clause to assign fitting value
        if (unit_clause->pos_literals_list.count(next_literal) == 1) {
            next_literal->assignValueDPLL(true, Assignment::IsForced);
        } else {
            next_literal->assignValueDPLL(false, Assignment::IsForced);
        }
    }
}