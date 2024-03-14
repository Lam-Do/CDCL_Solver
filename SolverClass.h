#ifndef CDCL_SOLVER_SOLVERCLASS_H
#define CDCL_SOLVER_SOLVERCLASS_H

#include <vector>
#include <stack>
#include <tuple>
#include <unordered_set>
#include <queue>
#include <algorithm>
#include <unordered_map>
#include <climits>

class Clause;
class Literal;
struct Assignment;

class Literal {
public:
    const int id;
    bool isFree = true; // decide if the literal is free to assign new value
    bool value = false; // value of true or false, the literal always has a value during processing but consider has no value if it's free.
    std::unordered_set<Clause*> pos_occ; // All positive/negative occurrences. This is not changed during solving process.
    std::unordered_set<Clause*> neg_occ;
    int branching_level_dp;
    Clause* reason = nullptr; // the clause which has this as the last unset literal, use in unitPropagation to trace back necessary value for assigning.

    static int count;
    static std::unordered_map<int, Literal*> unorderedMap; // dictionary id to address
    static std::unordered_set<int> id_list;
    static std::queue<Literal*> unit_queue;

    explicit Literal(int id) : id(id) {};
    void setFree();
    void assignValue(bool,bool);
    void unassignValue();
    void printData();
    void updateStaticData();
    static void setLiteral(int l, Clause* new_clause);
    int getActualPosOcc(int);

    int getActualNegOcc(int);
};

class Clause {
public:
    const int id;
    std::vector<Literal*> pos_literals_list; // List of positive/negative literals, is not changed duing solving process
    std::vector<Literal*> neg_literals_list;
    std::unordered_set<Literal*> unset_literals = {};// List of free literals, reduce when one is assigned, and added again when unassign
    std::unordered_set<Literal*> sat_by = {}; // List of positive literals with value 1 and negative literal with value 0, making the clause SAT
    bool SAT = false;

    static int count;
    static std::vector<Clause*> list;
    static bool conflict;

    explicit Clause(int id) : id(id) {};
    void appendLiteral(Literal*, bool);
    int getUnsetLiteralsCount() const;
    void printData();
    void updateStaticData();
    static void setNewClause(std::vector<int>& c);
    static bool checkSAT();
};

/**
 * Assignment is pushed to stack directly in constructor without calling any function.
 */
struct Assignment {
    bool isForced;
    Literal* assigned_literal;

    Assignment(bool status, Literal* lit) : isForced(status), assigned_literal(lit) {stack.push(this);};

    static std::stack<Assignment*> stack;
    static std::vector<std::stack<Assignment*>> assignment_history; // Not used variable
    static bool enablePrintAll;
    static std::string branching_heuristic;

    static void printAll();
    static void printHistory();
};

#endif //CDCL_SOLVER_SOLVERCLASS_H
