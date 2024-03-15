#ifndef CDCL_SOLVER_SATSOLVER_H
#define CDCL_SOLVER_SATSOLVER_H

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
    std::unordered_set<Clause*> pos_watched_occ;
    std::unordered_set<Clause*> neg_watched_occ;
    int branching_level_dp;
    Clause* reason = nullptr; // the clause which has this as the last unset literal, use in unitPropagation to trace back necessary value for assigning.

    static int count;
    static std::unordered_map<int, Literal*> id2Ad_dict; // dictionary id to address
    static std::unordered_set<int> id_list;
    static std::queue<Literal*> unit_queue;

    explicit Literal(int id) : id(id) {};
    void updateStaticData();
    void setFree();
    void assignValueDPLL(bool, bool);
    void assignValueCDCL(bool, bool);
    void unassignValueDPLL();
    void unassignValueCDCL();
    int getActualPosOcc(int);
    int getActualNegOcc(int);

    static void setLiteral(int l, Clause*);
    void printData();
};

class Clause {
public:
    const int id;
    std::unordered_set<Literal*> pos_literals_list; // List of positive/negative literals, doesn't change during solving process
    std::unordered_set<Literal*> neg_literals_list;
    std::unordered_set<Literal*> unset_literals = {};// List of free literals, reduce when one is assigned, and added again when unassign
    std::unordered_set<Literal*> sat_by = {}; // List of positive literals with value 1 and negative literal with value 0, making the clause SAT
    Literal* watched_literal_1 = nullptr;
    Literal* watched_literal_2 = nullptr;
    bool SAT = false;

    static int count;
    static std::vector<Clause*> list;
    static bool conflict;

    explicit Clause(int id) : id(id) {};
    void appendLiteral(Literal*, bool);
    int getUnsetLiteralsCount() const;
    void printData();
    void updateStaticData();
    void reportConflict();

    static void setNewClause(std::vector<int>& c);
    static void setWatchedLiterals();
    static bool checkSAT();
};

/**
 * Assignment is pushed to stack directly in constructor without calling any function.
 */
struct Assignment {
    bool status;
    Literal* assigned_literal;

    Assignment(bool status, Literal* lit) : status(status), assigned_literal(lit) {};

    static std::stack<Assignment*> stack;
    static std::vector<std::stack<Assignment*>> assignment_history; // Not used
    static bool enablePrintAll;
    static std::string branching_heuristic;
    const static bool isForced = true;

    void updateStaticData();
    static void backtrackingDPLL();
    static void backtrackingCDCL();
    static void printAll();
    static void printHistory();
};

struct Formula {
    static bool isSAT;
    static bool isUNSAT;
    static int var_count;
    static int clause_count;
};

#endif //CDCL_SOLVER_SATSOLVER_H