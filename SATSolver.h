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
    std::unordered_set<Clause*> pos_occ; // All positive/negative occurrences. Unchanged during solving process.
    std::unordered_set<Clause*> neg_occ;
    std::unordered_set<Clause*> pos_watched_occ;
    std::unordered_set<Clause*> neg_watched_occ;

    /** "reason":
     * the clause which has the variable as the last unset literal(unit clause)
     * unitPropagation use to trace back necessary value for assigning
     * CDCL use to represent edges
     * Always assigned right after the literal is pushed to unit_queue
     */
    Clause* reason = nullptr;
    int branching_level = -1;

    // For CDCL branching heuristics
    int prioty_level = 1;
    int learned_count = 0;

    static int count;
    static std::unordered_map<int, Literal*> id2Lit; // dictionary id to address
    static std::unordered_set<int> id_list;
    static std::queue<Literal*> unit_queue;
    static std::unordered_map<int, Literal*> bd2BranLit; // storing all literals assigned by branching
//    bool comparingPriorities = [](Literal* l1, Literal* l2) { return l1->prioty_level > l2->prioty_level;};
    class Compare {
    public:
        bool operator()(Literal* l1, Literal* l2) {return l1->prioty_level > l2->prioty_level;}
    };
    static std::priority_queue<Literal*, std::vector<Literal*>, Compare> pq;

    explicit Literal(int id) : id(id) {};
    void updateStaticData();
    void setFree();
    void assignValueDPLL(bool, bool);
    void assignValueCDCL(bool, bool);
    void unassignValueDPLL();
    void unassignValueCDCL();
    int getActualPosOcc(int);
    int getActualNegOcc(int);
    void printData();
    void deleteLiteral();

    static void setLiteral(int l, Clause*);
    static void updatePriorities();
};

class Clause {
public:
    const int id;
    std::unordered_set<Literal*> pos_literals_list; // List of positive/negative literals, unchanged during solving process
    std::unordered_set<Literal*> neg_literals_list;
    std::unordered_set<Literal*> free_literals = {};// List of free literals, reduce/add after one is assigned/unassigned
    std::unordered_set<Literal*> sat_by = {}; // List of positive literals with value 1 and negative literal with value 0, making the clause SAT
    Literal* watched_literal_1 = nullptr; // watched literals are set after clause is added
    Literal* watched_literal_2 = nullptr;
    bool SAT = false;

    static int count; // clauses uses this for id, initial with 1 instead of 0 because a clause is created with id = count before count got increment by 1.
    static std::vector<Clause*> list;
    static bool CONFLICT;
    static Clause* conflict_clause;
    static int learned_clause_assertion_level;

    explicit Clause(int id) : id(id) {};
    void appendLiteral(Literal*, bool);
    int getUnsetLiteralsCount() const;
    void printData();
    void updateStaticData();
    void reportConflict();
    std::unordered_set<Literal*> getAllLiterals();
    void setWatchedLiterals();
    void deleteClause();

    static void setNewClause(std::vector<int>& c);
    static void conflictAnalyze();
    static void unitPropagationDPLL();
    static void unitPropagationCDCL();
    static void learnCut(const std::unordered_set<Literal *>& cut);
    static bool isDecisionCut(const std::unordered_set<Literal *>& cut);
    static bool checkAllClausesSAT();
    static bool isAsserting(const std::unordered_set<Literal *> &cut);
};

class LearnedClause: public Clause {
public:
    // TODO: more field for deleting strategies

    static std::vector<LearnedClause*> learned_list;

    explicit LearnedClause(int i) : Clause(i) {};
    void updateLearnedStaticData();
    void setWatchedLiteral(Literal*);

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
    static int bd;

    // Code more readable
    const static bool IsForced = true;
    const static bool IsBranching = false;

    void updateStaticData();
    static void backtrackingDPLL();
    static void backtrackingCDCL();
    static void branchingDPLL();
    static void branchingCDCL();

};


struct Formula {
    static bool isSAT;
    static bool isUNSAT;
    static int var_count;
    static int clause_count;
    static int branching_count;

    static void restart();
    static void preprocessing();
    static void removeInitialUnitClauses();
};

struct Printer {
    static bool print_process;
    static bool print_parsing_result;
    static bool print_formula;
    static bool print_CDCL_process;
    static bool print_assignment;
    static bool print_learned_clause;
    static bool print_max_depth_literal;

    static void printAssignmentStack();
    static void printAssignmentHistory();
    static void printAllData();
    static void printResult();

};

struct Heuristic {
    static std::tuple<Literal*, bool> MOM();
    static std::tuple<Literal*, bool> VSIDS();
//    static std::tuple<Literal*, bool> BerkMin();
//    static std::tuple<Literal*, bool> VMTF();

};
#endif //CDCL_SOLVER_SATSOLVER_H