#ifndef MUS_H
#define MUS_H

#include "cadical.hpp"

#include <fstream>
#include <iostream>
#include <vector>

using CodeType = unsigned long long;

struct Instance;

struct VarSuite {
  int start, end;

  VarSuite () = default;
  VarSuite (int start, int size)
    : start {start}, end {start + size - 1} {}
  int ith (int i) const { return start + i - 1; }
  int size () const { return end + 1 - start; };

  std::vector<int> get_interpretation (CaDiCaL::Solver *solver, bool pos_phase) const;
  void print_interpretation (std::ostream &out, CaDiCaL::Solver *solver) const;
};

struct LitSuite {
  VarSuite content;

  LitSuite () = default;
  LitSuite (int start, int size) : content {start, 2*size} {}
  int ith (int i) const { return content.start + 2*(i > 0 ? i : -i) - (i > 0 ? 2 : 1); }
  matrix<int> bind (const std::vector<int> &clause, int &aux) const;
};

struct LitInClauseBlockers {
  std::vector<LitSuite> blockers;

  LitInClauseBlockers (int num_clause, int num_vars, int last_aux)
    : blockers (num_clause) {
    if (!blockers.empty ()) {
      blockers[0] = LitSuite {last_aux+1, num_vars};
      for (auto prev {blockers.begin ()}, current {std::next (prev)};
	   current != blockers.end (); ++prev, ++current) 
	{ *current = LitSuite {prev->content.end, num_vars}; }
    }
  }

  int idx (int clause_from_1, int literal) const {
    return blockers[clause_from_1-1].ith (literal);
  }

  int end_var () const {
    if (blockers.empty ()) { return -1; }
    return blockers.back ().content.end;
  }

  matrix<int> bind (const matrix<int> &formula, int &aux) const;
};

struct PermGen {
  std::vector<int> counter;
  int max;
  int stop_for_0;

  PermGen (int max, int width, int unit = 1, int special_stop = 0);
  
  bool fill_rest (std::vector<int>::iterator iter, int acc); 
  inline bool fill_rest (int start_idx, int start_val);

  int size () const { return (int) counter.size (); }
  int incr (auto iter);
  bool incr_0 ();
  bool incr ();  
  bool skip (int dest);    
  bool safe () const { return counter[counter.size () - 1] <= max; }
};

struct RenameLookup {
  struct Rename { int orig, loc; };

  std::vector<Rename> mappings;
  int counter;

  RenameLookup (int zero) : counter {zero} {}

  std::vector<Rename>::iterator locate (int orig, std::vector<Rename>::iterator start,
					std::vector<Rename>::iterator end);
  std::vector<Rename>::iterator locate (int orig) {
    return locate (orig, mappings.begin (), mappings.end ());
  }
  int insert (int num);
  int image (int lit) { return lit > 0 ? insert (lit) : -insert (-lit); }
};

struct Grouping {
  matrix<int> clauses;
  matrix<int> candidates;
  std::vector<VarSuite> ys;
  VarSuite xs, ss;
  int k, vars, solution_status {};

  Grouping (int num_clauses, int k, int v_start);

  inline void add_clause (const std::vector<int> &clause, int idx);
  inline void add_clause (const std::vector<int> &clause, matrix<int> &destination);
  inline void add_clause (const std::vector<int> &clause);
  inline void add_candidate (const std::vector<int> &clause);
  inline void add_clause (const matrix<int> &cl);

  int s (int i) const { return ss.ith (i); }
  int x (int i) const { return xs.ith (i); }
  int y (int sub, int sup) const { return ys[sub].ith (sup); } // [chunk][clause]

  int sum_seq (int start, int end, int important_var);
  int sum_sort (int start, int end, int important_var);
  inline int sum (int start, int end, int important_var);
  void exactly_k (int amount, int start, int end);
  int at_most_k (int k, int start, int end);

  inline void x_sum ();
  inline void y_sum ();
  inline void z_sum ();
  inline void cardinalities ();

  void bind_blockers (const matrix<int> &rules, const LitInClauseBlockers &blockers, int num_lits);
  void bind_xcs (const Instance &inst);
  void bind_yxs ();
  void bind_pseudo_selectors (const Instance &inst);
  std::vector<int> fresh_dupl (RenameLookup &map, std::vector<int> clause, bool negated);
  void bind_originals (const Instance &inst);
  void bind_duplicates (const Instance &inst);
  void different_ys ();
  void different_ys (int n);
  void bind_x_directly (int clause_number, int x_number, std::vector<int> clause);
  inline void bind_x_directly (int clause_number, std::vector<int> clause);
  void k_is_one (const Instance &inst);

  void apply (const Instance &inst);
  void apply_duplicated (const Instance &inst);

  void print_header (std::ostream &out);
  void print_dimacs (std::ostream &out, bool header);

  int check_sat (CaDiCaL::Solver *solver);
  void get_candidate (CaDiCaL::Solver *solver);
  void print_interpretation (std::ostream &out, CaDiCaL::Solver *solver) const;

  CodeType encode_candidate (const std::vector<int> &candidate) const;

  std::vector<CodeType> unsubsumed_complement (const matrix<int> &sat_subsets,
					       const std::vector<CodeType> &priors);
  int unsubsumed_complement (matrix<int> sat_subsets, Instance &inst, int t_num);
  bool cohere_different_type (const std::vector<int> &counter,
			      matrix<int>::const_iterator current,
			      matrix<int>::const_iterator end,
			      int &min, bool phase) const;
  bool cohere_same_type (PermGen &pg, matrix<int>::const_iterator current,
			 matrix<int>::const_iterator other_end, int &min) const;

  int check_subset_satisfiability (Instance &inst, const std::vector<int> &on_xs) const;
  bool query (Instance &inst, matrix<int> &subsets, auto &&test, int time_limit = -1, const matrix<int> & = {});
  int sat_set_test (bool verbose, Instance &inst);
  inline void sat_set_test (Instance &inst, matrix<int> &satisfiables);
  int unsat_test (bool _, Instance &inst);
  bool unsat_test (Instance &inst, matrix<int> &muses, int time_limit = -1, const matrix<int> &additional = {});
  int check_type_by_complement (Instance &inst, int t_num);
  int check_type (Instance &inst, int t_num, int k);
};

struct Instance {
  matrix<int> clauses;
  matrix<int> mus_blockers;
  std::vector<int> indices_of_mus_size_shifts;
  std::vector<CodeType> mus_codes;
  int vars, clause_num;
  int secs_per_k {-1};

  inline void mark_size_step ();
  std::vector<matrix<int>::const_iterator> type_starts () const;
  std::vector<matrix<int>::const_iterator> type_ends (const std::vector<matrix<int>::const_iterator> &starts) const;
  
  matrix<int> decode_as_clauses (int code) const;
  std::vector<int> decode_to_block (int code, int xs_var_start) const;
  inline void block (const matrix<int> &candidates);
  void block (const std::vector<CodeType> &new_codes, const matrix<int> &disjs, int xs_var_start);
  void block (const std::vector<CodeType> &new_codes, int xs_var_start);
  
  int k_is_two (int x_var_start);
  
  int check_sat ();
  int find_mus (int k, int t_num);
  int find_one_mus (int k_end, int t_num);
  int find_all_muses (int k_end, int t_num, int k_start = 2);
  int layer_k (int k, int t_num);
  int overlapping_k (int k, int t_num);

  void direct_init (matrix<int> clauses, int vars);

  void read_header (std::ifstream &dimacs);
  bool read_clause (std::ifstream &dimacs, int idx);
  void read_dimacs (char *path);

  void print_dimacs (std::ostream &out, bool header) const;
  void print_mus (std::ostream &out, const std::vector<int> &blocker) const;
  void print_muses (std::ostream &out) const;
  void print_mus_value (std::ostream &out, const std::vector<int> &blocker) const;
  void print_muses_values (std::ostream &out) const;
};
  
#endif
