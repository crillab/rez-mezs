#include "cadical.hpp"

#include "cardinality.hpp"
#include "util.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<T>>;
template<typename T, typename C = std::less<T>> using setlike_matrix = std::set<std::set<T>, C>;

template<typename T, typename C>
std::ostream &operator << (std::ostream &out, const setlike_matrix<T, C> &s_matrix) {
  for (const std::set<T> &s : s_matrix)
    { for (T i : s) { out << i << ' '; } out << '\n'; }
  return out;
}

template<typename T>
bool includes (const std::set<T> &big, const std::set<T> &small) {
  if (big.size () < small.size ()) { return false; }
  for (auto biter {big.cbegin ()}, smiter {small.cbegin ()};
       smiter != small.cend (); ) {
    if (biter == big.cend () || *biter > *smiter) { return false; }
    else if (*biter < *smiter) { ++biter; }
    else { ++biter; ++smiter; }
  }
  return true;
}

template<typename T>
bool partial_overlap (const std::set<T> &a, const std::set<T> &b) {
  bool a_in_b {true}, b_in_a {true};

  auto ater {a.cbegin ()}, bter {b.cbegin ()};

  while (ater != a.cend () && bter != b.cend ()) {
    if (*ater == *bter) { ++ater; ++bter; }
    else if (*ater < *bter) { a_in_b = false; ++ater; }
    else { b_in_a = false; ++bter; }
    if (!a_in_b && !b_in_a) { return true; }
  }
  
  if (ater != a.cend ()) { return !b_in_a; }
  if (bter != b.cend ()) { return !a_in_b; }
  return false;
}

struct NormalForm {
  matrix<int> content;
  std::vector<int> operator [] (int idx) { return content[idx]; }
  void add_expression (const std::vector<int> &expr) { content.push_back (expr); }
  void append_expressions (const matrix<int> &exprs) {
    auto idx {content.size ()};
    content.resize (idx+exprs.size ());
    std::copy (exprs.cbegin (), exprs.cend (), std::next (content.begin (), idx));
  }
};
struct CNF : public NormalForm {
  void add_clause (const std::vector<int> &expr) { add_expression (expr); }
  void append_cnf (const CNF &other) { append_expressions (other.content); }
};
struct DNF : public NormalForm {
  void add_term (const std::vector<int> &expr) { add_expression (expr); }
};

bool ovlp (const std::vector<int> &minor, const std::set<int> &major) {
  bool ans {};
  for (int lit : minor) { if (major.contains (lit)) { ans = true; break; } }
  return ans;
}

std::set<int> set_from_vec (const std::vector<int> &vec, auto &&callback) {
  std::set<int> set;
  for (int i : vec) { set.insert (callback (i)); }
  return set;
}

matrix<int> bind_each (const std::vector<int> &expr, int selector, auto &&func) {
  matrix<int> answer (expr.size ());
  auto cl {answer.begin ()};
  for (auto liter {expr.cbegin ()}; liter != expr.cend (); ++cl, ++liter)
    { *cl = func (*liter, selector); }
  return answer;
}

DNF alo (const CNF &phi, const std::vector<int> &l) {
  std::set<int> l_bar {set_from_vec (l, [] (int i) { return -i; })};
  DNF formula;

  for (const std::vector<int> &c : phi.content) {
    if (ovlp (c, l_bar)) {
      std::vector<int> new_clause;
      for (int lit : c) { if (!l_bar.contains (lit)) { new_clause.push_back (-lit); } }
      if (!new_clause.empty ()) { formula.content.push_back (new_clause); }
    }
  }
  return formula;
}

CNF nf (const CNF &phi, const std::vector<int> &l_vec) {
  std::set<int> l {set_from_vec (l_vec, [] (int i) { return i; })};
  CNF pi; pi.content.resize (phi.content.size ());
  std::copy_if (phi.content.cbegin (), phi.content.cend (), pi.content.begin (),
		[&l] (const std::vector<int> &cl) { return ovlp (cl, l); });
  std::transform (pi.content.begin (), pi.content.end (), pi.content.begin (),
		  [&l] (const std::vector<int> &old) {
		    std::vector<int> answer;
		    answer.resize (old.size ());
		    std::copy_if (old.cbegin (), old.end (), answer.begin (),
				  [&l] (int i) { return i && !l.contains (i); });
		    std::erase (answer, 0);
		    return answer; });
  std::erase (pi.content, std::vector<int> {});
  return pi;
}

matrix<int> inner_selection (const CNF &phi, const std::vector<int> &l, int &selector, bool cnf) {
  matrix<int> content {cnf ? nf (phi, l).content : alo (phi, l).content};
  matrix<int> answer (content.size ());
  for (auto iter {content.cbegin ()}; iter != content.cend (); ++selector, ++iter) {
    matrix<int> expr {cnf ? disjunction (*iter, selector) : conjunction (*iter, selector)};
    answer.insert (answer.end (), expr.begin (), expr.end ());
  }
  return answer;
}

matrix<int> outer_selection (const CNF &phi, const std::vector<int> &l, int overall_selector, int &vars, bool cnf) {
  int start {++vars};
  matrix<int> answer {inner_selection (phi, l, vars, cnf)};
  
  std::vector<int> inner_selectors (vars-start+1); auto seliter {inner_selectors.begin ()};
  for (int i {start}; i <= vars; ++i, ++seliter) { *seliter = i; }
  matrix<int> expr {cnf ? conjunction (inner_selectors, overall_selector) : disjunction (inner_selectors, overall_selector)};
  answer.insert (answer.end (), expr.begin (), expr.end ());
  std::erase (answer, std::vector<int> {});

  return answer;
}

CNF maximal_q_model_of_l_with_selection (const CNF &phi, const std::vector<int> &l, int big_wedge_l, int alo_selector, int nf_selector, int &vars) {
  matrix<int> antecedent {implies_term (big_wedge_l, l)};
  matrix<int> alo {outer_selection (phi, l, alo_selector, vars, false)};
  matrix<int> nf  {outer_selection (phi, l, nf_selector, vars, true)};
  CNF answer;
  answer.content.insert (answer.content.end (), antecedent.begin (), antecedent.end ());
  answer.content.insert (answer.content.end (), alo.begin (), alo.end ());
  answer.content.insert (answer.content.end (), nf.begin (), nf.end ());
  answer.content.resize (answer.content.size ()+1);
  answer.content.back () = {-big_wedge_l, -alo_selector, -nf_selector};
  return answer;
}
  
CNF selected_negated_alo (const CNF &phi, const std::vector<int> &l, int selector) {
  std::set<int> l_bar {set_from_vec (l, [] (int i) { return -i; })};
  CNF formula;

  bool rel_clause {};
  for (const std::vector<int> &c : phi.content) {
    if (ovlp (c, l_bar)) {
      rel_clause = true;
      std::vector<int> new_clause {-selector};
      for (int lit : c) { if (!l_bar.contains (lit)) { new_clause.push_back (lit); } }
      if (new_clause.size () > 1) { formula.content.push_back (new_clause); }
      else {
	CNF alo_top;
	alo_top.add_clause ({-selector});
	return alo_top;
      }
    }
  }
  if (formula.content.empty ()) { formula.add_clause ({selector}); }
  return formula;
}
    
matrix<int> negated_nf (const CNF &phi, const std::vector<int> &l, int &vars) {
  std::set<int> l_as_set {set_from_vec (l, [] (int i) { return i; })};
  std::set<int> l_bar    {set_from_vec (l, [] (int i) { return -i; })};
  CNF pi; pi.content.resize (phi.content.size ());
  std::copy_if (phi.content.cbegin (), phi.content.cend (), pi.content.begin (),
		[&l_as_set, &l_bar] (const std::vector<int> &cl) { return ovlp (cl, l_as_set) && !ovlp (cl, l_bar); });
  std::erase (pi.content, std::vector<int> {});

  matrix<int> answer;
  std::vector<int> nnf (pi.content.size ());
  for (int &aux : nnf) { aux = ++vars; }

  auto aux {nnf.cbegin ()};
  for (const std::vector<int> cl : pi.content) {
    std::vector<int> not_subclause;
    for (int i : cl) { if (!l_as_set.contains (i)) { not_subclause.push_back (-i); } }
    if (!not_subclause.empty ()) {
      matrix<int> binding {implies_term (*aux, not_subclause)};
      answer.insert (answer.end (), binding.begin (), binding.end ());
    }
    ++aux;
  }

  return answer;
}
 
CNF maximal_q_models_of_l (const CNF &phi, const std::vector<int> &l, int alo_selector, int &vars) {
  CNF answer {selected_negated_alo (phi, l, alo_selector)};
  int aux {--vars};
  matrix<int> neg_nf {negated_nf (phi, l, aux)};
  answer.content.insert (answer.content.end (), neg_nf.cbegin (), neg_nf.cend ());
  int idx {aux-vars};
  std::vector<int> clause (idx); for (int &i : clause) { i = ++vars; }
  clause.resize (idx+l.size ()); std::transform (l.cbegin (), l.cend (), std::next (clause.begin (), idx), [] (int i) { return -i; });
  clause.resize (clause.size ()+1);
  clause.back () = alo_selector;
  answer.add_clause (clause);
  return answer;
}

CNF l_not_improvable (const CNF &phi, const std::vector<int> &l, int big_wedge_l, int alo_selector) {
  CNF answer {selected_negated_alo (phi, l, alo_selector)};
  answer.add_clause ({-big_wedge_l, alo_selector});
  return answer;
}

matrix<int> l_beats_change (const CNF &phi, const std::vector<int> &l, int big_wedge_l, int nf_selector, int &aux_start) {
  matrix<int> neg_nf {negated_nf (phi, l, aux_start)};
  std::vector<int> disj_nf (aux_start-nf_selector);
  for (int idx {0}, val {nf_selector+1}; val <= aux_start; ++idx, ++val) { disj_nf[idx] = val; }
  matrix<int> disj_right {implied_by_clause (nf_selector, disj_nf)};

  neg_nf.insert (neg_nf.end (), disj_right.begin (), disj_right.end ());
  neg_nf.push_back ({-big_wedge_l, nf_selector});
  return neg_nf;
}
  
CNF conj_in_cons_of_l (const CNF &phi, const std::vector<int> &l, int alo_selector, int big_wedge_l, int &start_nf_sel) {
  matrix<int> antecedent {implied_by_clause (big_wedge_l, l)};
  CNF answer {l_not_improvable (phi, l, big_wedge_l, alo_selector)};
  int aux {start_nf_sel};
  matrix<int> rest_of_consequent {l_beats_change (phi, l, big_wedge_l, start_nf_sel, aux)};
  answer.content.insert (answer.content.end (), rest_of_consequent.begin (), rest_of_consequent.end ());
  start_nf_sel = aux;
  return answer;
}

struct ChoiceIter {
  std::vector<int>::iterator pos;
  ChoiceIter *succ;

  ChoiceIter (int num_succ) : succ {num_succ > 0 ? new ChoiceIter {num_succ-1} : nullptr} {}
  ~ChoiceIter () { delete succ; }
  
  bool set_pos (std::vector<int>::iterator pos, std::vector<int>::iterator end) {
    if (pos == end) { return false; }
    this->pos = pos;
    if (!succ) { return true; }
    return succ->set_pos (std::next (pos), end);
  }

  std::vector<int> get_l (int k) {
    std::vector<int> l (k);
    auto liter {l.begin ()};
    ChoiceIter *diter {this};
    while (true) {
      *liter = *(diter->pos);
      if (diter->succ) { diter = diter->succ; ++liter; }
      else { break; }
    }
    return l;
  }
    
  bool next (std::vector<int>::iterator end) {
    if (succ && succ->next (end)) { return true; }
    if (pos == std::prev (end)) { return false; }
    
    ++pos;
    return !succ || succ->set_pos (std::next (pos), end);
  }
};

std::ostream &operator << (std::ostream &out, const ChoiceIter &di) {
  out << *di.pos;
  if (di.succ) { out << ' ' << *di.succ; }
  return out;
}

struct PhaseIter {
  std::vector<bool> phases;

  PhaseIter (const std::vector<int> &l) : phases (l.size (), false) {}

  bool next (std::vector<bool>::iterator iter) {
    if (iter == std::prev (phases.cend ())) {
      if (*iter) { return false; }
      *iter = true;
      return true;
    }
    if (next (std::next (iter))) { return true; }
    if (*iter) { return false; }
    *iter = true;
    for (auto biter {std::next (iter)}; biter != phases.cend (); ++biter) { *biter = false; }
    return true;
  }

  bool next () { return next (phases.begin ()); }
};

std::ostream &operator << (std::ostream &out, const PhaseIter &pi) {
  for (bool sign : pi.phases) { out << sign; }
  return out;
}
    
struct Instance {
  CNF data, clauses;
  // setlike_matrix<int, decltype ([] (const std::set<int> &a, const std::set<int> &b) {
  // // if (!partial_overlap (a, b)) { for (int i : a) { std::cout << i << ' '; } std::cout << " --- "; for (int i : b) { std::cout << i << ' '; } std::cout << '\n'; return false; }
  // // if (a.size () != b.size ()) { return a.size () < b.size (); }
  // return a < b; })> q_models;
  // std::set<std::set<int>> q_models;
  matrix<int> q_models;
  std::vector<int> selectors;
  int vars, num_clauses;
  int aux;

  void bind_clauses_and_selectors () {
    auto cl {data.content.cbegin ()}; auto x {selectors.cbegin ()};
    for ( ; cl != data.content.cend (); ++cl, ++x)
      { clauses.append_expressions (disjunction (*cl, *x)); }
  }
  
  void init_clauses_and_selectors () {
    data.content.resize (num_clauses);
    selectors.resize (num_clauses);
    std::transform (selectors.begin (), selectors.end (), selectors.begin (),
		    [this] (int) { return ++aux; });
  }
  
  void read_header (std::ifstream &cnf) {
    std::string word;
    while (cnf.peek () == 'c') { std::getline (cnf, word); }
    cnf >> word >> word >> vars >> num_clauses;
    aux = vars;
    init_clauses_and_selectors ();
  }

  void read_clause (std::ifstream &cnf, matrix<int>::iterator dest) {
    int lit;
    while (cnf >> lit, lit) { dest->push_back (lit); } 
  }
    
  void read_dimacs (const char *path) {
    std::ifstream cnf {path};
    read_header (cnf);
    for (auto iter {data.content.begin ()}; iter != data.content.end (); ++iter)
      { read_clause (cnf, iter); }
    bind_clauses_and_selectors ();
  }

  void print_dimacs (std::ostream &out) const {
    for (const std::vector<int> &cl : clauses.content)
      { print_clause (out, cl); }
  }

  void pcnf (int k) {}
  
  void print_v_line (std::ostream &out, CaDiCaL::Solver *solver, bool pre2022 = true) const {
    auto print_clause {pre2022
      ? [] (int var, int idx, std::ostream &out, CaDiCaL::Solver *solver) { if (solver->val (var) > 0) { out << idx << ' '; } }
      : [] (int var, int _, std::ostream &out, CaDiCaL::Solver *solver) { out << (solver->val (var) > 0); } };
    
    if (solver->status () == CaDiCaL::SATISFIABLE) {
      out << "v ";
      int idx {1};
      for (int var : selectors) {
	print_clause (var, idx, out, solver);
	++idx;
      }
      out << (pre2022 ? "0\n" : "\n");
    }
  }

  void print_maximal_q_model (std::ostream &out, CaDiCaL::Solver *solver, bool as_v_line = false) const {
    if (solver->status () == CaDiCaL::SATISFIABLE) {
      if (as_v_line) { print_v_line (std::cout, solver); return; }
      
      matrix<int> included;
      auto diter {data.content.cbegin ()};
      for (int var : selectors) {
	if (solver->val (var) > 0) { included.push_back (*diter); }
	++diter;
      }
      print_pretty (std::cout, included);
      std::cout << '\n';
    }
  }

  matrix<int> selected_clauses (const std::vector<int> &selectors) const {
    matrix<int> subset (selectors.size ());
    auto diter {data.content.cbegin ()}; auto siter {subset.begin ()};
    auto iiter {selectors.cbegin ()};
    for (int i {1}; iiter != selectors.cend (); ++diter, ++siter, ++iiter, ++i) {
      while (i < *iiter) { ++diter; ++i; }
      *siter = *diter;
    }
    return subset;
  }

  void pretty_print_selected (std::ostream &out, const std::vector<int> &selectors) const {
    matrix<int> subset {selected_clauses (selectors)};
    print_pretty (out, subset);
  }

  void print_q_models_names (std::ostream &out) const {
    int all_sel {(int) data.content.size ()};
    int i {};
    for (const auto &mss : q_models) { out << "QM" << ++i << std::endl; }
  }
  
  void print_q_models_plain (std::ostream &out) const {
    for (const auto &mss : q_models) {
      out << "v ";
      for (int i : mss) { out << i << ' '; }
      out << "0\n";
    }
  }
		    
  void print_q_models_pretty (std::ostream &out) const {
    int i {};
    for (const auto &mss : q_models) {
      std::vector<int> msv {mss.cbegin (), mss.cend ()};
      out << "QM" << ++i << ": ";
      pretty_print_selected (out, msv);
      out << '\n';
    }
  }

  std::vector<int> complement_in_k (const std::set<int> &mss, int k) const {
    std::vector<int> mcs (k - mss.size ());
    auto vter {mcs.begin ()}; auto ster {mss.cbegin ()};
    
    for (int i {1}; vter != mcs.end () && ster != mss.cend ();  ++i) {
      if (i == *ster) { ++ster; }
      else { *vter = i; ++vter; }
    }
    for (int i {*std::prev (ster)+1}; vter != mcs.end (); ++i, ++vter) { *vter = i; }

    return mcs;
  }

  std::vector<int> complement_in_k (const std::vector<int> &mss, int k) const {
    std::vector<int> complement (k - mss.size ());
    std::vector<int> range (k); int j {};
    for (int &i : range) { i = ++j; }
    
    std::copy_if (range.cbegin (), range.cend (), complement.begin (),
		  [&mss] (int i) { return std::all_of (mss.cbegin (), mss.cend (), [i] (int j) { return i != j; }); });

    std::cout << "MSS "; for (int i : mss) { std::cout << i << ' '; } std::cout << '\n';
    std::cout << "Cmp "; for (int i : complement) { std::cout << i << ' '; } std::cout << '\n';
    
    return complement;
  }

  void print_q_mcs_names (std::ostream &out) const {
    int all_sel {(int) data.content.size ()};
    int i {};
    for (const auto &mss : q_models) { out << "MCS" << ++i << std::endl; }
    out << "Done" << std::endl;
  }
  
  void print_q_mcs_pretty (std::ostream &out) const {
    int all_sel {(int) data.content.size ()};
    int i {};
    for (const auto &mss : q_models) {
      out << "MCS" << ++i << ": ";
      pretty_print_selected (out, complement_in_k (mss, all_sel));
      out << '\n';
    }
  }

  void print_q_mcs_plain (std::ostream &out) const {
    int k {(int) data.content.size ()};
    for (const auto &mss : q_models) {
      out << "v ";
      int j {1};
      for ( ; j < *(mss.cbegin ()); ++j) { out << j << ' '; }
      for (auto iter {mss.cbegin ()}; iter != mss.cend (); ) {
	if (*iter == j) { ++iter; }
	else { out << j << ' '; }
	++j; 
      }
      for ( ; j <= k; ++j) { out << j << ' '; }
      out << "0\n";
    }
  }

  std::set<int> grow_local (const std::set<int> &start, std::vector<int> &to_block, std::vector<int> &to_force, CaDiCaL::Solver *global_solver) {
    CaDiCaL::Solver *local_solver {new CaDiCaL::Solver}; global_solver->copy (*local_solver);

    std::set<int> candidate {start.cbegin (), start.cend ()}, prev_cand;
    if (local_solver->solve () != CaDiCaL::SATISFIABLE) { return {}; }
    do {
      std::swap (candidate, prev_cand);
      to_block.clear (), to_force.clear (); 
      std::vector<int> sel_cand;
      for (int v : selectors) {
	if (local_solver->val (v) > 0) 
	  { candidate.insert (v-vars); sel_cand.push_back (v); to_block.push_back (-v); }
	else { to_force.push_back (v); }
      }
      for (int v : sel_cand) { local_solver->add (v), local_solver->add (0); }
      local_solver->clause (to_force);
    } while (local_solver->solve () == CaDiCaL::SATISFIABLE);

    if (to_force.empty ()) { std::swap (candidate, prev_cand); }

    delete local_solver;
    // std::cout << "Start: "; for (int i : start) { std::cout << i << ' '; } std::cout << '\n';
    // std::cout << "Candidate: "; for (int i : candidate) { std::cout << i << ' '; } std::cout << '\n';
    return candidate;
  }

  // matrix<int> add_candidate (const std::set<int> &candidate, const matrix<int> &urn, bool verbose = false) {
  //   matrix<int> no_inclusions;
  //   std::copy_if (urn.cbegin (), urn.cend (), std::inserter (no_inclusions, no_inclusions.begin ()),
  // 		  [&candidate] (const std::vector<int> &incumbent) { return std::any_of (incumbent.cbegin (), incumbent.cend (), [&candidate] (int i) { return !candidate.contains (i); }); });
  //   no_inclusions.resize (no_inclusions.size () + 1);
  //   std::vector<int> as_vec {candidate.cbegin (), candidate.cend ()};
  //   no_inclusions.back () = as_vec;
  //   if (verbose) { std::cout << no_inclusions.size () << ' ' << std::flush;
  //   return no_inclusions;
  // }
  
  void add_candidate (const std::set<int> &candidate, auto &urn, bool verbose = false) {
    // std::erase_if (urn, [&candidate] (const std::set<int> &incumbent) { return includes (candidate, incumbent); });
      // if (includes (candidate, incumbent)) {
      // std::cout << "Includes\n  F)"; for (int i : candidate) { std::cout << i << ' '; } std::cout << "\n  G)"; for (int i : incumbent) { std::cout << i << ' '; } std::cout << '\n'; }
    std::vector<int> to_push {candidate.cbegin (), candidate.cend ()};
    urn.push_back (to_push);
    if (verbose) { std::cout << urn.size () << ' ' << std::flush; }
  }

  CNF rule_out_interpretation (const std::vector<int> &complement, const std::vector<int> &current) {
    CNF outruling;
    int sel {++aux}; matrix<int> blocking {disjunction (current, sel)};
    int sel_prime {++aux}; matrix<int> forcing {disjunction (complement, sel_prime)};
    outruling.append_expressions (blocking); outruling.append_expressions (forcing);

    std::vector<int> if_missing_other {-sel, sel_prime};
    outruling.add_clause (if_missing_other);
    
    return outruling;
  }
    
  void recuperate_candidates (CaDiCaL::Solver *solver, bool verbose = false, bool grow = true) {
    CaDiCaL::Solver copy;
    solver->copy (copy);
    for (const std::vector<int> &cl : clauses.content) { copy.clause (cl); }

    decltype (q_models) ballot;
    // matrix<int> ballot;
    
    while (copy.solve () == CaDiCaL::SATISFIABLE) {
      std::vector<int> to_block; std::vector<int> to_force;
      std::set<int> candidate;
      for (int v : selectors) {
	if (copy.val (v) < 0) { to_force.push_back (v); }
	else { candidate.insert (v-vars); to_block.push_back (-v); } 
      }
      // std::cout << "Before: "; for (int i : to_block) { std::cout << i << ' '; } std::cout << '\n';
      // if (grow) { ballot = add_candidate (grow_local (candidate, to_block, &copy), ballot, verbose); }
      if (grow) {
	add_candidate (grow_local (candidate, to_block, to_force, &copy), ballot, verbose);
	std::cout << "MCS" << ballot.size () << std::endl;
	
	// CNF outruling {rule_out_interpretation (to_force, to_block)};
	// clauses.append_cnf (outruling);
	// std::cout << "Rule out\n";
	// for (const std::vector<int> &cl : outruling.content) 
	//   { for (int i : cl) { std::cout << i << ' '; } std::cout << "0\n"; }
	// std::cout << "Ruled\n";
	// for (const std::vector<int> &cl : outruling.content) { copy.clause (cl); }
      }
      else { add_candidate (candidate, ballot, verbose); }
      
      clauses.add_clause (to_force);
      copy.clause (to_force);
      // std::cout << "After: "; for (int i : to_block) { std::cout << i << ' '; } std::cout << '\n';
    }

    // decltype (ballot) temp;
    // for (auto friter {ballot.cbegin ()}, kniter {q_models.cbegin ()};
    // 	 friter != ballot.cend (); ) {
    //   if (kniter == q_models.cend ()) { break; }
    //   else if (*friter == *kniter) { ++friter, ++kniter; }
    //   else if (*friter < *kniter) { temp.insert (*friter); ++friter; }
    //   else { ++kniter; }
    // }

    for (const auto &cl : ballot) {
      std::vector<int> to_block (selectors.size ()-cl.size ());
      auto inter {cl.cbegin ()}; auto outter {to_block.begin ()};
      for (auto vter {selectors.cbegin ()}; outter != to_block.end (); ) {
	if (inter != cl.cend () && *vter == *inter) { ++vter, ++inter; }
	else {
	  *outter = *vter+vars;
	  ++vter; ++outter;
	}
      }
      solver->clause (to_block);
      clauses.add_clause (to_block);
    }

    q_models.insert (q_models.end (), ballot.cbegin (), ballot.cend ());
  }
    
  CNF k_maximal_q_models (int k, CaDiCaL::Solver *solver = nullptr, bool verbose = false, bool grow = true) {
    CNF answer;

    if (k < 0) { k = vars; }
    std::vector<int> vars_phi (vars);
    int acc {}; for (int &i : vars_phi) { i = ++acc; }
    for (int j {}; j < k; ++j) {
      ChoiceIter di {j};
      if (di.set_pos (vars_phi.begin (), vars_phi.end ())) {
	do {
	  std::vector<int> l {di.get_l (j+1)};
	  PhaseIter piter {l};
	  do {
	    std::vector<int> signed_l (l.size ());
	    auto sign {piter.phases.cbegin ()}; 
	    for (auto dest {signed_l.begin ()}, src {l.begin ()}; dest != signed_l.end (); ++dest, ++src, ++sign)
	      { *dest = *sign ? *src : -*src; }
	    int alo {++aux}, nf {++aux};
	    answer.append_cnf (maximal_q_models_of_l (data, signed_l, alo, aux));
	  } while (piter.next ());
	} while (di.next (vars_phi.end ()));
      }
      if (solver) { recuperate_candidates (solver, verbose, grow); }
    }
    if (verbose) { std::cout << '\n'; print_cnf (std::cout, answer.content); }

    return answer;
  }
    
  void enumerate_models (CaDiCaL::Solver *solver, auto &&func) const {
    while (solver->solve () == CaDiCaL::SATISFIABLE) {
      func (solver);
      std::vector<int> to_block;
      for (int v : selectors) { if (solver->val (v) > 0) { to_block.push_back (-v); }}
      solver->clause (to_block);
    }
  }
};

struct WeightedInstance : public Instance {
  int infinite_weight {-1};
  std::vector<int> weights;

  void read_header (std::ifstream &wcnf) {
    std::string word;
    if (wcnf.peek () == 'c') { std::getline (wcnf, word); }
    if (wcnf.peek () == 'p') {
      wcnf >> word >> word >> vars >> num_clauses >> infinite_weight;
      aux = vars;
      init_clauses_and_selectors ();
      weights.resize (num_clauses);
    }
  }

  void read_clause (std::ifstream &wcnf, matrix<int>::iterator cl_dest, std::vector<int>::iterator w_dest) {
    int lit;
    wcnf >> *w_dest;
    while (wcnf >> lit, lit) { cl_dest->push_back (lit); }
  }

  void read_clause (std::ifstream &wcnf, std::vector<int> &clause, int &weight) {
    char h; int lit;
    if (wcnf.peek () == 'h') { wcnf >> h; } else { wcnf >> weight; }
    while (wcnf >> lit, lit) { clause.push_back (lit); if (lit > vars) { vars = lit; } }
  }

  void read_dimacs (const char *path) {
    std::ifstream wcnf {path};
    read_header (wcnf);
    if (selectors.empty ()) {
      while (!wcnf.eof ()) {
	std::vector<int> clause;
	int weight {};
	read_clause (wcnf, clause, weight);
	data.add_clause (clause); weights.push_back (weight);
      }
      num_clauses = data.content.size (); aux = vars;
      init_clauses_and_selectors ();
    }
    else {
      auto diter {data.content.begin ()}; auto witer {weights.begin ()};
      for ( ; witer != weights.end (); ++diter, ++witer)
	{ read_clause (wcnf, diter, witer); }
      bind_clauses_and_selectors ();
    }
  }
};

struct MaxSATInstance : public Instance {
  std::vector<int> max_clauses;
  
  int run (char *path, CaDiCaL::Solver *solver, bool verbose, bool grow) {
    read_dimacs (path);
    clauses.append_cnf (k_maximal_q_models (-1, nullptr, verbose, grow));
    for (const std::vector<int> &cl : clauses.content) { solver->clause (cl); }

    for (int i {1}; i <= num_clauses; ++i) {
      while (solver->solve () == CaDiCaL::SATISFIABLE) {
	std::vector<int> candidate;
	std::vector<int> to_block;
	for (int v : selectors) {
	  if (solver->val (v) > 0) { candidate.push_back (v-vars); }
	  else { to_block.push_back (v); }
	}

	if (candidate.size () > max_clauses.size ()) {
	  if (candidate.size () == num_clauses) { std::cout << "SATISFIABLE\n"; return candidate.size (); }
	  else {
	    max_clauses.resize (candidate.size ());
	    std::copy (candidate.cbegin (), candidate.cend (), max_clauses.begin ());

	    KCardNet net_encoder {selectors, (int) max_clauses.size ()+1, aux, 1};
	    std::vector<int> card_clauses {net_encoder.card (net_encoder.data.begin (), net_encoder.data.end (), vars)};
	    clauses.append_expressions (net_encoder.clauses);
	    for (const std::vector<int> cl : net_encoder.clauses) { solver->clause (cl); }
	    clauses.add_clause ({card_clauses[max_clauses.size ()+2]});
	    solver->add (card_clauses[max_clauses.size ()+2]), solver->add (0);
	  }
	}
      }
    }

    if (!max_clauses.empty ()) {
      std::cout << "v ";
      for (int i : max_clauses) { std::cout << i << ' '; }
      std::cout << "0\n";
      return max_clauses.size ();
    }

    return 0;
  }
};

std::vector<int> get_complement (int phize, const std::vector<int> &included) {
  std::vector<int> complement (phize-included.size ());
  auto inter {included.cbegin ()}; auto outter {complement.begin ()};
  for (int i {1}; i <= phize; ++i) {
    if (inter == included.cend () || i != *inter) { *outter = i; ++outter; }
    else { ++inter; }
  }
  return complement;
}

bool growable (const matrix<int> &phi, const std::vector<int> &v_line) {
  std::vector<int> complement {get_complement ((int) phi.size (), v_line)};
  for (int sprout : complement) {
    CaDiCaL::Solver *solver {new CaDiCaL::Solver};
    for (int i : v_line) { solver->clause (phi[i-1]); }
    solver->clause (phi[sprout-1]);
    bool growth {solver->solve () == CaDiCaL::SATISFIABLE};
    delete solver;
    if (growth) { return true; }
  }
  return false;
}

bool test (CaDiCaL::Solver *main_solver, const Instance &instance) {
  for (const std::vector<int> &cl : instance.clauses.content) { main_solver->clause (cl); }

  bool problem {};
  auto func
    { [&problem, &instance] (CaDiCaL::Solver *main_solver) {
      std::vector<int> v_line;
      int selector_start {instance.selectors[0]-1};
      for (int i : instance.selectors) { if (main_solver->val (i) > 0) { v_line.push_back (i-selector_start); } }
      if (growable (instance.data.content, v_line)) {
	std::cout << "Fail ";
	instance.print_maximal_q_model (std::cout, main_solver);
	problem = true;
      }
      else { std::cout << "Pass "; } }};

  instance.enumerate_models (main_solver, func);
  std::cout << '\n';
  return problem;
}

bool read_options (int argc, char **argv, int &k, bool &one_max_q_model, bool &mcs, bool &max_sat, bool &print_v, bool &block_lit, bool &verbose, bool &grow, bool &quick_comp, bool &proj) {
  if (argc < 2) { return false; }
  
  for (int i {2}; i < argc; ++i) {
    if (argv[i][0] != '-') { return false; }

    switch (argv[i][1]) {
    case '1':
      one_max_q_model = true; break;
    case 'c':
      mcs = true; break;
    case 'e':
      grow = true; break;
    case 'g':
      verbose = true; break;
    case 'k':
      if (++i >= argc) { return false; }
      k = std::stoi (argv[i]);
      break;
    case 'l':
      block_lit = true; break;
    case 'm':
      max_sat = true; break;
    case 'n':
      quick_comp = true; break;
    case 'p':
      proj = true; break;
    case 'v':
      print_v = true; break;
    default:
      return false;
    }
  }

  return true;
}

void run_pmc (const char *filename, int k, std::ostream &out) {
  Instance inst;
  inst.read_dimacs (filename);
  inst.clauses.append_cnf (inst.k_maximal_q_models (k));
  out << "c t pmc\n"
      << "p cnf " << inst.aux << ' ' << inst.clauses.content.size ()
      << "\nc p show ";
  for (int c : inst.selectors) { out << c << ' '; }
  out << "0\n";
  inst.print_dimacs (out);
}

int main (int argc, char **argv) {
  int k {-1}; bool one_max_q_model {}, mcs {}, max_sat {}, print_v {}, block_lit {}, verbose {}, grow {}, quick_comp {}, proj {};
  if (!read_options (argc, argv, k, one_max_q_model, mcs, max_sat, print_v, block_lit, verbose, grow, quick_comp, proj)) {
    std::cerr << "Usage: " << argv[0] << " <input cnf> [-1] [-c] [-e] [-g] [-k <k>] [-l] [-m] [-n] [-p] [-v]\n"
	      << "       -1 will seek a single max q-model.\n"
	      << "       -c will print MCSes instead of MSSes.\n"
	      << "       -e will grow SSes to MSSes before retrying.\n"
	      << "       -g will print the number of (not necessarily maximal) SSes as they are found.\n"
	      << "       -l will block original literals while enumerating instead of selectors.\n"
	      << "       -m will do simple MaxSAT.\n"
	      << "       -n will not print M*Ses, just number them.\n"
	      << "       -p will print pcnf with clause selectors as shown variables.\n"
	      << "       -v will print as a competition v line.\n";
    return 1;
  }

  if (proj) {
    run_pmc (argv[1], k, std::cout);
    return 0;
  }
  
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};

  if (max_sat) {
    MaxSATInstance inst;
    int max {inst.run (argv[1], solver, verbose, grow)};
    std::cout << "Size = " << max << '/' << inst.num_clauses << '\n';
  }

  else if (k) {
    Instance inst;
    inst.read_dimacs (argv[1]);

    if (k < 0) {
      inst.clauses.append_cnf (inst.k_maximal_q_models (k, solver, verbose, grow));
      if (quick_comp) { std::cout << "Done" << std::endl; }
      else {
	if (mcs) { print_v ? inst.print_q_mcs_plain (std::cout)    : inst.print_q_mcs_pretty (std::cout); }
	else     { print_v ? inst.print_q_models_plain (std::cout) : inst.print_q_models_pretty (std::cout); }
      }
    }

    else {
      inst.clauses.append_cnf (inst.k_maximal_q_models (k, nullptr, verbose, grow));
      // inst.print_dimacs (std::cout);

      // bool result {test (solver, inst)};
      // std::cout << "Problem found: " << result << '\n';
      // return 0;

      for (const std::vector<int> &cl : inst.clauses.content) { solver->clause (cl); }
      if (one_max_q_model) {
	int status {solver->solve ()};
	inst.print_maximal_q_model (std::cout, solver, print_v);
	// if (solver->status () == CaDiCaL::SATISFIABLE) {for (int i {1}; i <= inst.vars; ++i) { std::cout << solver->val (i) << ' '; } std::cout << '\n'; }
      }
      else {
	while (solver->solve () == CaDiCaL::SATISFIABLE) {
	  inst.print_maximal_q_model (std::cout, solver, print_v);
	  std::vector<int> to_block;
	  if (block_lit) { for (int i {1}; i <= inst.vars; ++i) { to_block.push_back (solver->val (i) > 0 ? -i : i); } }
	  else { for (int v : inst.selectors) { to_block.push_back (solver->val (v) > 0 ? -v : v); } }
	  // for (int i {1}; i <= inst.vars; ++i) { std::cout << solver->val (i) << ' '; } std::cout << '\n';
	  solver->clause (to_block);
	}
      }
    }
  }
  else {
    int vars;
    solver->read_dimacs (argv[1], vars);
    if (solver->solve () == CaDiCaL::SATISFIABLE) {
      std::cout << "v ";
      for (int i {1}; i <= vars; ++i)
	{ std::cout << solver->val (i) << ' '; }
      std::cout << "0\n";
    }
    else { std::cout << "UNSATISFIABLE\n"; }
  }
  
  delete solver;
}
