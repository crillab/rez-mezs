#include "cardinality.hpp"
#include "mus.hpp"
#include "util.hpp"

#include <algorithm>
#include <chrono>
#include <future>
#include <sstream>
#include <string>

void load_solver (CaDiCaL::Solver *solver, const matrix<int> &context) {
  for (const std::vector<int> &clause : context)
    { solver->clause (clause); }
}
  
bool contradictory_clauses (const std::vector<int> &left, const std::vector<int> &right) {
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  solver->clause (left), solver->clause (right);
  bool answer {solver->solve () == CaDiCaL::UNSATISFIABLE};
  delete solver;
  return answer;
}

matrix<int> clause_contains_lit (const std::vector<int> &clause, int literal, int inner_selector, int discluder) {
  matrix<int> binding_i {disjunction (clause, inner_selector)};
  matrix<int> binding_o {conjunction ({-literal, inner_selector}, discluder)};
  binding_i.insert (binding_i.end (), binding_o.begin (), binding_o.end ());
  return binding_i;
}
  
std::vector<int> group_for_threads (const VarSuite &xs, int t_max = 4) {
  int num_threads {(int) std::thread::hardware_concurrency ()};
  if (num_threads > t_max) { num_threads = t_max; }

  if (num_threads > xs.size ()) { return {}; }
  
  std::vector<int> starts (num_threads);
  int step {xs.size () / num_threads}, current {xs.start};
  for (auto iter {starts.begin ()}; iter != starts.end (); ++iter)
    { *iter = current; current += step; }

  return starts;
}

std::vector<int> VarSuite::get_interpretation (CaDiCaL::Solver *solver, bool pos_phase) const {
  std::vector<int> true_lits;
  for (int i {start}; i <= end; ++i) {
    if (solver->val (i) > 0)
      { true_lits.push_back (pos_phase ? i : -i); }
  }
  return true_lits;
}
      
void VarSuite::print_interpretation (std::ostream &out, CaDiCaL::Solver *solver) const {
  if (solver->status () == CaDiCaL::SATISFIABLE) {
    for (int i {start}; i <= end; ++i)
      { out << (solver->val (i) > 0 ? std::to_string (i - start + 1) + "(" + std::to_string (i) +") " : ""); }
    out << '\n';
  }
  else
    { "Solver is not in a satisfied state.\n"; }
}

matrix<int> LitSuite::bind (const std::vector<int> &clause, int &aux) const {
  auto incr { [] (int i) { return i > 0 ? -i : ++i; } };

  matrix<int> answer;
  int blocker {content.start}; int lit {1};
  for (int blocker {content.start}, lit {1}; blocker <= content.end; ++blocker, lit = incr (lit)) {
    matrix<int> contains {clause_contains_lit (clause, lit, ++aux, blocker)};
    answer.insert (answer.end (), contains.begin (), contains.end ());
  }

  return answer;
}

matrix<int> LitInClauseBlockers::bind (const matrix<int> &formula, int &aux) const {
  matrix<int> answer;
    
  auto clause {formula.cbegin ()};
  for (auto suite {blockers.cbegin ()}; suite != blockers.cend (); ++suite, ++clause) {
    matrix<int> binding {suite->bind (*clause, aux)};
    answer.insert (answer.end (), binding.begin (), binding.end ());
  }

  return answer;
}

PermGen::PermGen (int max, int width, int unit, int special_stop) : max {max}, counter (width),
								    stop_for_0 {special_stop ? special_stop : max} {
  fill_rest (counter.begin (), unit-1);
}

bool PermGen::fill_rest (std::vector<int>::iterator iter, int acc) {
  std::transform (iter, counter.end (), iter, [&acc] (int _) { return ++acc; });
  return acc <= max;
}

bool PermGen::fill_rest (int start_idx, int start_val) {
  return fill_rest (std::next (counter.begin (), start_idx), start_val);
}

int PermGen::incr (auto iter) {
  if (++*iter > max)
    { return 0; }
  return *iter;
}

bool PermGen::incr_0 () {
  auto first {counter.begin ()};
  if (++*first <= stop_for_0)
    { return fill_rest (std::next (first), *first); }
  return false;
}

bool PermGen::incr () {
  for (auto iter {counter.rbegin ()}; iter != std::prev (counter.rend ()); ++iter) {
    if (incr (iter) && fill_rest (iter.base (), *iter))
      { return true; }
  }
  return incr_0 ();
}

bool PermGen::skip (int dest) {
  if (dest > stop_for_0) { return false; }
  return fill_rest (counter.begin (), dest-1);
}

std::ostream &operator << (std::ostream &out, const PermGen &pg) {
  for (int c : pg.counter) { out << c << ' '; }
  return out;
}

std::vector<RenameLookup::Rename>::iterator RenameLookup::locate (int orig,
								  std::vector<RenameLookup::Rename>::iterator start,
								  std::vector<RenameLookup::Rename>::iterator end) {
  auto distance {std::distance (start, end)};
  if (!distance) { return end; }
  std::vector<RenameLookup::Rename>::iterator mid {std::next (start, (distance / 2))};
  if (mid->orig == orig) { return mid; }
  return mid->orig > orig ? locate (orig, start, mid) : locate (orig, std::next (mid), end);
}

int RenameLookup::insert (int num) {
  auto pos {locate (num)};
  if (pos == mappings.end ()) {
    mappings.push_back ({num, ++counter});
    return counter;
  }
  else if (num == pos->orig)
    { return pos->loc; }
  else {
    auto dist {distance (mappings.begin (), pos)};
    mappings.resize (mappings.size () + 1);
    Rename current {num, ++counter};
    for (auto pos {std::next (mappings.begin (), dist)}; pos != mappings.end (); ++pos) 
      { Rename tmp {*pos}; *pos = current; current = tmp; }
    return counter;
  }
}

Grouping::Grouping (int num_clauses, int k, int v_start)
  : ys (k < num_clauses ? k : 0), k {k}, vars {v_start} {
  auto single_suite { [this, &num_clauses] (VarSuite &construenda, int length) { construenda = VarSuite {vars+1, length}; vars = construenda.end; } };
  single_suite (xs, num_clauses); single_suite (ss, num_clauses);
  for (int i {}; i < ys.size (); ++i)
    { single_suite (ys[i], num_clauses); }
}
    
void Grouping::add_clause (const std::vector<int> &clause, int idx) {
  clauses[idx] = clause;
}

void Grouping::add_clause (const std::vector<int> &clause, matrix<int> &destination) {
  destination.push_back (clause);
}
void Grouping::add_clause (const std::vector<int> &clause) {
  add_clause (clause, clauses);
}
void Grouping::add_candidate (const std::vector<int> &clause) {
  add_clause (clause, candidates);
}

void Grouping::add_clause (const matrix<int> &cl) {
  clauses.insert (clauses.end (), cl.cbegin (), cl.cend ());
}

int Grouping::sum_seq (int start, int end, int important_var) {
  SeqEncoding seq_encoder {vars, 1+end - start};
  vars = seq_encoder (start, end, vars);
  add_clause (seq_encoder.get_clauses ());
  return seq_encoder.kth_var (important_var);
}

int Grouping::sum_sort (int start, int end, int k) {
  std::vector<int> data (end - start + 1);
  std::iota (data.begin (), data.end (), start);
  KCardNet net_encoder {data, k, vars, 0};
  std::vector<int> card_clauses {net_encoder.card (net_encoder.data.begin (), net_encoder.data.end (), vars)};
  add_clause (net_encoder.clauses); add_clause (card_clauses); add_clause (std::vector<int> {-card_clauses[k]});
  return card_clauses[k-1];
}

int Grouping::sum (int start, int end, int k) {
  return sum_sort (start, end, k);
}
  
void Grouping::exactly_k (int amount, int start, int end) {
  int length {1+end - start}; 
  if (length >= amount) {
    int kth {sum (start, end, amount)};
    add_clause (std::vector<int> {kth}); 
    // if (amount > 0) { add_clause (std::vector<int> {kth}); }
    // if (length > amount) { add_clause (std::vector<int> {-kth-1}); }
  }
}

int Grouping::at_most_k (int k, int start, int end) {
  std::vector<int> data (end - start + 1);
  std::iota (data.begin (), data.end (), start);
  KCardNet net_encoder {data, k, vars, -1};
  std::vector<int> card_clauses {net_encoder.card (net_encoder.data.begin (), net_encoder.data.end (), vars)};
  add_clause (net_encoder.clauses); add_clause (card_clauses);
  return card_clauses [k];
}

void Grouping::x_sum () {
  exactly_k (k, xs.start, xs.end);
}
void Grouping::y_sum () {
  for (auto y_suite : ys) { exactly_k (k-1, y_suite.start, y_suite.end);  }
}
void Grouping::z_sum () {
  add_clause (std::vector<int> {-at_most_k (k-1, ss.start, ss.end)});
}

void Grouping::cardinalities () {
  x_sum (); y_sum (); z_sum ();
}

void Grouping::bind_blockers (const matrix<int> &rules, const LitInClauseBlockers &blockers, int num_lits) {
  clauses.insert (clauses.end (), rules.cbegin (), rules.cend ());
  auto incr_lit { [] (int i) { return i > 0 ? -i : ++i; } };
  
  for (int i {1}; i <= xs.size (); ++i) {
    for (int j {1}; j <= xs.size (); ++j) {
      if (i == j) { continue; }
      for (int lit {1}; lit != -num_lits; lit = incr_lit (lit)) {
	for (int y_chunk {0}; y_chunk < ys.size (); ++y_chunk) {
	  int term {++vars};
	  matrix<int> aux_implies (term, {y (y_chunk, j), -blockers.idx (j, -lit)});
	  std::cout << y (y_chunk, i) << ' ' << -x (i) << ' ' << term << ' ' << blockers.idx (i, lit) << " 0\n";
	  add_clause ({y (y_chunk, i), -x (i), term, blockers.idx (i, lit)});
	}
      }
    }
  }
}
  
void Grouping::bind_xcs (const Instance &inst) {
  int x_var {x (1)}, s_var {s (1)};
  for (auto clause {inst.clauses.cbegin ()}; clause != inst.clauses.cend (); ++clause, ++x_var, ++s_var) {
    int aux {++vars};
    add_clause (implied_by_clause (aux, *clause));
    add_clause ({-x_var, -aux, s_var});
  }
}

void Grouping::bind_yxs () {
  int skip {};
  for (auto block {ys.cbegin ()}; block != ys.cend (); ++block, ++skip) {
    for (int x_var {x (1)}, y_var {block->start}, sz_var {s (1)}, idx {};
	 y_var <= block->end; ++x_var, ++y_var, ++sz_var, ++idx) {
      if (idx == skip) { ++x_var, ++sz_var; }
      add_clause ({-y_var, x_var});
      add_clause ({-sz_var, y_var});
    }
  }
}

void Grouping::bind_pseudo_selectors (const Instance &inst) {
  bind_xcs (inst);
  bind_yxs ();
}

std::vector<int> Grouping::fresh_dupl (RenameLookup &map, std::vector<int> clause, bool negated) {
  std::transform (clause.cbegin (), clause.cend (), clause.begin (),
		  [&map, negated] (int lit) mutable { return negated ? -map.image (lit) : map.image (lit) ; });
  return clause;
}
  
void Grouping::bind_originals (const Instance &inst) {
  int x_var {x (1)}, z_var {s (1)};
  for (auto clause_iter {inst.clauses.cbegin ()}; clause_iter != inst.clauses.cend (); ++x_var, ++z_var, ++clause_iter) {
    add_clause ({-z_var, x_var});
    int aux {++vars};
    add_clause (disjunction (*clause_iter, aux));
    add_clause ({-aux, -x_var, z_var});
  }
}

void Grouping::bind_duplicates (const Instance &inst) {
  for (auto y_block {ys.cbegin ()}; y_block != ys.cend (); ++y_block) {
    int x_var {x (1)}, y_var {y_block->start};
    RenameLookup map {vars};
    for (auto clause_iter {inst.clauses.cbegin ()} ; clause_iter != inst.clauses.cend (); ++x_var, ++y_var, ++clause_iter) {
      add_clause ({-y_var, x_var});
      std::vector<int> cl_dupl {fresh_dupl (map, *clause_iter, true)};
      int aux {++map.counter};
      add_clause (disjunction (cl_dupl, aux));
      add_clause ({-aux, -x_var, y_var});
      add_clause ({-y_var, aux});
    }
    vars = map.counter;
  }
}
  
void Grouping::different_ys () {
  for (auto block1 {ys.cbegin ()}; block1 != ys.cend (); ++block1) {
    for (auto block2 {std::next (block1)}; block2 != ys.cend (); ++block2) {
      std::vector<int> clause (xs.size ());
      auto disjunct {clause.begin ()};
      for (int j {block1->start}, j_prime {block2->start}; disjunct != clause.cend (); ++j, ++j_prime, ++disjunct)
 	{ *disjunct = ++vars; add_clause (conjunction ({j, -j_prime}, *disjunct)); }
      add_clause (clause);
    }
  }
}

void Grouping::different_ys (int n) {
  for (auto block1 {ys.cbegin ()}; block1 != ys.cend (); ++block1) {
    for (auto block2 {std::next (block1)}; block2 != ys.cend (); ++block2) {
      std::vector<int> clause (n);
      auto disjunct {clause.begin ()};

      int gap1 {(int) std::distance (ys.cbegin (), block1)+1}, gap2 {(int) std::distance (ys.cbegin (), block2)};
      
      for (int j {block1->start}, j_prime {block2->start}; disjunct != clause.cend (); ++j, ++j_prime, ++disjunct) {
	if (!--gap1) { ++j_prime; }
	if (!--gap2) { *disjunct = j; --j_prime; }
	else 
	  { *disjunct = ++vars; add_clause (conjunction ({j, -j_prime}, *disjunct)); }
      }

      add_clause (clause);
    }
  }
}

// void Grouping::ovlp_k_pred_k () {
// }

void Grouping::bind_x_directly (int clause_number, int x_number, std::vector<int> clause) {
  int clause_size {(int) clause.size ()};
  clause.resize (clause_size + 1);
  clause[clause_size] = x_number;
  add_clause (clause, clause_number);
}
    
void Grouping::bind_x_directly (int clause_number, std::vector<int> clause) {
  bind_x_directly (clause_number, x (clause_number), clause);
}

void Grouping::k_is_one (const Instance &inst) {
  int clause_number {(int) clauses.size ()}, selector {xs.start};
  clauses.resize (clause_number + xs.size ());

  for (const std::vector<int> &clause : inst.clauses) {
    bind_x_directly (clause_number, selector, clause);
    ++selector; ++clause_number;
  }
}  

void Grouping::apply (const Instance &inst) {
  cardinalities ();

  if (k > 1) {
    bind_pseudo_selectors (inst);
    different_ys ((int) inst.clauses.size () - 1);
  }
  else
    { k_is_one (inst); }
}

void Grouping::apply_duplicated (const Instance &inst) {
  cardinalities ();
  bind_duplicates (inst); bind_originals (inst);
  different_ys ();
}

void Grouping::print_header (std::ostream &out) {
  out << "p cnf " << vars << ' ' << clauses.size ()
      << "\nc k    = " << ys.size () << '\n';
}
  
void Grouping::print_dimacs (std::ostream &out, bool header) {
  if (header) { print_header (out); }
  print_cnf (out, clauses);
}

int Grouping::check_sat (CaDiCaL::Solver *solver) {
  for (const matrix<int> &collection : {clauses, candidates}) {
    for (const std::vector<int> &clause : collection)
      { solver->clause (clause); }
  }
  solution_status = solver->solve ();
  return solution_status;
}

void Grouping::get_candidate (CaDiCaL::Solver *solver) {
  if (solution_status == CaDiCaL::SATISFIABLE) 
    { add_candidate (xs.get_interpretation (solver, false)); }
}

void Grouping::print_interpretation (std::ostream &out, CaDiCaL::Solver *solver) const {
  if (solution_status != CaDiCaL::SATISFIABLE) { return ; }

  out << "xs: "; xs.print_interpretation (out, solver);
  out << "ss: "; ss.print_interpretation (out, solver);
  for (int i {}; i < ys.size (); ++i)
    { out << 'y' << i << ": "; ys[i].print_interpretation (out, solver); }
}

CodeType Grouping::encode_candidate (const std::vector<int> &candidate) const {
  CodeType code {};
  int origin {-xs.start};

  for (int cl : candidate) 
    { code += (1 << (origin - cl)); }

  return code;
}

std::vector<CodeType> Grouping::unsubsumed_complement (const matrix<int> &sat_subsets,
						       const std::vector<CodeType> &priors) {
  std::vector<CodeType> setminus;
  CodeType available {choose (xs.size (), k)};
  if (available == sat_subsets.size ())
    { return setminus; }

  std::vector<CodeType> comparisons (sat_subsets.size ());
  auto subset {sat_subsets.cbegin ()};
  for (auto comp {comparisons.begin ()}; comp != comparisons.end (); ++comp, ++subset)
    { *comp = encode_candidate (*subset); }
  comparisons.insert (comparisons.end (), priors.cbegin (), priors.cend ());
    
  auto unsubsumed
    { [this, &comparisons] (int code) {
      for (int comp : comparisons)
	{ if (subsumes (comp, code)) { return false; } }
      return true;
    }};
  auto k_bits
    { [this] (int number) {
      int tally {};
      for ( ; number; ++tally) {
	if (tally > k)
	  { return false; }
	number &= number - 1;
      }
      return tally == k;
    }};

  int start {(1 << k) - 1};
  int end {start << (xs.size () - k)};
  
  for (int pos_mus {start}; pos_mus <= end; ++pos_mus) {
    if (k_bits (pos_mus) && unsubsumed (pos_mus))
      { setminus.push_back (pos_mus); }
  }

  return setminus;
}

bool update_min (int orig, int poss) {
  if (orig < 0) { return poss; }
  return orig > poss ? poss : orig;
}

bool Grouping::cohere_different_type (const std::vector<int> &counter,
				      matrix<int>::const_iterator current,
				      matrix<int>::const_iterator end,
				      int &min, bool phase) const {
  auto comp
    { [] (auto s1, auto e1, auto s2, auto e2, bool phase) {
      while (true) {
	if (s2 == e2) { return 0; }
	if (s1 == e1) { return 1; }

	int star_s2 {phase ? *s2 : -*s2};
	if (*s1 == star_s2) { ++s1; ++s2; }
	else if (*s1 < star_s2) { ++s1; }
	else { return -1; }
      }
    }};

  for ( ; current != end; ++current) {
    int cmp {comp (counter.cbegin (), counter.cend (), current->cbegin (), current->cend (), phase)};
    switch (cmp) {
    case 0:
      return true;
    case 1:
      min = update_min (min, phase ? *current->cbegin () : -*current->cbegin ());
      return false; 
    }
  }
  return false;
}

bool Grouping::cohere_same_type (PermGen &pg, matrix<int>::const_iterator current,
				 matrix<int>::const_iterator end, int &min) const {
  auto comp
    { [] (auto this_iter, auto that_iter, auto that_end) {
      // 0 means equal. -1 means that < this; +x means this < that and x is the next lowest value.
      while (that_iter != that_end) {
	if (*this_iter == *that_iter)
	  { ++this_iter, ++that_iter; }
	else if (*this_iter < *that_iter)
	  { return *that_iter; }
	else
	  { return -1; }
      }
      return 0;
    }};

  while (current != end) {
    int status {comp (pg.counter.begin (), current->cbegin (), current->cend ())};
    switch (status) {
    case 0:
      return true;
    case -1:
      ++current;
      break;
    default:
      min = update_min (min, current->at (0));
      return false;
    }
  }
  return false;
}
 
int Grouping::unsubsumed_complement (matrix<int> sat_subsets, Instance &inst, int t_num) {
  if (choose (xs.size (), k) == sat_subsets.size ())
    { return CaDiCaL::SATISFIABLE; }

  auto less_than
    { [] (const std::vector<int> &left, const std::vector<int> &right) {
      for (auto liter {left.cbegin ()}, riter {right.cbegin ()}; liter != left.cend (); ++liter, ++riter) {
	if (*liter < *riter) { return true; }
	if (*riter < *liter) { return false; }
      }
      return false;
    }};
  std::sort (sat_subsets.begin (), sat_subsets.end (), less_than);

  auto check_sec
    { [this, &inst, &sat_subsets] (int x_end, int k, int x_start, int zero_end) {
      int min {-1};
      auto smaller_starts {inst.type_starts ()};
      auto smaller_ends {inst.type_ends (smaller_starts)};
      auto current_start {sat_subsets.cbegin ()};
      PermGen pg {x_end, k, x_start, zero_end};
      
      matrix<int> candidates;
      auto propose_candidate
	{ [&candidates, &inst] (const std::vector<int> &clauses) {
	  int idx ((int) candidates.size ());
	  candidates.resize (idx+1);
	  candidates[idx].resize (clauses.size ());
	  std::transform (clauses.cbegin (), clauses.cend (), candidates[idx].begin (), [] (int c) { return -c; });
	  inst.print_mus (std::cout, candidates[idx]); std::cout << std::endl;
	}};

      while (pg.safe ()) {
	bool subsumed {};
	auto end {smaller_ends.cbegin ()};
	for (auto begin {smaller_starts.begin ()}; begin != smaller_starts.end (); ++begin, ++end) {
	  if (cohere_different_type (pg.counter, *begin, *end, min, false))
	    { subsumed = true; break; }
	}

	if (!subsumed) {
	  if (cohere_same_type (pg, current_start, sat_subsets.cend (), min))
	    { subsumed = true; }
	}

	if (!subsumed && pg.safe ())
	  { propose_candidate (pg.counter); }

	if (min > pg.counter[0]) 
	  { if (!pg.skip (min)) { break; } }
	else if (!pg.incr ())   { break; }
      }

      return candidates;
    }};

  matrix<int> candidates;
  std::vector<int> partitions {group_for_threads (xs, t_num)};
  
  if (partitions.size () <= 1 || partitions[1] <= partitions[0]) 
    { candidates = check_sec (xs.end, k, xs.start, xs.end); }
  else {
    std::vector<std::future<matrix<int>>> futures (partitions.size ());
    auto part_point {partitions.cbegin ()};
    for (auto &fut : futures) {
      auto succ {std::next (part_point)};
      fut = std::async (check_sec, xs.end, k, *part_point, succ == partitions.cend () ? xs.end : *std::next (part_point) - 1);
      ++part_point;
    }

    for (auto &fut : futures) {
      const matrix<int> &got {fut.get ()};
      candidates.insert (candidates.end (), got.begin (), got.end ());
    }
  }

  inst.mark_size_step ();
  inst.block (candidates);
 
  return solution_status;
}
  
int Grouping::check_subset_satisfiability (Instance &inst, const std::vector<int> &on_xs) const {
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  for (int cl_idx : on_xs)
    { solver->clause (inst.clauses[cl_idx - xs.start]); }
  int status {solver->solve ()};
  delete solver;
  return status;
}

bool Grouping::query (Instance &inst, matrix<int> &subsets, auto &&test, int time_limit, const matrix<int> &additional) {
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  load_solver (solver, clauses); load_solver (solver, inst.mus_blockers);
  solution_status = solver->solve ();

  bool check_time {time_limit > 0}, time_out {};
  auto t_w {std::chrono::system_clock::now () + std::chrono::seconds (time_limit)};
  
  while (solution_status != CaDiCaL::UNSATISFIABLE && !time_out) {
    std::vector<int> model {xs.get_interpretation (solver, true)};
    if (test (inst, model)) {
      std::vector<int> replace (model.size ());
      std::transform (model.cbegin (), model.cend (), replace.begin (), [] (int i) { return -i; });
      inst.print_mus (std::cout, replace); std::cout << std::endl;
      subsets.push_back (replace);
    }
    for (int var : model) { solver->add (-var); } solver->add (0);

    solution_status = solver->solve ();
    if (check_time && std::chrono::system_clock::now () > t_w) { time_out = true; }
  }

  delete solver;
  return !time_out;
}

int Grouping::sat_set_test (bool verbose, Instance &inst) {
  // finding all xSS type k
  CodeType available {choose (xs.size (), (int) ys.size ())};

  int i {};
  matrix<int> satisfiables;
  while (solution_status != CaDiCaL::UNSATISFIABLE) {
    CaDiCaL::Solver *solver {new CaDiCaL::Solver};

    for (const std::vector<int> &block : satisfiables) 
      { solver->clause (block); }

    check_sat (solver);
    if (solution_status == CaDiCaL::SATISFIABLE) {
      add_clause (xs.get_interpretation (solver, false), satisfiables);
      if (verbose) {
	std::cout << "X: "; xs.print_interpretation (std::cout, solver); 
	int i {};
	for (auto y_suite : ys)
	  { std::cout << "Y" << ++i << ": ";  y_suite.print_interpretation (std::cout, solver); }
      }
    }
    delete solver;

    if (satisfiables.size () == available)
      { break; }
  }

  inst.block (unsubsumed_complement (satisfiables, inst.mus_codes), xs.start);

  if (satisfiables.empty ())
    { return 0; }
    
  return solution_status;
}

void Grouping::sat_set_test (Instance &inst, matrix<int> &satisfiables) {
  query (inst, satisfiables, [] (Instance &, std::vector<int> &) { return true; });
}

int Grouping::unsat_test (bool _, Instance &inst) {

  auto check_sec
    { [&inst] (int k, int xs_begin, int xs_last, int zero_begin, int zero_last, const CaDiCaL::Solver *solver) {

      auto unsubsumed
	{ [&inst] (const std::vector<int> &stronger) {
	  for (const std::vector<int> &weaker : inst.mus_blockers) 
	    { if (subsumes (weaker, stronger, -2)) { return false; } }
	  return true;
	}};

      CaDiCaL::Solver local_solver;
      solver->copy (local_solver);

      for (int x_i {xs_begin}; x_i < zero_begin; ++x_i)
	{ local_solver.add (-x_i), local_solver.add (0); }
      for (int x_i {zero_begin}; x_i <= zero_last; ++x_i)
	{ local_solver.add (x_i); }
      local_solver.add (0); 
      
      matrix<int> candidates;
	
      if (local_solver.solve () == CaDiCaL::SATISFIABLE) {
	PermGen pg {xs_last, k, zero_begin, zero_last};
	if (pg.safe ()) {
	  std::vector<int> to_block (k);
	  do {
	    if (unsubsumed (pg.counter)) {
	      std::cout << pg << std::endl;
	      auto negandum {to_block.begin ()};
	      for (int c : pg.counter)
		{ local_solver.assume (c); *negandum++ = -c; }
	    }
	    if (local_solver.solve () == CaDiCaL::UNSATISFIABLE) {
	      candidates.push_back (to_block);
	      inst.print_mus (std::cout, to_block);
	      std::cout << '\n';
	    }
	  } while (pg.incr ());
	}
      }

      return candidates;
    }};

  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  load_solver (solver, clauses); load_solver (solver, inst.mus_blockers);
  if (solver->solve () == CaDiCaL::UNSATISFIABLE)
    { delete solver; return 0; }
  
  std::vector<int> starts {group_for_threads (xs)};
  if (starts.empty () || starts[1] <= starts[0]) {
    matrix<int> candidates {check_sec (k, xs.start, xs.end, xs.start, xs.end, solver)};
    inst.block (candidates);
  }
  else {
    std::vector<std::future<matrix<int>>> futures (starts.size ());

    auto start_points {starts.cbegin ()}; 
    for (auto &fut : futures) {
      auto succ {std::next (start_points)};
      fut = std::async (check_sec, k, xs.start, xs.end, *start_points, succ == starts.cend () ? xs.end : *std::next (start_points) - 1, solver);
      ++start_points;
    }

    for (auto &fut : futures) {
      const matrix<int> &got {fut.get ()};
      inst.block (got);
    }
  }
  
  solution_status = inst.mus_blockers.empty () ? CaDiCaL::SATISFIABLE : CaDiCaL::UNSATISFIABLE;
  return solution_status;
}
 
bool Grouping::unsat_test (Instance &inst, matrix<int> &muses, int time_limit, const matrix<int> &additional) {
  bool answer {query (inst, muses,
		      [this] (Instance &inst, std::vector<int> &model) {
			return check_subset_satisfiability (inst, model) == CaDiCaL::UNSATISFIABLE; },
		      time_limit)};

  inst.mus_blockers.insert (inst.mus_blockers.end (), muses.cbegin (), muses.cend ());
  return answer;
}

int Grouping::check_type_by_complement (Instance &inst, int t_num) {
  matrix<int> sat_subsets;
  sat_set_test (inst, sat_subsets);
  return unsubsumed_complement (sat_subsets, inst, t_num);
}

int Grouping::check_type (Instance &inst, int t_num, int k) {
  // std::vector<int> starts {group_for_threads (xs, t_num)};
  // std::vector<std::future<matrix<int>>> futures (starts.size ());

  // for (int start : starts) {

  matrix<int> sat_subsets;
  if (unsat_test (inst, sat_subsets, inst.secs_per_k))
    { std::cout << "Completed:" << k << std::endl; }
  else { std::cout << "TO:" << k << std::endl; }
  
  return solution_status;
}
  
void Instance::mark_size_step () {
  indices_of_mus_size_shifts.push_back ((int) mus_blockers.size ());
}

std::vector<matrix<int>::const_iterator> Instance::type_starts () const {
  std::vector<matrix<int>::const_iterator> starts (indices_of_mus_size_shifts.size () + 1);
  auto iter {starts.begin ()}; *iter = mus_blockers.begin ();
  for (int idx : indices_of_mus_size_shifts)
    { *++iter = std::next (mus_blockers.begin (), idx); }
  return starts;
}

std::vector<matrix<int>::const_iterator> Instance::type_ends (const std::vector<matrix<int>::const_iterator> &starts) const {
  std::vector<matrix<int>::const_iterator> ends (starts.size ());
  auto riter {ends.rbegin ()}; *riter = mus_blockers.end (); ++riter;
  std::copy (starts.crbegin (), std::prev (starts.crend ()), riter);
  return ends;
}

matrix<int> Instance::decode_as_clauses (int code) const {
  matrix<int> subset;
  int bit {1};

  for (auto cl {clauses.cbegin ()}; cl != clauses.cend () && bit <= code; bit <<= 1, ++cl) {
    if (code & bit)
      { subset.push_back (*cl); }
  }

  return subset;
}

std::vector<int> Instance::decode_to_block (int code, int xs_start) const {
  std::vector<int> clause;
  int n_lit {-xs_start};

  for ( ; code; code >>= 1, --n_lit) {
    if (code & 1)
      { clause.push_back (n_lit); }
  }

  return clause;
}

void Instance::block (const matrix<int> &to_block) {
  mus_blockers.insert (mus_blockers.end (), to_block.cbegin (), to_block.cend ());
}

void Instance::block (const std::vector<CodeType> &new_codes, const matrix<int> &to_block, int xs_var_start) {
  mus_codes.insert (mus_codes.end (), new_codes.cbegin (), new_codes.cend ());
  block (to_block);
}

void Instance::block (const std::vector<CodeType> &fresh_codes, int xs_start) {
  matrix<int> to_block (fresh_codes.size ());
  auto code {fresh_codes.cbegin ()};
  for (auto block {to_block.begin ()}; block != to_block.end (); ++block, ++code)
    { *block = decode_to_block (*code, xs_start); }
  block (to_block);
  
  block (fresh_codes, to_block, xs_start);
}

int Instance::k_is_two (int x_var_start) {
  if (clauses.size () < 2)
    { return CaDiCaL::SATISFIABLE; }

  auto encode { [x_var_start] (int idx) { return 1 << (idx - x_var_start); } };

  matrix<int> blockers;
  std::vector<CodeType> codes;
  
  int l_idx {x_var_start};
  for (auto l_clause {clauses.cbegin ()}; l_clause != clauses.cend (); ++l_clause, ++l_idx) {
    int r_idx {l_idx + 1};
    for (auto r_clause {std::next (l_clause)}; r_clause != clauses.cend (); ++r_clause, ++r_idx) {
      if (contradictory_clauses (*l_clause, *r_clause)) {
	blockers.push_back ({-l_idx, -r_idx});
	codes.push_back (encode (l_idx) + encode (r_idx));
      }
    }
  }

  block (codes, blockers, x_var_start);
  print_muses (std::cout);
  
  return codes.empty () ? CaDiCaL::SATISFIABLE : CaDiCaL::UNSATISFIABLE; 
}

int Instance::check_sat () {
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  
  for (const matrix<int> &collection : {clauses, mus_blockers}) {
    for (const std::vector<int> &cl : collection)
      { solver->clause (cl); }
  }
  
  int status {solver->solve ()};
  delete solver;
  return status;
}
  
// int check_sat (const std::vector<int> &clauses) { return 0; }
  
int Instance::find_mus (int k, int t_num) {
  int status {CaDiCaL::SATISFIABLE};
  if (k <= 1)
    { return status; }

  Grouping grouping {clause_num, k, vars};
  if (grouping.ys.empty ()) {
    status = check_sat ();
    if (status == CaDiCaL::SATISFIABLE)
      { std::cout << "Instance is satisfiable.\n"; }
    else
      { std::cout << "Instance is unsatisfiable.\n"; }
    return status;
  }

  if (k == 2)
    { return k_is_two (grouping.xs.start); }

  grouping.apply_duplicated (*this);
  return grouping.check_type (*this, t_num, k);
}

int Instance::find_one_mus (int k_end, int t_num) {
  if (k_end <= 0) { k_end = clause_num; }
    
  int status {};

  for (int type {2}; type <= k_end; ++type) {
    status = find_mus (type, t_num);
    if (status == CaDiCaL::UNSATISFIABLE) {
      std::cout << "UNSATISFIABLE at type " << type << '\n';
      return status;
    }
  }

  std::cout << "Instance satisfiable at type " << k_end << '\n';
  return status;
}

int Instance::find_all_muses (int k_end, int t_num, int k_start) {
  if (k_start < 0 || k_start > clause_num) { k_start = 2; }
  if (k_end <= 0 || k_end > clause_num) { k_end = clause_num; }

  int status {CaDiCaL::SATISFIABLE};
    
  for (int type {k_start}; type <= k_end; ++type) {
    status = find_mus (type, t_num);
    if (!status) {
      status = CaDiCaL::UNSATISFIABLE;
      break;
    }
  }
  
  if (status == CaDiCaL::UNSATISFIABLE) {
    std::cout << "MUSes:\n";
    if (mus_blockers.empty ()) { print_pretty (std::cout, clauses); std::cout << '\n'; }
    else { print_muses (std::cout); }
  }
  else if (k_end == clauses.size ())
    { std::cout << "Instance satisfiable.\n"; }
  else
    { std::cout << "Satisfiable up to type " << k_end << ".\n"; }
    
  return status; 
}

int Instance::layer_k (int k, int t_num) {
  if (k <= 0 || k > clause_num) { k = clause_num; }
  int status {find_mus (k, t_num)};
  std::cout << "MUS Candidates type " << k << ":\n";
  print_muses (std::cout);
  return status;
}

int Instance::overlapping_k (int k, int t_num) {
  int status {CaDiCaL::SATISFIABLE};
  if (k <= 1) { return status; }

  LitInClauseBlockers lic_blockers {clause_num, vars, vars};
  int aux {lic_blockers.end_var ()};
  matrix<int> lits_in_clauses {lic_blockers.bind (clauses, aux)};

  Grouping grouping {clause_num, k, aux};
  if (grouping.ys.empty ()) {
    status = check_sat ();
    if (status == CaDiCaL::SATISFIABLE)
      { std::cout << "Instance is satisfiable.\n"; }
    else
      { std::cout << "Instance is unsatisfiable.\n"; }
    return status;
  }

  if (k == 2)
    { return k_is_two (grouping.xs.start); }

  grouping.apply_duplicated (*this);
  grouping.bind_blockers (lits_in_clauses, lic_blockers, vars);
  return grouping.check_type (*this, t_num, k);
}

void Instance::direct_init (matrix<int> clauses, int vars) {
  this->clauses = clauses;
  this->vars    = vars;
}

void Instance::read_header (std::ifstream &dimacs) {
  std::string word;
  dimacs >> word >> word >> vars >> clause_num;
  clauses.resize (clause_num);
}

bool Instance::read_clause (std::ifstream &dimacs, int idx) {
  int lit;
  while (true) {
    dimacs >> lit;
    if (lit)
      { clauses[idx].push_back (lit); }
    else
      { return true; }
  }
}
	   
void Instance::read_dimacs (char *path) {
  std::ifstream dimacs {path};
  while (dimacs.peek () == 'c') { discard_comment (dimacs); }
  read_header (dimacs);

  for (int i {}; i < clause_num && !dimacs.eof (); ++i)
    { if (!read_clause (dimacs, i)) { --i; } }
}

void Instance::print_dimacs (std::ostream &out, bool header) const {
  if (header) { out << "p cnf " << vars << ' ' << clause_num << '\n'; }
  print_cnf (out, clauses);
}

void Instance::print_mus (std::ostream &out, const std::vector<int> &blocker) const {
  if (blocker.empty ()) { return; }

  auto inter {blocker.cbegin ()};
  print_disjunction (out, clauses[-*inter-vars-1]);

  for (++inter; inter != blocker.cend (); ++inter) 
    { out << " ∧ "; print_disjunction (out, clauses[-*inter-vars-1]); }
}

void Instance::print_muses (std::ostream &out) const {
  if (mus_blockers.empty ()) { return; }

  for (auto outer {mus_blockers.cbegin ()}; outer != mus_blockers.cend (); ++outer)
    { print_mus (out, *outer); out << '\n'; }
}

void Instance::print_mus_value (std::ostream &out, const std::vector<int> &blocker) const {
  if (blocker.empty ()) { return; }
  out << "v ";
  for (int b : blocker) { out << 1-(b+clause_num) << ' '; }
  std::cout << "0\n";
}

void Instance::print_muses_values (std::ostream &out) const {
  if (mus_blockers.empty ()) { return; }
  for (auto outer {mus_blockers.cbegin ()}; outer != mus_blockers.cend (); ++outer)
    { print_mus_value (out, *outer); }
}

void run_layer (char *path, int k, int t_num, int time_out) {
  Instance instance;
  instance.read_dimacs (path);
  instance.secs_per_k = time_out;
  instance.layer_k (k, t_num);
}

void run_limit (char *path, int k_end, int t_num, int time_out) {
  Instance instance;
  instance.read_dimacs (path);
  instance.secs_per_k = time_out;
  instance.find_all_muses (k_end, t_num);
}

void run_range (char *path, int k_start, int k_end, int t_num, int time_out) {
  Instance instance;
  instance.read_dimacs (path);
  instance.secs_per_k = time_out;
  instance.find_all_muses (k_end, t_num, k_start);
}

void run_overlapping (char *path, int k_end, int t_num, int time_out) {
  Instance instance;
  instance.read_dimacs (path);
  instance.secs_per_k = time_out;
  instance.overlapping_k (k_end, t_num);
}

bool read_options (int argc, char **argv, int &k_start, int &k_end, int &thread_num, int &time_out, bool &layer, std::string &path) {
  for (int i {1}; i < argc; ++i) {
    if (argv[i][0] != '-') { return false; }

    switch (argv[i][1]) {
    case 'K':
      if (++i >= argc) { return false; }
      k_start = std::stoi (argv[i]);
      break;
    case 'c':
      if (++i >= argc) { return false; }
      time_out = std::stoi (argv[i]);
      break;
    case 'i':
      if (++i >= argc) { return false; }
      path = argv[i];
      break;
    case 'k':
      if (++i >= argc) { return false; }
      k_end = std::stoi (argv[i]);
      break;
    case 'l':
      layer = true;
      break;
    case 't':
      if (++i >= argc) { return false; }
      thread_num = std::stoi (argv[i]);
    default:
      return false;
    }
  }

  return !path.empty ();
}
  
int main (int argc, char **argv) {
  std::string path;
  bool layer {}, range {};
  int k_end {-1}, time_out {-1}, k_start {2};
  int thread_num {4};

  if (!read_options (argc, argv, k_start, k_end, thread_num, time_out, layer, path)) {
    std::cerr << "Usage: " << argv[0] << " -i <input cnf> [-l][-r] [-k <k>] [-K <k start>] [-t <max cpus>] [-c <sec per layer>]\n"
	      << "       -l considers the layer of type k.\n"
	      << "       -r considers the range from K to k (lower precedence than -l).\n";
    return 1;
  }
  
  if (layer)
    { run_layer (const_cast<char *> (path.c_str ()), k_end, thread_num, time_out); }
  else if (range)
    { run_range (const_cast<char *> (path.c_str ()), k_start, k_end, thread_num, time_out); }
  else
    { run_limit (const_cast<char *> (path.c_str ()), k_end, thread_num, time_out); }
}
