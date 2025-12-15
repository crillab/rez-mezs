#include "cadical.hpp"

#include "cardinality.hpp"
#include "util.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<T>>;

struct Node {
  char type;
  int idx;
  std::vector<int> children;

  bool operator < (const Node &other) const { return idx < other.idx; }
  bool operator == (const Node &other) const { return type == other.type && idx == other.idx; }
};

std::ostream &operator << (std::ostream &out, const Node &node) {
  out << node.type << ':' << node.idx;
  return out;
}

struct Edge {
  int src, dest;
  std::vector<int> literals;

  bool operator < (const Edge &other) const {
    if (src == other.src) {
      if (dest == other.dest) { return literals < other.literals; }
      return dest < other.dest;
    }
    return src < other.src;
  }
};

std::ostream &operator << (std::ostream &out, const Edge &edge) {
  out << edge.src << "-[";
  for (int l : edge.literals) { out << l << ','; }
  out << (edge.literals.empty () ? "" : "\b") << "]->" << edge.dest;
  return out;
}

struct Path {
  std::set<int> literals;
  std::vector<int> nodes;
};

std::ostream &operator << (std::ostream &out, const Path &path) {
  out << "T = " << *path.nodes.cbegin () << '\n';
  out << "Lit = "; for (int lit : path.literals) { out << lit << ' '; } out << '\n';
  for (auto iter {path.nodes.crbegin ()}; iter != path.nodes.crend (); ++iter) 
    { out << *iter << ' '; }
  return out;
}

Node read_node (std::stringstream &line) {
  char type; int idx;
  line >> type >> idx;
  return Node {type, idx};
}

Edge read_edge (std::stringstream &line) {
  int src, dest, lit;
  line >> src >> dest;
  std::vector<int> literals;
  while (line >> lit, lit) { literals.push_back (lit); }
  return Edge {src, dest, literals};
}

matrix<int> merge (const matrix<int> &a, const matrix<int> &b) {
  if (a.empty ()) { return b; }
  if (b.empty ()) { return a; }
  
  matrix<int> answer;
  for (const std::vector<int> &a_vec : a) {
    if (!a_vec.empty ()) {
      for (std::vector<int> b_vec : b) {
	if (!b_vec.empty ()) {
	  b_vec.insert (b_vec.end (), a_vec.cbegin (), a_vec.cend ());
	  answer.push_back (b_vec);
	}
      }
    }
  }
  return answer;
}

struct Graph {
  std::map<int, matrix<int>> memoization;
  std::map<int, std::vector<int>> vec_memoization;
  std::set<Node> nodes;
  std::set<Edge> edges;
  int top {}, bot {};

  int find_node (char type) const {
    auto iter {std::find_if (nodes.cbegin (), nodes.cend (), [type] (const Node &n) { return n.type == type; })};
    return iter == nodes.cend () ? 0 : iter->idx;
  }
  int get_top () const { return find_node ('t'); }
  int get_bot () const { return find_node ('f'); }
  
  void read_file (char *path) {
    std::ifstream file {path};
    while (!file.eof ()) {
      std::string line;
      std::getline (file, line);
      if (line.empty ()) { break; }
      std::stringstream sstream {line};
      switch (line[0]) {
      case 'a': case 'f': case 'o': case 't':
	nodes.emplace (read_node (sstream));
	break;
      default: {
	Edge e {read_edge (sstream)};
	edges.emplace (e);
        auto iter {std::find_if (nodes.begin (), nodes.end (),
				 [&e] (const Node &n) { return n.idx == e.src; })};
	if (iter != nodes.end ()) {
	  Node &n {const_cast<Node &> (*iter)};
	  n.children.push_back (e.dest);
	}
      }}
    }

    top = get_top (); bot = get_bot ();
  }

  void print (std::ostream &out) const {
    out << *std::find_if (nodes.cbegin (), nodes.cend (), [] (const Node &n) { return n.type == 't'; }) << '\n';
    for (const Edge &edge : edges) 
      { out << edge << '\n'; }
  }

  char node_type (int idx) const {
    auto iter {std::find_if (nodes.cbegin (), nodes.cend (), [idx] (const Node &n) { return n.idx == idx; })};
    if (iter == nodes.cend ()) { return 0; }
    return iter->type;
  }

  int step_back_edge (int dest, const std::vector<int> &considered) const {
    auto iter {std::find_if (edges.cbegin (), edges.cend (),
			     [dest, &considered] (const Edge &e) {
			       return e.dest == dest
				 && std::find (considered.cbegin (), considered.cend (), e.src) == considered.cend (); })};
    if (iter == edges.cend ()) { return -1; }
    return iter->src;
  }

  Path choose_path () const {
    Path path; 
    int current {top};
    path.nodes.push_back (current);

    while (current != 1) {
      int prev {current};
      current = step_back_edge (current, path.nodes);
      if (current > 0) {
	path.nodes.push_back (current);
	auto eter {std::find_if (edges.cbegin (), edges.cend (), [prev, current] (const Edge &e) { return e.src == current && e.dest == prev; })};
	path.literals.insert (eter->literals.cbegin (), eter->literals.cend ());
      }
      else
	{ std::cout << "Current < 0\n"; break; }
    }
    return path;
  }

  matrix<int> fuse (const std::vector<matrix<int>> &streams) const {
    matrix<int> answer;
    for (const matrix<int> &str : streams) { answer = merge (answer, str); }
    return answer;
  }
  
  matrix<int> explore (int idx, std::vector<int> prev_lits) {
    std::cout << idx << ' ' << std::flush;
    for (auto &[k, v] : memoization) {
      std::cout << k << ' ';
    } std::cout << '\n';
    
    if (idx == bot) { return {}; }
    if (idx == top) { return {prev_lits}; }

    const std::vector<int> &children {std::find_if (nodes.cbegin (), nodes.cend (), [idx] (const Node &n) { return n.idx == idx; })->children};
    std::set<Edge> seen;
    
    auto get_next {
      [this, &seen] (std::vector<int> literals, int idx, int ch) {
	auto iter {std::find_if (edges.cbegin (), edges.cend (), [idx, ch, &seen] (const Edge &e) { return e.src == idx && e.dest == ch && !seen.contains (e); })};
	literals.insert (literals.end (), iter->literals.cbegin (), iter->literals.cend ());
	seen.insert (*iter);
	matrix<int> below {memoization.at (ch)};
	for (std::vector<int> &sub : below) { sub.insert (sub.end (), literals.cbegin (), literals.cend ()); }
	return below;
      }};

    matrix<int> answer;

    if (node_type (idx) == 'a') {
      std::vector<matrix<int>> separately;
      for (int ch : children) {
	if (!memoization.contains (ch)) { memoization[ch] = explore (ch, {}); }
	separately.push_back (get_next (prev_lits, idx, ch));
      }
      // return fuse (separately);
      answer = fuse (separately);
    }
    else {
      for (int ch : children) {
	if (!memoization.contains (ch)) { memoization[ch] = explore (ch, {}); }
	matrix<int> submatrix {get_next (prev_lits, idx, ch)};
	answer.insert (answer.end (), submatrix.cbegin (), submatrix.cend ());
      }
    }

    return answer;
  }

  std::vector<int> single_exploration (int idx, std::vector<int> prev_lits) {
    if (idx == bot) { return {}; } if (idx == top) { return prev_lits; }

    const std::vector<int> &children {std::find_if (nodes.cbegin (), nodes.cend (), [idx] (const Node &n) { return n.idx == idx; })->children};
    std::set<Edge> seen;

    auto get_next {
      [this, &seen] (std::vector<int> literals, int idx, int ch) {
	auto iter {std::find_if (edges.cbegin (), edges.cend (), [idx, ch, &seen] (const Edge &e) { return e.src == idx && e.dest == ch && !seen.contains (e); })};
	literals.insert (literals.end (), iter->literals.cbegin (), iter->literals.cend ());
	seen.insert (*iter);
	literals.insert (literals.end (), vec_memoization.at (ch).cbegin (), vec_memoization.at (ch).cend ());
	return literals;
      }};

    if (node_type (idx) == 'a') {
      for (int ch : children) {
	if (!vec_memoization.contains (ch)) { vec_memoization[ch] = single_exploration (ch, {}); }
	prev_lits = get_next (prev_lits, idx, ch);
      }
    }
    else {
      for (int ch : children) {
	if (ch != bot) {
	  if (!vec_memoization.contains (ch)) { vec_memoization[ch] = single_exploration (ch, {}); }
	  prev_lits = get_next (prev_lits, idx, ch);
	  break;
	}
      }
    }
    return prev_lits;
  }
};

struct StepRange {
  std::vector<int>::const_iterator begin, end, current;

  bool step () {
    if (std::next (current) == end) { return false; }
    ++current; return true;
  }
  
  bool step (std::map<int, std::map<int, std::map<int, std::set<int>>>> &nogoods,
	     const std::vector<StepRange> &steppers) {
    auto iter {std::find (steppers.cbegin (), steppers.cend (), *this)};
    if (std::next (current) == end) { return false; }
    ++current;
    int this_outer_dist {(int) std::distance (steppers.begin (), iter)};
    if (nogoods.contains (this_outer_dist)) {
      int this_inner_dist {(int) std::distance (begin, current)};
      if (nogoods[this_outer_dist].contains (this_inner_dist)) {
	for (auto &[other_dist, clashes] : nogoods[this_outer_dist][this_inner_dist]) {
	  if (clashes.contains ((int) std::distance (steppers[other_dist].begin, steppers[other_dist].current)))
	    { return step (nogoods, steppers); }
	}
      }
    }
    return true;
  }
  void init () { current = begin; }

  bool operator == (const StepRange &other) const { return begin == other.begin && end == other.end && current == other.current; }
};

struct Stepper {
  std::map<int, std::map<int, std::map<int, std::set<int>>>> nogoods;
  std::vector<StepRange> steppers;
  bool live;

  bool step (std::vector<StepRange>::iterator iter, bool plain = false) {
    if (std::next (iter) == steppers.end ()) { return plain ? iter->step () : iter->step (nogoods, steppers); }
    if (step (std::next (iter))) { return true; }
    if (plain && iter->step () || !plain && iter->step (nogoods, steppers))
      { for (auto other {std::next (iter)}; other != steppers.end (); ++other) { other->init (); return true; } }
    return false;
  }

  bool step () {
    live = step (steppers.begin ());
    return live;
  }
    
  void init (const matrix<int> &data) {
    steppers.resize (data.size ());
    auto iter {steppers.begin ()};
    for (auto diter {data.cbegin ()}; diter != data.cend (); ++diter, ++iter) {
      iter->current = iter->begin = diter->begin ();
      iter->end = diter->end ();
    }
    live = true;
  }

  std::vector<int> get (int &bad_var) const {
    std::set<int> so_far;
    std::vector<int> answer (steppers.size ());
    auto iter {steppers.cbegin ()};
    for (int &i : answer) {
      // i = (int) std::distance (iter->begin, iter->current);
      i = *(iter->current);
      // if (so_far.contains (-i)) { bad_var = i; return {}; }
      so_far.insert (i);
      ++iter;
    }
    return answer;
  }

  void block_pair (int bad_var) {
    auto pos {std::find_if (steppers.cbegin (), steppers.cend (), [bad_var] (const StepRange &sr) { return *(sr.current) == bad_var; })};
    auto neg {std::find_if (steppers.cbegin (), steppers.cend (), [bad_var] (const StepRange &sr) { return *(sr.current) == -bad_var; })};

    int dist1 {(int) std::distance (steppers.cbegin (), pos)}, dist2 {(int) std::distance (steppers.cbegin (), neg)};
    if (dist2 < dist1) { std::swap (neg, pos), std::swap (dist2, dist1); }

    int neg_dist {(int) std::distance (neg->begin, neg->current)}, inner_pos_dist {(int) std::distance (pos->begin, pos->current)};
    if (nogoods.contains (dist2)) {
      if (nogoods[dist2].contains (neg_dist)) {
	if (nogoods[dist2][neg_dist].contains (dist1))
	  { nogoods[dist2][neg_dist][dist1].insert (inner_pos_dist); }
	else
	  { nogoods[dist2][neg_dist][dist1] = {inner_pos_dist}; }
      }
      else
	{ nogoods[dist2][neg_dist] = {{dist1, {inner_pos_dist}}}; }
    }
    else 
      { nogoods[dist2] = {{neg_dist, {{dist1, {inner_pos_dist}}}}}; }
  };
};
  
matrix<int> naive_cnf_to_dnf (const matrix<int> &cnf) {
  Stepper stepper;
  stepper.init (cnf);

  std::set<std::set<int>> dnf;

  do {
    int bad_var {};
    std::vector<int> conjunction {stepper.get (bad_var)};
    if (bad_var) { stepper.block_pair (bad_var); }
    else {
      for (int i : conjunction) { std::cout << i << ' '; } std::cout << '\n';
      std::set<int> as_set {conjunction.cbegin (), conjunction.cend ()};
      dnf.emplace (std::set<int> {conjunction.cbegin (), conjunction.cend ()});
    }
    stepper.step ();
  } while (stepper.live);

  matrix<int> as_matrix (dnf.size ());
  auto ster {dnf.cbegin ()};
  for (auto vter {as_matrix.begin ()}; vter != as_matrix.end (); ++vter, ++ster) 
    { *vter = std::vector<int> {ster->cbegin (), ster->cend ()}; }

  return as_matrix;
}

matrix<int> cnf_to_dnf_solver (const matrix<int> &cnf) {
  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  for (const std::vector<int> &cl : cnf) { solver->clause (cl); }

  matrix<int> dnf;
  
  Stepper stepper; stepper.init (cnf);
  do {
    int bad_var {};
    std::vector<int> conjunction {stepper.get (bad_var)};
    if (!conjunction.empty ()) {
      for (int i : conjunction) { solver->assume (i); }
      if (solver->solve () == CaDiCaL::SATISFIABLE) { dnf.push_back (conjunction); }
    }
    stepper.step ();
  } while (stepper.live);

  delete solver;
  return dnf;
}
    
matrix<int> cnf_from_file (const char *path, int &vars) {
  std::ifstream file {path};
  std::string word;
  while (file.peek () == 'c') { std::getline (file, word); }
  file >> word >> word >> vars;
  int clauses; file >> clauses;

  matrix<int> cnf;
  for (int i {}; i < clauses; ++i) {
    std::vector<int> clause;
    int lit;
    while (file >> lit, lit) { clause.push_back (lit); }
    if (!clause.empty ()) { cnf.push_back (clause); }
  }

  return cnf;
}

struct Variable {
  std::vector<int> pos_clauses;
  std::vector<int> neg_clauses;

  bool unconstrained () const { return pos_clauses.empty () && neg_clauses.empty (); }
  int pure () const { if (pos_clauses.empty ()) { return -1; } if (neg_clauses.empty ()) { return 1; } return 0; }
  bool drop_clause (int clause_num, bool phase) {
    std::vector<int> &loc {phase ? pos_clauses : neg_clauses};
    std::erase (loc, clause_num);
    return loc.empty ();
  }

  void print (std::ostream &out, int var_num) const {
    out << var_num << ": "; for (int i : pos_clauses) { out << i << ' '; }
    out << "\b; -" << var_num << ": "; for (int i : neg_clauses) { out << i << ' '; }
    out << '\n';
  }
};

struct Suite {
  int pre, end;
};

template<typename T>
auto find_pos (auto cbegin, auto cend, T idx, auto if_fail) {
  if (cbegin >= cend) { return cend; }
  auto cmid {std::next (cbegin, std::distance (cbegin, cend) / 2)};
  if (*cmid == idx) { return cmid; }
  if (*cmid < idx) {
    auto iter {find_pos (cbegin, std::prev (cmid), idx, if_fail)};
    return iter == std::prev (cmid) ? (if_fail == cend ? cend : std::prev (cmid)) : iter;
  }
  return find_pos (std::next (cmid), cend, idx, if_fail);
}
 
template<typename T>
auto find_iter (auto cbegin, auto cend, T idx) { return find_pos (cbegin, cend, idx, cend); }
template<typename T>
bool find_between (auto cbegin, auto cend, T idx) { return find_iter (cbegin, cend, idx) != cend; }

struct Instance {
  matrix<int> phi;
  std::vector<Variable> variables;
  std::vector<int> backbone;
  Suite clause_selectors, flip_selectors;
  int aux;

  bool in_backbone (int lit) const { return find_between (backbone.cbegin (), backbone.cend (), lit); }
  
  void init_flip_selectors () {
    flip_selectors.pre = ++aux;
    aux = flip_selectors.end = aux + (int) variables.size ();
  }

  bool unit_propagate (int literal, bool in_progress);
  
  bool log_to_backbone (int literal, bool in_progress) {
    if (in_backbone (-literal)) { return false; }
    auto iter {find_pos (backbone.cbegin (), backbone.cend (), literal, backbone.cbegin ())};
    bool update {};
    if (iter == backbone.cend ()) { backbone.push_back (literal); update = true; }
    else if (*iter != literal) { backbone.insert (iter, literal); update = true; }

    return unit_propagate (literal, in_progress);
  }
    
  std::vector<int> drop_clause (int clause_num, int satisfier) {
    std::vector<int> purified;
    
    std::vector<int> &satisfied_clause {phi[clause_num-1]};
    for (int lit : satisfied_clause) {
      if (lit != satisfier) {
	Variable &var {variables[lit > 0 ? lit-1 : -lit-1]};
	if (var.drop_clause (clause_num, lit > 0)) { purified.push_back (lit); }
      }
    }

    return purified;
  }

  std::vector<int> tighten_clause (int clause_num, int negated) {
    std::vector<int> &clause {phi[clause_num-1]};
    std::erase (clause, -negated);
    return clause;
  }

  void read_clause (std::ifstream &file, int clause_num) {
    std::vector<int> curr_clause;
    int number;
    while (file >> number, number) {
      if (in_backbone (-number)) { continue; }
      if (in_backbone (number)) { return; }
      
      curr_clause.push_back (number);
      bool neg {number < 0};
      if (neg) { variables[-number-1].neg_clauses.push_back (clause_num); }
      else     { variables[number-1].pos_clauses.push_back (clause_num); }
    }
    if (curr_clause.size () == 1) {
      log_to_backbone (curr_clause.front (), true);
      // additional_clauses.push_back ({curr_clause.front ()});
    }
    else {
      phi.push_back (curr_clause);
      matrix<int> binding {disjunction (curr_clause, clause_num+clause_selectors.pre)};
      // additional_clauses.insert (additional_clauses.end (), binding.cbegin (), binding.cend ());
    }
  }
      
  void read_header (std::ifstream &file) {
    std::string word;
    while (file.peek () == 'c') { std::getline (file, word); }
    file >> word >> word;
    file >> clause_selectors.pre;
    variables.resize (clause_selectors.pre);
    file >> aux;
    phi.reserve (aux);
    aux = clause_selectors.end = clause_selectors.pre + aux;

    init_flip_selectors ();
  }

  void read_dimacs (char *path) {
    std::ifstream file {path};
    read_header (file);
    int clause {1};
    while (!file.eof ()) { read_clause (file, clause); ++clause; }
  }

  bool pure_variables () {
    int var_num {1};
    for (Variable &var : variables) {
      if (!in_backbone (var_num) && !in_backbone (-var_num)) {
	int phase {var.pure ()};
	if (phase) { if (!unit_propagate (var_num*phase, false)) { return false; } }
      }
      ++var_num;
    }
    return true;
  }

  void print_dimacs (std::ostream &out) const {
    for (const std::vector<int> &cl : phi) {
      for (int lit : cl) { out << lit << ' '; }
      out << "0\n";
    }
  }

  void print_var_locations (std::ostream &out) const {
    int i {1};
    for (const Variable &var : variables) { var.print (std::cout, i); ++i; }
  }

  matrix<int> phi_with_backbone () const {
    matrix<int> answer {phi};
    for (int i : backbone) { answer.push_back ({i}); }
    return answer;
  }
};

bool Instance::unit_propagate (int literal, bool in_progress) {
  Variable &var {variables[literal > 0 ? literal-1 : -literal-1]};
  std::vector<int> &satisfied {literal > 0 ? var.pos_clauses : var.neg_clauses},
    &removendum {literal > 0 ? var.neg_clauses : var.pos_clauses};

  for (int cl : satisfied) {
    std::vector<int> purified {drop_clause (cl, literal)};
    if (!in_progress) { for (int lit : purified) { if (!unit_propagate (lit, false)) { return false; } } }
  }
  for (int cl : removendum) {
    const std::vector<int> &reduced {tighten_clause (cl, literal)};
    if (reduced.empty ()) { return false; }
    if (reduced.size () == 1) { if (!unit_propagate (reduced.front (), in_progress)) { return false; } }
  }
  satisfied.clear ();
  removendum.clear ();

  return true;
}

int difference (const std::vector<bool> &a, const std::vector<bool> &b) {
  int variant {(int) a.size ()};
  bool different {};

  for (auto ater {a.cbegin ()}, bter {b.cbegin ()}; ater != a.cend (); ++ater, ++bter) {
    if (*ater != *bter) {
      if (different) { return (int) a.size (); }
      else { different = true; variant = (int) std::distance (a.cbegin (), ater); }
    }
  }
  return different ? variant : (int) a.size ();
}

bool duplicate (auto acbegin, auto acend, auto bcbegin, auto bcend) {
  for (auto ater {acbegin}, bter {bcbegin}; ater != acend; ++ater, ++bter) 
    { if (*ater != *bter) { return false; } }
  return true;
}

int hamming_abs (const std::vector<bool> &vec) {
  int answer {};
  for (bool v : vec) { if (v) { ++answer; } }
  return answer;
}

struct BoolStep {
  std::set<int> units;
  std::vector<bool> variables;

  void clear (std::vector<bool>::iterator iter) {
    int idx {(int) std::distance (variables.begin (), iter) + 1};
    for (auto i {iter}; i != variables.cend (); ++i, ++idx) { if (!units.contains (idx)) { *i = false; } }
  }
  
  bool step (std::vector<bool>::iterator iter);
  inline bool step ();

  int count () const { return hamming_abs (variables); }

  void init () { for (int u : units) { if (u > 0) { variables[u+1] = true; } } }
};

std::ostream &operator << (std::ostream &out, const BoolStep &bstep) {
  for (int b : bstep.variables) { out << b; }
  return out;
}

bool BoolStep::step (std::vector<bool>::iterator iter) {
  if (iter == variables.cend ()) { return false; }
  if (step (std::next (iter))) { return true; }
  if (*iter || units.contains ((int) std::distance (variables.begin (), iter) + 1)) { return false; }
  *iter = true;
  clear (std::next (iter));
  return true;
}

bool BoolStep::step () { return step (variables.begin ()); }

struct Minterm {
  std::vector<int> variables; // -1 false; 0 do not care; 1 true
  Minterm (const std::vector<bool> &orig) :
    variables (orig.size ()) { std::transform (orig.cbegin (), orig.cend (), variables.begin (), [] (bool b) { return b ? 1 : -1; }); }
  Minterm (const Minterm &orig, int block) {
    variables = orig.variables;
    variables[block] = 0;
  }

  int count () const;
  
  bool operator < (const Minterm &other) const { return variables < other.variables; }

  std::vector<int> as_term () const {
    std::vector<int> term;
    int idx {1};
    for (int i : variables) {
      if (i) { term.push_back (i == 1 ? idx : -idx); }
      ++idx;
    }
    return term;
  }
};

std::ostream &operator << (std::ostream &out, const Minterm &minterm) {
  for (int i : minterm.variables) {
    switch (i) {
    case -1: out << 0; break;
    case 1:  out << 1; break;
    default: out << '-';
    }
  }
  return out;
}

int Minterm::count () const {
  int answer {};
  for (int i : variables) { if (i == 1) { ++answer; } }
  return answer;
}

int difference (const Minterm &a, const Minterm &b) {
  int variant {(int) a.variables.size ()};
  bool different {};

  for (auto ater {a.variables.cbegin ()}, bter {b.variables.cbegin ()}; ater != a.variables.cend (); ++ater, ++bter) {
    if (*ater != *bter) {
      if (!*ater || !*bter || different) { return (int) a.variables.size (); }
      else { different = true; variant = (int) std::distance (a.variables.cbegin (), ater); }
    }
  }
  return different ? variant : (int) a.variables.size ();
}

std::set<int> unit_propagate (matrix<int> &cnf, int num_vars) {
  std::vector<Variable> variables (num_vars);
  std::set<int> backbone;
  auto known_size {backbone.size ()};
  
  do {
    known_size = backbone.size ();
    int cl_num {1};
    for (std::vector<int> &cl : cnf) {
      if (cl.size () == 1 && !backbone.contains (cl.front ())) { backbone.insert (cl.front ()); }
      else {
	std::vector<int> before {cl};
	for (int lit : cl) {
	  if (backbone.contains (-lit)) {
	    Variable &as_var {variables[lit > 0 ? lit-1 : -lit-1]};
	    std::vector<int> &noisy_clause {lit > 0 ? as_var.pos_clauses : as_var.neg_clauses};
	    std::erase (noisy_clause, cl_num);
	    std::erase (before, lit);

	    if (before.size () == 1 && !backbone.contains (before.front ())) { backbone.insert (before.front ()); }
	  }
	}
	cl = before;
      }
      ++cl_num;
    }
  } while (backbone.size () != known_size);

  return backbone;
}

std::set<int> check_units (CaDiCaL::Solver *solver, int num_vars) {
  std::set<int> answer;
  for (int v {1}; v <= num_vars; ++v) {
    for (int l : {v, -v}) {
      solver->assume (-l);
      if (solver->solve () == CaDiCaL::UNSATISFIABLE) { answer.insert (l); }
    }
  }

  return answer;
}

struct QM {
  std::map<int, std::vector<Minterm>> minterms;
  int num_vars;
  
  std::map<int, std::vector<Minterm>> calc_minterms_long (const matrix<int> &cnf, int num_vars) {
    this->num_vars = num_vars;
    std::map<int, std::vector<Minterm>> answer;
    
    CaDiCaL::Solver *solver {new CaDiCaL::Solver};
    for (const std::vector<int> &cl : cnf) { solver->clause (cl); }

    BoolStep bstep; bstep.variables.resize (num_vars); bstep.units = check_units (solver, num_vars); bstep.init ();
    do {
      auto bter {bstep.variables.cbegin ()};
      for (int i {1}; bter != bstep.variables.cend (); ++i, ++bter) { solver->assume (*bter ? i : -i); }
      if (solver->solve () == CaDiCaL::SATISFIABLE) {
	int count {bstep.count ()};
	Minterm mterm {bstep.variables};
	if (answer.contains (count)) { answer[count].push_back (mterm); }
	else { answer[count] = {mterm}; }
      }
      std::cout << bstep << ' ' << answer.size () << std::endl;
    } while (bstep.step ());

    delete solver;
    return answer;
  }

  std::map<int, std::vector<Minterm>> calc_minterms (const matrix<int> &cnf, int num_vars) {
    std::map<int, std::vector<Minterm>> answer;
    this->num_vars = num_vars;

    CaDiCaL::Solver *solver {new CaDiCaL::Solver};
    for (const std::vector<int> &cl : cnf) { solver->clause (cl); }
    std::set<int> units {check_units (solver, num_vars)};
    for (int i : units) { solver->add (i), solver->add (0); }

    std::vector<bool> model (num_vars);
    std::vector<int> to_block (num_vars);
    while (solver->solve () == CaDiCaL::SATISFIABLE) {
      auto vter {model.begin ()}; auto bter {to_block.begin ()};
      for (int i {1}; i <= num_vars; ++i, ++vter, ++bter) 
	{ int val {solver->val (i)}; *vter = val > 0; *bter = -val; }
      solver->clause (to_block);
      Minterm mterm {model}; int count {mterm.count ()};
      if (answer.contains (count)) { answer[count].push_back (mterm); }
      else { answer[count] = {mterm}; }
    }

    delete solver;
    return answer;
  }
	
  bool reduce () {
    std::map<int, std::set<Minterm>> reduction;
    
    for (auto &[counter, terms] : minterms) {
      if (minterms.contains (counter + 1)) {
	for (const Minterm &small_minterm : terms) {
	  std::set<int> matched;
	  for (const Minterm &big_minterm : minterms[counter+1]) {
	    int diff_idx {difference (small_minterm, big_minterm)};
	    if (diff_idx != small_minterm.variables.size ()) { matched.insert (diff_idx); }
	  }

	  for (int i : matched) {
	    Minterm with_block {small_minterm, i};
	    int ones {with_block.count ()};
	    if (reduction.contains (ones))
	      { reduction[ones].insert (with_block); }
	    else
	      { reduction[ones] = {with_block}; }
	  }
	}
      }
    }

    if (reduction.empty ()) { return false; }
    
    minterms.clear ();
    for (auto &[count, terms] : reduction) 
      { minterms[count] = std::vector<Minterm> {terms.cbegin (), terms.cend ()}; }
    return true;
  }

  matrix<int> as_dnf () const {
    matrix<int> dnf;
    for (auto &[_, value] : minterms) 
      { std::transform (value.cbegin (), value.cend (), std::inserter (dnf, dnf.end ()), [] (const Minterm &minterm) { return minterm.as_term (); }); }
    return dnf;
  }

  void print_dnf (std::ostream &out, bool header) const {
    matrix<int> dnf {as_dnf ()};
    if (header) { out << "p dnf " << num_vars << ' ' << dnf.size () << '\n'; }
    print_cnf (out, dnf);
  }
};

std::ostream &operator << (std::ostream &out, const QM &qm) {
  for (auto &[score, terms] : qm.minterms) {
    out << score << ":\n";
    for (const Minterm &minterm : terms) { out << "  " << minterm << '\n'; }
  }
  return out;
}

matrix<int> implicant_cover (const matrix<int> &cnf, int vars, std::string dnf_out = "") {
  QM qm; qm.minterms = qm.calc_minterms (cnf, vars);
  while (qm.reduce ());
  if (!dnf_out.empty ()) {
    std::ofstream output {dnf_out.c_str ()};
    qm.print_dnf (output, true);
    output.close ();
    std::cout << "Implicants in " << dnf_out << '.' << std::endl;
  }
  return qm.as_dnf ();
}

matrix<int> resistant_models (const matrix<int> &phi, const matrix<int> &p_cover, int aux, int k) {
  int num_vars {aux};
  matrix<int> additional_clauses;
  std::vector<int> at_least_one_close;

  for (std::vector<int> pi : p_cover) {
    if (pi.empty ()) { continue; }
    for (int &l : pi) { l = -l; }
    KCardNet cardinality {pi, k+1, aux, 1};
    std::vector<int> card_clause {cardinality.card (cardinality.data.begin (), cardinality.data.end (), aux)};
    additional_clauses.insert (additional_clauses.end (), cardinality.clauses.cbegin (), cardinality.clauses.cend ());
    additional_clauses.push_back (card_clause);
    at_least_one_close.push_back (card_clause[k+1]);
  }

  CaDiCaL::Solver *solver {new CaDiCaL::Solver};
  for (const matrix<int> &subformula : {phi, additional_clauses})
    { for (const std::vector<int> &cl : subformula) { solver->clause (cl); } }
  for (int i : at_least_one_close) { solver->add (i), solver->add (0); }
  
  matrix<int> omega;
  while (solver->solve () == CaDiCaL::SATISFIABLE) {
    std::vector<int> model (num_vars); int i {};
    std::vector<int> block (num_vars);
    for (auto val {model.begin ()}, blocker {block.begin ()}; val != model.end (); ++val, ++blocker)
      { *val = solver->val (++i); *blocker = -*val; }
    solver->clause (block);
    omega.push_back (model);
  }

  delete solver;
  return omega;
}

bool read_options (int argc, char **argv, int &k, std::string &input, std::string &dnf_output, std::string &cover_file) {
  if (argc < 2) { return false; }

  for (int i {1}; i < argc; ++i) {
    if (argv[i][0] != '-' || i >= argc-1) { return false; }
    switch (argv[i][1]) {
    case 'c': cover_file = argv[++i]; break;
    case 'd': dnf_output = argv[++i]; break;
    case 'i': input = argv[++i]; break;
    case 'k': k = std::stoi (argv[++i]); break;
    default: return false;
    }
  }

  return !input.empty ();
}
      
int main (int argc, char **argv) {
  int k {5}; std::string input, dnf_output, cover_file;
  if (!read_options (argc, argv, k, input, dnf_output, cover_file)) {
    std::cerr << "Usage: " << argv[0] << " -i <input cnf> [-c <cover file>] [-d <output dnf>] [-k <k>]\n"
	      << "       <cover file> is location of already prepared DNF of implicants.\n"
	      << "       Implicants will be stored in <output dnf>.\n"
	      << "       <k> is 5 by default.\n";
    return 1;
  }
  
  // Graph d_dnnf; d_dnnf.read_file (argv[1]);
  // d_dnnf.print (std::cout);
  // std::cout << d_dnnf.choose_path () << '\n';

  // for (std::vector<int> &cl : d_dnnf.explore (1, {})) 
  //   { for (int i : cl) { std::cout << i << ' '; } std::cout << '\n'; }

  // std::vector<int> cover {d_dnnf.single_exploration (1, {})};
  // std::cout << cover.size () << '\n';
  // for (int i : cover) { std::cout << i << ' '; } std::cout << '\n';

  // matrix<int> dnf {naive_cnf_to_dnf (cnf_from_file (argv[1]))};
  // matrix<int> cnf {cnf_from_file (argv[1])};
  // std::cout << cnf.size () << '\n';
  // for (std::vector<int> &cl : cnf) { for (int i : cl) { std::cout << i << ' '; } std::cout << "0\n"; }

  // Instance inst; inst.read_dimacs (argv[1]); inst.pure_variables ();
  // matrix<int> cnf {inst.phi_with_backbone ()};

  int vars;
  matrix<int> cnf {cnf_from_file (input.c_str (), vars)};
  int other_vars;
  matrix<int> p_cover {cover_file.empty () ? implicant_cover (cnf, vars, dnf_output) : cnf_from_file (cover_file.c_str (), other_vars)};
  
  matrix<int> models {resistant_models (cnf, p_cover, vars, k)};
  if (models.empty ()) { std::cout << "No " << k << "-resistant models.\n"; }
  else { for (const std::vector<int> &omega : models) { for (int i : omega) { std::cout << i << ' '; } std::cout << '\n'; } }
  // matrix<int> dnf {cnf_to_dnf_solver (cnf)};

  // for (const std::vector<int> &term : dnf) 
  //   { for (int lit : term) { std::cout << lit << ' '; } std::cout << "0\n"; }

  // QM qm; qm.minterms = qm.calc_minterms (cnf, vars);
  // std::cout << qm;
  // while (qm.reduce ()) { std::cout << '\n' << qm; }
  // std::cout << '\n';
  // for (const std::vector<int> &cl : qm.as_dnf ()) 
  //   { for (int i : cl) { std::cout << i << ' '; } std::cout << '\n'; }
  
}  
  
