#include "cadical.hpp"

#include "util.hpp"

#include <algorithm>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<T>>;

template<typename T>
std::ostream &operator << (std::ostream &out, const matrix<T> &formula) {
  for (const std::vector<T> &constraint : formula)
    { for (T lit : constraint) { out << lit << ' '; } out << "0\n"; }
  return out;
}

template<typename T>
auto find_iter (auto cbegin, auto cend, T idx) {
  if (cbegin >= cend) { return cend; }
  auto cmid {std::next (cbegin, std::distance (cbegin, cend) / 2)};
  if (*cmid == idx) { return cmid; }
  if (*cmid < idx) {
    auto iter {find_iter (cbegin, std::prev (cmid), idx)};
    return iter == std::prev (cmid) ? cend : iter;
  }
  return find_iter (std::next (cmid), cend, idx);
}
  
template<typename T>
bool find_between (auto cbegin, auto cend, T idx) { return find_iter (cbegin, cend, idx) != cend; }
 
struct Variable {
  std::vector<int> pos_clauses;
  std::vector<int> neg_clauses;

  bool unconstrained () const { return pos_clauses.empty () && neg_clauses.empty (); }
  bool pure () const { return pos_clauses.empty () || neg_clauses.empty (); }
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

struct Instance {
  matrix<int> phi;
  matrix<int> additional_clauses;
  std::vector<Variable> variables;
  std::vector<int> backbone;
  Suite clause_selectors, flip_selectors;
  int aux;

  void init_flip_selectors () {
    flip_selectors.pre = ++aux;
    aux = flip_selectors.end = aux + (int) variables.size ();
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

  bool log_to_backbone (int literal) {
    if (find_between (backbone.cbegin (), backbone.cend (), -literal)) { return false; }
    auto iter {std::find (backbone.cbegin (), backbone.cend (), literal)}
    if (*iter != literal) { backbone.insert (iter, literal); }

    return true;
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
	
  bool unit_propagate (int literal) {
    if (!log_to_backbone (literal)) { return false; }
    Variable &var {variables[literal > 0 ? literal-1 : -literal-1]};
    std::vector<int> &satisfied {literal > 0 ? var.pos_clauses : var.neg_clauses},
      &removendum {literal > 0 ? var.neg_clauses : var.pos_clauses};

    return true;
  }
    
  void read_clause (std::ifstream &file, int clause_num) {
    std::vector<int> curr_clause;
    int number;
    while (file >> number, number) {
      curr_clause.push_back (number);
      bool neg {number < 0};
      if (neg) { variables[-number-1].neg_clauses.push_back (clause_num); }
      else     { variables[number-1].pos_clauses.push_back (clause_num); }
    }
    if (curr_clause.size () == 1) {
      unit_propagate (curr_clause.front ());
      additional_clauses.push_back ({curr_clause.front ()});
    }
    else {
      phi.push_back (curr_clause);
      matrix<int> binding {disjunction (curr_clause, clause_num+clause_selectors.pre)};
      additional_clauses.insert (additional_clauses.end (), binding.cbegin (), binding.cend ());
    }
  }
      
  void read_dimacs (char *path) {
    std::ifstream file {path};
    read_header (file);
    int clause {1};
    while (!file.eof ()) { read_clause (file, clause); ++clause; }
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

  std::vector<int> flippable (int var, CaDiCaL::Solver *solver) const {
    const std::vector<int> &pos_clauses {variables[var > 0 ? var-1 : -var-1].pos_clauses}, &neg_clauses {variables[var > 0 ? var-1 : -var-1].neg_clauses};

    int clause_num {1};
    for (const std::vector<int> &clause : phi) {
      if (find_between (pos_clauses.cbegin (), pos_clauses.cend (), clause_num) || find_between (neg_clauses.cbegin (), neg_clauses.cend (), clause_num)) {
	for (int lit : clause) { if (lit != var && lit != -var) { solver->add (lit); } }
	solver->add (0);
      }
      else { solver->add (clause_selectors.pre+clause_num), solver->add (0); }
      ++clause_num;
    }

    std::vector<int> answer;
    if (solver->solve () == CaDiCaL::SATISFIABLE) {
      answer.resize (variables.size ());
      int i {};
      for (int &v : answer) { v = solver->val (++i); }
    }
    return answer;
  }

  std::vector<int> flippable (int var) const {
    CaDiCaL::Solver *solver {new CaDiCaL::Solver};
    std::vector<int> answer {flippable (var, solver)};
    delete solver;
    return answer;
  }

  matrix<int> select_flippability (int var, int auxiliary, int &aux) const {
    matrix<int> answer;
    const std::vector<int> &pos_clauses {variables[var-1].pos_clauses}, &neg_clauses {variables[var-1].neg_clauses};

    int clause_num {1};
    std::vector<int> selector_vector (phi.size ()); auto clause_iter {selector_vector.begin ()};

    for (const std::vector<int> &clause : phi) {
      if (find_between (pos_clauses.cbegin (), pos_clauses.cend (), clause_num) || find_between (neg_clauses.cbegin (), neg_clauses.cend  (), clause_num)) {
	*clause_iter = -++aux;
	std::vector<int> binding {*clause_iter};
	for (int lit : clause) { if (lit != var && lit != -var) { binding.push_back (lit); } }
	answer.push_back (binding);
      }
      else { *clause_iter = -clause_selectors.pre-clause_num; }

      ++clause_iter; ++clause_num;
    }
    selector_vector.resize (selector_vector.size ()+1);
    selector_vector.back () = auxiliary;

    answer.push_back (selector_vector);
    return answer;
  }

  matrix<int> encode_flip_independence (int &aux) const {
    matrix<int> answer;
    for (int var {1}, sel {flip_selectors.pre}; var <= variables.size (); ++var, ++sel) {
      matrix<int> partial_answer {select_flippability (var, sel, aux)};
      answer.insert (answer.end (), partial_answer.cbegin (), partial_answer.cend ());
    }
    return answer;
  }
      
  std::vector<int> block_intrp (const std::vector<int> &intrp) const {
    std::vector<int> blocker (intrp.size ());
    std::transform (intrp.cbegin (), intrp.cend (), blocker.begin (), [] (int i) { return -i; });
    return blocker;
  }
  
  matrix<int> delta_r () const {
    matrix<int> answer;

    CaDiCaL::Solver *solver {new CaDiCaL::Solver};
    int vars {aux};
    for (const matrix<int> &subformula : {phi, encode_flip_independence (vars)})
      { for (const std::vector<int> &cl : subformula) { solver->clause (cl); } }

    while (solver->solve () == CaDiCaL::SATISFIABLE) {
      std::vector<int> to_keep (variables.size ());
      int i {1};
      for (auto kiter {to_keep.begin ()}; kiter != to_keep.end (); ++kiter, ++i) {
	int val {solver->val (i)};
	*kiter = val;
      }
      answer.push_back (to_keep);
      solver->clause (block_intrp (to_keep));
    }

    delete solver;
    return answer;
  }
};   

int main (int argc, char **argv) {
  Instance instance;
  instance.read_dimacs (argv[1]);
  instance.print_var_locations (std::cout);

  std::cout << instance.delta_r ();
}
