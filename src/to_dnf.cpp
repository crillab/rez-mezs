#include "cadical.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<int>>;

struct Variable {
  std::vector<int> pos_clauses, neg_clauses;
  int status {}; // (1 . ⊤) (-1 . ⊥) (0 . Unknown)

  void add_clause (int cl, bool phase) { phase ? pos_clauses.push_back (cl) : neg_clauses.push_back (cl); }
  void set_val (bool phase) { status = phase ? 1 : -1; } 
  void remove_clause (int cl) {
    if (cl > 0) { std::erase (pos_clauses, cl); }
    else { std::erase (neg_clauses, -cl); }
  }
};

std::ostream &operator << (std::ostream &out, const Variable &var) {
  if (var.status) { out << (var.status == 1 ? "True" : "False"); }
  else {
    auto print_clauses { [&out] (const std::vector<int> &cl) { for (int i : cl) { out << i << ' '; } } };

    bool p {};
    for (const std::vector<int> &clauses : {var.pos_clauses, var.neg_clauses}) {
      if (!clauses.empty ()) {
	out << (p ? "Neg: " : "Pos: ");
	for (int i : clauses) { out << i << ' '; }
      }
      p = true;
    }
  }
  return out;
}
	  
struct Instance {
  matrix<int> clauses;
  std::vector<Variable> variables;
  std::set<int> satisfied_clauses;
  bool unsatisfiable {};
  int top_var {};
  
  Variable &get_var (int lit) { return lit > 0 ? variables[lit-1] : variables[-lit-1]; }
  const Variable &get_varc (int lit) const { return lit > 0 ? variables[lit-1] : variables[-lit-1]; }
  
  int check_lit (int lit) {
    if (lit > 0) { return variables[lit-1].status; }
    return -variables[-lit-1].status;
  }

  bool small_clause (const std::vector<int> &cl, int cl_num);
    
  void satisfy_clause (int cl_num) {
    for (int lit : clauses[cl_num-1]) { get_var (lit).remove_clause (lit > 0 ? cl_num : -cl_num); }
    satisfied_clauses.insert (cl_num);
  }
  void remove_from (const std::vector<int> &cl_nums, int lit) { for (int i : cl_nums) { std::erase (clauses[i-1], lit); } }
  void remove_false (std::vector<int> &clause, int cl_num, int lit) { std::erase (clause, lit); small_clause (clause, cl_num); }
  
  void set_val (int lit) {
    Variable &var {get_var (lit)};

    bool phase (lit > 0);
    var.set_val (phase);

    std::vector<int> &satisfied {phase ? var.pos_clauses : var.neg_clauses};
    std::vector<int> &to_satisfy {phase ? var.neg_clauses : var.pos_clauses};

    remove_from (satisfied, lit); remove_from (to_satisfy, lit);
    for (int i : satisfied) { satisfy_clause (i); }
    for (int i : to_satisfy) { remove_false (clauses[i-1], i, lit); }
  }

  void clauses_to_solver (CaDiCaL::Solver *solver) const {
    int cl_num {};
    int i {};
    for (const std::vector<int> &cl : clauses)
      { if (!satisfied_clauses.contains (++cl_num) && !cl.empty ()) { solver->clause (cl); } }
  }
  std::vector<int> known_literals () const {
    std::vector<int> literals;
    int i {};
    for (const Variable &var : variables)
      { ++i; if (var.status) { literals.push_back (var.status == 1 ? i : -i); } }
    return literals;
  }

  void check_top_var (int lit) {
    int var {lit > 0 ? lit : -lit};
    if (var > top_var) { top_var = var; }
  }
  
  void analyse (CaDiCaL::Solver *solver, std::vector<int> &implicants, std::vector<int> &blockers) {
    std::set<int> implicates {satisfied_clauses};

    auto sat_lit { [solver] (int lit) { if (lit > 0) { return solver->val (lit) > 0; } return solver->val (-lit) < 0; }};

    for (int cl_num {1}; cl_num <= clauses.size (); ++cl_num) {
      if (implicates.size () == clauses.size ()) { return; }
      if (!implicates.contains (cl_num)) {
	auto lit_relevance
	  { [this, cl_num] (int lit) mutable {
	    const Variable &var {get_varc (lit)};
	    const std::vector<int> &other_implicates {lit > 0 ? var.pos_clauses : var.neg_clauses};
	    return (int) std::distance (std::find (other_implicates.cbegin (), other_implicates.cend (), cl_num), other_implicates.cend ());
	  }};
	
	int lit, max {};
	for (int disj : clauses[cl_num-1]) {
	  if (sat_lit (disj)) {
	    int rel {lit_relevance (disj)};
	    if (rel > max) { lit = disj; max = rel; }
	  }
	}
	
	if (!max) {
	  int lit;
	  for (int disj : clauses[cl_num-1]) { if (sat_lit (disj)) { lit = disj; break; } }
	  implicants.push_back (lit); blockers.push_back (-lit);
	  check_top_var (lit);
	}
	else {
	  implicants.push_back (lit); blockers.push_back (-lit);
	  check_top_var (lit);
	  const std::vector<int> &other_clauses {lit > 0 ? get_varc (lit).pos_clauses : get_varc (lit).neg_clauses};
	  std::for_each (std::find (other_clauses.cbegin (), other_clauses.cend (), cl_num), other_clauses.cend (),
			 [&implicates] (int cl) { implicates.insert (cl); });
	}
      }
    }
  }
  
  matrix<int> with_solver (std::ostream &out) {
    CaDiCaL::Solver *solver {new CaDiCaL::Solver};

    clauses_to_solver (solver);
    std::vector<int> known {known_literals ()};
    for (int i : known) { solver->add (i), solver->add (0); }

    matrix<int> cubes;
    while (solver->solve () == CaDiCaL::SATISFIABLE) {
      std::vector<int> implicants {known}, blockers;
      analyse (solver, implicants, blockers);
      cubes.push_back (implicants); solver->clause (blockers);
      // for (int pi : implicants) { out << pi << ' '; } out << '0' << std::endl;
    }
    
    delete solver;
    return cubes;
  }
  
  void read_header (std::ifstream &in) {
    std::string word;
    while (in.peek () == 'c') { std::getline (in, word); }
    in >> word >> word;
    int size;
    in >> size; variables.resize (size);
    in >> size; clauses.resize (size); 
  }
    
  void read_clause (std::ifstream &in, std::vector<int> &cl, int cl_num) {
    if (satisfied_clauses.contains (cl_num)) { return; }
    int lit;
    std::vector<int> data;
    while (in >> lit, lit) {
      switch (check_lit (lit)) { case -1: continue; case 1: satisfied_clauses.insert (cl_num); while (in >> lit, lit); return; }
      data.push_back (lit);
    }

    if (!small_clause (data, cl_num)) {
      for (int lit : data) { get_var (lit).add_clause (cl_num, lit > 0); }
      clauses[cl_num-1] = data;
    }
  }
      
  void read_dimacs (char *path) {
    std::ifstream cnf {path};
    read_header (cnf);
    int cl_num {1};
    for (auto cl {clauses.begin ()}; cl != clauses.end (); ++cl, ++cl_num) 
      { read_clause (cnf, *cl, cl_num); }
  }

  void print_dimacs (std::ostream &out) const {
    for (const std::vector<int> &cl : clauses)
      { for (int lit : cl) { out << lit << ' '; } out << "0\n"; }
  }

  void print_vars (std::ostream &out) const {
    int i {};
    for (const Variable &var : variables)  { out << ++i << ": " << var << '\n'; }
  }
  
  void print_known (std::ostream &out) const {
    int i {1};
    for (const Variable &var : variables)
      { if (var.status) { out << var.status * i << ' '; } ++i; }
    out << '\n';
  }
};

bool Instance::small_clause (const std::vector<int> &cl, int cl_num) {
  if (cl.empty ()) { unsatisfiable = true; }
  else if (cl.size () == 1) { set_val (cl[0]); satisfied_clauses.insert (cl_num); }
  else { return false; }
  return true;
}

int main (int argc, char **argv) {
  Instance instance;
  instance.read_dimacs (argv[1]);
  // instance.print_dimacs (std::cout);
  // return 0;
  // instance.print_vars (std::cout);
  matrix<int> cubes {instance.with_solver (std::cout)};
  std::ofstream out {argv[2]};
  out << "p dnf " << instance.top_var << ' ' << cubes.size () << '\n';
  for (const std::vector<int> &term : cubes)
    { for (int i : term) { out << i << ' '; } out << "0\n"; }
  out.close ();
}
