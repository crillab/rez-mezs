#include "cadical.hpp"

#include "cardinality.hpp"

#include <algorithm>
#include <fstream>
#include <set>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<T>>;

template<typename T>
struct Step  {
  std::vector<T> variables;

  void clear (std::vector<T>::iterator iter);
  void increment (std::vector<T>::iterator iter);
  bool top (std::vector<T>::iterator iter);

  bool step (std::vector<T>::iterator iter) {
    if (iter == variables.cend ()) { return false; }
    if (step (std::next (iter))) { return true; }
    if (top (iter)) { return false; }
    increment (iter);
    clear (std::next (iter));
    return true;
  }

  bool step () { return step (variables.begin ()); }
};

template<> void Step<bool>::clear (std::vector<bool>::iterator iter) { for (auto i {iter}; i != variables.cend (); ++i) { *i = false; } }
template<> void Step<bool>::increment (std::vector<bool>::iterator iter) { *iter = true; }
template<> bool Step<bool>::top (std::vector<bool>::iterator iter) { return *iter; }

template<> void Step<int>::clear (std::vector<int>::iterator iter) { for (auto i {iter}; i != variables.cend (); ++i) { if (*i > 0) { *i = -*i; } } }
template<> void Step<int>::increment (std::vector<int>::iterator iter) { if (*iter < 0) { *iter = -*iter; } }
template<> bool Step<int>::top (std::vector<int>::iterator iter) { return *iter > 0; }

matrix<int> gt (const std::vector<int> &data, int k, int &aux) {
  if (data.size () <= k) { return {{++aux}, {-aux}}; }
  if (!k) { return {data}; }
  
  KCardNet card {data, k+1, aux, 1}; std::vector<int> card_clause {card.card (card.data.begin (), card.data.end (), aux)};
  matrix<int> ret_val {card.clauses}; ret_val.push_back ({card_clause[k]});
  return ret_val;
}

matrix<int> leq (const std::vector<int> &data, int k, int &aux) {
  if (!k) { return {{++aux}, {-aux}}; }
  if (data.size () <= k) { return {}; }

  KCardNet card {data, k, aux, -1}; std::vector<int> card_clause {card.card (card.data.begin (), card.data.end (), aux)};
  matrix<int> ret_val {card.clauses}; ret_val.push_back ({-card_clause[k]});
  return ret_val;
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

matrix<int> alofc (const matrix<int> &phi, const std::vector<int> &l, bool cnf) {
  std::set<int> l_as_set {l.cbegin (), l.cend ()};
  matrix<int> constraints;
  std::copy_if (phi.cbegin (), phi.cend (), std::inserter (constraints, constraints.end ()),
		[&l_as_set, cnf] (const std::vector<int> &cl) { return std::all_of (cl.cbegin (), cl.cend (),
										    [&l_as_set, cnf] (int lit) { return !l_as_set.contains (cnf ? lit : -lit); }); });
  std::transform (constraints.cbegin (), constraints.cend (), constraints.begin (),
		  [&l_as_set, cnf] (const std::vector<int> &cl) {
		    std::vector<int> changed;
		    std::copy_if (cl.cbegin (), cl.end (), std::inserter (changed, changed.end ()),
				  [&l_as_set, cnf] (int lit) { return !l_as_set.contains (cnf ? -lit : lit); });
		    return changed; });
  return constraints;
}

matrix<int> dnf_to_cnf (const matrix<int> &dnf, int &aux) {
  matrix<int> cnf;
  std::vector<int> alo (dnf.size ()); for (int &i : alo) { i = ++aux; }

  int sel {alo[0]};
  for (const std::vector<int> &term : dnf) { for (int i : term) { cnf.push_back ({-sel, i}); } ++sel; }
  cnf.push_back (alo);
  return cnf;
}
    
matrix<int> delta_h (const matrix<int> &p_cover, int k, int &aux) {
  matrix<int> answer {}; // {dnf_to_cnf (p_cover, aux)};
  for (const std::vector<int> &pi : p_cover) {
    if (pi.size () < k+1) { answer.push_back ({++aux}); answer.push_back ({-aux}); return answer; }
    std::vector<int> negate_each (pi.size ());
    std::transform (pi.cbegin (), pi.cend (), negate_each.begin (), [] (int i) { return -i; });
    matrix<int> greater_than_k {gt (negate_each, k, aux)};
    std::copy (greater_than_k.cbegin (), greater_than_k.cend (), std::inserter (answer, answer.end ()));
  }
  return answer;
}
matrix<int> delta_h_dnf (const matrix<int> &p_cover, const std::vector<int> &, int k, int &aux) { return delta_h (p_cover, k, aux); }

matrix<int> dnf_k_is_size_x (const matrix<int> &phi, const std::vector<int> &l) {
  std::set<int> l_as_set {l.cbegin (), l.cend ()};
  std::vector<int> falsificanda;
  for (const std::vector<int> &term : phi) {
    std::copy_if (term.cbegin (), term.cend (), std::inserter (falsificanda, falsificanda.end ()),
		  [&l_as_set] (int lit) { return !l_as_set.contains (lit) && !l_as_set.contains (-lit); });
  }
  matrix<int> answer (falsificanda.size ());
  std::transform (falsificanda.cbegin (), falsificanda.cend (), answer.begin (), [] (int lit) { return std::vector<int> {-lit}; });
  return answer;
}
    
matrix<int> size_then_alofc (const matrix<int> &phi, const std::vector<int> &l, int k, int &aux, bool cnf) {
  std::vector<int> not_l (l.size ()); std::transform (l.cbegin (), l.cend (), not_l.begin (), [] (int i) { return -i; });
  KCardNet card {not_l, k+1, aux, 1}; std::vector<int> card_clause {card.card (card.data.begin (), card.data.end (), aux)};
  matrix<int> answer {card.clauses};
  
  if (cnf) {
    matrix<int> alo {alofc (phi, l, true)};
    std::vector<int> orxialiaries (alo.size ()); for (int &i : orxialiaries) { i = ++aux; }
    std::transform (alo.cbegin (), alo.cend (), std::inserter (answer, answer.end ()),
		    [iter=orxialiaries.cbegin ()] (std::vector<int> cl) mutable { cl.push_back (-*iter); ++iter; return cl; });
    orxialiaries.push_back (card_clause[k]);
    answer.push_back (orxialiaries);
  }
  else {
    if (k == l.size ()) { return dnf_k_is_size_x (phi, l); }
    
    matrix<int> alo {alofc (phi, l, false)}; 
    std::transform (alo.cbegin (), alo.cend (), std::inserter (answer, answer.end ()),
		    [card_aux = card_clause[k]] (std::vector<int> cl) { cl.push_back (card_aux); return cl; });
  }
    
  return answer;
}

matrix<int> d_hx_resistant_impl (const matrix<int> &phi, const std::vector<int> &x, int k, int &aux, bool cnf) {
  matrix<int> answer;
  Step<int> vstep; vstep.variables = x; vstep.clear (vstep.variables.begin ());
  while (vstep.step ()) {
    matrix<int> partial {size_then_alofc (phi, vstep.variables, k, aux, cnf)};
    std::copy (partial.cbegin (), partial.cend (), std::inserter (answer, answer.end ()));
  }
  return answer;
}

matrix<int> d_hx_resistant_cnf (const matrix<int> &phi, const std::vector<int> &x, int k, int &aux) { return d_hx_resistant_impl (phi, x, k, aux, true); }
matrix<int> d_hx_resistant_dnf (const matrix<int> &phi, const std::vector<int> &x, int k, int &aux) { return d_hx_resistant_impl (phi, x, k, aux, false); }

matrix<int> nu_o (const matrix<int> &phi, int k, int &aux, bool cnf) {
  matrix<int> answer;
  
  if (cnf) {
    std::vector<int> fresh (phi.size ());
    auto p_c {fresh.begin ()};
    for (const std::vector<int> &clause : phi) {
      *p_c = ++aux;
      for (int lit : clause) { answer.push_back ({-*p_c, -lit}); }
      ++p_c;
    }
    matrix<int> cardinality {gt (fresh, k, aux)};
    std::copy (cardinality.cbegin (), cardinality.cend (), std::inserter (answer, answer.end ()));
  }

  else {
    for (const std::vector<int> &term : phi) {
      std::vector<int> negated (term.size ());
      std::transform (term.cbegin (), term.cend (), negated.begin (), [] (int i) { return -i; });
      matrix<int> partial {gt (negated, k, aux)};
      std::copy (partial.cbegin (), partial.cend (), std::inserter (answer, answer.end ()));
    }
  }

  return answer;
}

matrix<int> nu_o_cnf (const matrix<int> &phi, const std::vector<int> &, int k, int &aux) { return nu_o (phi, k, aux, true); }
matrix<int> nu_o_dnf (const matrix<int> &phi, const std::vector<int> &, int k, int &aux) { return nu_o (phi, k, aux, false); }

matrix<int> nr (const matrix<int> &phi, int k, int &aux, int satisfy) {
  // maybe num_vars /= aux
  std::vector<int> xs (aux); for (int &x : xs) { x = ++aux; }

  auto pos
    { [&xs, &aux, k] (matrix<int> left) {
      for (std::vector<int> &cl : left) {
	size_t size {cl.size ()};
	cl.resize (size * 2);
	std::transform (cl.cbegin (), std::next (cl.cbegin (), size), std::next (cl.begin (), size),
			[&xs] (int lit) { return xs[lit > 0 ? lit-1 : -lit-1]; });
      }
      matrix<int> right {leq (xs, k, aux)};
      std::copy (right.cbegin (), right.cend (), std::inserter (left, left.end ()));

      return left;
    }};

  auto neg
    { [&phi, k, &aux, &xs] () mutable {
      std::vector<int> selectors (phi.size ()); for (int &sel : selectors) { sel = ++aux; }

      matrix<int> answer; // {{selectors}};

      int sel {selectors[0]};
      for (const std::vector<int> &cl : phi)
	{ for (int i : cl) { answer.push_back ({-sel, -i}); answer.push_back ({-sel, -xs[i > 0 ? i-1 : -i-1]}); } }
      
      KCardNet card {xs, k+1, aux, 1}; std::vector<int> card_clause {card.card (card.data.begin (), card.data.end (), aux)};
      matrix<int> ret_val {card.clauses}; std::copy (ret_val.cbegin (), ret_val.cend (), std::inserter (answer, answer.end ()));
      selectors.push_back ({card_clause[k]});

      answer.push_back (selectors);

      return answer;
    }};

  return satisfy ? pos (phi) : neg ();
}

matrix<int> pos_nr (const matrix<int> &phi, const std::vector<int> &, int k, int &aux) { return nr (phi, k, aux, true); }
matrix<int> neg_nr (const matrix<int> &phi, const std::vector<int> &, int k, int &aux) { return nr (phi, k, aux, false); }

matrix<int> solve (const matrix<int> &phi, int k, int &aux, auto &&func, bool enumerate, const std::vector<int> &important_lits = {}) {
  int num_vars {aux};
  matrix<int> clauses {func (phi, important_lits, k, aux)};
  std::cout << "Encoded for " << k << std::endl;

  CaDiCaL::Solver *solver {new CaDiCaL::Solver};

  for (const std::vector<int> &cl : clauses) { solver->clause (cl); }

  auto get_model
    { [num_vars] (CaDiCaL::Solver *solver) -> std::vector<int> {
      if (solver->solve () == CaDiCaL::SATISFIABLE) {
	std::vector<int> model (num_vars); auto iter {model.begin ()};
	for (int i {1}; i <= num_vars; ++i, ++iter) { *iter = solver->val (i); }
	return model;
      }
      return std::vector<int> {};
    }};

  matrix<int> answer;
  
  if (enumerate) {
    while (true) {
      std::vector<int> model {get_model (solver)};
      if (model.empty ()) { break; }
      answer.push_back (model);
      for (int i : model) { std::cout << i << ' '; } std::cout << '0' << std::endl;
      for (int &i : model) { i = -i; }
      solver->clause (model);
    }
  }
  else {
    std::vector<int> model {get_model (solver)};
    if (!model.empty ()) { answer.push_back (model); }
  }

  delete solver;
  return answer;
}    

int dich_resistance_gap (const matrix<int> &phi, int num_vars, auto &&func, const std::vector<int> &important_lits = {}) {
  int max {}, bot {1}, top {num_vars};
  while (bot <= top) {
    int mid {(top-bot)/2 + bot}; int aux {num_vars};
    matrix<int> solution {solve (phi, mid, aux, func, false, important_lits)};
    if (solution.empty ()) { std::cout << "Empty@" << mid << std::endl;; top = mid-1; }
    else {
      std::cout << "Solution@" << mid << std::endl;
      max = mid > max ? mid : max;
      bot = mid+1;
    }
  }
  return max;
}

int incr_resistance_gap (const matrix<int> &phi, int num_vars, auto &&func, const std::vector<int> &important_lits = {}) {
  for (int k {1}; k <= num_vars; ++k) {
    std::cout << k << std::endl;
    int aux {num_vars};
    matrix<int> solution {solve (phi, k, aux, func, false, important_lits)};
    if (solution.empty ()) { return k-1; }
  }
  return num_vars;
}

void print_encoding (const matrix<int> &phi, int k, int &aux, auto &&func, const std::vector<int> &important_lits = {}, std::ostream &out = std::cout) {
  matrix<int> clauses {func (phi, important_lits, k, aux)};
  out << "p cnf " << aux << ' ' << clauses.size () << '\n';
  print_cnf (out, clauses);
}
  
bool read_options (int argc, char **argv, std::string &input, std::string &output, int &k, char &approach, bool &cnf, bool &enumerate, bool &print_enc) {
  if (argc < 2) { return false; }
  input = argv[1];
  
  for (int i {2}; i < argc; ++i) {
    if (argv[i][0] != '-') { return false; }
    switch (argv[i][1]) {
    case 'a': case 'b': case 'c': case 'd':
      approach = argv[i][1]; break;
    case 'e':
      enumerate = true; break;
    case 'k':
      if (++i >= argc) { return false; }
      k = std::stoi (argv[i]);
      break;
    case 'o':
      if (++i >= argc) { return false; }
      output = argv[i];
      break;
    case 'p':
      print_enc = true; break;
    case 'v':
      cnf = true; break;
    default:
      return false;
    }
  }
  return true;
}  
  
int main (int argc, char **argv) {
  std::string input, output;
  int k {1};
  char approach {'a'};
  bool cnf {}, enumerate {}, print_enc {};
  if (!read_options (argc, argv, input, output, k, approach, cnf, enumerate, print_enc)) {
    std::cerr << "Usage: " << argv[0] << " <input> [-k <k>] [-[abcd]] [-e] [-p] [-v]\n"
	      << "       Modes: (a . δ_H) (b . δ_{H,X}) (c ν_o)\n"
	      << "       -e enumerates. -p prints encoding. -v treats input as CNF.\n";
    return 1;
  }
  
  int vars;
  matrix<int> phi {cnf_from_file (argv[1], vars)};

  auto run
    { [&phi, k, &vars, enumerate, cnf, print_enc, output] (auto &&func) {
      if (print_enc) {
	if (output.empty ()) { print_encoding (phi, k, vars, func); }
	else {
	  std::ofstream out {output.c_str ()};
	  print_encoding (phi, k, vars, func, {}, out);
	}
      }
      else if (enumerate) {
	matrix<int> answer {solve (phi, k, vars, func, true, {})};
	std::cout << "Count = " << answer.size () << std::endl;
      }
      else {
	int answer {dich_resistance_gap (phi, vars, func)};
	std::cout << "Max Resistance Gap: " << answer << std::endl;
      }
    }};
  
  switch (approach) {
  case 'a':
    run (delta_h_dnf); break;
  case 'b': {
    matrix<int> answer {solve (phi, k, vars, cnf ? d_hx_resistant_cnf : d_hx_resistant_dnf, true, {1, 2, 3, 4, 5})};
    std::cout << "Count = " << answer.size () << std::endl; break; }
  case 'c': 
    run (cnf ? nu_o_cnf : nu_o_dnf); break;
  case 'd':
    run (pos_nr); break;
  }
}
