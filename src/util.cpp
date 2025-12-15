#include "util.hpp"

CodeType choose (int n, int r) {
  if (r < 0 || n < r || n < 0) { return 0; }

  auto mult
    { [] (auto &&func, unsigned start, unsigned end, CodeType acc) {
      if (start > end)
	{ return acc; }
      return func (func, start+1, end, acc*start);
    }};

  CodeType top {mult (mult, n-r+1, n, 1)};
  CodeType bot {mult (mult, 1, r, 1)};

  return top / bot;
}

matrix<int> bind (int selector, std::vector<int> &&literals, bool term) {
  matrix<int> clauses (literals.size ()+1);
  std::vector<int> long_clause (clauses.size ());
  auto cl {clauses.begin ()};
  auto conj {long_clause.begin ()};

  if (term) { selector = -selector; }

  for (int lit : literals) {
    *cl   = {term ? lit : -lit, selector}; ++cl;
    *conj = term ? -lit : lit;             ++conj;
  }

  *conj = -selector;
  *cl = {long_clause};

  return clauses;
}

matrix<int> conjunction (std::vector<int> conjuncts, int selector) {
  return bind (selector, std::move (conjuncts), true);
}
matrix<int> disjunction (std::vector<int> disjuncts, int selector) {
  return bind (selector, std::move (disjuncts), false);
}

std::vector<int> add_one_lit (int lit, std::vector<int> clause) {
  int idx {(int) clause.size ()};
  clause.resize (idx+1);
  clause[idx] = lit;
  return clause;
}

std::vector<int> implies_clause (int implicant, std::vector<int> clause) {
  return add_one_lit (-implicant, clause);
}

matrix<int> bind_each (const std::vector<int> &expr, int selector, auto &&func) {
  matrix<int> answer (expr.size ());
  auto cl {answer.begin ()};
  for (auto liter {expr.cbegin ()}; liter != expr.cend (); ++cl, ++liter)
    { *cl = func (*liter, selector); }
  return answer;
}

matrix<int> implied_by_clause (int implicate, const std::vector<int> &clause) {
  return bind_each (clause, implicate, [] (int lit, int sel) -> std::vector<int> { return {-lit, sel}; });
}

matrix<int> implies_term (int implicant, const std::vector<int> &term) {
  return bind_each (term, implicant, [] (int lit, int sel) -> std::vector<int> { return {-sel, lit}; });
}

std::vector<int> implied_by_term (int implicate, std::vector<int> term) {
  std::transform (term.begin (), term.end (), term.begin (), [] (int i) { return -i; });
  return add_one_lit (implicate, term);
}

bool subsumes (const std::vector<int> &weaker, const std::vector<int> &stronger) {
  // Pre: both sorted
  for (auto witer {weaker.cbegin ()}, siter {stronger.cbegin ()};
       witer != weaker.cend (); ++witer) {
    if (siter == stronger.cend () || *siter > *witer) { return false; }

    while (*siter < *witer && siter != stronger.cend ()) { ++siter; }

    if (*witer == *siter) { ++siter; }
    else { return false; }
  }

  return true;
}

bool subsumes (std::vector<int> weaker, std::vector<int> stronger, int sorted) {
  auto negate
    { [] (std::vector<int> &vector) { std::transform (vector.begin (), vector.end (), vector.begin (), [] (int i) { return -i; }); } };
  auto sort
    { [] (std::vector<int> &vector) { std::sort (vector.begin (), vector.end ()); } };

  switch (sorted) {
  case -2: negate (weaker); break;
  case -1: negate (stronger); break;
  case 0:  sort (weaker); sort (stronger); break;
  case 1:  sort (stronger); break;
  case 2:  sort (weaker); break;
  }

  return subsumes (weaker, stronger);
}

bool subsumes (int weaker, int stronger) {
  return (stronger & weaker) == weaker;
}

void discard_comment (std::istream &in) {
  std::string discard;
  std::getline (in, discard);
}

void print_clause (std::ostream &out, const std::vector<int> &clause) {
  for (int lit : clause) { out << lit << ' '; } out << "0\n";
}

void print_cnf (std::ostream &out, const matrix<int> &cnf) {
  for (const std::vector<int> &clause : cnf) { print_clause (out, clause); }
}

void print_disjunction (std::ostream &out, const std::vector<int> &clause) {
  out << '(';
  auto iter {clause.cbegin ()};
  if (iter != clause.cend ()) {
    auto lnot { [&out] (int lit) { out << (lit > 0 ? std::to_string (lit) : "¬" + std::to_string (-lit)); } };
    lnot (*iter);
    for (++iter; iter != clause.cend (); ++iter) { out << " ∨ "; lnot (*iter); }
  }
  out << ')';
}

void print_pretty (std::ostream &out, const matrix<int> &cnf) {
  if (cnf.empty ()) { return; }

  auto iter {cnf.cbegin ()};
  print_disjunction (out, *iter);

  for (++iter; iter != cnf.cend (); ++iter) { out << " ∧ "; print_disjunction (out, *iter); }
}

