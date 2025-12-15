#ifndef UTIL_H
#define UTIL_H

#include <algorithm>
#include <iostream>
#include <vector>

template<typename T> using matrix = std::vector<std::vector<T>>;
using CodeType = unsigned long long;

CodeType choose (int n, int r);

matrix<int> bind (int selector, std::vector<int> &&literals, bool term);
matrix<int> conjunction (std::vector<int> conjuncts, int selector);
matrix<int> disjunction (std::vector<int> disjuncts, int selector);

std::vector<int> add_one_lit (int lit, std::vector<int> clause);

std::vector<int> implies_clause (int implicant, std::vector<int> clause);
matrix<int> implied_by_clause (int implicate, const std::vector<int> &clause);
matrix<int> implies_term (int implicant, const std::vector<int> &term);
std::vector<int> implied_by_term (int implicate, const std::vector<int> &term);  

bool subsumes (const std::vector<int> &weaker, const std::vector<int> &stronger);
bool subsumes (std::vector<int> weaker, std::vector<int> stronger, int sorted);
bool subsumes (int weaker, int stronger);

void discard_comment (std::istream &in);

void print_clause (std::ostream &out, const std::vector<int> &clause);
void print_cnf (std::ostream &out, const matrix<int> &cnf);
void print_disjunction (std::ostream &out, const std::vector<int> &clause);
void print_pretty (std::ostream &out, const matrix<int> &cnf);

#endif 
