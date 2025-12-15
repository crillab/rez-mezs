#include "cardinality.hpp"

matrix<int> SeqEncoding::iff (int lit1, int lit2) {
  constexpr int n {2};
  matrix<int> clauses (n);
  int lits[n] {lit1, lit2};
  for (int i {}; i < n; ++i)
    { clauses[i] = {-lits[i], lits[(i+1)%n]}; }
  return clauses;
}

void SeqEncoding::first_determines_first (int el_begin) {
  for (const std::vector<int> &cl : iff (el_begin, s_idx (1, 1)))
    { clauses.push_back (cl); }
}

void SeqEncoding::first_counts_for_at_most_one () {
  for (int k {2}; k < width; ++k)
    { clauses.push_back ({-s_idx (1, k)}); }
}

void SeqEncoding::one_iff (int j, int q) {
  matrix<int> disj {disjunction ({q, s_idx (j-1, 1)}, s_idx (j, 1))};
  clauses.insert (clauses.end (), disj.begin (), disj.end ());
}

int SeqEncoding::k_iff (int j, int q, int last_var) {
  for (int k {2}; k <= width; ++k) {
    int inner {++last_var};
    int outer {s_idx (j,k)};
    matrix<int> term {conjunction ({q, s_idx (j-1, k-1)}, inner)};
    clauses.insert (clauses.end (), term.begin (), term.end ());
    matrix<int> cl {disjunction ({inner, s_idx (j-1, k)}, outer)};
    clauses.insert (clauses.end (), cl.begin (), cl.end ());
  }
  return last_var;
}
    
int SeqEncoding::operator () (int el_begin, int el_end, int last_var) {
  first_determines_first (el_begin);
  first_counts_for_at_most_one ();
  for (int q {el_begin+1}, j {2}; q <= el_end; ++q, ++j) {
    one_iff (j,q);
    last_var = k_iff (j,q,last_var);
  }
  return last_var;
}

std::vector<int> by_extremes (std::vector<int>::iterator begin, std::vector<int>::iterator end) {
  std::vector<int> vec (std::distance (begin, end));
  std::copy (begin, end, vec.begin ());
  return vec;
}

std::vector<int> SortCardNetwork::fresh_seq (int &var, int size) {
  std::vector<int> seq (size);
  std::iota (seq.begin (), seq.end (), var+1);
  var += seq.size ();
  return seq;
}

std::vector<int> SortCardNetwork::half (const std::vector<int> &orig, bool odd) {
  std::vector<int> copy (orig.size () / 2);
  auto src {std::next (orig.cbegin (), odd ? 0 : 1)};
  for (auto dest {copy.begin ()}; dest != copy.end (); ++dest, ++src, ++src)
    { *dest = *src; }
  return copy;
}

std::vector<int> SortCardNetwork::make_even (const std::vector<int> &odd_seq, int &var) {
  int dummy {++var};
  std::vector<int> even_seq (odd_seq.size ()+1);
  std::copy (odd_seq.cbegin (), odd_seq.cend (), std::next (even_seq.begin ()));
  even_seq[0] = dummy; clauses.push_back ({-dummy});
  return even_seq;
}

void SortCardNetwork::bind (const std::vector<int> &c, const std::vector<int> &d, const std::vector<int> &e, int i, int phase) {
  int big_c {c[2*(i+1)]}, little_c {c[2*i+1]};
  int &c3 {phase > 0 ? big_c : little_c}, &c2 {phase > 0 ? little_c : big_c};

  clauses.push_back ({phase * -d[i+1], phase * -e[i], phase * c3});
  clauses.push_back ({phase * -d[i+1], phase * c2});
  clauses.push_back ({phase * -e[i],   phase * c2});
}

std::vector<int> SortCardNetwork::merge (const std::vector<int> &a, const std::vector<int> &b, int &var) {
  if (a.size () == 1) { return merge_base (a, b, var); }
  if (a.size () % 2 == 1) { return merge (make_even (a, var), make_even (b, var), var); }

  std::vector<int> d {merge_half (a, b, var, true)};
  std::vector<int> e {merge_half (a, b, var, false)};
  std::vector<int> c {get_c (a, d, e, var)};

  for (int i {}; i < loop_limit (a); ++i) {
    if (amk) { bind (c, d, e, i, 1); }
    if (alk) { bind (c, d, e, i, -1); }
  }

  return c;
}
  
std::vector<int> SortCardNetwork::merge (const std::vector<int> &a, const std::vector<int> &b, int &var, bool verbose) {
  std::vector<int> result;
  if (a.size () == 1) { result = merge_base (a, b, var); }
  else if (a.size () % 2 == 1) { result = merge (make_even (a, var), make_even (b, var), var, verbose); }

  else {
    std::vector<int> d {merge_half (a, b, var, true, true)};
    std::vector<int> e {merge_half (a, b, var, false, true)};
    std::vector<int> c {get_c (a, d, e, var)};

    for (int i {}; i < loop_limit (a); ++i) {
      if (amk) { bind (c, d, e, i, 1); }
      if (alk) { bind (c, d, e, i, -1); }
    }
  
    result = c;
  }

  if (verbose) {
    std::cout << "MERGE ["; for (int i : a) { std::cout << i << ", "; } std::cout << "\b\b] [";
    for (int i : b) { std::cout << i << ", "; } std::cout << "\b\b] = [";
    for (int i : result) { std::cout << i << ", "; } std::cout << "\b\b]\n";
  }

  return result;
}

std::vector<int> SortCardNetwork::merge_base (const std::vector<int> &a, const std::vector<int> &b, int &var) {
  std::vector<int> c {++var, ++var};
  int idx {(int) clauses.size ()}; clauses.resize (idx + ((amk && alk) ? 6 : 3)); --idx;
  if (amk)
    { clauses[++idx] = {-a[0], -b[0], c[1]}; clauses[++idx] = {-a[0], c[0]}; clauses[++idx] = {-b[0], c[0]}; }
  if (alk)
    { clauses[++idx] = {a[0], b[0], -c[0]}; clauses[++idx] = {a[0], -c[1]}, clauses[++idx] = {b[0], -c[1]}; }
  return c;
}

std::vector<int> SortCardNetwork::merge_half (const std::vector<int> &a, const std::vector<int> &b, int &var, bool odd) {
  return merge (half (a, odd), half (b, odd), var);
}

std::vector<int> SortCardNetwork::merge_half (const std::vector<int> &a, const std::vector<int> &b, int &var, bool odd, bool verbose) {
  return merge (half (a, odd), half (b, odd), var, verbose);
}

std::vector<int> HalfSCN::get_c (const std::vector<int> &a, const std::vector<int> &d, const std::vector<int> &e, int &var) {
  std::vector<int> c (2*a.size ());
  std::iota (std::next (c.begin ()), std::prev (c.end ()), var+1);
  var += c.size () - 2;
  c.front () = d.front (); c.back () = e.back ();
  return c;
}

int HalfSCN::loop_limit (const std::vector<int> &a) {
  return a.size () - 1;
}

std::vector<int> HalfSCN::hsort (std::vector<int> &seq, int &vars) {
  std::vector<int>::iterator mid {std::next (seq.begin (), (int) seq.size () / 2)};
  std::vector<int> a {by_extremes (seq.begin (), mid)}, b {by_extremes (mid, seq.end ())};
  if (seq.size () == 2) { return merge (a, b, vars); }
  return merge (hsort (a, vars), hsort (b, vars), vars);
}

std::vector<int> HalfSCN::hsort (std::vector<int> &seq, int &vars, bool verbose) {
  std::vector<int>::iterator mid {std::next (seq.begin (), (int) seq.size () / 2)};
  std::vector<int> a {by_extremes (seq.begin (), mid)}, b {by_extremes (mid, seq.end ())};
  std::vector<int> result;
  if (seq.size () == 2) { result = merge (a, b, vars, verbose); }
  else { result = merge (hsort (a, vars, verbose), hsort (b, vars, verbose), vars, verbose); }
  if (verbose) {
    std::cout << "HSort ["; for (int i : seq) { std::cout << i << ", "; } std::cout << "\b\b] = [";
    for (int i : result) { std::cout << i << ", "; } std::cout << "\b\b]\n";
  }
  return result;
}
  
std::vector<int> SimplSCN::get_c (const std::vector<int> &a, const std::vector<int> &d, const std::vector<int> &e, int &var) {
  std::vector<int> c (a.size ()+1);
  std::iota (std::next (c.begin ()), c.end (), var+1);
  var += c.size () - 1;
  c[0] = d[0];
  return c;
}

int SimplSCN::loop_limit (const std::vector<int> &a) {
  return a.size () / 2;
}

KCardNet::KCardNet (std::vector<int> data, int p, int &vars, int dir)
  : data {data}, amk {dir != 1}, alk {dir != -1}, k {1} {
  while (k <= p && (amk || k < p)) { k <<= 1; }

  if (data.size () % k) {
    int idx {(int) data.size ()};
    this->data.resize (idx + k - (idx % k));
    for (auto iter {std::next (this->data.begin (), idx)}; iter != this->data.end (); ++iter) {
      int dummy {++vars};
      *iter = dummy;
      clauses.push_back ({-dummy});
    }
  }
}

std::vector<int> KCardNet::card (std::vector<int>::iterator begin, std::vector<int>::iterator end, int &vars) {
  if (std::distance (begin, end) == k) {
    HalfSCN hscn; hscn.amk = amk; hscn.alk = alk;
    auto k_data {by_extremes (begin, end)};
    auto c1_k {hscn.hsort (k_data, vars)};
    auto capture {hscn.clauses};
    clauses.insert (clauses.end (), capture.begin (), capture.end ());
    return c1_k;
  }

  auto to_k {card (begin, std::next (begin, k), vars)}, rest {card (std::next (begin, k), end, vars)};
  SimplSCN sscn; sscn.amk = amk; sscn.alk = alk;
  auto mersion {sscn.merge (to_k, rest, vars)};
  auto capture {sscn.clauses};
  clauses.insert (clauses.end (), capture.begin (), capture.end ());
  mersion.resize (k);
  return mersion;
}
