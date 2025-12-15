#ifndef CARD_H
#define CARD_H

#include "util.hpp"

#include <numeric>
#include <vector>

template <typename T> using matrix = std::vector<std::vector<T>>;

struct CardEncoding {
  matrix<int> clauses;
  matrix<int> get_clauses () { return clauses; }
};

struct SeqEncoding : public CardEncoding {
  int before_s_start;
  int width;

  SeqEncoding (int &last_var, int width)
    : before_s_start {last_var}, width {width} { last_var += width * width; }

  int s_idx (int i, int j) const { return before_s_start + (i - 1) * width + j; }
  int kth_var (int k) const { return s_idx (width, k); }

  matrix<int> iff (int lit1, int lit2);
  inline void first_determines_first (int el_begin);
  inline void first_counts_for_at_most_one ();
  inline void one_iff (int j, int q);
  int k_iff (int j, int q, int last_var);
  int operator () (int el_begin, int el_end, int last_var);
};

struct SortCardNetwork : public CardEncoding {
  bool amk {true}, alk {};
  
  std::vector<int> fresh_seq (int &var, int size);
  std::vector<int> half (const std::vector<int> &orig, bool odd);
  std::vector<int> make_even (const std::vector<int> &odd_seq, int &var);

  virtual std::vector<int> get_c (const std::vector<int> &, const std::vector<int> &, const std::vector<int> &, int &) = 0;
  virtual int loop_limit (const std::vector<int> &) = 0;

  void bind (const std::vector<int> &c, const std::vector<int> &d, const std::vector<int> &e, int i, int phase);

  std::vector<int> merge (const std::vector<int> &a, const std::vector<int> &b, int &var);
  std::vector<int> merge (const std::vector<int> &a, const std::vector<int> &b, int &var, bool verbose);
  std::vector<int> merge_base (const std::vector<int> &a, const std::vector<int> &b, int &var);
  inline std::vector<int> merge_half (const std::vector<int> &a, const std::vector<int> &b, int &var, bool odd);
  inline std::vector<int> merge_half (const std::vector<int> &a, const std::vector<int> &b, int &var, bool odd, bool verbose);
};

struct HalfSCN : public SortCardNetwork {
  std::vector<int> get_c (const std::vector<int> &a, const std::vector<int> &d, const std::vector<int> &e, int &var);
  inline int loop_limit (const std::vector<int> &a);

  std::vector<int> hsort (std::vector<int> &seq, int &vars);
  std::vector<int> hsort (std::vector<int> &seq, int &vars, bool verbose);
};

struct SimplSCN : public SortCardNetwork {
  std::vector<int> get_c (const std::vector<int> &a, const std::vector<int> &d, const std::vector<int> &e, int &var);
  inline int loop_limit (const std::vector<int> &a);
};

struct KCardNet : public CardEncoding {
  matrix<int> clauses;
  std::vector<int> data;
  int k;
  bool amk, alk;

  KCardNet (std::vector<int> data, int p, int &vars, int dir); // dir = (-1 . <=) (0 . =) (1 . >=)

  std::vector<int> card (std::vector<int>::iterator begin, std::vector<int>::iterator end, int &vars);
};

#endif 
