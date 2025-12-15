#ifndef CODES_H
#define CODES_H

#include <iostream>
#include <vector>

struct Rename { int orig, loc; };

struct RenameLookup {
  std::vector<Rename> mappings;
  int counter {};

  std::vector<Rename>::iterator locate (int orig,
					std::vector<Rename>::iterator start,
					std::vector<Rename>::iterator end) {
    auto distance {std::distance (start, end)};
    if (!distance) { return end; }
    std::vector<Rename>::iterator mid {std::next (start, (distance / 2))};
    if (mid->orig == orig) { return mid; }
    return mid->orig > orig ? locate (orig, start, mid) : locate (orig, std::next (mid), end);
  }

  std::vector<Rename>::iterator locate (int orig) {
    return locate (orig, mappings.begin (), mappings.end ());
  }

  int insert (int num) {
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
      for (auto pos {std::next (mappings.begin (), dist)}; pos != mappings.end (); ++pos) {
	Rename tmp {*pos};
	*pos = current;
	current = tmp;
      }
      return counter;
    }
  }

  std::vector<int> codomain () const {
    std::vector<int> to_return (mappings.size ());
    auto writer {to_return.begin ()};
    for (auto rniter {mappings.cbegin ()}; rniter != mappings.cend (); ++rniter, ++writer)
      { *writer = rniter->loc; }
    return to_return;
  }
  
  std::vector<int> init (const std::vector<int> &traducenda) {
    for (int i : traducenda) { insert (i); }
    return codomain ();
  }

  std::vector<int> make_comparison (const std::vector<int> &others) const {
    RenameLookup copy {*this};
    std::vector<int> to_return (others.size ());
    auto writer {to_return.begin ()};
    for (int other : others)
      { *writer = copy.insert (other); ++writer; }
    return to_return;
  }
};

std::ostream &operator << (std::ostream &out, const Rename &rn) {
  out << '(' << rn.orig << ',' << rn.loc << ')';
  return out;
}

std::ostream &operator << (std::ostream &out, const RenameLookup &rl) {
  for (const Rename &rn : rl.mappings)
    { out << rn; }
  return out;
}

struct Code {
  bool *clauses;
  int width;

  Code (int width) : clauses {new bool [width] {}}, width {width} {}
  ~Code () { delete[] clauses; }

  Code (int width, int val) : Code {width} {
    for (int i {}; val && i <= width; val >>= 1, ++i) 
      { if (val & 1) { clauses[i] = true; } }
  }
  Code (int width, const std::string &str) : Code {width} {
    int idx {};
    for (auto iter {str.crbegin ()}; iter != str.crend () && idx <= width; ++iter, ++idx)
      { if (*iter == '1') { clauses[idx] = true; } }
  }
  Code (int width, const std::vector<int> &numbered) : Code {width} {
    for (int i : numbered)
      { if (i < width) { clauses[i] = true; } }
  }
  
  Code (const Code &old) : Code {old.width} {
    int idx {};
    for (bool *copy {clauses}, *orig {old.clauses}; idx <= width; ++copy, ++orig, ++idx)
      { if (*orig) { *copy = true; } }
  }

  void set_val (int val) {
    for (int i {}; val && i <= width; val >>= 1, ++i)
      { clauses[i] = val & 1; }
  }
  void set_val (const std::string &str) {
    int idx {};
    for (auto iter {str.crbegin ()}; iter != str.crend () && idx <= width; ++iter, ++idx) 
      { clauses[idx] = *iter == '1'; }
    for ( ; idx <= width; ++idx)
      { clauses[idx] = false; }
  }
  void set_val (const std::vector<int> &numbered) {
    blank ();
    for (int i : numbered)
      { if (i < width) { clauses[i] = true; } }
  }

  bool pass (auto test, bool def_phase, int begin = 0, int end = -1) const {
    if (end == -1)
      { end = width; }
    for (int i {begin}; i < end; ++i) 
      { if (test (i)) { return !def_phase; } }
    return def_phase;
  }
      
  bool simple_pass (auto test, bool def_phase, int begin = 0, int end = -1) const {
    return pass ([this, &test] (int i) { return test (clauses[i]); }, def_phase, begin, end);
  }
  bool none (int begin = 0, int end = -1) const { return simple_pass ([] (bool p) { return p; },  true,  begin, end); }
  bool all  (int begin = 0, int end = -1) const { return simple_pass ([] (bool p) { return !p; }, false, begin, end); }
  bool any  (int begin = 0, int end = -1) const { return simple_pass ([] (bool p) { return p; },  false, begin, end); }

  bool subsumes (const Code &stronger, int begin = 0, int end = -1) const {
    return pass ([&stronger, this] (int i) { return !clauses[i] || stronger.clauses[i]; }, true, begin, end);
  }
  bool subsumes (const Code &stronger, bool unsure_size) const {
    if (width == stronger.width)
      { return subsumes (stronger); }

    else if (width < stronger.width) {
      if (subsumes (stronger, 0, width))
	{ return true; }
      else if (stronger.subsumes (*this, 0, width))
	{ return false; }
      else
	{ return stronger.none (width); }
    }

    else
      { return subsumes (stronger, stronger.width) && none (stronger.width); }
  }

  void blank () {
    for (int i {}; i < width; ++i)
      { clauses[i] = false; }
  }
};
 
#endif 
