// Created by Basel Khouri 2024

#ifndef _drup2itptypes_hpp_INCLUDED
#define _drup2itptypes_hpp_INCLUDED

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <unordered_map>
#include <vector>

namespace DRUP2ITP {

using namespace std;

#define PART_UNDEF 0

class Range {
  unsigned m_min : 16, m_max : 16;

public:
  Range ();
  Range (const unsigned c);
  bool undef () const;
  void reset ();
  bool singleton () const;
  void join (const unsigned np);
  void join (const Range &o);
  unsigned min () const;
  unsigned max () const;
  bool operator== (const Range &r);
  bool operator!= (const Range &r);
};

struct Clause {
  Clause *next;
  uint64_t hash;
  uint64_t id;
  bool garbage;
  bool core;
  bool original;
  Range range;
  unsigned size;
  int literals[1];
  typedef int *literal_iterator;
  typedef const int *const_literal_iterator;
  literal_iterator begin () { return literals; }
  literal_iterator end () { return literals + size; }
  const_literal_iterator begin () const { return literals; }
  const_literal_iterator end () const { return literals + size; }
};

struct Watch {
  Clause *clause;
  int blit;
  int size;
  Watch (int b, Clause *c) : clause (c), blit (b), size (c->size) {}
  Watch () {}
  bool binary () const { return size == 2; }
};

typedef vector<Watch> Watches;
typedef Watches::iterator watch_iterator;
typedef Watches::const_iterator const_watch_iterator;

class WatchSort {
  const vector<unsigned> *trail;
  const signed char *vals;

public:
  WatchSort (const vector<unsigned> *lit2trail, const signed char *values);
  void reset (const vector<unsigned> *lit2trail, const signed char *values);
  bool operator() (int x, int y) const;
};

inline void remove_watch (Watches &ws, Clause *clause) {
  const auto end = ws.end ();
  auto i = ws.begin ();
  for (auto j = i; j != end; j++) {
    const Watch &w = *i++ = *j;
    if (w.clause == clause)
      i--;
  }
  assert (i + 1 == end);
  ws.resize (i - ws.begin ());
}

inline void update_watch_size (Watches &ws, int blit, Clause *conflict) {
  bool found = false;
  const int size = conflict->size;
  for (Watch &w : ws) {
    if (w.clause == conflict)
      w.size = size, w.blit = blit, found = true;
    assert (w.clause->garbage || w.size == 2 || w.clause->size != 2);
  }
  assert (found), (void) found;
}

struct ChainDerivation {
  vector<int> pivots;
  vector<Clause *> clauses;
  void clear () {
    clauses.clear ();
    pivots.clear ();
  }
  void append (Clause *c) { clauses.push_back (c); }
  void append (int lit, Clause *c) {
    assert (lit);
    pivots.push_back (lit);
    clauses.push_back (c);
  }
  bool empty () const { return clauses.empty () && pivots.empty (); }
};

struct ResolutionProofIterator {
  // antecedents for chain resolution
  ChainDerivation chain;
  virtual ~ResolutionProofIterator () {}
  // trivial resolution
  virtual void resolution (int resolvent, int antecedent1,
                           Clause *antecedent2) = 0;
  // chain resolution
  virtual void chain_resolution (int resolvent) = 0;
  // chain resolution. resolvent == 0 for the empty clause.
  virtual void chain_resolution (Clause *resolvent = 0) = 0;
};

class TraceCheck : public ResolutionProofIterator {
private:
  FILE *file;
  unordered_map<Clause *, int> visited;
  vector<int> units;
  int ids;

  bool visit_antecedent (int);
  bool visit_antecedent (Clause *);
  void visit_derived (int);
  void visit_derived (Clause *);
  void output (int);
  void output (Clause *);
  void output_chain ();

public:
  TraceCheck (FILE *, unsigned);
  void resolution (int, int, Clause *);
  void chain_resolution (int);
  void chain_resolution (Clause *parent = 0);
};

} // namespace DRUP2ITP

#endif
