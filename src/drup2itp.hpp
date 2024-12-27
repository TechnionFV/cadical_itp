// Created by Basel Khouri 2024

#ifndef _drup2itp_hpp_INCLUDED
#define _drup2itp_hpp_INCLUDED

#include "../src/cadical.hpp"
#include "../src/tracer.hpp"
#include "drup2itptypes.hpp"

#include <cstdio>
#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace DRUP2ITP {

using namespace std;
using CaDiCaL::ConclusionType;
using CaDiCaL::External;
using CaDiCaL::Internal;
using CaDiCaL::Solver;

class MiniTracer {
  const vector<Range> &ranges;
  const vector<Clause *> &reasons;

public:
  MiniTracer (const vector<Range> &r, const vector<Clause *> &s)
      : ranges (r), reasons (s) {}

  const Range &range (int lit) const {
    assert (lit);
    unsigned idx = abs (lit);
    assert (idx < ranges.size ());
    return ranges[idx];
  }

  const Clause *reason (int lit) const {
    assert (lit);
    unsigned idx = abs (lit);
    assert (idx < reasons.size ());
    return reasons[idx];
  }
};

class Drup2Itp : public CaDiCaL::StatTracer {
  Internal *internal;
  External *external;
  vector<Clause *> assumption_clauses; // assumptions lemmas in last solve
  Clause *conflict;          // conflict clause in last propagation
  Clause *confl_assumes;     // conflict clause in last propagation
  ConclusionType conclusion; // unsat conclusion type
  vector<Clause *> proof;    // clausal proof
  vector<Clause *> reasons;  // reasons for literals on trail
  vector<int> assumptions;
  vector<int> constraint;
  vector<Watches> wtab; // table of watches for all literals
  WatchSort sorter;
  vector<int> trail;          // currently assigned literals
  vector<unsigned> lit2trail; // map from literal to trail index
  vector<char> seen;
  vector<signed char> marks;
  vector<Range> vars_range;    // Range of variables
  vector<Range> trail_range;   // Range of variables on trail (units)
  unsigned current_part;       // current partition
  unsigned maximal_part;       // maximal partition
  vector<int> imported_clause; // last imported clause
  bool imported_tautological;  // last imported clause is tautological
  int max_var;
  int64_t size_vars;
  signed char *vals;            // assignment [-max_var,max_var]
  bool inconsistent;            // empty clause found
  bool empty_original_clause;   // empty original clause found
  uint64_t num_clauses;         // number of clauses
  uint64_t num_watched;         // number of watched clauses in wtab
  uint64_t num_watched_garbage; // number of garbage watched clauses in wtab
  uint64_t size_clauses;        // size of clause hash table
  Clause **clauses;             // hash table of clauses
  unsigned next_to_propagate;   // next to propagate on trail
  int last_assumed_trail;       // trail index of last assumed literal
  int top_root_trail;           // top trail index of root level units
  static const unsigned num_nonces = 4;
  uint64_t nonces[num_nonces]; // random numbers for hashing
  bool detach_eagerly;
  bool reorder_proof;
  unsigned vlit (int);
  Watches &watches (int);
  bool watching () const;
  void watch_literal (int, int, Clause *);
  void watch_clause (Clause *);
  void unwatch_clause (Clause *);
  void enlarge_marks (unsigned); // Dynamicly managed
  signed char marked (int lit) const;
  void mark (int);
  void unmark (int);
  void import_clause (const vector<int> &);
  uint64_t compute_hash (uint64_t);
  static uint64_t reduce_hash (uint64_t, uint64_t);
  void enlarge_clauses ();
  Clause *insert (const vector<int> &, uint64_t);
  Clause **find (const uint64_t);
  Clause *new_clause (const vector<int> &, uint64_t, uint64_t);
  void delete_clause (Clause *);
  void deallocate_clause (Clause *);
  signed char val (int) const;
  void assign (int, Clause *);
  void assume (int);
  bool propagate (bool core = false, unsigned part = 0);
  bool ordered_propagate (bool core = false);
  void backtrack (unsigned);
  void sort_watch (Clause *);
  void init_watches ();
  void clear_watches ();
  void reset_watches ();
  void flush_watches (int, Watches &);
  void flush_watches ();
  void detach_clause (Clause *c);
  void attach_clause (Clause *c);
  bool satisfied (Clause *);
  void init_trail_and_reasons ();
  void init_vals ();
  int init_data_structures ();
  void RUP (Clause *, unsigned &);
  bool is_on_trail (Clause *);
  void undo_trail_literal (int);
  void undo_trail_core (Clause *, unsigned &);
  void shrink_trail (unsigned);
  void analyze_core_literal (int);
  void analyze_core ();
  void mark_core_trail_antecedents ();
  void append (uint64_t id, const vector<int> &, bool);
  void traverse_core (ItpClauseIterator &);
  void mark_top_conflict ();
  void restore_proof_garbage_marks ();
  bool trim ();
  void restore_trail (bool original = false, bool core = false);
  void label_root_level (ResolutionProofIterator &, int &);
  void label_final (ResolutionProofIterator &, Clause *);
  bool skip_lemma (Clause *, unsigned);
  bool clauses_are_identical (Clause *, const vector<int> &);
  bool colorize (ResolutionProofIterator &, Clause *, unsigned,
                 vector<int> &, Range &);
  Clause *recursively_colorize (ResolutionProofIterator &, Clause *);

  struct {
    int64_t added;        // number of added clauses
    int64_t original;     // number of added original clauses
    int64_t derived;      // number of added derived clauses
    int64_t deleted;      // number of deleted clauses
    int64_t assumptions;  // number of assumed literals
    int64_t propagations; // number of propagated literals
    int64_t insertions;   // number of clauses added to hash table
    int64_t collisions;   // number of hash collisions in 'find'
    int64_t searches;     // number of searched clauses in 'find'
    int64_t trims;        // number of trims
    int64_t core;         // number of original core clauses in last trim
    int64_t units;
  } stats;

public:
  Drup2Itp ();
  ~Drup2Itp ();
  void connect_internal (Internal *i) override;
  void add_original_clause (uint64_t, bool, const vector<int> &,
                            bool) override;
  void add_derived_clause (uint64_t, bool, const vector<int> &,
                           const vector<uint64_t> &) override;
  void delete_clause (uint64_t, bool, const vector<int> &) override;
  // void weaken_minus (uint64_t, const vector<int> &) override;
  // void strengthen (uint64_t) override;
  // void report_status (int, uint64_t) override;
  void solve_query () { assumption_clauses.clear (); };
  void add_assumption (int) override;
  void add_constraint (const vector<int> &) override;
  void reset_assumptions () override;
  void add_assumption_clause (uint64_t, const vector<int> &,
                              const vector<uint64_t> &) override;
  void conclude_unsat (ConclusionType, const vector<uint64_t> &) override;
  // void conclude_sat (const vector<int> &) override;
  void print_stats () override;
  bool trim (ItpClauseIterator *, bool undo = true);
  void set_current_partition (unsigned);
  unsigned get_current_partition () const;
  unsigned get_maximal_partition () const;
  bool replay (ResolutionProofIterator &, bool incremental = true);
  bool set_reorder_proof (bool);
  bool consistent () const;
  void dump (const char *);
  MiniTracer mini_tracer () const;
  void connect_to (Solver &);
};

} // namespace DRUP2ITP

#endif
