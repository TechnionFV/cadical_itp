// Created by Basel Khouri 2024

#include "drup2itp.hpp"
#include "../src/internal.hpp"
#include "../src/random.hpp"
#include "../src/util.hpp"

extern "C" {
#include <assert.h>
}

namespace DRUP2ITP {

#define FOREACH_CLAUSE(c) \
  for (uint64_t i = 0; i < size_clauses; i++) \
      for (Clause *c = clauses[i]; c; c = c->next)

inline unsigned Drup2Itp::vlit (int lit) {
  unsigned res = (lit < 0) + 2u * (unsigned) abs (lit);
  return res;
}

inline signed char Drup2Itp::val (int lit) const {
  assert (lit && vals);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

/*------------------------------------------------------------------------*/

Clause *Drup2Itp::new_clause (const vector<int> &literals, uint64_t id,
                              uint64_t hash) {
  const size_t size = literals.size ();
  assert (size <= UINT_MAX);
  const int off = size ? 1 : 0;
  const size_t bytes = sizeof (Clause) + (size - off) * sizeof (int);
  Clause *res = (Clause *) new char[bytes];
  res->next = 0;
  res->hash = hash;
  res->id = id;
  res->garbage = false;
  res->core = false;
  res->original = false;
  res->range = Range ();
  res->size = size;
  int *p = res->literals;
  for (int lit : literals)
    *p++ = lit;
  num_clauses++;
  if (literals.size () == 1)
    stats.units++;
  return res;
}

void Drup2Itp::delete_clause (Clause *c) {
  assert (c && num_clauses);
  Clause **p = find (c->id);
  assert (*p == c);
  *p = c->next;
  c->next = 0;
  deallocate_clause (c);
}

void Drup2Itp::deallocate_clause (Clause *c) {
  assert (num_clauses);
  num_clauses--;
  delete[] (char *) c;
}

void Drup2Itp::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2 * size_clauses : 1;
  Clause **new_clauses;
  new_clauses = new Clause *[new_size_clauses];
  CaDiCaL::clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (Clause *c = clauses[i], *next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete[] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

/*------------------------------------------------------------------------*/

Drup2Itp::Drup2Itp ()
    : internal (0), conflict (0), confl_assumes (0),
      sorter (&lit2trail, vals), current_part (0), maximal_part (0),
      imported_tautological (false), size_vars (0), vals (0),
      inconsistent (false), empty_original_clause (false), num_clauses (0),
      num_watched (0), num_watched_garbage (0), size_clauses (0),
      clauses (0), next_to_propagate (0), reorder_proof (false) {
  // Imported from Checker
  CaDiCaL::Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1))
      nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }
  memset (&stats, 0, sizeof (stats));
}

Drup2Itp::~Drup2Itp () {
  vals -= size_vars;
  delete[] vals;
  for (size_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i], *next; c; c = next)
      next = c->next, deallocate_clause (c);
  delete[] clauses;
}

/*------------------------------------------------------------------------*/

uint64_t Drup2Itp::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t) 1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

void Drup2Itp::enlarge_marks (unsigned idx) {
  assert (0 < idx), assert (idx <= INT_MAX);
  unsigned size = 2;
  while (idx >= size)
    size *= 2;
  assert (size >= marks.size ());
  marks.resize (2 * size);
  assert (vars_range.size () == trail_range.size ());
  while (trail_range.size () < 2 * size) {
    trail_range.push_back (Range ());
    vars_range.push_back (Range ());
  }
  assert (vars_range.size () == trail_range.size ());
}

signed char Drup2Itp::marked (int lit) const {
  assert (abs (lit) < marks.size ());
  signed char res = marks[abs (lit)];
  if (lit < 0)
    res = -res;
  return res;
}

void Drup2Itp::mark (int lit) {
  assert (!marked (lit));
  marks[abs (lit)] = (lit > 0) - (lit < 0);
  assert (marked (lit) > 0);
  assert (marked (-lit) < 0);
}

void Drup2Itp::unmark (int lit) {
  assert (abs (lit) < marks.size ());
  marks[abs (lit)] = 0;
  assert (!marked (lit));
}

void Drup2Itp::import_clause (const vector<int> &c) {
  assert (imported_clause.empty ());
  for (int lit : c) {
    assert (lit);
    assert (lit != INT_MIN);
    int idx = abs (lit);
    if (idx >= size_vars)
      enlarge_db (idx);
  }
  imported_falsified = true;
  imported_tautological = false;
  int tmp;
  for (int lit : c) {
    tmp = marked (lit);
    if (tmp < 0)
      imported_tautological = true;
    else if (!tmp) {
      imported_clause.push_back (lit);
      mark (lit);
    }
    imported_falsified &= val (lit) < 0;
  }
  for (const auto &lit : c)
    unmark (lit);
}

uint64_t Drup2Itp::compute_hash (const uint64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;
  uint64_t tmp = nonces[j] * (uint64_t) id;
  return tmp;
}

Clause **Drup2Itp::find (const uint64_t id) {
  stats.searches++;
  Clause **res, *c;
  const uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id)
      break;
    stats.collisions++;
  }
  return res;
}

Clause *Drup2Itp::insert (const vector<int> &literals, uint64_t id) {
  stats.insertions++;
  if (num_clauses == size_clauses)
    enlarge_clauses ();
  uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  Clause *c = new_clause (literals, id, hash);
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

/*------------------------------------------------------------------------*/

void Drup2Itp::enqueue (int lit, Clause *c) {
  const auto tmp = val (lit);
  if (tmp > 0)
    return;
  else if (tmp < 0) {
    conflict = c;
    inconsistent = true;
  } else
    assign (lit, c);
}

inline void Drup2Itp::assign (int lit, Clause *reason) {
  assert (!val (lit));
  vals[lit] = 1;
  vals[-lit] = -1;
  int idx = abs (lit);
  lit2trail[idx] = trail.size ();
  trail.push_back (lit);
  reasons[idx] = reason;
  if (reason) {
    int *lits = reason->literals;
    for (unsigned i = 0; i < reason->size && lits[0] != lit; i++) {
      if (lits[i] != lit)
        continue;
      lits[i] = lits[0];
      lits[0] = lit;
    }
    assert (lit == lits[0]);
  }
}

inline void Drup2Itp::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0)
    return;
  assert (!tmp);
  stats.assumptions++;
  last_assumed_trail = trail.size ();
  assign (lit, 0);
}

void Drup2Itp::backtrack (unsigned previously_propagated) {

  assert (previously_propagated <= trail.size ());

  while (trail.size () > previously_propagated) {
    int lit = trail.back ();
    undo_trail_literal (lit);
    trail.pop_back ();
  }

  trail.resize (previously_propagated);
  next_to_propagate = previously_propagated;
  assert (trail.size () == next_to_propagate);
  conflict = 0;
}

/*------------------------------------------------------------------------*/

// Imported from Checker
// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.

bool Drup2Itp::propagate (bool core, unsigned part) {
  bool res = true;
  while (res && next_to_propagate < trail.size ()) {
    int lit = trail[next_to_propagate++];
    stats.propagations++;
    assert (val (lit) > 0);
    assert (abs (lit) < size_vars);
    Watches &ws = watches (-lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; res && i != end; i++) {
      Watch &w = *j++ = *i;
      const int blit = w.blit;
      assert (blit != -lit);
      if (core && !w.clause->core)
        continue;
      if (part && part < w.clause->range.max ())
        continue;
      if (w.clause->garbage)
        continue;
      const signed char blit_val = val (blit);
      if (blit_val > 0)
        continue; // blocking literal satisfied
      const unsigned size = w.size;
      if (size == 2) {
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        } else
          assign (w.blit, w.clause); // but still sound
      } else {
        assert (size > 2);
        Clause *c = w.clause;
        if (!c->size) {
          j--;
          continue;
        } // skip garbage clauses
        assert (size == c->size);
        int *lits = c->literals;
        int other = lits[0] ^ lits[1] ^ (-lit);
        assert (other != -lit);
        signed char other_val = val (other);
        if (other_val > 0) {
          j[-1].blit = other;
          continue;
        }
        lits[0] = other, lits[1] = -lit;
        unsigned k;
        int replacement = 0;
        signed char replacement_val = -1;
        for (k = 2; k < size; k++)
          if ((replacement_val = val (replacement = lits[k])) >= 0)
            break;
        if (replacement_val >= 0) {
          watches (replacement).push_back (Watch (-lit, c));
          swap (lits[1], lits[k]);
          j--;
        } else if (!other_val)
          assign (other, c);
        else {
          res = false;
          conflict = c;
        }
      }
    }
    while (i != end)
      *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return res;
}

bool Drup2Itp::ordered_propagate (bool core) {
  const auto before = next_to_propagate;
  bool res = true;
  for (unsigned i = 1; res && i <= maximal_part; i++) {
    next_to_propagate = before;
    res = propagate (core, i);
  }
  return res;
}

void Drup2Itp::detach_clause (Clause *c) {
  assert (c && !c->garbage);
  c->garbage = true;
  if (c->size > 1)
    unwatch_clause (c);
}

void Drup2Itp::attach_clause (Clause *c) {
  assert (c && c->garbage);
  c->garbage = false;
  if (c->size > 1)
    watch_clause (c);
}

bool Drup2Itp::satisfied (Clause *c) const {
  assert (c);
  for (int lit : *c)
    if (val (lit) > 0)
      return true;
  return false;
}

void Drup2Itp::enlarge_db (int64_t idx) {

  assert (0 < idx), assert (idx <= INT_MAX);

  int64_t new_size_vars = size_vars ? 2 * size_vars : 2;
  while (idx >= new_size_vars)
    new_size_vars *= 2;

  signed char *new_vals;
  new_vals = new signed char[2 * new_size_vars];
  CaDiCaL::clear_n (new_vals, 2 * new_size_vars);
  new_vals += new_size_vars;
  if (size_vars) // To make sanitizer happy (without '-O').
    memcpy ((void *) (new_vals - size_vars), (void *) (vals - size_vars),
            2 * size_vars);
  vals -= size_vars;
  delete[] vals;
  vals = new_vals;

  wtab.resize (2 * new_size_vars);
  marks.resize (2 * new_size_vars);
  seen.resize (2 * new_size_vars);
  lit2trail.resize (2 * new_size_vars);
  vars_range.resize (2 * new_size_vars);
  trail_range.resize (2 * new_size_vars);
  reasons.resize (2 * new_size_vars);
  for (int i = size_vars; i < new_size_vars; i++) {
    assert (!reasons[i]);
    assert (!marks[i]);
    assert (!seen[i]);
    assert (!lit2trail[i]);
    assert (trail_range[i].undef ());
    assert (vars_range[i].undef ());
  }
  sorter.reset (&lit2trail, vals);

  assert (idx < new_size_vars);
  size_vars = new_size_vars;
}

// TODO: Some of the derived clauses from the tracer API
// are trivial resolutions than can be skipped.
void Drup2Itp::RUP (Clause *c, unsigned &trail_sz) {
  assert (c && !c->original);
  shrink_trail (trail_sz);
  top_root_trail = trail.size () - 1;
  for (int lit : *c)
    assume (-lit);
  if (propagate ()) {
    assert (next_to_propagate >= c->size);
    next_to_propagate = 0;
    if (propagate ()) {
      CaDiCaL::fatal_message_start ();
      fputs ("RUP failed for proof core lemma: ", stderr);
      for (const auto &lit : *c)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      CaDiCaL::fatal_message_end ();
    }
  }
  analyze_core ();
  backtrack (trail_sz);
}

bool Drup2Itp::is_on_trail (Clause *c) {
  assert (c);
  int lit = c->literals[0];
  return val (lit) > 0 && (reasons[abs (lit)]->id == c->id);
}

void Drup2Itp::undo_trail_literal (int lit) {
  unsigned idx = abs (lit);
  assert (idx < reasons.size ());
  reasons[idx] = 0;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  vals[lit] = vals[-lit] = 0;
  lit2trail[idx] = 0; // or -1 ? it shouldn't be accessed anyway...
  // trail_range[idx].reset ();
}

void Drup2Itp::undo_trail_core (Clause *c, unsigned &trail_sz) {
#ifndef NDEBUG
  assert (trail_sz > 0);
  assert (trail_sz <= trail.size ());
  assert (c && is_on_trail (c));
#endif

  int clit = c->literals[0];

#ifndef NDEBUG
  assert (reasons[abs (clit)] == c);
  assert (val (clit) > 0);
#endif

  while (trail[--trail_sz] != clit) {
    assert (trail_sz > 0);
    int l = trail[trail_sz];

    Clause *r = reasons[abs (l)];
    assert (r && r->literals[0] == l);

    undo_trail_literal (l);

    if (r->core)
      for (unsigned j = 1; j < r->size; j++) {
        Clause *cr = reasons[abs (r->literals[j])];
        assert (cr);
        cr->core = true;
      }
  }

  assert (clit == trail[trail_sz]);
  undo_trail_literal (clit);
}

void Drup2Itp::shrink_trail (unsigned trail_sz) {
  assert (trail_sz <= trail.size ());
  trail.resize (trail_sz);
  next_to_propagate = trail_sz;
}

void Drup2Itp::analyze_core_literal (int lit) {
  int idx = abs (lit), trail_idx = lit2trail[idx];
  assert (idx < size_vars);
  if (trail_idx > last_assumed_trail) {
    seen[idx] = true;
  } else if (trail_idx <= top_root_trail) {
    Clause *reason = reasons[idx];
    assert (reason);
    reason->core = true;
  }
}


void Drup2Itp::analyze_core () {
  assert (conflict);
  conflict->core = true;

  for (int lit : *conflict)
    analyze_core_literal (lit);

  for (int i = trail.size () - 1; i > last_assumed_trail; i--) {
    int lit = trail[i], idx = abs (lit);
    assert (idx < size_vars);
    if (!seen[idx])
      continue;

    seen[idx] = false;

    Clause *c = reasons[idx];
    assert (c);
    c->core = true;

#ifndef NDEBUG
    assert (reasons[abs (c->literals[0])] == c);
    assert (val (c->literals[0]) > 0);
    assert (c->literals[0] == lit);
#endif

    for (unsigned j = 1; j < c->size; j++)
      analyze_core_literal (c->literals[j]);
  }
}

void Drup2Itp::mark_core_trail_antecedents () {
  for (int i = trail.size () - 1; i >= 0; i--) {
    int lit = trail[i];
    assert (abs (lit) < size_vars);
    Clause *reason = reasons[abs (lit)];
    assert (reason);
    if (reason->core) {
      assert (reason->literals[0] == lit);
      for (int l : *reason) {
        assert (abs (l) < size_vars);
        Clause *cr = reasons[abs (l)];
        assert (cr);
        cr->core = true;
      }
      next_to_propagate = i;
    }
  }
}

void Drup2Itp::mark_top_conflict () {
  confl_assumes = 0;
  switch (conclusion) {
  case ConclusionType::CONFLICT: {
    assert (conflict);
    conflict->core = true;
    for (int lit : *conflict) {
      assert (abs (lit) < size_vars);
      if (Clause *c = reasons[abs (lit)])
        c->core = true;
    }
  } break;
  case ConclusionType::ASSUMPTIONS: {
    assert (assumption_clauses.size () == 1);
    confl_assumes = assumption_clauses[0];
    assert (proof.back () == confl_assumes);
    confl_assumes->core = true;
    if (confl_assumes->size == 1)
      for (int lit : *confl_assumes) {
        assert (abs (lit) < size_vars);
        if (Clause *c = reasons[abs (lit)])
          c->core = true;
      }
  } break;
  case ConclusionType::CONSTRAINT: {
    assert (0 && "not implemented yet");
  } break;
  default:
    assert (false && "should not reach here");
  }
}

// Proof, trail, and clauses DB need to be mirrored in the internal
// solver as well. Currently, we don't want to manupulate the internal
// solver's state. Therefore, we undo the effects of trim and replay.
//
void Drup2Itp::restore_state () {
  // Restore proof state
  for (Clause *c : proof)
    c->garbage = !c->original;
  for (Clause *c : proof)
    c->garbage = !c->garbage;

  // Restore trail state
  //
  for (int l : trail)
    undo_trail_literal (l);
  trail.clear ();
  int unit;
  unsigned idx;
  for (const auto &p : trail_backup) {
    unit = p.first;
    if (val (unit))
      continue;
    idx = abs (unit);
    if (p.second->size == 1 && !p.second->original)
      p.second->range = trail_range[idx];
    assign (unit, p.second);
  }
  next_to_propagate = 0;

  // Reset conflict
  conflict = 0;
}

bool Drup2Itp::restored (Clause *c, unsigned index) const {
  assert (c);
  const auto &it = restored_clauses.find(c->id);
  if (it == restored_clauses.end())
    return false;
  return it->second <= index;
}

void Drup2Itp::restore_clause (Clause *c, unsigned index) {
  assert (c && index);
  if (!restored (c, index))
    restored_clauses[c->id] = index;
}

void Drup2Itp::trim () {

  stats.trims++;

  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = trail.size ();

  int i = confl_assumes && confl_assumes->size == 1 ? proof.size () - 1 : proof.size ();
  while (--i >= 0) {
    Clause *c = proof[i];

    if (c->garbage) {
      attach_clause (c);
      continue;
    }

    if (is_on_trail (c))
      undo_trail_core (c, trail_sz);

    detach_clause (c);

    if (!c->core || restored (c, i))
      continue;

    RUP (c, trail_sz);

    if (internal->terminated_asynchronously ())
      return;
  }

  shrink_trail (trail_sz);
  mark_core_trail_antecedents ();
}

bool Drup2Itp::trim (ItpClauseIterator *it, bool undo) {

  if (empty_original_clause)
    return true;

  // Store the trail
  backup_trail ();

  // Connect watches
  if (watching ())
    reset_watches ();
  init_watches (), connect_watches ();

  assert (!next_to_propagate);

  // Propagate the trail
  if (!conflict)
    propagate ();

  mark_top_conflict ();

  // Main trimming procedure
  trim ();

  // Collect statistics and report the UNSAT core
  stats.core_clauses = stats.core_lemmas = 0;
  const bool mark = !undo;
  FOREACH_CLAUSE(c) {
    if (!c->core)
      continue;
    if (c->original) {
      assert (c->range.singleton ());
      if (it)
        it->clause (c);
      stats.core_clauses++;
    } else {
      stats.core_lemmas++;
    }
    c->core = mark;
  }
  if (it) {
    for (int lit : assumptions)
      if (external->failed (lit))
        it->assume (lit);
    if (conclusion == ConclusionType::CONSTRAINT)
      assert (0 && "not implemented yet");
  }

  // For applications where only trimming is required
  if (undo) restore_state ();

  return true;
}

void Drup2Itp::label_root_level (ResolutionProofIterator &it,
                                 int &trail_label_idx) {

  int trail_sz = trail.size ();

  while (trail_label_idx < trail_sz) {

    const int lit = trail[trail_label_idx++];
    const unsigned idx = abs (lit);

    Clause *c = reasons[idx];

    if (!c)
      continue;

    assert (c->literals[0] == lit);
    assert (abs (lit) < size_vars);

    Range range = c->range;
    assert (!range.undef ());

    switch (c->size) {
    case 1:
      trail_range[idx] = range;
      break;
    case 2: {
      int blit = -c->literals[1];
      assert (abs (blit) < size_vars);
      range.join (trail_range[abs (blit)]);
      trail_range[idx] = range;
      it.resolution (lit, blit, c);
    } break;
    default:
      it.chain.clear ();
      it.chain.append (c);
      for (unsigned j = 1; j < c->size; j++) {
        int other = -c->literals[j];
        assert (abs (other) < size_vars);
        range.join (trail_range[abs (other)]);
        it.chain.append (other, 0);
      }
      trail_range[idx] = range;
      it.chain_resolution (lit);
    }
  }
}

void Drup2Itp::label_final (ResolutionProofIterator &it, Clause *source) {
  assert (source);
  it.chain.clear ();
  it.chain.append (source);
  for (int lit : *source)
    it.chain.append (-lit, 0);
  it.chain_resolution (/*, 0*/);
}

bool Drup2Itp::skip_lemma (Clause *c, unsigned index) {
  assert (c);
  if (!c->garbage) {
    if (c->core)
      return true;
    if (!restored (c, index))
      if (!is_on_trail (c) || satisfied (c))
        detach_clause (c);
    return true;
  } else {
    if (restored (c, index))
      return true;
    if (!c->core)
      return true;
    assert (!is_on_trail (c));
    if (satisfied (c))
      return true;
  }

  int *literals = c->literals;
  if (val (literals[0]))
    for (unsigned j = 1; j < c->size; j++)
      if (!val (literals[j])) {
        int lit = literals[0];
        literals[0] = literals[j];
        literals[j] = lit;
        break;
      }

  return false;
}

bool Drup2Itp::clauses_are_identical (Clause *c, const vector<int> &lits) {
  assert (c);
  if (c->size != lits.size ())
    return false;
  bool identical = true;
  for (const auto &lit : *c)
    mark (lit);
  for (int lit : lits)
    if (!marked (lit))
      identical = false;
  for (const auto &lit : *c)
    unmark (lit);
  return identical;
}

Clause *Drup2Itp::recursively_colorize (ResolutionProofIterator &it,
                                        Clause *anchor) {
  assert (anchor);

  vector<int> learnt;
  Range range;
  unsigned part = anchor->range.max ();

  if (!colorize (it, anchor, part, learnt, range) ||
      clauses_are_identical (anchor, learnt))
    return anchor;

  assert (range.max () <= part);

  Clause *resolvent = insert (learnt, ++(internal->clause_id));
  if (resolvent->size > 1)
    watch_clause (resolvent);

  resolvent->range = range;
  resolvent->core = true;

  int lit = resolvent->literals[0];
  if (val (lit) > 0)
    reasons[abs (lit)] = resolvent;

  it.chain_resolution (resolvent);

  return resolvent;
}

bool Drup2Itp::colorize (ResolutionProofIterator &it, Clause *reason,
                         unsigned part, vector<int> &learnt, Range &range) {

  assert (reason && learnt.empty () && range.undef ());

  vector<char> opened (size_vars, 0);
  int i = trail.size (), open = 0, uip = 0;
  ChainDerivation chain;

  int lit = reason->literals[0];
  if (val (lit) > 0)
    learnt.push_back (uip = lit);

  for (;;) {
    assert (reason);
    if (reorder_proof && reason->range.max () < part) {
      // Attempt to turn into a shared derived clause.
      reason = recursively_colorize (it, reason);
    }
    chain.clauses.push_back (reason);
    if (uip && chain.clauses.size () > 1)
      chain.pivots.push_back (uip);
    range.join (reason->range);
    assert (reason->range.max () <= part);
    for (const auto &other : *reason)
      if (other != uip) {
        unsigned idx = abs (other);
        assert (idx && idx < size_vars);
        if (opened[idx] || seen[idx])
          continue;
        assert (val (other) < 0);
        if (reasons[idx] && reasons[idx]->range.max () <= part) {
          open++;
          opened[idx] = 1;
          continue;
        }
        seen[idx] = 1;
        learnt.push_back (other);
      }

    if (!open--)
      break;

    uip = 0;
    while (!uip) {
      assert (i > 0);
      const int lit = trail[--i];
      if (!opened[abs (lit)])
        continue;
      opened[abs (lit)] = 0;
      uip = lit;
    }
    assert (abs (uip) < size_vars);
    reason = reasons[abs (uip)];
  }

  for (int lit : learnt)
    seen[abs (lit)] = 0;

  assert (chain.clauses.size () == chain.pivots.size () + 1);

  it.chain = chain;
  return it.chain.pivots.size ();
}

void Drup2Itp::set_current_partition (unsigned part) {
  current_part = part;
  maximal_part = max (maximal_part, current_part);
}

unsigned Drup2Itp::get_current_partition () const { return current_part; }

unsigned Drup2Itp::get_maximal_partition () const { return maximal_part; }

// Post-condition: formula has been already trimmed.
bool Drup2Itp::replay (ResolutionProofIterator &it, bool incremental) {

  if (empty_original_clause)
    return true;

  const auto max_id = internal->clause_id;

  FOREACH_CLAUSE (c)
    if (c->size == 1 && c->original && c->core) {
      int lit = *c->begin ();
      if (val (lit))
        continue;
      assign (lit, c);
    }

  propagate (true /*core only*/);

  int trail_label_idx = 0;
  label_root_level (it, trail_label_idx);

  if (conflict) {
    // Initial data base is inconsistent.
    label_final (it, conflict);
    return true;
  }

  for (int index = 0; index < proof.size (); index++) {
    Clause *c = proof[index];
    if (skip_lemma (c, index))
      continue;

    assert (c->garbage);
    assert (!val (c->literals[0]));

    auto previously_propagated = next_to_propagate;
    for (int lit : *c)
      assume (-lit);

    if (ordered_propagate (true)) {
      next_to_propagate = previously_propagated;
      if (ordered_propagate ()) {
        CaDiCaL::fatal_message_start ();
        fputs ("replay failed for proof core lemma: ", stderr);
        for (const auto &lit : *c)
          fprintf (stderr, "%d ", lit);
        fputc ('0', stderr);
        CaDiCaL::fatal_message_end ();
      }
    }
    assert (conflict);

    if (internal->terminated_asynchronously ())
      return false;

    Clause *p = conflict;
    bool learned = true;
    vector<int> learnt;
    Range range;
    unsigned part = reorder_proof ? p->range.max () : maximal_part;

    while (part <= maximal_part) {
      learnt.clear (), range.reset ();
      learned = colorize (it, p, part, learnt, range);

      if (!learned) {
        part++;
        continue;
      }

#if DNDEBUG
      for (int lit : learnt)
        assert (val (lit) < 0);
#endif

      if (clauses_are_identical (c, learnt)) {
        c->range = range;
        c->garbage = false;
        if (c->size > 1)
          watch_clause (c); // will be sorted here
        it.chain_resolution (c);
        break;
      }

      part = maximal_part + 1;
      for (int lit : learnt) {
        unsigned idx = abs (lit);
        assert (idx < size_vars);
        int trail_idx = lit2trail[idx];
        if (trail_idx > last_assumed_trail) {
          Clause *r = reasons[idx];
          assert (r);
          part = min (r->range.max (), part);
        }
      }

      p = insert (learnt, ++(internal->clause_id));
      if (p->size > 1)
        watch_clause (p);
      p->range = range;
      p->core = true;
      c->core = false;

      if (c == confl_assumes)
        confl_assumes = p;

      it.chain_resolution (p);

      if (part > maximal_part) {
        c->core = false;
        c = p;
      }
    }

    assert (c);
    backtrack (previously_propagated);

    if (!learned) {
      assert (c->garbage && c->core);
      c->core = false;
      if (c == confl_assumes)
        confl_assumes = p;
      continue;
    }

    c->garbage = false;

    if (c->size == 1 || val (c->literals[1]) < 0) {
      assert (!val (c->literals[0]));
#ifndef NDEBUG
      for (unsigned j = 1; j < c->size; ++j)
        assert (val (c->literals[j]) < 0);
#endif
      assign (c->literals[0], c);
      bool conflicting = !ordered_propagate (true);
      label_root_level (it, trail_label_idx);
      if (conflicting) {
        label_final (it, conflict);
        break;
      }
    }
  }

  if (!conflict) {
    assert (confl_assumes && confl_assumes->core);
    if (confl_assumes->size == 1)
      label_final (it, reasons[abs (*confl_assumes->begin ())]);
    else
      label_final (it, confl_assumes);
  }

  if (incremental) {
    restore_state ();

    vector<Clause *> to_delete;
    FOREACH_CLAUSE(c) {
      c->core = false;
      assert (!c->original || c->range.singleton ());
      if (!c->original)
        c->range.reset ();
      // TODO: Is this even needed?
      if (max_id < c->id)
        to_delete.push_back (c);
    }

    for (int i = 0; i < to_delete.size (); i++)
      delete_clause (to_delete[i]);
  }

  return true;
}

bool Drup2Itp::set_reorder_proof (bool val) {
  bool pval = reorder_proof;
  reorder_proof = val;
  return pval != val;
}

void Drup2Itp::backup_trail () {
  trail_backup.clear ();
  for (int l : trail)
    trail_backup.push_back ({l, reasons[abs (l)]});
}

void Drup2Itp::append (uint64_t id, const vector<int> &literals,
                       bool deletion) {
  stats.added++;
  Clause *c = size_clauses ? *find (id) : 0;
  if (deletion) {
    stats.deleted++;
    if (c) {
      assert (c->size == literals.size ());
      assert (!c->garbage);
      c->garbage = true;
      proof.push_back (c);
    } else {
      CaDiCaL::fatal_message_start ();
      fputs ("deleted clause not in proof:\n", stderr);
      for (const auto &lit : literals)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      CaDiCaL::fatal_message_end ();
    }
  } else {
    assert (!c);
    stats.derived++;
    c = insert (literals, id);
    if (c->size == 1)
      enqueue (c->literals[0], c);
    proof.push_back (c);
  }
}

// stats.core_lemmas may be inaccurate if traversal aborts early
void Drup2Itp::traverse_core (ItpClauseIterator &it, bool undo_core_marks) {
  stats.core_clauses = stats.core_lemmas = 0;
  const bool mark = !undo_core_marks;
  FOREACH_CLAUSE (c) {
    if (!c->core)
      continue;
    if (!c->original) {
      stats.core_lemmas++;
      c->core = mark;
      continue;
    }
    stats.core_clauses++;
    c->core = mark;
    assert (c->range.singleton ());
    if (!it.clause (c))
      return;
  }
  for (int lit : assumptions)
    if (external->failed (lit)) {
      // Range range = trail_range[abs (lit)];
      // if (!it.clause (clause, range.min ()))
      if (!it.assume (lit))
        return;
    }
  if (conclusion == ConclusionType::CONSTRAINT) {
    assert (0 && "not implemented yet");
    // for (int lit : constraint)
    //   clause.push_back (lit);
    // if (!it.clause (clause))
    //   return;
    // clause.clear ();
  }
}

Watches &Drup2Itp::watches (int lit) {
  return (Watches &) (wtab[vlit (lit)]);
}

void Drup2Itp::sort_watch (Clause *c) {
  assert (c);
  if (c->size <= 2)
    return;
  int *lits = c->literals;
  const int size = c->size;
  for (int i = 0; i < 2; i++)
    for (int j = i + 1; j < size; j++)
      if (!sorter (lits[i], lits[j]))
        swap (lits[i], lits[j]);
}

void Drup2Itp::init_watches () {
  assert (wtab.empty () && vals);
  wtab.resize (2 * (size_vars));
}

void Drup2Itp::connect_watches () {
  // First connect binary clauses.
  //
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (c->garbage || c->size != 2)
        continue;
      watch_clause (c);
    }

  // Then connect non-binary clauses.
  //
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (c->garbage || c->size <= 2)
        continue;
      watch_clause (c);
    }
}

void Drup2Itp::clear_watches () {
  for (int idx = 1; idx < size_vars; idx++) {
    watches (idx).clear ();
    watches (-idx).clear ();
  }
}

void Drup2Itp::reset_watches () {
  assert (!wtab.empty ());
  CaDiCaL::erase_vector (wtab);
}

void Drup2Itp::flush_watches (int lit, Watches &saved) {
  assert (saved.empty ());
  Watches &ws = watches (lit);
  const const_watch_iterator end = ws.end ();
  watch_iterator j = ws.begin ();
  const_watch_iterator i;
  for (i = j; i != end; i++) {
    Watch w = *i;
    Clause *c = w.clause;
    if (c->garbage) {
      num_watched--;
      continue;
    }
    w.size = c->size;
    const int new_blit_pos = (c->literals[0] == lit);
    assert (c->literals[!new_blit_pos] == lit); /*FW1*/
    w.blit = c->literals[new_blit_pos];
    if (w.binary ())
      *j++ = w;
    else
      saved.push_back (w);
  }
  ws.resize (j - ws.begin ());
  for (const auto &w : saved)
    ws.push_back (w);
  saved.clear ();
  CaDiCaL::shrink_vector (ws);
}

void Drup2Itp::flush_watches () {
  int max_var = size_vars;
  CaDiCaL::Range vars (max_var);
  if (watching ()) {
    Watches tmp;
    for (auto idx : vars)
      flush_watches (idx, tmp), flush_watches (-idx, tmp);
  }
  num_watched_garbage = 0;
}

bool Drup2Itp::watching () const { return !wtab.empty (); }

inline void Drup2Itp::watch_literal (int lit, int blit, Clause *c) {
  assert (lit != blit);
  Watches &ws = watches (lit);
  ws.push_back (Watch (blit, c));
}

void Drup2Itp::watch_clause (Clause *c) {
  assert (c && c->size > 1);
  sort_watch (c);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
}

void Drup2Itp::unwatch_clause (Clause *c) {
  assert (c && c->size > 1);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  remove_watch (watches (l0), c);
  remove_watch (watches (l1), c);
}

/*------------------------------------------------------------------------*/

void Drup2Itp::connect_internal (Internal *i) {
  assert (i);
  internal = i;
  external = i->external;
}

void Drup2Itp::add_original_clause (uint64_t id, bool, const vector<int> &c,
                                    bool restore) {
  stats.added++;
  if (c.empty ()) {
    stats.original++;
    assert (!restore);
    Clause *oc = insert (c, id);
    oc->original = true;
    oc->range.join (current_part);
    inconsistent = empty_original_clause = true;
  } else {
    if (restore) {
      stats.restored++;
      Clause *pc = *find (id);
      assert (pc && pc->garbage);
      pc->garbage = false;
      restore_clause (pc, proof.size ());
      if (pc->size == 1)
        enqueue (pc->literals[0], pc);
      proof.push_back (pc);
    } else {
      import_clause (c);
      if (!imported_tautological) {
        assert (imported_clause.size());
        stats.original++;
        assert (!size_clauses || !*find (id));
        Clause *oc = insert (imported_clause, id);
        oc->original = true;
        if (oc->size == 1)
          enqueue (oc->literals[0], oc);
        assert (current_part);
        oc->range.join (current_part);
        assert (oc->range.singleton ());
        for (int lit : c) {
          unsigned idx = abs (lit);
          assert (idx < vars_range.size ());
          vars_range[idx].join (current_part);
        }
        if (imported_falsified) {
          conflict = oc;
          inconsistent = true;
        }
      }
      imported_clause.clear ();
    }
  }
}

void Drup2Itp::add_derived_clause (uint64_t id, bool, const vector<int> &c,
                                   const vector<uint64_t> &) {
  if (c.empty ()) {
    insert (c, id);
    inconsistent = true;
  } else {
    import_clause (c);
    if (!imported_tautological)
      append (id, imported_clause, false /*addition*/);
    assert (!imported_falsified);
    imported_clause.clear ();
  }
}

void Drup2Itp::add_assumption_clause (uint64_t id, const vector<int> &c,
                                      const vector<uint64_t> &) {
  stats.added++;
  import_clause (c);
  if (!imported_tautological) {
    append (id, imported_clause, false /*addition*/);
    assumption_clauses.push_back (proof.back ());
  }
  imported_clause.clear ();
}

void Drup2Itp::delete_clause (uint64_t id, bool, const vector<int> &c) {
  import_clause (c);
  if (!imported_tautological) {
    append (id, imported_clause, true /*deletion*/);
    int *lits = proof.back ()->literals, size = proof.back ()->size;
    for (int i = 0; i < size; i++)
      if (external->fixed (lits[i]) < 0)
        swap (lits[i], lits[--size]);
  }
  imported_clause.clear ();
}

void Drup2Itp::add_assumption (int lit) { assumptions.push_back (lit); }

void Drup2Itp::add_constraint (const vector<int> &c) {
  constraint.clear ();
  for (int lit : c)
    constraint.push_back (lit);
}

void Drup2Itp::reset_assumptions () {
  assumptions.clear ();
  constraint.clear ();
  assumption_clauses.clear ();
}

void Drup2Itp::conclude_unsat (ConclusionType c, const vector<uint64_t> &) {
  conclusion = c;
}

void Drup2Itp::print_stats () {
  if (!stats.added && !stats.deleted)
    return;

  SECTION ("drup2itp statistics");

  MSG ("trims:           %15" PRId64 "", stats.trims);
  MSG ("assumptions:     %15" PRId64 "   %10.2f    per trim",
       stats.assumptions,
       CaDiCaL::relative (stats.assumptions, stats.trims));
  MSG ("propagations:    %15" PRId64 "   %10.2f    per trim",
       stats.propagations,
       CaDiCaL::relative (stats.propagations, stats.trims));
  MSG ("original:        %15" PRId64 "   %10.2f %%  of all clauses",
       stats.original, CaDiCaL::percent (stats.original, stats.added));
  MSG ("derived:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.derived, CaDiCaL::percent (stats.derived, stats.added));
  MSG ("deleted:         %15" PRId64 "   %10.2f %%  of all clauses",
       stats.deleted, CaDiCaL::percent (stats.deleted, stats.added));
  MSG ("insertions:      %15" PRId64 "   %10.2f %%  of all clauses",
       stats.insertions, CaDiCaL::percent (stats.insertions, stats.added));
  MSG ("collisions:      %15" PRId64 "   %10.2f    per search",
       stats.collisions,
       CaDiCaL::relative (stats.collisions, stats.searches));
  MSG ("searches:        %15" PRId64 "", stats.searches);
  MSG ("units:           %15" PRId64 "", stats.units);
  MSG ("original core:   %15" PRId64
       "   %10.2f %%  of all original clauses",
       stats.core_clauses, CaDiCaL::percent (stats.core_clauses, stats.original));
}

bool Drup2Itp::consistent () const { return !inconsistent; }

void Drup2Itp::dump (const char *type) {
  if (strcmp (type, "proof") == 0) {
    fprintf (stderr, "DUMP PROOF TAIL\n");
    for (int i = proof.size () - 1; i >= 0; i--) {
      Clause *c = proof[i];
      fprintf (stderr, "[%lu] [%s] [ ", c->id, c->garbage ? "d" : "a");
      for (int lit : *c)
        fprintf (stderr, "%d ", lit);
      fprintf (stderr, "] {%d-%d} %s\n", c->range.min (), c->range.max (),
               c->core ? "*" : "");
    }
    fprintf (stderr, "DUMP PROOF HEAD\n");
  } else if (strcmp (type, "core") == 0) {
    fprintf (stderr, "DUMP CORE START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        if (!c->core || !c->original)
          continue;
        fprintf (stderr, "[%s] id:[%lu] clause:[ ",
                 c->original ? "orig" : "deri", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "] range:[%d-%d]\n", c->range.min (),
                 c->range.max ());
      }
    fprintf (stderr, "DUMP CORE END\n");
  } else if (strcmp (type, "clauses") == 0) {
    fprintf (stderr, "DUMP CLAUSES START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        fprintf (stderr, "[%s] [%s] [%lu] [ ",
                 c->original ? "orig" : "deri",
                 c->garbage ? "garb" : "activ", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    fprintf (stderr, "DUMP CLAUSES END\n");
  } else if (strcmp (type, "active") == 0) {
    fprintf (stderr, "DUMP ACTIVE CLAUSES START\n");
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        if (c->garbage)
          continue;
        fprintf (stderr, "[%s] [%lu] [ ", c->original ? "orig" : "deri",
                 c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    fprintf (stderr, "DUMP ACTIVE CLAUSES END\n");
  } else if (strcmp (type, "trail") == 0) {
    fprintf (stderr, "DUMP TRAIL TAIL\n");
    for (int i = trail.size () - 1; i >= 0; i--) {
      int lit = trail[i];
      fprintf (stderr, "%d <- ", lit);
      Clause *c = reasons[abs (lit)];
      if (!c)
        fprintf (stderr, "[0] [0]\n");
      else {
        fprintf (stderr, "[%lu] [ ", c->id);
        for (int lit : *c)
          fprintf (stderr, "%d ", lit);
        fprintf (stderr, "]\n");
      }
    }
    fprintf (stderr, "DUMP TRAIL HEAD\n");
  } else
    assert (0 && "Unknown dump option");
}

MiniTracer Drup2Itp::mini_tracer () const {
  return MiniTracer (vars_range, reasons);
}

void Drup2Itp::connect_to (Solver &s) {
  s.connect_proof_tracer (this, false /* without antecedents */);
  return;
}

// TODO: Use this in Minimzer
void Drup2Itp::resize (int64_t idx) {
  if (idx >= size_vars)
    enlarge_db (idx);
}

} // namespace DRUP2ITP
