// Created by Basel Khouri 2024

#include "drup2itp.hpp"
#include "../src/internal.hpp"
#include "../src/random.hpp"
#include "../src/util.hpp"

extern "C" {
#include <assert.h>
}

namespace DRUP2ITP {

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
    : internal (0), top_conflict (0), conflict (0),
      sorter (&lit2trail, vals), current_part (0), maximal_part (0),
      imported_tautological (false), max_var (0), size_vars (0), vals (0),
      inconsistent (false), empty_original_clause (false), num_clauses (0),
      num_watched (0), num_watched_garbage (0), size_clauses (0),
      clauses (0), next_to_propagate (0), detach_eagerly (true),
      reorder_proof (false) {
  // Initialize random number table for hash function.
  //
  CaDiCaL::Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1))
      nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  memset (&stats, 0, sizeof (stats)); // Initialize statistics.
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
  int idx, marks_sz = marks.size ();
  for (int lit : c) {
    idx = abs (lit);
    if (idx >= marks_sz) {
      enlarge_marks (idx);
      marks_sz = marks.size ();
    }
  }
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
  // if (detach_eagerly) {
  if (c->size > 1)
    unwatch_clause (c);
  // } else if (num_watched_garbage * 2 >= num_watched)
  //   flush_watches ();
  // else
  //   num_watched_garbage += 2;
}

void Drup2Itp::attach_clause (Clause *c) {
  assert (c && c->garbage);
  c->garbage = false;
  if (c->size > 1)
    watch_clause (c);
}

bool Drup2Itp::satisfied (Clause *c) {
  assert (c);
  for (int lit : *c)
    if (val (lit) > 0)
      return true;
  return false;
}

void Drup2Itp::init_vals () {
  assert (0 < max_var && max_var <= INT_MAX);
  size_vars = 2;
  while (max_var >= size_vars)
    size_vars *= 2;
  vals = new signed char[2 * size_vars];
  CaDiCaL::clear_n (vals, 2 * size_vars);
  vals += size_vars;
  assert (max_var < size_vars);
}

void Drup2Itp::init_trail_and_reasons () {
  assert (vals); // should be already initialized
  reasons.clear (), reasons.resize (size_vars, 0);
  const auto &itrail = internal->trail;
  const size_t size = itrail.size ();
  const auto &iunit_clauses = internal->unit_clauses;
  trail.resize (size);
  lit2trail.clear (), lit2trail.resize (size_vars, 0);
  int lit, idx;
  for (size_t i = 0; i < size; i++) {
    lit = trail[i] = itrail[i], idx = abs (lit);
    assert (!vals[lit] && !vals[-lit]);
    vals[lit] = 1, vals[-lit] = -1;
    lit2trail[idx] = i;
    CaDiCaL::Clause *reason = internal->var (idx).reason;
    if (reason) {
      reasons[idx] = *find (reason->id);
      assert (reasons[idx]);
    } else if (int id = iunit_clauses[internal->vlit (lit)]) {
      reasons[idx] = *find (id);
      assert (reasons[idx]);
    } else {
      assert (0 && "no assumptions at level zero");
    }
    assert (reasons[idx]);
    assert (reasons[idx]->literals[0] == lit);
    if (reasons[idx]->size == 1 && !reasons[idx]->original)
      reasons[idx]->range = trail_range[idx];
  }
  next_to_propagate = trail.size ();
  top_root_trail = trail.size () - 1;
  last_assumed_trail = 0;
}

int Drup2Itp::init_data_structures () {
  if (!internal) {
    CaDiCaL::fatal_message_start ();
    fputs ("Internal solver is not connected. ", stderr);
    CaDiCaL::fatal_message_end ();
  }
  internal->backtrack ();
  assert (!internal->level);
  assert (external->max_var >= max_var);
  if (watching ())
    reset_watches ();
  if (vals) {
    vals -= size_vars;
    delete[] vals;
    vals = 0;
  }
  max_var = external->max_var;
  if (!max_var)
    return 0;
  // The order of the below methods is critical.
  init_vals ();
  init_trail_and_reasons ();
  sorter.reset (&lit2trail, vals);
  init_watches ();
  marks.resize (size_vars, 0);
  seen.resize (size_vars, 0);
  return 1;
}

// TODO: Another issue is that the tracer API treats removing duplicates
// as a derivation step. In such case the RUP check will fail.
void Drup2Itp::RUP (Clause *c, unsigned &trail_sz) {
  assert (c);
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
      for (int lit : *reason) {
        assert (abs (lit) < size_vars);
        Clause *cr = reasons[abs (lit)];
        assert (cr);
        cr->core = true;
      }
      next_to_propagate = i;
    }
  }
}

void Drup2Itp::mark_top_conflict () {
  switch (conclusion) {
  case ConclusionType::CONFLICT: {
    assert (top_conflict);
    top_conflict->core = true;
    for (int lit : *top_conflict) {
      assert (abs (lit) < size_vars);
      if (Clause *c = reasons[abs (lit)])
        c->core = true;
    }
  } break;
  case ConclusionType::ASSUMPTIONS: {
    if (size_clauses)
      for (int lit : assumptions)
        if (external->failed (lit)) {
          assert (abs (lit) < size_vars);
          Clause *c = reasons[abs (lit)];
          if (c)
            c->core = true;
        }
  } break;
  case ConclusionType::CONSTRAINT: {
    if (size_clauses)
      for (int lit : constraint) {
        assert (abs (lit) < size_vars);
        Clause *c = reasons[abs (lit)];
        if (c)
          c->core = true;
      }
  } break;
  default:
    assert (false && "should not reach here");
  }
  for (Clause *c : assumption_clauses) {
    bool root_level_satisfied = false;
    for (int lit : *c)
      if (val (lit) > 0) {
        root_level_satisfied = true;
        break;
      }
    if (root_level_satisfied)
      continue;
    c->core = true;
    proof.push_back (c);
    stats.derived++;
    proof.push_back (c);
    stats.deleted++;
  }
  assumption_clauses.clear (); // they are part of the proof now
}

bool Drup2Itp::trim () {

  stats.trims++;
  mark_top_conflict ();

  // 'trail_sz' is used for lazy shrinking of the trail.
  unsigned trail_sz = trail.size ();

  // Main trimming loop
  for (int i = proof.size () - 1; i >= 0; i--) {
    Clause *c = proof[i];

    if (c->garbage) {
      attach_clause (c);
      continue;
    }

    if (is_on_trail (c))
      undo_trail_core (c, trail_sz);

    detach_clause (c);

    if (c->core)
      RUP (c, trail_sz);
  }

  shrink_trail (trail_sz);
  mark_core_trail_antecedents ();

  return true;
}

bool Drup2Itp::trim (ItpClauseIterator *it, bool undo) {

  if (empty_original_clause || !init_data_structures ())
    return true;

  if (!trim ())
    return false;

  if (it)
    traverse_core (*it);

  if (undo) {
    // For application where only core is needed
    for (Clause *c : proof)
      c->garbage = !c->garbage;
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next)
        c->core = false;
    // // restore_trail ();
  }

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

bool Drup2Itp::skip_lemma (Clause *c) {
  assert (c);
  if (!c->garbage) {
    if (c->core)
      return true;
    if (!is_on_trail (c) || satisfied (c))
      detach_clause (c);
    return true;
  } else {
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

  restore_trail (true /*original*/, true /*core*/);

  vector<Clause *> new_proof;

  int trail_label_idx = 0;
  label_root_level (it, trail_label_idx);

  if (conflict) {
    // Initial data base is inconsistent.
    label_final (it, conflict);
    return true;
  }

  for (Clause *c : proof) {

    if (skip_lemma (c))
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
        new_proof.push_back (c);
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
      new_proof.push_back (p);
      c->core = false;

      it.chain_resolution (p);

      if (part > maximal_part) {
        c->core = false;
        c = p;
        if (new_proof.back () != c)
          new_proof.push_back (p);
      }
    }

    assert (c);
    backtrack (previously_propagated);

    if (!learned) {
      assert (c->garbage && c->core);
      c->core = false;
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
    assert (proof.size ());
    label_final (it, proof.back ());
  }

#if DNDEBUG
  for (Clause *c : new_proof)
    assert (c && c->core && !c->garbage);
#endif

  if (incremental) {
    // Currently, we don't want to manupulate the internal solver's
    // data base. Therefore, we undo the effects of the replay.
    // TODO: Clean the proof post replay
    for (Clause *c : proof)
      c->garbage = true;

    for (Clause *c : proof)
      if (!c->original)
        c->garbage = !c->garbage;

    vector<Clause *> to_delete;
    for (uint64_t i = 0; i < size_clauses; i++)
      for (Clause *c = clauses[i]; c; c = c->next) {
        c->core = false;
        assert (!c->original || c->range.singleton ());
        if (!c->original)
          c->range.reset ();
        if (max_id < c->id) {
          if (!c->garbage)
            detach_clause (c);
          to_delete.push_back (c);
        }
      }

    for (int i = 0; i < to_delete.size (); i++) {
      Clause *c = to_delete[i];
      delete_clause (c);
    }
  }

  return true;
}

bool Drup2Itp::set_reorder_proof (bool val) {
  bool pval = reorder_proof;
  reorder_proof = val;
  return pval != val;
}

void Drup2Itp::restore_trail (bool original, bool core) {
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (c->size != 1)
        continue;
      if (original && !c->original)
        continue;
      if (core && !c->core)
        continue;
      int unit = c->literals[0];
      if (val (unit))
        continue;
      // if (c == top_conflict) {
      //   // This is a falsified original unit.
      //   continue;
      // }
      assign (unit, c);
      propagate (core);
    }
  // The units are not put by back by there original order. Therefore,
  // we repropagate all units on trail to restore all of the trail.
  next_to_propagate = 0;
  propagate (core);
}

void Drup2Itp::append (uint64_t id, const vector<int> &literals,
                       bool deletion) {
  stats.added++;
  Clause *c = size_clauses ? *find (id) : 0;
  if (deletion) {
    stats.deleted++;
    if (c) {
      assert (c->size == literals.size () && c->id == id);
      // assert (!c->garbage);
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
    proof.push_back (c);
    inconsistent |= !c->size;
  }
}

void Drup2Itp::traverse_core (ItpClauseIterator &it) {
  stats.core = 0;
  vector<int> clause;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (Clause *c = clauses[i]; c; c = c->next) {
      if (!c->original || !c->core)
        continue;
      stats.core++;
      for (int lit : *c)
        clause.push_back (lit);
      assert (c->range.singleton ());
      if (!it.clause (clause, c->range.min ()))
        return;
      clause.clear ();
    }
  for (int lit : assumptions)
    if (external->failed (lit)) {
      clause.push_back (lit);
      // Range range = trail_range[abs (lit)];
      // if (!it.clause (clause, range.min ()))
      if (!it.assume (lit))
        return;
      clause.clear ();
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

// We create and connect watches from scratch separatly from the internal
// solver therefore we need to sort the literals in the clause s.t. the
// first two literals are the last to be propagated in the clause.
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
  for (int idx = 1; idx <= max_var; idx++) {
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
  assert (c);
  sort_watch (c);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  watch_literal (l0, l1, c);
  watch_literal (l1, l0, c);
  // num_watched += 2;
}

void Drup2Itp::unwatch_clause (Clause *c) {
  assert (c);
  const int l0 = c->literals[0];
  const int l1 = c->literals[1];
  remove_watch (watches (l0), c);
  remove_watch (watches (l1), c);
  // num_watched -= 2;
}

/*------------------------------------------------------------------------*/

void Drup2Itp::connect_internal (Internal *i) {
  assert (i);
  internal = i;
  external = i->external;
}

void Drup2Itp::add_original_clause (uint64_t id, bool, const vector<int> &c,
                                    bool) {
  START (checking);
  stats.added++;
  stats.original++;
  if (c.empty ()) {
    Clause *oc = insert (c, id);
    oc->original = true;
    oc->range.join (current_part);
    inconsistent = true;
    empty_original_clause = true;
  } else {
    import_clause (c);
    if (!imported_tautological) {
      Clause *oc = insert (imported_clause, id);
      oc->original = true;
      assert (current_part);
      oc->range.join (current_part);
      assert (oc->range.singleton ());
      for (int lit : c) {
        unsigned idx = abs (lit);
        assert (idx < vars_range.size ());
        vars_range[idx].join (current_part);
      }
    }
    imported_clause.clear ();
  }
  STOP (checking);
}

void Drup2Itp::add_derived_clause (uint64_t id, bool, const vector<int> &c,
                                   const vector<uint64_t> &) {
  if (inconsistent)
    return;
  START (checking);
  if (c.empty ()) {
    insert (c, id);
    inconsistent = true;
    // TODO: It's unclear how the current
    // tracer API can provide the necessary information on the top
    // conflict without antecedents. This is a temporary hack to handle
    // the top conflict. It's fragile and should be replaced with a better
    // solution.
    if (internal->conflict) {
      // Falsified clause found during propagation
      top_conflict = *find (internal->conflict->id);
    }
  } else {
    import_clause (c);
    if (!imported_tautological)
      append (id, imported_clause, false /*addition*/);
    imported_clause.clear ();
  }
  STOP (checking);
}

void Drup2Itp::add_assumption_clause (uint64_t id, const vector<int> &c,
                                      const vector<uint64_t> &) {
  stats.added++;
  import_clause (c);
  if (!imported_tautological) {
    Clause *as = insert (c, id);
    as->garbage = true; // So we do not connect it to watches.
    assumption_clauses.push_back (as);
  }
  imported_clause.clear ();
}

void Drup2Itp::delete_clause (uint64_t id, bool, const vector<int> &c) {
  if (inconsistent) {
    if (!top_conflict) {
      // Falsified original clause found during propagation
      top_conflict = *find (id);
    }
    return;
  }
  START (checking);
  import_clause (c);
  if (!imported_tautological) {
    append (id, imported_clause, true /*deletion*/);
    int *lits = proof.back ()->literals, size = proof.back ()->size;
    for (int i = 0; i < size; i++)
      if (external->fixed (lits[i]) < 0)
        swap (lits[i], lits[--size]);
  }
  imported_clause.clear ();
  STOP (checking);
}

void Drup2Itp::add_assumption (int lit) { assumptions.push_back (lit); }

void Drup2Itp::add_constraint (const vector<int> &c) {
  // If the user adds a constraint while there is already one,
  // the previous one is discarded. It's better if discarding the previous
  // was done explicitly through the tracer API however.
  // assert (constraint.empty ());
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
       stats.core, CaDiCaL::percent (stats.core, stats.original));
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
  bool configured = true;
  configured &= s.set ("compact", 0);
  configured &= s.set ("ilbassumptions", 0);
  configured &= s.set ("probe", 0);
  configured &= s.set ("block", 0);
  configured &= s.set ("condition", 0);
  configured &= s.set ("elim", 0);
  assert (configured);
  s.connect_proof_tracer (this, false /* without antecedents */);
  return;
}

} // namespace DRUP2ITP
