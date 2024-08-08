// Created by Basel Khouri 2024

#include "drup2itptypes.hpp"
#include <cstdio>
#include <iostream>

namespace DRUP2ITP {

Range::Range () : m_min (PART_UNDEF), m_max (PART_UNDEF) {}

Range::Range (const unsigned c) : m_min (c), m_max (c) {}

bool Range::undef () const { return m_min == PART_UNDEF; }

void Range::reset () { m_min = m_max = PART_UNDEF; }

bool Range::singleton () const { return m_min == m_max; }

void Range::join (const unsigned np) {
  if (np == 0)
    return;
  if (undef ())
    m_min = m_max = np;
  else if (np > m_max)
    m_max = np;
  else if (np < m_min)
    m_min = np;
}

void Range::join (const Range &o) {
  if (o.undef ())
    return;
  join (o.min ());
  join (o.max ());
}

unsigned Range::min () const { return m_min; }

unsigned Range::max () const { return m_max; }

bool Range::operator== (const Range &r) {
  return m_min == r.min () && m_max == r.max ();
}

bool Range::operator!= (const Range &r) {
  return m_min != r.min () || m_max != r.max ();
}

WatchSort::WatchSort (const vector<unsigned> *lit2trail,
                      const signed char *values)
    : trail (lit2trail), vals (values) {}

void WatchSort::reset (const vector<unsigned> *lit2trail,
                       const signed char *values) {
  trail = lit2trail;
  vals = values;
}

bool WatchSort::operator() (int x, int y) const {
  assert (x && y && vals && trail);
  assert (abs (x) < trail->size ());
  assert (abs (y) < trail->size ());
  if (!vals[x])
    return true;
  if (!vals[y])
    return false;
  if ((*trail)[abs (x)] > (*trail)[abs (y)])
    return true;
  return false;
}

bool TraceCheck::visit_antecedent (int lit) {
  assert (lit);
  auto &unit = units[abs (lit)];
  if (!unit) {
    output (ids);
    unit = ids++;
    output (lit);
    fprintf (file, "0 0\n");
    return true;
  }
  return false;
}

bool TraceCheck::visit_antecedent (Clause *c) {
  assert (c);
  if (!visited[c]) {
    output (ids);
    visited[c] = ids++;
    output (c);
    fprintf (file, "0 0\n");
    if (c->size == 1 && !units[abs (c->literals[0])])
      units[abs (c->literals[0])] = ids - 1;
    return true;
  }
  return false;
}

void TraceCheck::visit_derived (int parent) {
  assert (parent);
  output (ids);
  assert (abs (parent) < units.size ());
  units[abs (parent)] = ids++;
  output (parent);
  output_chain ();
}

void TraceCheck::visit_derived (Clause *parent) {
  output (ids);
  if (parent) {
    if (parent->size == 1) {
      unsigned idx = abs (parent->literals[0]);
      visited[parent] = units[idx] = ids;
    } else {
      visited[parent] = ids;
    }
    output (parent);
  }
  ids++;
  output_chain ();
}

void TraceCheck::output (int lit) { fprintf (file, "%d ", lit); }

void TraceCheck::output (Clause *c) {
  assert (c);
  for (int lit : *c)
    output (lit);
}

void TraceCheck::output_chain () {
  fprintf (file, "0 ");
  const unsigned pivots_size = chain.pivots.size ();
  const unsigned clauses_size = chain.clauses.size ();
  unsigned i = 0;
  output (visited[chain.clauses[0]]);
  for (; i < pivots_size; i++)
    if (i + 1 < clauses_size && chain.clauses[i + 1])
      output (visited[chain.clauses[i + 1]]);
    else
      output (units[abs (chain.pivots[i])]);
  fprintf (file, "0\n");
}

TraceCheck::TraceCheck (FILE *f, unsigned size_vars)
    : file (f), units (size_vars + 1, 0), ids (1) {}

void TraceCheck::resolution (int parent, int p1, Clause *p2) {
  visit_antecedent (p1);
  visit_antecedent (p2);
  output (ids);
  units[abs (parent)] = ids++;
  output (parent);
  fprintf (file, "0 ");
  output (units[abs (p1)]);
  output (visited[p2]);
  fprintf (file, "0\n");
}

void TraceCheck::chain_resolution (int parent) {
  assert (chain.clauses.size ());
  visit_antecedent (chain.clauses[0]);
  for (unsigned i = 0; i < chain.pivots.size (); i++)
    if (i + 1 < chain.clauses.size () && chain.clauses[i + 1])
      visit_antecedent (chain.clauses[i + 1]);
    else
      visit_antecedent (chain.pivots[i]);
  visit_derived (parent);
}

void TraceCheck::chain_resolution (Clause *parent) {
  assert (chain.clauses.size ());
  visit_antecedent (chain.clauses[0]);
  for (unsigned i = 0; i < chain.pivots.size (); i++)
    if (i + 1 < chain.clauses.size () && chain.clauses[i + 1])
      visit_antecedent (chain.clauses[i + 1]);
    else
      visit_antecedent (chain.pivots[i]);
  visit_derived (parent);
}

} // namespace DRUP2ITP
