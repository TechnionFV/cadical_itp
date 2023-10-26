#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

IrupTracer::IrupTracer (Internal *i, File *f, bool b)
    : internal (i), file (f), binary (b),
      num_clauses (0), size_clauses (0), last_hash (0), last_id (0),
      last_clause (0), added (0), deleted (0) {
  (void) internal;

  // Initialize random number table for hash function.
  //
  Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1))
      nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }
#ifndef NDEBUG
  binary = b;
#else
  (void) b;
#endif
}

void IrupTracer::connect_internal (Internal *i) {
  internal = i;
  file->connect_internal (internal);
  LOG ("IRUP TRACER connected to internal");
}

IrupTracer::~IrupTracer () {
  LOG ("IRUP TRACER delete");
  delete file;
  for (size_t i = 0; i < size_clauses; i++)
    for (IrupClause *c = clauses[i], *next; c; c = next)
      next = c->next, delete_clause (c);
  delete[] clauses;
}

/*------------------------------------------------------------------------*/

void IrupTracer::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2 * size_clauses : 1;
  LOG ("IRUP Tracer enlarging clauses of tracer from %" PRIu64
       " to %" PRIu64,
       (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  IrupClause **new_clauses;
  new_clauses = new IrupClause *[new_size_clauses];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (IrupClause *c = clauses[i], *next; c; c = next) {
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

IrupClause *IrupTracer::new_clause () {
  const size_t size = imported_clause.size ();
  assert (size <= UINT_MAX);
  const int off = size ? -1 : 0;
  const size_t bytes =
      sizeof (IrupClause) + (size - off) * sizeof (int);
  IrupClause *res = (IrupClause *) new char[bytes];
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  int *literals = res->literals, *p = literals;
  for (const auto &lit : imported_clause) {
    *p++ = lit;
  }
  last_clause = res;
  num_clauses++;
  return res;
}

void IrupTracer::delete_clause (IrupClause *c) {
  assert (c);
  num_clauses--;
  delete c;
}

uint64_t IrupTracer::reduce_hash (uint64_t hash, uint64_t size) {
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

uint64_t IrupTracer::compute_hash (const uint64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;
  uint64_t tmp = nonces[j] * (uint64_t) id;
  return last_hash = tmp;
}

bool IrupTracer::find_and_delete (const uint64_t id) {
  if (!num_clauses)
    return false;
  IrupClause **res = 0, *c;
  const uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id) {
      break;
    }
    if (!c->next)
      return false;
  }
  if (!c)
    return false;
  assert (c && res);
  *res = c->next;
  int *begin = c->literals;
  for (size_t i = 0; i < c->size; i++) {
    imported_clause.push_back (begin[i]);
  }
  delete c;
  return true;
}

void IrupTracer::insert () {
  if (num_clauses == size_clauses)
    enlarge_clauses ();
  const uint64_t h = reduce_hash (compute_hash (last_id), size_clauses);
  IrupClause *c = new_clause ();
  c->next = clauses[h];
  clauses[h] = c;
}

/*------------------------------------------------------------------------*/

inline void IrupTracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void IrupTracer::put_binary_lit (int lit) {
  assert (binary);
  assert (file);
  assert (lit != INT_MIN);
  unsigned x = 2 * abs (lit) + (lit < 0);
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

inline void IrupTracer::put_binary_id (uint64_t id) {
  assert (binary);
  assert (file);
  uint64_t x = id;
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

/*------------------------------------------------------------------------*/

void IrupTracer::irup_add_restored_clause (const vector<int> &clause) {
  if (binary)
    file->put ('r');
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void IrupTracer::irup_add_derived_clause (const vector<int> &clause) {
  if (binary)
    file->put ('a');
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void IrupTracer::irup_delete_clause (uint64_t id, const vector<int> &clause) {
  if (find_and_delete (id)) {
    assert (imported_clause.empty ());
    if (binary)
      file->put ('w');
    else
      file->put ("w ");    
  } else {
    if (binary)
      file->put ('d');
    else
      file->put ("d ");
  }
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void IrupTracer::irup_conclude_and_delete (const vector<uint64_t> & conclusion) {
  uint64_t size = conclusion.size ();
  if (size > 1) {
    if (binary) {
      file->put ('J');
      put_binary_id (size);  // TODO: put_binary_id ok for size?
    } else {
      file->put ("J ");
      file->put (size), file->put ("\n");
    }
  }
  for (auto & id : conclusion) {
    if (binary)
      file->put ('j');
    else
      file->put ("j ");
    (void) find_and_delete (id);
    for (const auto & external_lit : imported_clause) {
      if (binary)
        put_binary_lit (external_lit);
      else
        file->put (external_lit), file->put (' ');
    }
    if (binary)
      put_binary_zero ();
    else
      file->put ("0\n");
    imported_clause.clear ();
  }
}


void IrupTracer::irup_report_status (StatusType status) {
  if (binary)
    file->put ('s');
  else
    file->put ("s ");
  if (status == UNSAT) {
    file->put ("UN");
  }
  file->put ("SATISFIABLE");
  if (!binary)
    file->put ("\n");
}


void IrupTracer::irup_conclude_sat (const vector<int> &model) {
  if (binary)
    file->put ('v');
  else
    file->put ("v ");
  for (auto & lit : model) {
    if (binary)
      put_binary_lit (lit);
    else
      file->put (lit), file->put (' ');
  }
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

/*------------------------------------------------------------------------*/


void IrupTracer::add_derived_clause (uint64_t, bool, const vector<int> &clause,
                                     const vector<uint64_t> &) {
  if (file->closed ())
    return;
  assert (imported_clause.empty ());
  LOG (clause, "IRUP TRACER tracing addition of derived clause");
  irup_add_derived_clause (clause);
  added++;
}

void IrupTracer::add_assumption_clause (uint64_t id, const vector<int> &clause,
                                    const vector<uint64_t> &) {
  if (file->closed ())
    return;
  assert (imported_clause.empty ());
  LOG (clause, "IRUP TRACER tracing addition of assumption clause");
  for (auto & lit : clause)
    imported_clause.push_back (lit);
  last_id = id;
  insert ();
  imported_clause.clear ();
}

void IrupTracer::delete_clause (uint64_t id, bool,
                                  const vector<int> &clause) {
  if (file->closed ())
    return;
  assert (imported_clause.empty ());
  LOG ("IRUP TRACER tracing deletion of clause[%" PRId64 "]", id);
  irup_delete_clause (id, clause);
  deleted++;
}

void IrupTracer::weaken_minus (uint64_t id, const vector<int> &) {
  if (file->closed ())
    return;
  assert (imported_clause.empty ());
  LOG ("IRUP TRACER tracing weaken minus of clause[%" PRId64 "]", id);
  last_id = id;
  insert ();
}

void IrupTracer::conclude_unsat (ConclusionType, const vector<uint64_t> & conclusion) {
  if (file->closed ())
    return;
  assert (imported_clause.empty ());
  LOG (conclusion, "IRUP TRACER tracing conclusion of clause(s)");
  irup_conclude_and_delete (conclusion);
}

void IrupTracer::add_original_clause (uint64_t, bool, const vector<int> &clause,
                                    bool restored) {
  if (file->closed ())
    return;
  if (!restored)
    return;
  LOG (clause, "IRUP TRACER tracing addition of restored clause");
  irup_add_restored_clause (clause);
}

void IrupTracer::report_status (StatusType status, uint64_t) {
  if (file->closed ())
    return;
  if (status == OTHER)
    return;
  LOG ("IRUP TRACER tracing report of status %d", status);
  irup_report_status (status);
}
 
void IrupTracer::conclude_sat (const vector<int> &model) {
  if (file->closed ())
    return;
  LOG (model, "IRUP TRACER tracing conclusion of model");
  irup_conclude_sat (model);
}

/*------------------------------------------------------------------------*/

bool IrupTracer::closed () { return file->closed (); }

void IrupTracer::close () {
  assert (!closed ());
  file->close ();
}

void IrupTracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses", added,
       deleted);
}

} // namespace CaDiCaL
