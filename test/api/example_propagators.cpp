#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <iostream>


static int n = 5;

static int ph (int p, int h) {
    assert (0 <= p), assert (p < n + 1);
    assert (0 <= h), assert (h < n);
    return 1 + h * (n+1) + p;
}

static void formula (CaDiCaL::Solver &solver) {
  int p_limit = n;
  
  for (int h = 0; h < n; h++)
      for (int p1 = 0; p1 < p_limit; p1++)
          for (int p2 = p1 + 1; p2 < p_limit; p2++)
              solver.add (-ph (p1, h)), solver.add (-ph (p2, h)), solver.add (0);

  for (int p = 0; p < p_limit; p++) {
      for (int h = 0; h < n; h++)
          solver.add (ph (p, h));
      solver.add (0);
  }
}


/*----------------------------------------------------------------------------*/
//
// ObserverPropagator:
//
// This class implements a very simple ExternalPropagator that only reports
// the called IPASIR-UP functions with their arguments, without any actual
// interaction with the solver.
// 
// The code includes several "Fatal error" scenarios in comments to demonstrate
// possible invalid uses of the interface. These commands can be compiled, but
// will trigger a runtime error during solving.
//
class ObserverPropagator : CaDiCaL::ExternalPropagator, CaDiCaL::FixedAssignmentListener {
  CaDiCaL::Solver *solver;

public:
  ObserverPropagator (CaDiCaL::Solver *s) : solver(s) {
    // In case the following flag is true, the solver will invoke only the
    // cb_check_found_model callback, without any additional callbacks or
    // notifications. This can be useful for example in model enumeration
    // tasks, or for very lazy propagators where only the final complete
    // solution is planned to be checked.
    is_lazy = false;

    // The following flag determines if the solver is allowed to forget those
    // clauses that are given through the 'cb_add_reason_clause_lit' callback.
    // If the propagator does not use cb_propagate, the value of this flag
    // is irrelevant.
    are_reasons_forgettable = false;
    
    solver->connect_external_propagator (this);

    // In case it is important to know when an assignment is fixed (i.e., when
    // it is guaranteed to have the assigned value in any found model), the
    // propagator needs to implement the 'FixedAssignmentListener' interface
    // and needs to be connected as a listener as well. It is recommended to
    // connect the FixedAssignmentListener before the formula is given to the
    // solver. Note that the FixedAssignmentListener interface reports every
    // fixed assignments, not just the ones over observed variables.
    // See 'notify_fixed_assignment' function.
    solver->connect_fixed_listener (this);
    
    //Fatal error: can not connect more than one propagator
    //solver->connect_external_propagator (this);

    std::cout << "[up] ObserverPropagator is created and connected both as ";
    std::cout << "ExternalPropagator and as FixedAssignmentListener.";
    std::cout << std::endl;

    // Fatal error: invalid literal '0'
    // solver->add_observed_var(0);

    for (int h = 0; h < n; h++)
      for (int p = 0; p < n + 1; p++)
        solver->add_observed_var(ph(p,h));

    int max_var = solver->vars();
    std::cout << "Maximum variable in solver: " << max_var << std::endl;

    // Observing a variable before using it in any clause will force the
    // solver to create the variable. In the new interface this will not
    // be correct anymore, since every variable has to be asked from the
    // solver. Thus, in the future this call will trigger a fatal error.
    solver->add_observed_var(max_var+5);

    

    // Removing a non-observed (or not even existing) variable has no
    // effect, the solver will not create the variable and will not throw
    // any error.
    solver->remove_observed_var(max_var+223);

    max_var = solver->vars();
    std::cout << "New maximum variable in solver: " << max_var << std::endl;

    solver->clause(-max_var);
  }

  ~ObserverPropagator () {
    std::cout << "[up][~ObserverPropagator starts]" << std::endl;
    solver->disconnect_external_propagator(); 
  
    // Fatal error: can not unobserve variables without a connected propagator
    // solver->remove_observed_var (6);

    // Fatal error: can not disconnect propagator without a connected propagator
    // solver->disconnect_external_propagator();

    // Note that disconnecting a propagator will also invoke unobserving
    // every observed variable. In case any of these variables are currently
    // assigned (e.g., because the solver is in a SAT state), it will force
    // the solver to backtrack in order to unassign the variables.
    std::cout << "[up] ObserverPropagator is disconnected." << std::endl;
  }

  void notify_fixed_assignment (int lit) {
    std::cout << "[up][notify_fixed_assignment][" << lit << "]" << std::endl;
  }

  void notify_assignment (const std::vector<int> &lits) {
    std::cout << "[up][notify_assignment][ ";
    for (const auto lit: lits) {
      std::cout << lit << " ";
    }
    std::cout << "]" << std::endl;
  }

  void notify_new_decision_level () {
    std::cout << "[up][notify_new_decision_level]" << std::endl;
  }

  void notify_backtrack (size_t new_level) {
    std::cout << "[up][notify_backtrack][ to level " << new_level << " ]" << std::endl;

  }

  bool cb_check_found_model (const std::vector<int> &model) {
    std::cout << "[up][cb_check_found_model][ ";
    for (const auto lit: model) {
      std::cout << lit << " ";
    }
    std::cout << "]" << std::endl;

    return true;
  }
  
  int cb_decide () { 
    std::cout << "[up][cb_decide]" << std::endl; 
    return 0;
  };


  int cb_propagate () {
    std::cout << "[up][cb_propagate]" << std::endl; 
    return 0;
  };

  int cb_add_reason_clause_lit (int propagated_lit) {
    (void) propagated_lit;
    return 0;
  };

  bool cb_has_external_clause (bool &is_forgettable) {
    (void) is_forgettable;
    return false;
  }

  int cb_add_external_clause_lit () {
    return 0;
  }
};

void observer_example () {
  CaDiCaL::Solver solver;

  //Fatal error: can not observe variables without a connected propagator
  //solver.add_observed_var(4);

  ObserverPropagator observer (&solver);
  formula(solver);
  
  int res = solver.solve();
  std::cout << "Result: " << res << std::endl;
  if (res == 10) {
    std::cout << "s ";
    for (int h = 1; h <= n*(n+1)+5; h++)
        std::cout << solver.val(h) << " ";
    
    std::cout << std::endl;
  }
}


int main () {
  observer_example ();

  return 0;
}
