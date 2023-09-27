############################################################################
##    This file is part of OMTPlan.
##
##    OMTPlan is free software: you can redistribute it and/or modify
##    it under the terms of the GNU General Public License as published by
##    the Free Software Foundation, either version 3 of the License, or
##    (at your option) any later version.
##
##    OMTPlan is distributed in the hope that it will be useful,
##    but WITHOUT ANY WARRANTY; without even the implied warranty of
##    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##    GNU General Public License for more details.
##
##    You should have received a copy of the GNU General Public License
##    along with OMTPlan.  If not, see <https://www.gnu.org/licenses/>.
############################################################################

from z3 import *
from planner import plan
from planner import encoder
import utils
import numpy as np

class ChronologicalHeuristic(UserPropagateBase):
    """
    A User Propagator for Z3 that does the following:
    Every restart, it switches between default variable selection heuristic (VSIDS)
    and a chronological one. That is, it forces the solver to decide all variables
    on timestep t before proceeding onto decide anything on timestep t+1

    "Satisfiability Modulo Custom Theories in Z3", Bjorner et al. has a
    reference of the methods that can be overwritten and what they do.

    The big plan is to:
    - at each step added, register all the Booleans that refer to actions
      put them in an ordered list
      Maintain a pointer to the chronologically first non-assigned variable

    - When we're getting a Decide() (the solver has decided on a variable)
      update the pointer if needed
      call NextSplit() on the chronologically first non-assigned variable
    """
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)

        self.var2idx = {} # A map from variables to idxs (where they are located)
        self.ordered_actions = [] # The action Boolean variables, sorted in chronological order
        self.decided_actions = [] # An array of 0/1 variables, stating if the corresponding action has been decided upon
        self.next_decision_ptr = 0 # The idx of the next variable to decide on

        self.add_fixed(self._fixed)
        self.add_final(self._final)

        # TODO : decide is not fully implemented on 4.12.2 (it is half-done on master branch?)
        # Therefore we take an alternative approach: we call next_split in
        #self.decide = None
        #self.add_decide(self._decide)

    def _print(self):
        print(self.ordered_actions)
        print(self.decided_actions)
        print(self.next_decision_ptr)
        print(f"next decision on action {self.next_decision_ptr}: {self.ordered_actions[self.next_decision_ptr]}")

    def register_action(self, horizon, name, var):
        self.add(var) # we register the action first
        self.var2idx[var] = len(self.ordered_actions)
        self.ordered_actions.append(var)
        self.decided_actions.append(0)

    def _fixed(self, x, v):
        print("fixed: ", x, " := ", v)

        self.decided_actions[self.var2idx[x]] = 1
        self.next_decision_ptr += 1
        #self.next_split(t, idx, phase)
        # let Z3 decide the phase
        # TODO: decide on a non-decided variable!
        self.next_split(self.ordered_actions[self.next_decision_ptr], 1, 0)

    def _final(self):
        #print("finished")
        self._print()

    #def _decide(self, t, idx, phase):
    #    print(f"deciding on {t}?")

    """ Overrides a base class method """
    def push(self):
        pass#print("push!")

    """ Overrides a base class method """
    def pop(self, num_scopes):
        print(f"pop! {num_scopes}")


class Search():
    """
    Base class defining search schemes.
    """
    def __init__(self, encoder, ub):
        self.encoder = encoder
        self.found = False
        self.solution = None
        self.solver = None
        self.ub = ub



class SearchSMT(Search):
    """
    Search class for SMT-based encodings.
    """

    def do_linear_search(self):
        """
        Linear search scheme for SMT encodings with unit action costs.

        Optimal plan is obtained by simple ramp-up strategy
        """

        # Defines initial horizon for ramp-up SMT search

        self.horizon = 1

        print('Start linear search SMT')

        # Build formula until a plan is found or upper bound is reached

        while not self.found and self.horizon < self.ub:
            # Create SMT solver instance
            self.solver = Solver()

            # Build planning subformulas
            formula =  self.encoder.encode(self.horizon)

            # Assert subformulas in solver
            for k,v in formula.items():
                self.solver.add(v)

            # Check for satisfiability
            res = self.solver.check()

            if res == sat:
                self.found = True
            else:
                # Increment horizon until we find a solution
                self.horizon = self.horizon + 1


        if self.found:
            # Extract plan from model
            model = self.solver.model()
            self.solution = plan.Plan(model, self.encoder)
        else:
            self.solution = []
            print('Problem not solvable')
            
        return self.solution


class SearchOMT(Search):
    """
    Search class for OMT-based encodings.
    """

    def computeHorizonSchedule(self):
        """
        Computes horizon schedule given upper bound for search.
        Here percentages are fixed.
        """

        schedule = []
        percentages = [10,15,25,35,50,75,100]

        def percentage(percent, whole):
            return int((percent * whole) / 100)

        for p in percentages:
            schedule.append(percentage(p,self.ub))

        return schedule


    def do_search(self):
        """
        Search scheme for OMT encodings with unit, constant or state-dependent action costs.
        """

        print('Start search OMT')

        # Try different horizons

        horizon_schedule = self.computeHorizonSchedule()

        # Start building formulae

        for horizon in horizon_schedule:
            print('Try horizon {}'.format(horizon))

            # Create OMT solver instance
            self.solver = Optimize()

            # Build planning subformulas
            formula = self.encoder.encode(horizon)

            # Assert subformulas in solver
            for label, sub_formula in formula.items():

                if label == 'objective':
                    # objective function requires different handling
                    # as per Z3 API
                    objective = self.solver.minimize(sub_formula)
                elif label ==  'real_goal':
                    # we don't want to assert goal formula at horizon
                    # see construction described in related paper
                    pass
                else:
                    self.solver.add(sub_formula)

            print('Checking formula')

            res = self.solver.check()

            # If formula is unsat, the problem does not admit solution
            # see Theorem 1 in related paper

            if res == unsat:
                self.solution = []
                print('Problem not solvable')

            else:
                # Check if model satisfied concrete goal
                model = self.solver.model()
                opt = model.eval(formula['real_goal'])

                # if formula is sat and G_n is satisfied, solution is optimal
                # see Theorem 2 in related paper

                if opt:
                    self.solution =  plan.Plan(model, self.encoder, objective)
                    break

        return self.solution


class SearchR2E(Search):
    """
    Class that implements linear search using the R2E encoding
    TODO: Check if we can merge with linearSMT class as it seems superficially the same to me
    """
    def do_search(self):
        self.horizon = 1 
        solver = Solver()

        while self.horizon < self.ub :
            
            print(f'Checking horizon: {self.horizon}/{self.ub }')
            # Build planning subformulas
            
            formula, all_formula =  self.encoder.incremental_encoding(self.horizon)

            # Assert subformulas in solver
            for k,v in formula.items():
                if not k in ['goal']:
                    solver.add(v)

            # Now create a new instance of the solver and add the goal.
            solver.push()

            # Add the goal
            solver.add(formula['goal'])

            # Check for satisfiability
            res = solver.check()

            if res == sat:
                self.found = True
                self.encoder.horizon = self.horizon
                break
            else:
                # Remove the old goal formula
                solver.pop()
                # Increment horizon until we find a solution
                self.horizon = self.horizon + 1
        
        if self.found:
            # Extract plan from model
            model = solver.model()
            self.solution = plan.Plan(model, self.encoder)
            if not self.solution.validate():
                raise Exception('R2E: Plan found invalid!')
        else:
            self.solution = []
            print('Problem not solvable')
            
        return self.solution


class ChronologicalSearchR2E(Search):
    """
    Class that implements linear search using the R2E encoding
    It also adds a UserPropagator to search chronologically
    """
    def do_search(self):
        self.horizon = 1
        solver = SimpleSolver()
        up = ChronologicalHeuristic(solver)

        while self.horizon < self.ub :

            print(f'Checking horizon: {self.horizon}/{self.ub }')
            # Build planning subformulas

            formula, all_formula =  self.encoder.incremental_encoding(self.horizon)

            # Assert subformulas in solver
            for k,v in formula.items():
                if not k in ['goal']:
                    solver.add(v)

            # Now create a new instance of the solver and add the goal.
            solver.push()

            # Add the goal
            solver.add(formula['goal'])

            # register all action variables for the UserPropagator
            # This needs to be done after the variables have been created in the solver
            for name, var in self.encoder.action_variables[self.horizon].items():
                up.register_action(self.horizon, name, var)

            # Check for satisfiability
            res = solver.check()

            if res == sat:
                self.found = True
                self.encoder.horizon = self.horizon
                break
            else:
                # Remove the old goal formula
                solver.pop()
                # Increment horizon until we find a solution
                self.horizon = self.horizon + 1

        if self.found:
            # Extract plan from model
            model = solver.model()
            self.solution = plan.Plan(model, self.encoder)
            if not self.solution.validate():
                raise Exception('R2E: Plan found invalid!')
        else:
            self.solution = []
            print('Problem not solvable')

        return self.solution
