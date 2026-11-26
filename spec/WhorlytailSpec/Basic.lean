import Mathlib.Combinatorics.Digraph.Basic

structure Uid (_ : Type) where
  val : Nat
  deriving DecidableEq

structure Interval where
  start : Nat
  stop : Nat
  valid : start ≤ stop

def Interval.contains (outer inner : Interval) : Prop :=
  outer.start ≤ inner.start ∧ inner.stop ≤ outer.stop

theorem Interval.contains_trans {outer middle inner : Interval} (hom : outer.contains middle)
    (hmi : middle.contains inner) : outer.contains inner := by
  unfold Interval.contains at *
  omega

structure Cycle where
  id : Uid Cycle
  interval : Interval
  parent? : Option (Uid Cycle)

def Cycle.within (inner outer : Cycle) : Prop :=
  outer.interval.contains inner.interval

theorem Cycle.within_trans {inner middle outer : Cycle} (him : inner.within middle)
    (hmo : middle.within outer) : inner.within outer := by exact Interval.contains_trans hmo him

inductive Goal where

structure GoalData where
  title : String
  description : String

inductive GoalState where
  | needsAction
  | inProgress
  | completed
  | cancelled

def GoalState.finished (state : GoalState) : Prop :=
  match state with
  | needsAction | inProgress => False
  | completed | cancelled => True

def GoalState.unfinished (state : GoalState) : Prop :=
  ¬state.finished

structure PlanState where
  goals : Finset (Uid Goal)
  data : goals -> GoalData
  state : goals -> GoalState
  blocks : Digraph goals
  hWellFounded : WellFounded blocks.Adj
  parent? : (g : goals) -> Option { b : goals // blocks.Adj g b }
  hNoPendingChildren : ∀ c p, parent? c = some p → (state p.val).finished → (state c).finished

def PlanState.unfinished {plan : PlanState} (g : plan.goals) : Prop :=
  (plan.state g).unfinished

def PlanState.blocked {plan : PlanState} (g : plan.goals) : Prop :=
  ∃ b : plan.goals, Relation.TransGen plan.blocks.Adj b g ∧ unfinished b

def PlanState.ready {plan : PlanState} (g : plan.goals) : Prop :=
  unfinished g ∧ ¬blocked g

def PlanState.nextGoals (plan : PlanState) :=
  { goal : plan.goals // ready goal }
