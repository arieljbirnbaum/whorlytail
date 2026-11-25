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
  id : Nat
  interval : Interval
  parent? : Option Nat

def Cycle.within (inner outer : Cycle) : Prop :=
  outer.interval.contains inner.interval

theorem Cycle.within_trans {inner middle outer : Cycle} (him : inner.within middle)
    (hmo : middle.within outer) : inner.within outer := by exact Interval.contains_trans hmo him

structure Goal where
  id : Nat
  title : String
  parent? : Option Nat

def uniqueIds (goals : List Goal) : Prop :=
  ∀ g1 ∈ goals, ∀ g2 ∈ goals, g1.id = g2.id → g1 = g2

def reachesRoot (goals : List Goal) : Nat → Goal → Prop
  | 0, _ => False
  | fuel + 1, g =>
    match g.parent? with
    | none => True
    | some pid => ∃ p ∈ goals, p.id = pid ∧ reachesRoot goals fuel p

def allGoalsReachRoot (goals : List Goal) : Prop :=
  ∀ g ∈ goals, reachesRoot goals goals.length g

structure Model where
  goals : List Goal
  valid : uniqueIds goals ∧ allGoalsReachRoot goals

theorem self_parent_never_reaches_root {goals : List Goal} {goal : Goal} (hUnique : uniqueIds goals)
    (hInGoals : goal ∈ goals) (hSelfParent : goal.parent? = some goal.id) (fuel : Nat) :
    ¬reachesRoot goals fuel goal := by
  induction fuel with
  | zero => exact id
  | succ fuel ih =>
    intro hReachesRootInSuccFuel
    obtain ⟨parent, hParentInGoals, hParentGoalSameId, hParentReachesRootInFuel⟩ :
      ∃ parent ∈ goals, parent.id = goal.id ∧ reachesRoot goals fuel parent := by
      simpa only [reachesRoot, hSelfParent] using hReachesRootInSuccFuel
    obtain rfl : parent = goal := hUnique parent hParentInGoals goal hInGoals hParentGoalSameId
    exact ih hParentReachesRootInFuel

theorem Model.no_self_parent {model : Model} : ∀ g ∈ model.goals, g.parent? ≠ some g.id := by
  intro goal hInGoals hSelfParent
  obtain ⟨hUnique, hAllReachRoot⟩ := model.valid
  have hReach : reachesRoot model.goals model.goals.length goal := hAllReachRoot goal hInGoals
  exact self_parent_never_reaches_root hUnique hInGoals hSelfParent _ hReach
