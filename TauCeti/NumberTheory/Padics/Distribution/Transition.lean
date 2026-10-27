/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage

/-!
# Transitions between arbitrary analytic levels

The adjacent-level re-expansion `TauCeti.AnalyticStage.transition` extends by composition
to a continuous linear map `transitionLE S hhk : LA_h(E) →L[S] LA_k(E)` for every `h ≤ k`.
These maps form a directed system: equal levels give the identity, and splitting a transition
at any intermediate level leaves the resulting coefficient vector unchanged.
Every transition is norm-decreasing and preserves the evaluated continuous function.

This system is defined on coefficient vectors over complete ultrametric `ℤ_p`-modules.
No injectivity assumption is needed to compose transitions or to compare their evaluations.
-/

public section

namespace TauCeti.AnalyticStage

variable {p : ℕ} [Fact p.Prime] {E : Type*} [NormedAddCommGroup E]
  [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  {h k l : ℕ}

/-- Re-expansion from level `h` to level `k`, obtained by composing adjacent transitions. -/
noncomputable def transitionLE (hhk : h ≤ k) : AnalyticStage p h E →L[S] AnalyticStage p k E :=
  Nat.leRecOn hhk (fun {_} L ↦ (transition S).comp L) (ContinuousLinearMap.id S _)

/-- Re-expansion from a level to itself is the identity. -/
@[simp]
theorem transitionLE_self :
    transitionLE (p := p) (E := E) S (le_refl h) = ContinuousLinearMap.id S _ :=
  Nat.leRecOn_self _

/-- Re-expansion to the next target level appends one adjacent transition. -/
theorem transitionLE_succ (hhk : h ≤ k) :
    transitionLE (p := p) (E := E) S (Nat.le_succ_of_le hhk) =
      (transition S).comp (transitionLE S hhk) :=
  Nat.leRecOn_succ hhk _

/-- Re-expansion to the adjacent level is the original transition. -/
@[simp]
theorem transitionLE_succ_self :
    transitionLE (p := p) (E := E) S (Nat.le_succ h) = transition S := by
  rw [transitionLE_succ S (le_refl h), transitionLE_self, ContinuousLinearMap.comp_id]

/-- Re-expansion through an intermediate level equals the transition to the final level. -/
@[simp]
theorem transitionLE_comp (hhk : h ≤ k) (hkl : k ≤ l) :
    (transitionLE (p := p) (E := E) S hkl).comp (transitionLE S hhk) =
      transitionLE S (hhk.trans hkl) := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
    rw [transitionLE_succ S hkl, transitionLE_succ S (hhk.trans hkl),
      ContinuousLinearMap.comp_assoc, ih]

/-- Applying two successive transitions is the transition across the combined levels. -/
@[simp]
theorem transitionLE_transitionLE (hhk : h ≤ k) (hkl : k ≤ l) (c : AnalyticStage p h E) :
    transitionLE S hkl (transitionLE S hhk c) = transitionLE S (hhk.trans hkl) c := by
  simpa only [ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun (transitionLE_comp S hhk hkl) c

/-- Analytic-stage transitions form a directed system of coefficient vectors. -/
instance instDirectedSystemTransitionLE :
    DirectedSystem (fun h ↦ AnalyticStage p h E)
      (fun {_ _} hhk ↦ transitionLE (p := p) (E := E) S hhk) where
  map_self := fun {_} c ↦ by simp
  map_map := fun {_ _ _} hhk hkl c ↦
    transitionLE_transitionLE S hhk hkl c

/-- Re-expansion between any two analytic levels does not increase the Gauss norm. -/
theorem norm_transitionLE_le (hhk : h ≤ k) (c : AnalyticStage p h E) :
    ‖transitionLE S hhk c‖ ≤ ‖c‖ := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply]
    exact (norm_transition_le S _).trans ih

/-- Re-expansion between any two analytic levels preserves the evaluated function. -/
@[simp]
theorem eval_transitionLE (hhk : h ≤ k) (c : AnalyticStage p h E) :
    eval S (transitionLE S hhk c) = eval S c := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, eval_transition, ih]

end TauCeti.AnalyticStage
