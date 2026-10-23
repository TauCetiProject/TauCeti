/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.MinimumCut.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Capping large capacities

Let `cap` be nonnegative capacities on a finite arrow family, and let `b` exceed the capacity of
some cut separating the terminal sets `A` and `B`. Capping every capacity at `b`, that is replacing
the capacities by `cap ⊓ fun _ _ _ ↦ b`, changes neither the minimum cut value nor the set of
minimum cuts. Arrows that must never cross a minimum cut can therefore be given a finite capacity
exceeding a known cut, rather than an infinite one.

Ordinary `s`–`t` flows behave compatibly. A flow of the capped network is a flow of the original
network with the same assignment, by `TauCeti.Flow.mono`. Conversely, removing the cycle
components of a decomposition of a flow of the original network gives a flow of the capped network
with the same value and an arrowwise no larger assignment. The cycle components cannot be kept in
general, since a cycle can carry more than `b`.

Nonnegativity of the capacities is needed: with arrows `s → a`, `a → t` and `s → t` of capacities
`2`, `1` and `-1`, capping at `1` makes `{s}` a minimum cut alongside `{s, a}`.

## Main results

* `TauCeti.min_arrowSum_le_arrowSum_inf`: capping a nonnegative assignment at `b` leaves every
  arrow sum at least the smaller of its original value and `b`.
* `TauCeti.isMinimum_arrowSum_inf_iff` and `TauCeti.minimumValue_arrowSum_inf`: capping
  preserves the minimum cuts and the minimum cut value.
* `TauCeti.PathCycleDecomposition.cappedFlow`: the path components of a decomposition of an
  ordinary flow of value at most `b`, as a flow of the capped network.
* `TauCeti.Flow.exists_flow_inf`: every flow of the original network gives a flow of the capped
  network of the same value with an arrowwise no larger assignment.
-/

public section

namespace TauCeti

open Finset TerminalCut

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w} [∀ x y, Fintype (Q x y)]

section ArrowSum

variable [AddCommMonoid K] [LinearOrder K] [IsOrderedAddMonoid K] {f : Assignment Q K} {b : K}

/-- Capping a nonnegative assignment at a nonnegative bound `b` leaves every arrow sum at least
the smaller of its original value and `b`. -/
theorem min_arrowSum_le_arrowSum_inf (hf : 0 ≤ f) (hb : 0 ≤ b) (S T : Finset V) :
    min (arrowSum f S T) b ≤ arrowSum (f ⊓ fun _ _ _ ↦ b) S T := by
  by_cases h : ∃ v ∈ S, ∃ w ∈ T, ∃ e : Q v w, b < f e
  · -- A single capped arrow already contributes `b`.
    obtain ⟨v, hv, w, hw, e, he⟩ := h
    refine (min_le_right _ _).trans ?_
    calc b = (f ⊓ fun _ _ _ ↦ b) e := by simp [he.le]
      _ ≤ _ := apply_le_arrowSum (le_inf hf fun _ _ _ ↦ hb) hv hw e
  · -- No arrow from `S` to `T` is capped.
    push Not at h
    refine (min_le_left _ _).trans (le_of_eq ?_)
    simp only [arrowSum_def]
    exact sum_congr rfl fun v hv ↦ sum_congr rfl fun w hw ↦ sum_congr rfl fun e _ ↦ by
      simp [h v hv w hw e]

/-- Capping a nonnegative assignment at a bound `b` does not change an arrow sum below `b`. -/
theorem arrowSum_inf_eq_of_lt (hf : 0 ≤ f) {S T : Finset V} (hb : arrowSum f S T < b) :
    arrowSum (f ⊓ fun _ _ _ ↦ b) S T = arrowSum f S T :=
  eq_of_le_of_min_le_of_lt (arrowSum_mono inf_le_left S T)
    (min_arrowSum_le_arrowSum_inf hf ((arrowSum_nonneg hf S T).trans hb.le) S T) hb

end ArrowSum

/-! ### Minimum cuts -/

section MinimumCut

variable [Fintype V] [DecidableEq V] [AddCommMonoid K] [LinearOrder K] [IsOrderedAddMonoid K]
  {cap : Assignment Q K} {b : K} {A B S₀ : Finset V}

/-- **Capping preserves minimum cuts.** For nonnegative capacities and a bound `b` exceeding the
capacity of some cut separating `A` from `B`, the capacities capped at `b` have the same minimum
cuts separating `A` from `B` as the original capacities. -/
theorem isMinimum_arrowSum_inf_iff (hcap : 0 ≤ cap) (hS₀ : IsAdmissible A B S₀)
    (hb : arrowSum cap S₀ S₀ᶜ < b) {S : Finset V} :
    IsMinimum (fun S ↦ arrowSum (cap ⊓ fun _ _ _ ↦ b) S Sᶜ) A B S ↔
      IsMinimum (fun S ↦ arrowSum cap S Sᶜ) A B S := by
  have hb₀ : 0 ≤ b := (arrowSum_nonneg hcap S₀ S₀ᶜ).trans hb.le
  exact isMinimum_iff_of_le_of_min_le (fun S ↦ arrowSum_mono inf_le_left S Sᶜ)
    (fun S ↦ min_arrowSum_le_arrowSum_inf hcap hb₀ S Sᶜ) hS₀ hb

/-- **Capping preserves the minimum cut value.** For nonnegative capacities and a bound `b`
exceeding the capacity of some cut separating `A` from `B`, the capacities capped at `b` have the
same minimum cut value as the original capacities. -/
theorem minimumValue_arrowSum_inf (hcap : 0 ≤ cap) (hAB : Disjoint A B)
    (hS₀ : IsAdmissible A B S₀) (hb : arrowSum cap S₀ S₀ᶜ < b) :
    minimumValue (fun S ↦ arrowSum (cap ⊓ fun _ _ _ ↦ b) S Sᶜ) hAB =
      minimumValue (fun S ↦ arrowSum cap S Sᶜ) hAB := by
  have hb₀ : 0 ≤ b := (arrowSum_nonneg hcap S₀ S₀ᶜ).trans hb.le
  exact minimumValue_eq_of_le_of_min_le hAB (fun S ↦ arrowSum_mono inf_le_left S Sᶜ)
    (fun S ↦ min_arrowSum_le_arrowSum_inf hcap hb₀ S Sᶜ) hS₀ hb

end MinimumCut

/-! ### Flows -/

variable [Fintype V] [AddCommGroup K] {cap : Assignment Q K} {s t : V} {b : K} {S : Finset V}

section Lattice

variable [Lattice K] [IsOrderedAddMonoid K]

/-- The path components of a decomposition of an ordinary `s`–`t` flow form an ordinary `s`–`t`
flow for the capacities capped at `b`, whenever the value of the flow is at most `b`: every arrow
carries at most the value of the flow. -/
noncomputable def PathCycleDecomposition.cappedFlow {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) (hb : f.val ≤ b) : Flow (cap ⊓ fun _ _ _ ↦ b) s t where
  toFun := D.pathAssignment
  mem_Icc := ⟨D.pathAssignment_nonneg, le_inf (D.pathAssignment_le.trans f.mem_Icc.2)
    fun _ _ e ↦ (D.pathAssignment_apply_le_val e).trans hb⟩
  conserve v hvs hvt := by rw [D.excessAt_pathAssignment]; exact f.conserve v hvs hvt
  excessAt_sink_nonneg := by rw [D.excessAt_pathAssignment]; exact f.excessAt_sink_nonneg

@[simp]
theorem PathCycleDecomposition.cappedFlow_toFun {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) (hb : f.val ≤ b) :
    (D.cappedFlow hb).toFun = D.pathAssignment :=
  (rfl)

/-- The path components of a decomposition of an ordinary flow, as a flow for the capped
capacities, have the value of the original flow. -/
@[simp]
theorem PathCycleDecomposition.val_cappedFlow {f : Flow cap s t}
    (D : PathCycleDecomposition f.toFun) (hb : f.val ≤ b) : (D.cappedFlow hb).val = f.val := by
  rw [BoundedFlow.val_def, BoundedFlow.val_def, cappedFlow_toFun, excessAt_pathAssignment]

end Lattice

/-- Every ordinary `s`–`t` flow gives an ordinary `s`–`t` flow of the same value with an arrowwise
no larger assignment for the capacities capped at `b`, whenever `b` exceeds the capacity of a cut
separating `s` from `t`. -/
theorem Flow.exists_flow_inf [DecidableEq V] [LinearOrder K] [IsOrderedAddMonoid K]
    (f : Flow cap s t) (hs : s ∈ S) (ht : t ∉ S) (hb : arrowSum cap S Sᶜ < b) :
    ∃ g : Flow (cap ⊓ fun _ _ _ ↦ b) s t, g.toFun ≤ f.toFun ∧ g.val = f.val := by
  obtain ⟨D⟩ := nonempty_pathCycleDecomposition (f := f.toFun) fun _ _ e ↦ f.nonneg e
  have hb' : f.val ≤ b := (f.val_le_arrowSum hs ht).trans hb.le
  exact ⟨D.cappedFlow hb', D.pathAssignment_le, D.val_cappedFlow hb'⟩

-- On `s = 0`, `a = 1` and `t = 2`, the arrows `s → t`, `a → t` and `t → a` have capacities `1`,
-- `5` and `5`, so the cut `{s}` has capacity `1`. The flow carrying `1` on `s → t` and `3` around
-- the cycle `a → t → a` has value `1`. Capping at `2` keeps a flow of value `1` below it, but not
-- the original assignment.
example :
    let cap : Assignment (fun _ _ : Fin 3 ↦ Unit) ℤ :=
      fun x y _ ↦ ![![0, 0, 1], ![0, 0, 5], ![0, 5, 0]] x y
    let f : Assignment (fun _ _ : Fin 3 ↦ Unit) ℤ :=
      fun x y _ ↦ ![![0, 0, 1], ![0, 0, 3], ![0, 3, 0]] x y
    ∃ F : Flow cap 0 2, F.toFun = f ∧ F.val = 1 ∧ arrowSum cap {0} {0}ᶜ = 1 ∧
      ¬f ≤ (cap ⊓ fun _ _ _ ↦ 2) ∧
      ∃ G : Flow (cap ⊓ fun _ _ _ ↦ 2) 0 2, G.toFun ≤ f ∧ G.val = 1 := by
  intro cap f
  let F : Flow cap 0 2 :=
    { toFun := f
      mem_Icc := ⟨fun x y _ ↦ by fin_cases x <;> fin_cases y <;> simp [f],
        fun x y _ ↦ by fin_cases x <;> fin_cases y <;> simp [f, cap]⟩
      conserve v hv₀ hv₂ := by
        fin_cases v <;> simp_all [f, excessAt_def, Fin.sum_univ_three]
      excessAt_sink_nonneg := by simp [f, excessAt_def, Fin.sum_univ_three] }
  have hF : F.val = 1 := by simp [F, BoundedFlow.val_def, f, excessAt_def, Fin.sum_univ_three]
  have hcut : arrowSum cap {0} {0}ᶜ = 1 := by
    rw [show ({0}ᶜ : Finset (Fin 3)) = {1, 2} by decide]
    simp [cap, arrowSum_def]
  obtain ⟨G, hGf, hG⟩ := F.exists_flow_inf (mem_singleton_self 0) (by decide) (b := 2)
    (by rw [hcut]; norm_num)
  refine ⟨F, rfl, hF, hcut, fun h ↦ ?_, G, hGf, hG.trans hF⟩
  have h₁₂ := h 1 2 ()
  simp [f, cap] at h₁₂

end TauCeti
