/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Hoffman
public import TauCeti.Combinatorics.Network.MinimumCut.Residual
import Mathlib.Tactic.NormNum

/-!
# The interval of feasible bounded terminal values

For finite signed arrow bounds, the values of bounded terminal assignments form a closed,
attained interval. Its endpoints are certified by cuts: the largest value is the least upper
cut bound, and the smallest value is the greatest lower cut bound. The latter is characterized
by the absence of a positive residual path in the reverse terminal direction.

Hoffman's theorem realizes every intermediate value, without division or an Archimedean
hypothesis on the ordered coefficient group. When the bounds and the requested value belong to
an additive subgroup, the realizing assignment can be chosen in that subgroup. In particular,
subgroup-valued extrema exist even if the supplied feasible starting assignment is not
subgroup-valued. Values and bounds may all be negative.

## References

* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3 and Exercises 2.4–2.6.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Volume A, Chapter 10.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

namespace BoundedFlow

variable [LinearOrder K] [IsOrderedAddMonoid K]
variable {lo hi : Assignment Q K} {s t : V}

/-- **Subgroup-valued intermediate values.** Between any two feasible terminal values, every
value in an additive subgroup containing the bounds has a realizing assignment in that subgroup.
The endpoint assignments themselves need not take values in the subgroup. -/
theorem exists_val_eq_mem (f g : BoundedFlow lo hi s t)
    {q : K} (hfq : f.val ≤ q) (hqg : q ≤ g.val) (H : AddSubgroup K)
    (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H) (hhi : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H)
    (hq : q ∈ H) :
    ∃ h : BoundedFlow lo hi s t, h.val = q ∧ ∀ ⦃x y⦄ (e : Q x y), h.toFun e ∈ H := by
  classical
  let b : V → K := Pi.single t q - Pi.single s q
  have hsum (S : Finset V) : ∑ v ∈ S, b v =
      (if t ∈ S then q else 0) - (if s ∈ S then q else 0) := by
    simp [b, sum_sub_distrib, sum_pi_single']
  obtain ⟨h, hh⟩ := ExcessFlow.exists_mem_of_forall_cut (f.mem_Icc.1.trans f.mem_Icc.2)
    (b := b) (by simpa using hsum univ)
    (sum_single_sub_single_add_arrowSum_le f g hfq hqg) H hlo hhi (fun v ↦ by
      dsimp [b]
      exact H.sub_mem (by by_cases hv : v = t <;> simp [hv, hq])
        (by by_cases hv : v = s <;> simp [hv, hq]))
  refine ⟨⟨h.val, h.mem_Icc, fun v hvs hvt ↦ ?_⟩, ?_, hh⟩
  · rw [h.excessAt_eq]
    simp [b, hvs, hvt]
  · rw [val_def, h.excessAt_eq]
    by_cases hst : s = t
    · have hq0 : q = 0 := le_antisymm (hqg.trans (g.val_eq_zero_of_eq hst).le)
        ((f.val_eq_zero_of_eq hst).ge.trans hfq)
      simp [b, hq0]
    · simp [b, Ne.symm hst]

/-- Every value between two feasible bounded terminal values is feasible. -/
theorem exists_val_eq (f g : BoundedFlow lo hi s t) {q : K}
    (hfq : f.val ≤ q) (hqg : q ≤ g.val) : ∃ h : BoundedFlow lo hi s t, h.val = q := by
  obtain ⟨h, hh, -⟩ := exists_val_eq_mem f g hfq hqg ⊤
    (fun _ _ _ ↦ AddSubgroup.mem_top _) (fun _ _ _ ↦ AddSubgroup.mem_top _)
    (AddSubgroup.mem_top _)
  exact ⟨h, hh⟩

/-- Minimum and maximum assignments are the endpoints of the entire interval of feasible
terminal values. -/
theorem range_val_eq_Icc {f g : BoundedFlow lo hi s t}
    (hf : f.IsMinimum) (hg : g.IsMaximum) :
    Set.range (val : BoundedFlow lo hi s t → K) = Set.Icc f.val g.val := by
  ext q
  exact ⟨fun ⟨h, hh⟩ ↦ hh ▸ ⟨isMinimum_iff.1 hf h, isMaximum_iff.1 hg h⟩,
    fun hq ↦ exists_val_eq f g hq.1 hq.2⟩

/-- The feasible values are precisely the interval between the two directed minimum-cut
bounds. The left endpoint uses the minimum upper cut bound with the terminals exchanged. -/
theorem range_val_eq_Icc_pairMinimumValue [DecidableEq V] (hst : s ≠ t)
    (f : BoundedFlow lo hi s t) :
    Set.range (val : BoundedFlow lo hi s t → K) =
      Set.Icc (-TerminalCut.pairMinimumValue (cutBound lo hi) t s)
        (TerminalCut.pairMinimumValue (cutBound lo hi) s t) := by
  obtain ⟨m, hm⟩ := f.exists_isMinimum
  obtain ⟨M, hM⟩ := f.exists_isMaximum
  rw [range_val_eq_Icc hm hM, hM.val_eq_pairMinimumValue hst]
  have hmval := ((isMaximum_swap m).2 hm).val_eq_pairMinimumValue hst.symm
  rw [← neg_neg m.val, ← val_swap, hmval]

/-- **Integral extrema without an integral starting assignment.** If the bounds take values
in an additive subgroup, a feasible bounded terminal problem has both minimum and maximum
assignments in that subgroup. -/
theorem exists_isMinimum_isMaximum_mem (f : BoundedFlow lo hi s t) (H : AddSubgroup K)
    (hlo : ∀ ⦃x y⦄ (e : Q x y), lo e ∈ H) (hhi : ∀ ⦃x y⦄ (e : Q x y), hi e ∈ H) :
    ∃ m M : BoundedFlow lo hi s t, m.IsMinimum ∧ M.IsMaximum ∧
      (∀ ⦃x y⦄ (e : Q x y), m.toFun e ∈ H) ∧ ∀ ⦃x y⦄ (e : Q x y), M.toFun e ∈ H := by
  classical
  by_cases hst : s = t
  · obtain ⟨g, -, hg⟩ := exists_val_eq_mem f f le_rfl le_rfl H hlo hhi
      (by simp [f.val_eq_zero_of_eq hst])
    exact ⟨g, g, isMinimum_of_eq hst g, isMaximum_of_eq hst g, hg, hg⟩
  have hcut (S : Finset V) : cutBound lo hi S ∈ H := by
    rw [cutBound_def]
    exact H.sub_mem (arrowSum_mem hhi S Sᶜ) (arrowSum_mem hlo Sᶜ S)
  obtain ⟨m, hm⟩ := f.exists_isMinimum
  obtain ⟨M, hM⟩ := f.exists_isMaximum
  obtain ⟨S, -, -, hS⟩ := hm.exists_val_eq_neg_cutBound_compl hst
  obtain ⟨T, -, -, hT⟩ := hM.exists_val_eq_cutBound hst
  obtain ⟨m', hm', hmH⟩ := exists_val_eq_mem m m le_rfl le_rfl H hlo hhi
    (hS ▸ H.neg_mem (hcut Sᶜ))
  obtain ⟨M', hM', hMH⟩ := exists_val_eq_mem M M le_rfl le_rfl H hlo hhi (hT ▸ hcut T)
  exact ⟨m', M', isMinimum_iff.2 (fun g ↦ hm' ▸ isMinimum_iff.1 hm g),
    isMaximum_iff.2 (fun g ↦ hM' ▸ isMaximum_iff.1 hM g), hmH, hMH⟩

end BoundedFlow

/-!
## A negative feasible interval

There is one arrow for each ordered pair of Boolean vertices. Only the arrow `false → true`
can carry a nonzero value; its bounds are `[-5, -2]`. The entire feasible interval is negative.
The subgroup example realizes an integer value between two nonintegral feasible values.
-/

private abbrev ValueExampleHom (_ _ : Bool) : Type := Unit

private def valueExampleLower : Assignment ValueExampleHom ℚ :=
  fun x y _ ↦ if x = false ∧ y = true then -5 else 0

private def valueExampleUpper : Assignment ValueExampleHom ℚ :=
  fun x y _ ↦ if x = false ∧ y = true then -2 else 0

private def valueExampleFlow (q : ℚ) (hq : q ∈ Set.Icc (-5 : ℚ) (-2)) :
    BoundedFlow valueExampleLower valueExampleUpper false true where
  toFun x y _ := if x = false ∧ y = true then q else 0
  mem_Icc := by
    constructor <;> intro x y e <;>
      dsimp [valueExampleLower, valueExampleUpper] <;> split_ifs <;> simp_all
  conserve v hfalse htrue := by cases v <;> contradiction

private theorem valueExampleFlow_val (q : ℚ) (hq : q ∈ Set.Icc (-5 : ℚ) (-2)) :
    (valueExampleFlow q hq).val = q := by
  simp [BoundedFlow.val_def, excessAt_def, valueExampleFlow]

private theorem valueExampleFlow_isMinimum :
    (valueExampleFlow (-5) (by norm_num)).IsMinimum := by
  apply (valueExampleFlow (-5) (by norm_num)).isMinimum_of_val_eq_neg_cutBound_compl
    (S := {false}) (by simp) (by simp)
  simp [valueExampleFlow_val, cutBound_def, arrowSum_eq_sum_ite,
    valueExampleLower, valueExampleUpper]

private theorem valueExampleFlow_isMaximum :
    (valueExampleFlow (-2) (by norm_num)).IsMaximum := by
  apply (valueExampleFlow (-2) (by norm_num)).isMaximum_of_val_eq_cutBound
    (S := {false}) (by simp) (by simp)
  simp [valueExampleFlow_val, cutBound_def, arrowSum_eq_sum_ite,
    valueExampleLower, valueExampleUpper]

example : Set.range (BoundedFlow.val :
    BoundedFlow valueExampleLower valueExampleUpper false true → ℚ) = Set.Icc (-5) (-2) := by
  simpa only [valueExampleFlow_val] using
    BoundedFlow.range_val_eq_Icc valueExampleFlow_isMinimum valueExampleFlow_isMaximum

example : ¬PositiveReachable
    (residualCapacity valueExampleLower valueExampleUpper
      (valueExampleFlow (-5) (by norm_num)).toFun)
    true false :=
  (BoundedFlow.isMinimum_iff_not_positiveReachable (by decide) _).1 valueExampleFlow_isMinimum

example : ∃ h : BoundedFlow valueExampleLower valueExampleUpper false true,
    h.val = -3 ∧ ∀ ⦃x y⦄ (e : ValueExampleHom x y),
      h.toFun e ∈ AddSubgroup.zmultiples (1 : ℚ) := by
  refine BoundedFlow.exists_val_eq_mem
    (valueExampleFlow (-9 / 2) (by norm_num)) (valueExampleFlow (-5 / 2) (by norm_num))
    (by norm_num [valueExampleFlow_val]) (by norm_num [valueExampleFlow_val])
    (AddSubgroup.zmultiples (1 : ℚ)) ?_ ?_ ?_
  · intro x y e
    dsimp [valueExampleLower]
    split_ifs
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-5, by norm_num⟩
    · exact AddSubgroup.zero_mem _
  · intro x y e
    dsimp [valueExampleUpper]
    split_ifs
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-2, by norm_num⟩
    · exact AddSubgroup.zero_mem _
  · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-3, by norm_num⟩

end TauCeti
