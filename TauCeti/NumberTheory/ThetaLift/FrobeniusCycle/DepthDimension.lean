/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Antidiag.ProductMoment
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
import Mathlib.Tactic.Positivity
import TauCeti.LinearAlgebra.Submodule.WeightedCoordinates

/-!
# Counting dimensions from deep monomials

For a Frobenius cycle, a variable in the deep part has weight `P⁻¹` below row `2r`
and weight `P⁻²ʳ` from row `2r` onwards. For a fixed letter at most `r` variables carry
weight `P⁻¹`. This and the mean exponent in each block of a multihomogeneous monomial
bound the sum of dimensions once the existence of a sufficiently costly monomial
has been established at each depth.

The dimension estimate is the counting step of `New.FrobeniusCycle.sum_finrank_deepForms_le`
in `grh/src/New/UpperBound/ElementaryDivisors/Depth.lean` of lsernau/grh-lean at `72fead1`.
-/

public noncomputable section

open Finset Module

namespace TauCeti.FrobeniusCycle

variable {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R]
    {N k n : ℕ}

/-- The cost of a variable for the dimension estimate at depth cut `r`. -/
def depthWeight (T : FrobeniusCycle W R N) (r : ℕ) (x : Fin k × ZMod N) : ℝ :=
  if T.IsDeep r x then
    if 2 * r ≤ x.1.val then ((T.P : ℝ) ^ (2 * r))⁻¹ else (T.P : ℝ)⁻¹
  else 0

/-- Non-deep variables contribute zero; the deep part is split at row `2r`. -/
theorem depthWeight_def (T : FrobeniusCycle W R N) (r : ℕ) (x : Fin k × ZMod N) :
    T.depthWeight r x = if T.IsDeep r x then
      if 2 * r ≤ x.1.val then ((T.P : ℝ) ^ (2 * r))⁻¹ else (T.P : ℝ)⁻¹
    else 0 := (rfl)

/-- All costs in the depth dimension estimate are nonnegative. -/
theorem depthWeight_nonneg (T : FrobeniusCycle W R N) (r : ℕ) (x : Fin k × ZMod N) :
    0 ≤ T.depthWeight r x := by
  rw [depthWeight_def]
  split_ifs <;> positivity

private theorem card_short_deep (T : FrobeniusCycle W R N) (r : ℕ) (s : ZMod N) :
    #(univ.filter fun b : Fin k ↦ T.IsDeep r (b, s) ∧ b.val < 2 * r) ≤ r := by
  let A := univ.filter fun b : Fin k ↦ T.IsDeep r (b, s) ∧ b.val < 2 * r
  have hcard : #A ≤ #(range r) := by
    cases hs : T.isEven s
    · refine card_le_card_of_injOn Fin.val ?_ (fun _ _ _ _ he ↦ Fin.ext he)
      intro b hb
      have hb' := (mem_filter.mp hb).2.1
      simpa [isDeep_iff, hs] using hb'
    · refine card_le_card_of_injOn (fun b : Fin k ↦ b.val - r) ?_ ?_
      · intro b hb
        obtain ⟨hb₁, hb₂⟩ := (mem_filter.mp hb).2
        have hb₁' : r ≤ b.val := by simpa [isDeep_iff, hs] using hb₁
        exact mem_range.mpr (by dsimp; omega)
      · intro b hb c hc he
        have hb' : r ≤ b.val := by simpa [isDeep_iff, hs] using (mem_filter.mp hb).2.1
        have hc' : r ≤ c.val := by simpa [isDeep_iff, hs] using (mem_filter.mp hc).2.1
        dsimp at he
        exact Fin.ext (by omega)
  simpa only [card_range] using hcard

/-- The weights in one letter sum to at most `k/P^(2r) + r/P`: only `r` variables can have
weight `P⁻¹` on the deep side below row `2r`. -/
theorem sum_depthWeight_le (T : FrobeniusCycle W R N) (r : ℕ) (s : ZMod N) :
    ∑ b : Fin k, T.depthWeight r (b, s) ≤
      k / (T.P : ℝ) ^ (2 * r) + r / (T.P : ℝ) := by
  let A := univ.filter fun b : Fin k ↦ T.IsDeep r (b, s) ∧ b.val < 2 * r
  calc
    _ ≤ ∑ b : Fin k, (((T.P : ℝ) ^ (2 * r))⁻¹ + if b ∈ A then (T.P : ℝ)⁻¹ else 0) := by
      refine sum_le_sum fun b _ ↦ ?_
      simp only [depthWeight_def, A, mem_filter, mem_univ, true_and]
      have h₂ : 0 ≤ ((T.P : ℝ) ^ (2 * r))⁻¹ := by positivity
      by_cases hd : T.IsDeep r (b, s)
      · by_cases hb : 2 * r ≤ b.val
        · simp only [hd, hb, not_lt.mpr hb, true_and, ite_true, ite_false, add_zero, le_refl]
        · simp only [hd, hb, Nat.lt_of_not_ge hb, true_and, ite_true, ite_false]
          exact le_add_of_nonneg_left h₂
      · simp only [hd, false_and, ite_false, add_zero]
        exact h₂
    _ = k / (T.P : ℝ) ^ (2 * r) + (A.card : ℝ) / (T.P : ℝ) := by
      simp [sum_add_distrib, A, ← sum_filter, div_eq_mul_inv]
    _ ≤ _ := by gcongr; exact_mod_cast T.card_short_deep (k := k) r s

/-- Bound the sum of dimensions of subspaces of forms of degree `n` in each letter. The input
at threshold `d` is that every nonzero form has a nonzero coefficient of cost at least `d`.
The equivalence `e` lets the coefficients use any indexing of these multihomogeneous monomials.
The bound uses `r/(kP)` rather than `r²/(kP)`, and does not require `2r ≤ k`. -/
theorem sum_finrank_le_of_depthWeight {K ι : Type*} [DivisionRing K] [Fintype ι] [NeZero N]
    (T : FrobeniusCycle W R N) (r : ℕ) {M : ℕ}
    (e : ι ≃ (ZMod N → ↥((univ : Finset (Fin k)).finsuppAntidiag n)))
    (U : ℕ → Submodule K (ι → K))
    (h : ∀ d ∈ Icc 1 M, ∀ v ∈ U d, v ≠ 0 → ∃ i, v i ≠ 0 ∧
      (d : ℝ) ≤ ∑ s : ZMod N, ∑ b : Fin k, (((e i) s).val b : ℝ) * T.depthWeight r (b, s)) :
    ∑ d ∈ Icc 1 M, (finrank K (U d) : ℝ) ≤
      (N : ℝ) * n * (((T.P : ℝ) ^ (2 * r))⁻¹ + r / (k * (T.P : ℝ))) * Fintype.card ι := by
  classical
  let w (i : ι) := ∑ s : ZMod N, ∑ b : Fin k, (((e i) s).val b : ℝ) * T.depthWeight r (b, s)
  refine (Submodule.sum_finrank_le_sum_of_exists_le_weight U w ?_ ?_).trans ?_
  · exact fun i ↦ sum_nonneg fun s _ ↦ sum_nonneg fun b _ ↦
      mul_nonneg (Nat.cast_nonneg _) (T.depthWeight_nonneg r (b, s))
  · exact fun d hd v hv hv₀ ↦ Exists.imp (fun _ he ↦ he.symm) (h d hd v hv hv₀)
  obtain rfl | hk := k.eq_zero_or_pos
  · simp only [w, Finset.univ_eq_empty, sum_empty, sum_const_zero, Nat.cast_zero, zero_mul,
      div_zero, add_zero]
    positivity
  have hm (s : ZMod N) (b : Fin k) :
      ∑ i, (((e i) s).val b : ℝ) = (n * Fintype.card ι : ℝ) / k := by
    apply (eq_div_iff (by positivity : (k : ℝ) ≠ 0)).2
    rw [mul_comm, Fintype.sum_equiv e _ (fun v ↦ ((v s).val b : ℝ)) (fun _ ↦ rfl),
      Fintype.card_congr e]
    have hmoment := Finset.card_mul_sum_pi_finsuppAntidiag_apply
      (fun _ : ZMod N ↦ (univ : Finset (Fin k))) (fun _ ↦ n) s (mem_univ b)
    rw [card_univ, Fintype.card_fin] at hmoment
    exact_mod_cast hmoment
  calc
    ∑ i, w i = ∑ s : ZMod N, ((n * Fintype.card ι : ℝ) / k) *
        ∑ b : Fin k, T.depthWeight r (b, s) := by
      simp only [w]
      rw [sum_comm]
      refine sum_congr rfl fun s _ ↦ ?_
      rw [sum_comm, mul_sum]
      simp only [← sum_mul, hm]
    _ ≤ ∑ _ : ZMod N, ((n * Fintype.card ι : ℝ) / k) *
        (k / (T.P : ℝ) ^ (2 * r) + r / (T.P : ℝ)) := by
      exact sum_le_sum fun s _ ↦
        mul_le_mul_of_nonneg_left (T.sum_depthWeight_le r s) (by positivity)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card]
      have hP : 0 < (T.P : ℝ) := Nat.cast_pos.mpr ((by decide : 0 < 5).trans_le T.five_le_P)
      have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      field_simp [hP.ne', hk'.ne']

end TauCeti.FrobeniusCycle
