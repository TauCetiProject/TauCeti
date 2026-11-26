/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
import TauCeti.Probability.Distributions.Uniform.Finite.Hoeffding
import TauCeti.Algebra.Order.Antidiag.Moments

/-!
# Weighted support counts for multihomogeneous polynomials

A uniformly chosen monomial of fixed multidegree has independent exponent vectors in its
blocks. In each block, weighting the normalized exponents gives a random convex combination
of the weights with mean equal to their arithmetic mean. Hoeffding's inequality then bounds
the number of high-weight monomials, uniformly in the positive block degrees.
The mean calculation uses `Finset.card_mul_sum_finsuppAntidiag_apply` via
`TauCeti.mean_normalized_sum_finsuppAntidiag`, and the concentration step uses
`TauCeti.Probability.ncard_setOf_sum_sub_mean_ge_le_card_mul_exp`.

In Evertse and Ferretti's auxiliary-polynomial construction, each high-weight monomial in a
specified coordinate system imposes one linear condition on the polynomial's coefficients.
The simultaneous count bounds the number of equations over all the coordinate systems.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace theorem*,
  Ann. of Math. 177 (2013), §13, Lemma 13.3 and the equation count in Lemma 13.5.
-/

public section

open Finset Real

open MvPolynomial

namespace TauCeti

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- The monomials whose total normalized weight exceeds the sum of the block means by more than
`Fintype.card κ * γ * ε` form a fraction at most `exp (-card κ * ε² / 2)` of the multidegree
monomials. The weights in each block may vary independently, with absolute values at most `γ`. -/
theorem card_filter_multiMons_weight_gt_le [DecidableEq κ] [DecidableEq ι] [Nonempty ι]
    {r : κ → ℕ} (hr : ∀ h, 0 < r h) {w : κ → ι → ℝ} {γ ε : ℝ}
    (hγ : 0 ≤ γ) (hw : ∀ h i, |w h i| ≤ γ) (hε : 0 ≤ ε) :
    (#{n ∈ multiMons ι r | (∑ h, (∑ i, w h i) / Fintype.card ι) +
        Fintype.card κ * γ * ε < n.weight (fun p ↦ w p.1 p.2 / r p.1)} : ℝ) ≤
      #(multiMons ι r) * exp (-(Fintype.card κ : ℝ) * ε ^ 2 / 2) := by
  classical
  rcases hγ.eq_or_lt with rfl | hγ
  · have hw₀ h i : w h i = 0 := abs_nonpos_iff.mp (hw h i)
    simp only [hw₀, Finsupp.weight_prod_eq_sum, smul_zero, sum_const_zero, zero_div,
      mul_zero, zero_mul, add_zero, lt_self_iff_false, filter_false, card_empty, Nat.cast_zero]
    positivity
  let S (h : κ) := (univ : Finset ι).finsuppAntidiag (r h)
  let X (h : κ) (n : S h) := (∑ i, (n.val i : ℝ) * w h i) / r h
  have hx (h : κ) (n : S h) : X h n ∈ Set.Icc (-γ) γ := by
    have hsum : ∑ i, (n.val i : ℝ) = r h := by
      exact_mod_cast (mem_finsuppAntidiag.1 n.property).1
    have hmass : 0 < ∑ i, (n.val i : ℝ) := hsum.symm ▸ Nat.cast_pos.2 (hr h)
    simpa [X, Finset.centerMass, hsum, div_eq_inv_mul] using
      (convex_Icc (-γ) γ).centerMass_mem (fun i _ ↦ Nat.cast_nonneg (n.val i))
        hmass (fun i _ ↦ abs_le.mp (hw h i))
  have hmean (h : κ) : (∑ y, X h y) / Fintype.card (S h) =
      (∑ i, w h i) / Fintype.card ι :=
    mean_normalized_sum_finsuppAntidiag (hr h) (w h)
  have htail := Probability.ncard_setOf_sum_sub_mean_ge_le_card_mul_exp X hx
    (t := Fintype.card κ * γ * ε) (by positivity)
  simp only [hmean] at htail
  let e : (∀ h, S h) ≃ multiMons ι r := multiMonsEquiv r
  have he (x : ∀ h, S h) :
      (e x).val.weight (fun p ↦ w p.1 p.2 / r p.1) = ∑ h, X h (x h) := by
    simp only [e, Finsupp.weight_prod_eq_sum, multiMonsEquiv_apply, nsmul_eq_mul,
      X, sum_div, mul_div_assoc]
  refine le_trans ?_ (htail.trans_eq ?_)
  · apply Nat.cast_le.2
    let bad := (multiMons ι r).filter fun n ↦ (∑ h, (∑ i, w h i) / Fintype.card ι) +
      Fintype.card κ * γ * ε < n.weight (fun p ↦ w p.1 p.2 / r p.1)
    have hbad : #bad = Nat.card bad := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hbad, ← Nat.card_coe_set_eq]
    let f (n : bad) := e.symm ⟨n.val, (mem_filter.1 n.property).1⟩
    have hf (n : bad) : (Fintype.card κ : ℝ) * γ * ε ≤
        ∑ h, (X h (f n h) - (∑ i, w h i) / Fintype.card ι) := by
      have hvalue := he (f n)
      simp only [f, Equiv.apply_symm_apply] at hvalue
      rw [sum_sub_distrib, ← hvalue, le_sub_iff_add_le, add_comm]
      exact (mem_filter.1 n.property).2.le
    refine Nat.card_le_card_of_injective (fun n ↦ ⟨f n, hf n⟩) fun n m h ↦ ?_
    have heq := e.symm.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg (fun n : multiMons ι r ↦ n.val) heq)
  · rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    congr 2
    rw [sum_const, card_univ, nsmul_eq_mul]
    by_cases hk : Fintype.card κ = 0
    · simp [hk]
    · have hk' : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      field_simp [hk', hγ.ne']
      ring

/-- The high-weight conditions in several coordinate systems occupy at most half the monomial
count if the number of systems is small enough relative to the number of blocks.
An individual threshold may be any upper bound for the corresponding mean plus the deviation. -/
theorem two_mul_sum_card_filter_multiMons_weight_gt_le [DecidableEq κ] [DecidableEq ι]
    [Nonempty ι] {ν : Type*} [Fintype ν] {r : κ → ℕ} (hr : ∀ h, 0 < r h)
    {w : ν → κ → ι → ℝ} {γ θ : ν → ℝ} {ε : ℝ}
    (hγ : ∀ v, 0 ≤ γ v) (hw : ∀ v h i, |w v h i| ≤ γ v) (hε : 0 ≤ ε)
    (hθ : ∀ v, (∑ h, (∑ i, w v h i) / Fintype.card ι) +
      Fintype.card κ * γ v * ε ≤ θ v)
    (hbudget : 2 * (Fintype.card ν : ℝ) ≤ exp (Fintype.card κ * ε ^ 2 / 2)) :
    2 * (∑ v, #{n ∈ multiMons ι r | θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1)}) ≤
      #(multiMons ι r) := by
  classical
  let B (v : ν) := (multiMons ι r).filter fun n ↦ θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1)
  have hcount (v : ν) : (#(B v) : ℝ) ≤
      #(multiMons ι r) * exp (-(Fintype.card κ : ℝ) * ε ^ 2 / 2) := by
    refine le_trans (Nat.cast_le.2 <| card_le_card ?_) <|
      card_filter_multiMons_weight_gt_le hr (hγ v) (hw v) hε
    exact monotone_filter_right _ fun _ _ hn ↦ (hθ v).trans_lt hn
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  calc
    2 * ∑ v, (#(B v) : ℝ) ≤
        2 * ∑ _v : ν, (#(multiMons ι r) : ℝ) * exp (-(Fintype.card κ : ℝ) * ε ^ 2 / 2) := by
      gcongr with v
      exact hcount v
    _ ≤ #(multiMons ι r) := by
      rw [sum_const, card_univ, nsmul_eq_mul, neg_mul, neg_div, exp_neg]
      calc
        _ = (#(multiMons ι r) : ℝ) *
            (2 * Fintype.card ν / exp (Fintype.card κ * ε ^ 2 / 2)) := by ring
        _ ≤ _ := mul_le_of_le_one_right (Nat.cast_nonneg _)
          (div_le_one_of_le₀ hbudget (exp_pos _).le)

end TauCeti
