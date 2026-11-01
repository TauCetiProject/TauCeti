/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Colorings with small discrepancy on every test set

Let `p` be a probability distribution on a finite palette `κ`, and color the points of a finite
set `ι` independently at random according to `p`. For a set `T ⊆ ι` and a color `c`, the number
of points of `T` with color `c` has mean `p c * #T`, and by Hoeffding's inequality it deviates
from its mean by at least `a` with probability at most `2 * exp (-2 a² / #T)`. A union bound
over a finite family of test sets and over the palette therefore gives a single coloring whose
color counts are within `a` of their means on every test set, as soon as the number of tests
times the palette size times `2 * exp (-2 a² / N)` is less than one, where `N` bounds the sizes
of the test sets (`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`).

This is the probabilistic method for colorings of low discrepancy. It supplies quasi-random
colorings with prescribed color densities, for example colorings of the pairs between two vertex
sets in which every color has the same density on every large rectangle.

## Main results

* `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`: a coloring of `ι` whose color counts
  on every test set are within `a` of their means.

## Implementation notes

The random coloring is replaced by the weights `∏ e, p (x e)` on the colorings `x : ι → κ`, which
add up to one. The exponential moment of a color count factors over the points of `ι`
(`Fintype.prod_sum`), and each factor is bounded by Hoeffding's lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, applied to the indicator of
a color under the distribution `p`. Markov's inequality for the exponential moment is then a
comparison of finite sums, so no product measure on the colorings is needed.

## References

* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Theorem 13.1.1
  and Appendix A.
* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Amer.
  Statist. Assoc. 58 (1963), 13–30.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] {p : κ → ℝ}

/-- **Hoeffding's lemma for the indicator of a color.** If `p` is a probability distribution on
`κ`, the indicator of `c` minus its mean `p c` has exponential moments at most
`exp (θ ^ 2 / 8)`. -/
private theorem sum_mul_exp_mul_indicator_sub_le (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (c : κ) (θ : ℝ) :
    ∑ k, p k * exp (θ * ((if k = c then 1 else 0) - p c)) ≤ exp (θ ^ 2 / 8) := by
  let : MeasurableSpace κ := ⊤
  have : MeasurableSingletonClass κ := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  let q : PMF κ := PMF.ofFintype (fun k ↦ ENNReal.ofReal (p k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hp k, hp1, ENNReal.ofReal_one])
  have hint (f : κ → ℝ) : ∫ k, f k ∂q.toMeasure = ∑ k, p k * f k := by
    rw [PMF.integral_eq_sum]
    exact sum_congr rfl fun k _ ↦ by simp [q, ENNReal.toReal_ofReal (hp k)]
  set X : κ → ℝ := fun k ↦ (if k = c then 1 else 0) - p c with hX
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := q.toMeasure) (X := X) (a := -p c) (b := 1 - p c) measurable_from_top.aemeasurable
    (MeasureTheory.ae_of_all _ fun k ↦ by
      simp only [hX, Set.mem_Icc]
      split_ifs <;> constructor <;> linarith [hp c])
    (by
      rw [hint]
      simp only [hX, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq',
        mem_univ, ite_true, ← sum_mul, hp1, one_mul, sub_self])
  have h := hsub.mgf_le θ
  rw [ProbabilityTheory.mgf, hint] at h
  convert h using 2
  simp only [sub_neg_eq_add, sub_add_cancel, nnnorm_one, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat]
  ring

/-- The exponential moment of the deviation of a color count on `T` from its mean, under the
product weights `∏ e, p (x e)`, is at most `exp (θ ^ 2 * #T / 8)`. -/
private theorem sum_prod_mul_exp_le [Fintype ι] [DecidableEq ι] (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (T : Finset ι) (c : κ) (θ : ℝ) :
    ∑ x : ι → κ, (∏ e, p (x e)) *
        exp (θ * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c)) ≤ exp (θ ^ 2 * #T / 8) := by
  -- The summand is a product over the points of `ι`, so the sum factors over `ι`.
  have hfactor (x : ι → κ) : (∏ e, p (x e)) *
      exp (θ * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c)) =
        ∏ e, p (x e) * exp (if e ∈ T then θ * ((if x e = c then 1 else 0) - p c) else 0) := by
    rw [prod_mul_distrib, ← exp_sum, sum_ite_mem, univ_inter, mul_sum]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun e k ↦ p k * exp (if e ∈ T then θ * ((if k = c then 1 else 0) - p c)
    else 0))]
  calc ∏ e, ∑ k, p k * exp (if e ∈ T then θ * ((if k = c then 1 else 0) - p c) else 0)
      ≤ ∏ e, if e ∈ T then exp (θ ^ 2 / 8) else 1 := by
        refine prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun k _ ↦ mul_nonneg (hp k) (exp_pos _).le)
          fun e _ ↦ ?_
        split_ifs
        · exact sum_mul_exp_mul_indicator_sub_le hp hp1 c θ
        · simp [hp1]
    _ = exp (θ ^ 2 * #T / 8) := by
        rw [prod_ite_mem, univ_inter, prod_const, ← exp_nat_mul]
        ring_nf

/-- **Chernoff bound for a color count.** Under the product weights `∏ e, p (x e)`, the colorings
in which the number of points of `T` with color `c` exceeds its mean by at least `a > 0` (for
`σ = 1`), or falls short of it by at least `a` (for `σ = -1`), have total weight at most
`exp (-2 a² / N)` whenever `#T ≤ N`. -/
private theorem sum_prod_ite_le [Fintype ι] [DecidableEq ι] (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (T : Finset ι) (c : κ) {N : ℕ} (hT : #T ≤ N) {a : ℝ} (ha : 0 < a)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∑ x : ι → κ, (∏ e, p (x e)) *
        (if a ≤ σ * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c) then 1 else 0) ≤
      exp (-2 * a ^ 2 / N) := by
  have hw (x : ι → κ) : 0 ≤ ∏ e, p (x e) := prod_nonneg fun e _ ↦ hp (x e)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- All test sets are empty, so no coloring deviates.
    rw [Nat.le_zero, card_eq_zero] at hT
    subst hT
    simp [ha.not_ge]
  set θ : ℝ := 4 * a / N with hθ
  have hθ0 : 0 ≤ θ := by positivity
  -- Markov's inequality for the exponential moment, with parameter `θ = 4 a / N`.
  calc _ ≤ ∑ x : ι → κ, (∏ e, p (x e)) *
          exp (θ * (σ * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c) - a)) := by
        refine sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (hw x)
        split_ifs with h
        · exact one_le_exp (mul_nonneg hθ0 (sub_nonneg.2 h))
        · exact (exp_pos _).le
    _ = exp (-(θ * a)) * ∑ x : ι → κ, (∏ e, p (x e)) *
          exp (θ * σ * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c)) := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [mul_left_comm (exp _), ← exp_add]
        congr 2
        ring
    _ ≤ exp (-(θ * a)) * exp ((θ * σ) ^ 2 * #T / 8) :=
        mul_le_mul_of_nonneg_left (sum_prod_mul_exp_le hp hp1 T c _) (exp_pos _).le
    _ ≤ exp (-2 * a ^ 2 / N) := by
        rw [← exp_add, exp_le_exp, mul_pow, hσ, mul_one, hθ]
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        have hT' : (#T : ℝ) ≤ N := by exact_mod_cast hT
        have h₁ : (4 * a / N) ^ 2 * #T / 8 ≤ (4 * a / N) ^ 2 * N / 8 := by gcongr
        have h₂ : -(4 * a / N * a) + (4 * a / N) ^ 2 * N / 8 = -2 * a ^ 2 / N := by
          field_simp
          ring
        linarith

/-- **Two-sided Chernoff bound for a color count.** Under the product weights `∏ e, p (x e)`, the
colorings in which the number of points of `T` with color `c` deviates from its mean `p c * #T`
by at least `a > 0` have total weight at most `2 * exp (-2 a² / N)` whenever `#T ≤ N`. -/
private theorem sum_prod_ite_le_abs_le [Fintype ι] [DecidableEq ι] (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (T : Finset ι) (c : κ) {N : ℕ} (hT : #T ≤ N) {a : ℝ} (ha : 0 < a) :
    ∑ x : ι → κ, (∏ e, p (x e)) *
        (if a ≤ |(#{e ∈ T | x e = c} : ℝ) - p c * #T| then 1 else 0) ≤
      2 * exp (-2 * a ^ 2 / N) := by
  have h₁ := sum_prod_ite_le hp hp1 T c hT ha (σ := 1) (by norm_num)
  have h₂ := sum_prod_ite_le hp hp1 T c hT ha (σ := -1) (by norm_num)
  have hdev (x : ι → κ) : (#{e ∈ T | x e = c} : ℝ) - p c * #T =
      ∑ e ∈ T, ((if x e = c then 1 else 0) - p c) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm (#T : ℝ), ← sum_boole]
  -- A deviation of at least `a` is an excess or a shortfall of at least `a`.
  calc _ ≤ ∑ x : ι → κ, ((∏ e, p (x e)) *
          (if a ≤ 1 * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c) then 1 else 0) +
        (∏ e, p (x e)) *
          (if a ≤ -1 * ∑ e ∈ T, ((if x e = c then 1 else 0) - p c) then 1 else 0)) := by
        refine sum_le_sum fun x _ ↦ ?_
        rw [← mul_add, hdev]
        refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun e _ ↦ hp (x e))
        split_ifs with h <;> first | linarith | (rcases le_abs'.1 h with h' | h' <;> linarith)
    _ ≤ 2 * exp (-2 * a ^ 2 / N) := by
        rw [sum_add_distrib, two_mul]
        exact add_le_add h₁ h₂

/-- **Colorings with small discrepancy.** Let `p` be a probability distribution on a finite
palette `κ` and `T i ⊆ ι`, for `i` in a finite index type `I`, test sets of size at most `N`.
If `2 * card I * card κ * exp (-2 a² / N) < 1` for some `a > 0`, then some coloring `x : ι → κ`
has, on every test set `T i` and for every color `c`, a number of points of color `c` within
`a` of `p c * #(T i)`. -/
theorem exists_forall_abs_card_filter_sub_mul_card_lt [Finite ι] {I : Type*} [Fintype I]
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (T : I → Finset ι) {N : ℕ}
    (hT : ∀ i, #(T i) ≤ N) {a : ℝ} (ha : 0 < a)
    (h : 2 * Fintype.card I * Fintype.card κ * exp (-2 * a ^ 2 / N) < 1) :
    ∃ x : ι → κ, ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| < a := by
  classical
  have := Fintype.ofFinite ι
  by_contra! hbad
  have hterm (x : ι → κ) (i : I) (c : κ) : 0 ≤ (∏ e, p (x e)) *
      (if a ≤ |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| then 1 else 0) :=
    mul_nonneg (prod_nonneg fun e _ ↦ hp (x e)) (by split_ifs <;> norm_num)
  -- Every coloring has a large deviation on some test set, for some color.
  have hcover (x : ι → κ) : ∏ e, p (x e) ≤ ∑ i, ∑ c, (∏ e, p (x e)) *
      (if a ≤ |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| then 1 else 0) := by
    obtain ⟨i, c, hic⟩ := hbad x
    refine le_trans ?_ (single_le_sum (fun i _ ↦ sum_nonneg fun c _ ↦ hterm x i c) (mem_univ i))
    refine le_trans ?_ (single_le_sum (fun c _ ↦ hterm x i c) (mem_univ c))
    simp [hic]
  -- So the total weight one is at most the sum of the weights of the large deviations.
  refine h.not_ge ?_
  calc 1 = ∑ x : ι → κ, ∏ e, p (x e) := by
        rw [← Fintype.prod_sum (fun _ ↦ p), hp1, prod_const_one]
    _ ≤ ∑ x : ι → κ, ∑ i, ∑ c, (∏ e, p (x e)) *
          (if a ≤ |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| then 1 else 0) :=
        sum_le_sum fun x _ ↦ hcover x
    _ = ∑ i, ∑ c, ∑ x : ι → κ, (∏ e, p (x e)) *
          (if a ≤ |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| then 1 else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ sum_comm
    _ ≤ ∑ _i : I, ∑ _c : κ, 2 * exp (-2 * a ^ 2 / N) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun c _ ↦ sum_prod_ite_le_abs_le hp hp1 (T i) c (hT i) ha
    _ = 2 * Fintype.card I * Fintype.card κ * exp (-2 * a ^ 2 / N) := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring

end TauCeti
