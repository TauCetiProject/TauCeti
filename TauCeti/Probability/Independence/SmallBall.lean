/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tensorization of small-ball probabilities

Suppose that random vectors `ζ k`, indexed by a finite type of cardinality `n` and possibly
taking values in different spaces, have independent norms and all satisfy a small-ball bound that
is linear in the radius at every radius `r ≥ ε`: `P(‖ζ k‖ < r) ≤ K r + a`. Then the probability
that the sum of their squared norms is less than `ε ^ 2 * n` is bounded by an `n`-th power:
`P(∑ k, ‖ζ k‖ ^ 2 < ε ^ 2 * n) ≤ (2 e (2 K ε + a)) ^ n`.
For fixed parameters with `2 e (2 K ε + a) < 1`, the bound decays exponentially in `n`.

For `a = 0` this is the tensorization lemma of Rudelson and Vershynin, stated there for the
independent nonnegative random variables `‖ζ k‖`; requiring the
small-ball bound only at radii `r ≥ ε` recovers their lower threshold `ε₀`. The additive term `a`
absorbs radius-independent error terms of small-ball estimates, such as the term `C / D` for a
lower bound `D` on the least common denominator of the coefficients.

The application to the image of a fixed vector under a matrix with independent rows is in
`TauCeti.Probability.RandomMatrix.SmallBall`.

The bound assumes only independence of the norms, not measurability, so it holds for outer
probabilities of arbitrary random vectors, which need not themselves be independent.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_sum_norm_sq_lt_le`: tensorization of small-ball
  bounds for random vectors with independent norms.
* `ProbabilityTheory.iIndepFun.measureReal_sum_norm_sq_lt_le'`: the same bound for independent
  random vectors.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 2.2.
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} {E : ι → Type*} [MeasurableSpace Ω] [Fintype ι]
  [∀ k, SeminormedAddCommGroup (E k)] {P : Measure Ω} {ζ : ∀ k, Ω → E k}

omit [MeasurableSpace Ω] in
/-- An outcome with `∑ k, ‖ζ k ω‖ ^ 2 < ε ^ 2 * n` lies in a product of balls of radii
`(j k + 1) * ε`, for a grid point `j` with `∑ k, j k ^ 2 < n` and coordinates below `n`. -/
private theorem setOf_sum_norm_sq_lt_subset_iUnion [DecidableEq ι] {ε : ℝ} (hε : 0 ≤ ε) :
    {ω | ∑ k, ‖ζ k ω‖ ^ 2 < ε ^ 2 * Fintype.card ι} ⊆
      ⋃ j ∈ (Fintype.piFinset fun _ : ι ↦ range (Fintype.card ι)).filter
          (fun j ↦ ∑ k, j k ^ 2 < Fintype.card ι),
        ⋂ k, {ω | ‖ζ k ω‖ < (j k + 1) * ε} := by
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  rcases hε.eq_or_lt with rfl | hε
  · rw [zero_pow two_ne_zero, zero_mul] at hω
    exact absurd hω (sum_nonneg fun k _ ↦ sq_nonneg _).not_gt
  let j (k : ι) : ℕ := ⌊‖ζ k ω‖ / ε⌋₊
  have hlt (k : ι) : ‖ζ k ω‖ < (j k + 1) * ε :=
    (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one _)
  have hle (k : ι) : (j k : ℝ) * ε ≤ ‖ζ k ω‖ :=
    (le_div_iff₀ hε).mp (Nat.floor_le (by positivity))
  have hsum : ∑ k, j k ^ 2 < Fintype.card ι := by
    have hsq : ε ^ 2 * ∑ k, (j k : ℝ) ^ 2 < ε ^ 2 * Fintype.card ι := calc
      ε ^ 2 * ∑ k, (j k : ℝ) ^ 2 = ∑ k, ((j k : ℝ) * ε) ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ ↦ by ring
      _ ≤ ∑ k, ‖ζ k ω‖ ^ 2 :=
        sum_le_sum fun k _ ↦ pow_le_pow_left₀ (by positivity) (hle k) 2
      _ < ε ^ 2 * Fintype.card ι := hω
    exact_mod_cast lt_of_mul_lt_mul_left hsq (sq_nonneg ε)
  simp only [Set.mem_iUnion, Set.mem_iInter, mem_filter, Fintype.mem_piFinset, mem_range,
    Set.mem_ofPred_eq, exists_prop]
  refine ⟨j, ⟨fun k ↦ ?_, hsum⟩, hlt⟩
  calc j k ≤ j k ^ 2 := Nat.le_self_pow two_ne_zero _
    _ ≤ ∑ k, j k ^ 2 :=
      single_le_sum (f := fun k ↦ j k ^ 2) (fun _ _ ↦ Nat.zero_le _) (mem_univ k)
    _ < Fintype.card ι := hsum

omit [MeasurableSpace Ω] [∀ k, SeminormedAddCommGroup (E k)] in
/-- The grid sum of products of the radius bounds `K * ((i + 1) * ε) + a` over grid points
`j` with `∑ k, j k ^ 2 < n` is at most `(2 e (2 K ε + a)) ^ n`. -/
private theorem sum_filter_prod_le [DecidableEq ι] {ε K a : ℝ}
    (hb : ∀ i : ℕ, 0 ≤ K * ((i + 1) * ε) + a) :
    ∑ j ∈ (Fintype.piFinset fun _ : ι ↦ range (Fintype.card ι)).filter
        (fun j ↦ ∑ k, j k ^ 2 < Fintype.card ι), ∏ k, (K * ((j k + 1) * ε) + a) ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card ι := by
  set n := Fintype.card ι
  set b : ℕ → ℝ := fun i ↦ K * ((i + 1) * ε) + a
  -- Since `b` is affine, `2⁻ⁱ b i = F i - F (i + 1)` for `F i = 2 * 2⁻ⁱ b (i + 1)`.
  set F : ℕ → ℝ := fun i ↦ 2 * (1 / 2) ^ i * b (i + 1)
  have hexp (i : ℕ) : Real.exp (-(i : ℝ) ^ 2) ≤ (1 / 2) ^ i := calc
    Real.exp (-(i : ℝ) ^ 2) ≤ Real.exp (i * (-1)) := by
      have : (i : ℝ) ≤ (i : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero i
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-1) ^ i := Real.exp_natCast_mul i _
    _ ≤ (1 / 2) ^ i := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le i
  have hfactor : ∑ i ∈ range n, Real.exp (-(i : ℝ) ^ 2) * b i ≤ 2 * b 1 := calc
    _ ≤ ∑ i ∈ range n, (1 / 2 : ℝ) ^ i * b i :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hexp i) (hb i)
    _ = F 0 - F n := by
      rw [← sum_range_sub']
      refine sum_congr rfl fun i _ ↦ ?_
      push_cast [F, b]
      ring
    _ ≤ F 0 := sub_le_self _ (mul_nonneg (by positivity) (hb (n + 1)))
    _ = 2 * b 1 := by simp [F]
  calc
    _ ≤ ∑ j ∈ Fintype.piFinset fun _ : ι ↦ range n,
          Real.exp (n - ∑ k, (j k : ℝ) ^ 2) * ∏ k, b (j k) := by
      refine (sum_le_sum fun j hj ↦ ?_).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ ↦ ?_)
      · have : ∑ k, (j k : ℝ) ^ 2 < n := by exact_mod_cast (mem_filter.mp hj).2
        exact le_mul_of_one_le_left (prod_nonneg fun k _ ↦ hb _)
          (Real.one_le_exp (by linarith))
      · exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun k _ ↦ hb _)
    _ = Real.exp n * ∏ _k : ι, ∑ i ∈ range n, Real.exp (-(i : ℝ) ^ 2) * b i := by
      rw [prod_univ_sum, mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      have hw :
          Real.exp (n - ∑ k, (j k : ℝ) ^ 2) = Real.exp n * ∏ k, Real.exp (-(j k : ℝ) ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add, ← sum_neg_distrib, Real.exp_sum]
      simp only [hw, prod_mul_distrib, mul_assoc]
    _ ≤ Real.exp n * ∏ _k : ι, 2 * b 1 :=
      mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun i _ ↦
        mul_nonneg (Real.exp_pos _).le (hb i)) fun _ _ ↦ hfactor) (Real.exp_pos _).le
    _ = (Real.exp 1 * (2 * b 1)) ^ n := by
      simp only [prod_const, card_univ, mul_pow, Real.exp_one_pow, n]
    _ = (2 * Real.exp 1 * (2 * K * ε + a)) ^ n := by
      congr 1
      push_cast [b]
      ring

/-- **Tensorization of small-ball probabilities.** Let `ζ k` be random vectors with
independent norms, indexed by a finite type of cardinality `n`, and let `ε ≥ 0`. If each `ζ k`
satisfies the linear small-ball bound `P(‖ζ k‖ < r) ≤ K * r + a` at every radius `r ≥ ε`, then
`P(∑ k, ‖ζ k‖ ^ 2 < ε ^ 2 * n) ≤ (2 e (2 K ε + a)) ^ n`.

The random vectors may take values in different spaces, need not be measurable and need not be
independent themselves; the probabilities are outer measures. -/
theorem measureReal_sum_norm_sq_lt_le (hind : iIndepFun (fun k ω ↦ ‖ζ k ω‖) P) {ε K a : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : ∀ k, ∀ r, ε ≤ r → P.real {ω | ‖ζ k ω‖ < r} ≤ K * r + a) :
    P.real {ω | ∑ k, ‖ζ k ω‖ ^ 2 < ε ^ 2 * Fintype.card ι} ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card ι := by
  classical
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · simp
  have hb (r : ℝ) (hr : ε ≤ r) : 0 ≤ K * r + a := measureReal_nonneg.trans (hsmall k₀ r hr)
  have hprod (r : ι → ℝ) :
      P.real (⋂ k, {ω | ‖ζ k ω‖ < r k}) = ∏ k, P.real {ω | ‖ζ k ω‖ < r k} := by
    simp only [measureReal_def, ← ENNReal.toReal_prod]
    rw [hind.meas_iInter fun k ↦ ⟨Set.Iio (r k), measurableSet_Iio, by rfl⟩]
  have hr (i : ℕ) : ε ≤ (i + 1) * ε :=
    le_mul_of_one_le_left hε (by linarith [i.cast_nonneg (α := ℝ)])
  calc
    _ ≤ ∑ j ∈ (Fintype.piFinset fun _ : ι ↦ range (Fintype.card ι)).filter
          (fun j ↦ ∑ k, j k ^ 2 < Fintype.card ι),
        P.real (⋂ k, {ω | ‖ζ k ω‖ < (j k + 1) * ε}) :=
      (measureReal_mono (setOf_sum_norm_sq_lt_subset_iUnion hε) (measure_ne_top _ _)).trans
        (measureReal_biUnion_finset_le _ _)
    _ ≤ _ := sum_le_sum fun j _ ↦ (hprod _).trans_le <|
      prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) fun k _ ↦ hsmall k _ (hr (j k))
    _ ≤ _ := sum_filter_prod_le fun i ↦ hb _ (hr i)

/-- **Tensorization of small-ball probabilities** for independent random vectors `ζ k`, indexed
by a finite type of cardinality `n`: if `ε ≥ 0` and each `ζ k` satisfies the linear small-ball
bound `P(‖ζ k‖ < r) ≤ K * r + a` at every radius `r ≥ ε`, then
`P(∑ k, ‖ζ k‖ ^ 2 < ε ^ 2 * n) ≤ (2 e (2 K ε + a)) ^ n`. -/
theorem measureReal_sum_norm_sq_lt_le' [∀ k, MeasurableSpace (E k)]
    [∀ k, OpensMeasurableSpace (E k)] (hind : iIndepFun ζ P) {ε K a : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ k, ∀ r, ε ≤ r → P.real {ω | ‖ζ k ω‖ < r} ≤ K * r + a) :
    P.real {ω | ∑ k, ‖ζ k ω‖ ^ 2 < ε ^ 2 * Fintype.card ι} ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card ι :=
  (hind.comp (fun _ ↦ norm) fun _ ↦ continuous_norm.measurable).measureReal_sum_norm_sq_lt_le hε
    hsmall

end ProbabilityTheory.iIndepFun
