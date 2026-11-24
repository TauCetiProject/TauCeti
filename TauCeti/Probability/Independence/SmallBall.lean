/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Tensorization of small-ball probabilities

Suppose that independent random vectors `ζ k`, indexed by a finite type of cardinality `n`, all
satisfy a small-ball bound that is linear in the radius at every radius `r ≥ ε`:
`P(‖ζ k‖ < r) ≤ K r + a`. Then the probability that the sum of their squared norms is less than
`ε ^ 2 * n` is exponentially small in `n`:
`P(∑ k, ‖ζ k‖ ^ 2 < ε ^ 2 * n) ≤ (2 e (2 K ε + a)) ^ n`.

For `a = 0` this is the tensorization lemma of Rudelson and Vershynin; requiring the
small-ball bound only at radii `r ≥ ε` recovers their lower threshold `ε₀`. The additive term `a`
absorbs radius-independent error terms of small-ball estimates, such as the term `C / D` for a
lower bound `D` on the least common denominator of the coefficients.

For a matrix `A` with independent rows, indexed by a finite type of cardinality `m`, the
coordinates of the image `A x` of a fixed vector are independent. Small-ball bounds for the
coordinates then give `P(‖A x‖ < ε √m) ≤ (2 e (2 K ε + a)) ^ m`. This is the single-vector
estimate of invertibility arguments on level sets of the least common denominator.

The bounds assume only independence, not measurability, so they hold for outer probabilities
of arbitrary random vectors.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_sum_norm_sq_lt_le`: tensorization of small-ball
  bounds for independent random vectors.
* `ProbabilityTheory.iIndepFun.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le`: the small-ball
  bound for the image of a fixed vector under a matrix with independent rows.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 2.2 and Lemma 5.5.
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 4.6.
-/

public section

open MeasureTheory Finset Matrix

namespace ProbabilityTheory.iIndepFun

variable {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [SeminormedAddCommGroup E]
  {P : Measure Ω} {ζ : ι → Ω → E}

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

omit [MeasurableSpace Ω] [SeminormedAddCommGroup E] in
/-- The grid sum of products of the radius bounds `K * ((i + 1) * ε) + a` over grid points
`j` with `∑ k, j k ^ 2 < n` is at most `(2 e (2 K ε + a)) ^ n`. -/
private theorem sum_filter_prod_le [DecidableEq ι] {ε K a : ℝ}
    (hb : ∀ i : ℕ, 0 ≤ K * ((i + 1) * ε) + a) :
    ∑ j ∈ (Fintype.piFinset fun _ : ι ↦ range (Fintype.card ι)).filter
        (fun j ↦ ∑ k, j k ^ 2 < Fintype.card ι), ∏ k, (K * ((j k + 1) * ε) + a) ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card ι := by
  set n := Fintype.card ι
  set b : ℕ → ℝ := fun i ↦ K * ((i + 1) * ε) + a
  -- Since `b` is affine, `∑ i < m, 2⁻ⁱ b i = 2 b 1 - 2 * 2⁻ᵐ b (m + 1)`.
  have hgeom (m : ℕ) :
      ∑ i ∈ range m, (1 / 2 : ℝ) ^ i * b i + 2 * (1 / 2) ^ m * b (m + 1) = 2 * b 1 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ← ih]; simp only [b]; push_cast; ring
  have hexp (i : ℕ) : Real.exp (-(i : ℝ) ^ 2) ≤ (1 / 2) ^ i := calc
    Real.exp (-(i : ℝ) ^ 2) ≤ Real.exp (i * (-1)) := by
      have : (i : ℝ) ≤ (i : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero i
      exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-1) ^ i := Real.exp_natCast_mul i _
    _ ≤ (1 / 2) ^ i := by
      refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ i
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ two_pos (by linarith [Real.add_one_le_exp 1])
  have hfactor : ∑ i ∈ range n, Real.exp (-(i : ℝ) ^ 2) * b i ≤ 2 * b 1 := calc
    _ ≤ ∑ i ∈ range n, (1 / 2 : ℝ) ^ i * b i :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hexp i) (hb i)
    _ ≤ 2 * b 1 := by
      have := hgeom n
      have : 0 ≤ 2 * (1 / 2 : ℝ) ^ n * b (n + 1) := by have := hb (n + 1); positivity
      linarith
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
      rw [prod_mul_distrib, ← Real.exp_sum, ← mul_assoc, ← Real.exp_add, sum_neg_distrib,
        sub_eq_add_neg]
    _ ≤ Real.exp n * ∏ _k : ι, 2 * b 1 :=
      mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun _ _ ↦ sum_nonneg fun i _ ↦
        mul_nonneg (Real.exp_pos _).le (hb i)) fun _ _ ↦ hfactor) (Real.exp_pos _).le
    _ = (2 * Real.exp 1 * (2 * K * ε + a)) ^ n := by
      rw [prod_const, card_univ, ← Real.exp_one_pow, ← mul_pow]
      simp only [b]
      push_cast
      ring

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Tensorization of small-ball probabilities.** Let `ζ k` be independent random vectors,
indexed by a finite type of cardinality `n`, and let `ε ≥ 0`. If each `ζ k` satisfies the
linear small-ball bound `P(‖ζ k‖ < r) ≤ K * r + a` at every radius `r ≥ ε`, then
`P(∑ k, ‖ζ k‖ ^ 2 < ε ^ 2 * n) ≤ (2 e (2 K ε + a)) ^ n`.

The random vectors need not be measurable, and the probabilities are outer measures. -/
theorem measureReal_sum_norm_sq_lt_le (hind : iIndepFun ζ P) {ε K a : ℝ} (hε : 0 ≤ ε)
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
    rw [hind.meas_iInter fun k ↦ ⟨Metric.ball 0 (r k), measurableSet_ball, by ext ω; simp⟩]
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

/-- **Small-ball bound for the image of a fixed vector.** Let `A` be a random matrix with
independent rows, indexed by a finite type of cardinality `m`, let `x` be a fixed vector and let
`ε ≥ 0`. If every coordinate of `A x` satisfies the linear small-ball bound
`P(‖(A x) i‖ < r) ≤ K * r + a` at every radius `r ≥ ε`, then
`P(‖A x‖ < ε √m) ≤ (2 e (2 K ε + a)) ^ m`. -/
theorem measureReal_norm_toEuclideanLin_lt_mul_sqrt_le {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [RCLike 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    {A : Ω → Matrix m n 𝕜}
    (hind : iIndepFun (fun i ω ↦ (A ω).row i) P) (x : EuclideanSpace 𝕜 n) {ε K a : ℝ}
    (hε : 0 ≤ ε) (hsmall : ∀ i, ∀ r, ε ≤ r → P.real {ω | ‖A ω i ⬝ᵥ x‖ < r} ≤ K * r + a) :
    P.real {ω | ‖toEuclideanLin (A ω) x‖ < ε * Real.sqrt (Fintype.card m)} ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card m := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hY : iIndepFun (fun i ω ↦ ‖A ω i ⬝ᵥ x‖) P :=
    hind.comp (fun _ (w : n → 𝕜) ↦ ‖w ⬝ᵥ x‖) fun _ ↦
      Continuous.measurable (by simp only [dotProduct]; fun_prop)
  refine le_trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _))
    (hY.measureReal_sum_norm_sq_lt_le hε (by simpa only [norm_norm] using hsmall))
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hnorm : ‖toEuclideanLin (A ω) x‖ ^ 2 = ∑ i, ‖‖A ω i ⬝ᵥ x‖‖ ^ 2 := by
    simp only [norm_norm, EuclideanSpace.norm_sq_eq, toLpLin_apply, mulVec]
  have hsq := pow_lt_pow_left₀ hω (norm_nonneg _) two_ne_zero
  rwa [hnorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq

end ProbabilityTheory.iIndepFun
