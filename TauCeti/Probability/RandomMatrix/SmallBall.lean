/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Independence.LeastCommonDenominator
public import TauCeti.Probability.Independence.SmallBall
import TauCeti.Probability.Independence.Matrix

/-!
# Small-ball bounds for the image of a fixed vector

For a matrix `A` with independent rows, indexed by a finite type of cardinality `m`, the
coordinates of the image `A x` of a fixed vector are independent. Tensorization of small-ball
probabilities (`ProbabilityTheory.iIndepFun.measureReal_sum_norm_sq_lt_le`) turns small-ball
bounds `P(‖(A x) i‖ < r) ≤ K r + a` at every radius `r ≥ ε` into
`P(‖A x‖ < ε √m) ≤ (2 e (2 K ε + a)) ^ m`. This is the tensorization step of the single-vector
estimate of invertibility arguments on level sets of the least common denominator.

When the entries are independent and each row has identically distributed entries, the
coordinate bounds come from the small-ball inequality through the least common denominator,
`iIndepFun.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator`. If the LCD
`LCD_{α,γ}(x)` is at least `L > 0` and the row laws put mass at most `1 - b` in every open
interval of length `2`, then
`P(‖A x‖ < t √m) ≤ (2 e (16 π (2 t + L⁻¹) / (γ ‖x‖ √b) + 4 exp (1 - α² b / 2))) ^ m`.
Once the base of this power is below `1`, the probability that the matrix maps a vector with a
large LCD close to `0` decays exponentially in the number of rows.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le`: the small-ball
  bound for the image of a fixed vector under a matrix with independent rows.
* `iIndepFun.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le_of_ofReal_le_leastCommonDenominator`:
  the small-ball bound for the image of a vector with a large least common denominator.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 5.5.
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 4.6.
-/

public section

open MeasureTheory Matrix Metric Real
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

/-- **Small-ball bound for the image of a fixed vector.** Let `A` be a random matrix with
independent rows, indexed by a finite type of cardinality `m`, let `x` be a fixed vector and let
`ε ≥ 0`. If every coordinate of `A x` satisfies the linear small-ball bound
`P(‖(A x) i‖ < r) ≤ K * r + a` at every radius `r ≥ ε`, then
`P(‖A x‖ < ε √m) ≤ (2 e (2 K ε + a)) ^ m`. -/
theorem measureReal_norm_toEuclideanLin_lt_mul_sqrt_le {Ω m n 𝕜 : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq n] [RCLike 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] {P : Measure Ω} {A : Ω → Matrix m n 𝕜}
    (hind : iIndepFun (fun i ω ↦ (A ω).row i) P) (x : EuclideanSpace 𝕜 n) {ε K a : ℝ}
    (hε : 0 ≤ ε) (hsmall : ∀ i, ∀ r, ε ≤ r → P.real {ω | ‖A ω i ⬝ᵥ x‖ < r} ≤ K * r + a) :
    P.real {ω | ‖toEuclideanLin (A ω) x‖ < ε * Real.sqrt (Fintype.card m)} ≤
      (2 * Real.exp 1 * (2 * K * ε + a)) ^ Fintype.card m := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hY : iIndepFun (fun i ω ↦ ‖A ω i ⬝ᵥ x‖) P :=
    hind.comp (fun _ (w : n → 𝕜) ↦ ‖w ⬝ᵥ x‖) fun _ ↦
      (continuous_id.dotProduct continuous_const).norm.measurable
  refine le_trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _))
    (hY.measureReal_sum_norm_sq_lt_le hε hsmall)
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hnorm : ‖toEuclideanLin (A ω) x‖ ^ 2 = ∑ i, ‖A ω i ⬝ᵥ x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, ofLp_toLpLin, toLin'_apply, mulVec]
  have hsq := pow_lt_pow_left₀ hω (norm_nonneg _) two_ne_zero
  rwa [hnorm, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq

/-- **Small-ball bound for a vector with a large least common denominator.** Let `A` be a random
matrix whose entries are independent, with the entries of row `i` distributed according to
`μ i`, and suppose every `μ i` gives mass at most `1 - b` to each open interval of length `2`. If
the least common denominator `LCD_{α,γ}(x)` of a vector `x ≠ 0` is at least `L > 0`, with
`γ > 0`, then for every `t ≥ 0`,
`P(‖A x‖ < t √m) ≤ (2 e (16 π (2 t + L⁻¹) / (γ ‖x‖ √b) + 4 exp (1 - α² b / 2))) ^ m`,
where `m` is the number of rows. -/
theorem measureReal_norm_toEuclideanLin_lt_mul_sqrt_le_of_ofReal_le_leastCommonDenominator
    {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
    {P : Measure Ω} {A : Ω → Matrix m n ℝ}
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    {μ : m → Measure ℝ} (hμ : ∀ i j, HasLaw (fun ω ↦ A ω i j) (μ i) P) {b : ℝ}
    (hb : ∀ i v, (μ i).real (ball v 1) ≤ 1 - b) {x : EuclideanSpace ℝ n} (hx : x ≠ 0)
    {α : ℝ≥0} {γ L : ℝ} (hγ : 0 < γ) (hL : 0 < L)
    (hLx : ENNReal.ofReal L ≤ TauCeti.leastCommonDenominator α γ x) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | ‖toEuclideanLin (A ω) x‖ < t * √(Fintype.card m)} ≤
      (2 * exp 1 * (16 * π * (2 * t + L⁻¹) / (γ * ‖x‖ * √b) +
        4 * exp (1 - α ^ 2 * b / 2))) ^ Fintype.card m := by
  have := hind.isProbabilityMeasure
  -- Each coordinate `(A x) i` is a weighted sum of the independent entries of row `i`.
  have hsmall (i : m) (r : ℝ) (hr : t ≤ r) : P.real {ω | ‖A ω i ⬝ᵥ x‖ < r} ≤
      16 * π / (γ * ‖x‖ * √b) * r +
        (16 * π * L⁻¹ / (γ * ‖x‖ * √b) + 4 * exp (1 - α ^ 2 * b / 2)) := by
    have hrow : iIndepFun (fun j ω ↦ A ω i j) P :=
      hind.precomp (g := fun j ↦ (i, j)) fun _ _ h ↦ (Prod.mk.inj h).2
    refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
      ((hrow.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator (hμ i)
        (hb i) hx hγ hL hLx 0 (ht.trans hr)).trans_eq ?_)
    · rw [Set.mem_ofPred_eq] at hω ⊢
      rw [dotProduct_comm, Real.norm_eq_abs] at hω
      rw [sub_zero]
      exact hω.le
    · ring
  have hrows := hind.matrix_row fun i j ↦ (hμ i j).aemeasurable
  refine (hrows.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le x ht hsmall).trans_eq ?_
  congr 2
  ring

end ProbabilityTheory.iIndepFun
