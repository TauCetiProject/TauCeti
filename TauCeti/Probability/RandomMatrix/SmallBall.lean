/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Independence.SmallBall

/-!
# Small-ball bounds for the image of a fixed vector

For a matrix `A` with independent rows, indexed by a finite type of cardinality `m`, the
coordinates of the image `A x` of a fixed vector are independent. Tensorization of small-ball
probabilities (`ProbabilityTheory.iIndepFun.measureReal_sum_norm_sq_lt_le`) turns small-ball
bounds `P(‖(A x) i‖ < r) ≤ K r + a` at every radius `r ≥ ε` into
`P(‖A x‖ < ε √m) ≤ (2 e (2 K ε + a)) ^ m`. This is the tensorization step of the single-vector
estimate of invertibility arguments on level sets of the least common denominator; the
coordinate bounds `P(‖(A x) i‖ < r) ≤ K r + a` must be supplied separately, by a one-dimensional
small-ball bound for each row.

## Main results

* `ProbabilityTheory.iIndepFun.measureReal_norm_toEuclideanLin_lt_mul_sqrt_le`: the small-ball
  bound for the image of a fixed vector under a matrix with independent rows.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 5.5.
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 4.6.
-/

public section

open MeasureTheory Matrix

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

end ProbabilityTheory.iIndepFun
