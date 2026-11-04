/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
public import TauCeti.Probability.Moments.Covariance
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The quadratic Fenchel–Young inequality in mean

For a positive-semidefinite matrix `A` with pseudoinverse `A⁺`, the quadratic Fenchel–Young
inequality `⟪u, y⟫ ≤ (⟪A y, y⟫ + ⟪A⁺ u, u⟫) / 2` holds for every `y` and every `u` in the range
of `A`. This file takes it in mean, for a centred random vector `u = X - 𝔼 X` and a random vector
`y = Y` with finite second moments, when the covariance matrix of `X` has the form `A * T * A`.

The hypothesis on the covariance forces the centred variable into the range of `A` almost surely,
which is what allows `A` to be singular: the mean of `‖(1 - A * A⁺) (X - 𝔼 X)‖ ^ 2` is a trace
against the covariance that vanishes.

## Main statements

* `TauCeti.ae_sub_integral_mem_range_toEuclideanLin`: if the covariance matrix of `X` has the
  form `A * T`, the centred variable lies almost surely in the range of `A`.
* `TauCeti.integral_inner_sub_integral_le`: the quadratic Fenchel–Young inequality in mean, for a
  random vector whose covariance has the form `A * T * A`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → EuclideanSpace ℝ ι}

/-- **The centred variable lies in the range of the covariance.** If the covariance matrix of a
square-integrable random vector `X` has the form `A * T` for a positive-semidefinite matrix `A`,
then `X - 𝔼 X` lies almost surely in the range of `A`. -/
theorem ae_sub_integral_mem_range_toEuclideanLin (hX : MemLp X 2 P) {A T : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hcov : covMatrix (P.map X) = A * T) :
    ∀ᵐ ω ∂P, X ω - ∫ ω', X ω' ∂P ∈ LinearMap.range A.toEuclideanLin := by
  -- With `R = 1 - A * A⁺`, the mean of `‖R (X - m)‖ ^ 2` is the trace of `Rᴴ * R * (A * T)`, and
  -- `R * A = 0`.
  set m := ∫ ω', X ω' ∂P
  set D := A.covariancePseudoInverse
  set R : Matrix ι ι ℝ := 1 - A * D
  have hRA : R * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_covariancePseudoInverse_mul hA, sub_self]
  have hR (x : EuclideanSpace ℝ ι) :
      R.toEuclideanLin x = x - A.toEuclideanLin (D.toEuclideanLin x) := by
    simp [R, Matrix.toLpLin_mul_same]
  have hRR (x : EuclideanSpace ℝ ι) :
      ⟪(Rᴴ * R).toEuclideanLin x, x⟫ = ‖R.toEuclideanLin x‖ ^ 2 := by
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  have hsq : ∫ ω, ‖R.toEuclideanLin (X ω - m)‖ ^ 2 ∂P = 0 := by
    have h := integral_inner_toEuclideanLin_sub_integral_eq_trace_mul_covMatrix_map hX (Rᴴ * R)
    rw [hcov, Matrix.mul_assoc, ← Matrix.mul_assoc R, hRA, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero] at h
    simpa only [hRR] using h
  have hU : MemLp (fun ω ↦ X ω - m) 2 P := hX.sub (memLp_const m)
  have hint : Integrable (fun ω ↦ ‖R.toEuclideanLin (X ω - m)‖ ^ 2) P := by
    simpa only [hRR] using hU.integrable_inner_toEuclideanLin (Rᴴ * R)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω ↦ by positivity) hint).1 hsq
  filter_upwards [hae] with ω hω
  have : R.toEuclideanLin (X ω - m) = 0 := by simpa using hω
  rw [hR, sub_eq_zero] at this
  exact ⟨_, this.symm⟩

/-- **The quadratic Fenchel–Young inequality in mean.** Let `X` and `Y` be square-integrable
random vectors, where the law of `X` has covariance matrix `A * T * A` for a positive-semidefinite
matrix `A`. Then the correlation of the centred variable `X - 𝔼 X` with `Y` is at most
`(𝔼 ⟪A Y, Y⟫ + tr (A * T)) / 2`. -/
theorem integral_inner_sub_integral_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {A T : Matrix ι ι ℝ} (hA : A.PosSemidef) (hcov : covMatrix (P.map X) = A * T * A) :
    ∫ ω, ⟪X ω - ∫ ω', X ω' ∂P, Y ω⟫ ∂P ≤
      (∫ ω, ⟪A.toEuclideanLin (Y ω), Y ω⟫ ∂P + (A * T).trace) / 2 := by
  set m := ∫ ω', X ω' ∂P
  set D := A.covariancePseudoInverse
  have hU : MemLp (fun ω ↦ X ω - m) 2 P := hX.sub (memLp_const m)
  have hsa : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.2 hA.isHermitian
  have hsd : D.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.2 (A.posSemidef_covariancePseudoInverse).isHermitian
  have hpos : A.toEuclideanLin.IsPositive := Matrix.isPositive_toEuclideanLin_iff.2 hA
  have hdad (x : EuclideanSpace ℝ ι) :
      D.toEuclideanLin (A.toEuclideanLin (D.toEuclideanLin x)) = D.toEuclideanLin x := by
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
      congrArg (fun M : Matrix ι ι ℝ ↦ M.toEuclideanLin x) A.covariancePseudoInverse_mul_self_mul
  -- On the range of `A`, the pointwise inequality is `0 ≤ ⟪A (D u - y), D u - y⟫`.
  have hpt : ∀ᵐ ω ∂P, ⟪X ω - m, Y ω⟫ ≤
      (⟪A.toEuclideanLin (Y ω), Y ω⟫ + ⟪D.toEuclideanLin (X ω - m), X ω - m⟫) / 2 := by
    filter_upwards [ae_sub_integral_mem_range_toEuclideanLin hX hA
      (hcov.trans (Matrix.mul_assoc _ _ _))] with ω hω
    set u := X ω - m
    set y := Y ω
    set v := D.toEuclideanLin u
    have hu : A.toEuclideanLin v = u := by
      have h := LinearMap.congr_fun (Matrix.toEuclideanLin_mul_covariancePseudoInverse hA) u
      rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        Submodule.starProjection_eq_self_iff.2 hω] at h
      exact h
    have h0 : 0 ≤ ⟪A.toEuclideanLin (v - y), v - y⟫ := by
      simpa only [RCLike.re_to_real] using hpos.re_inner_nonneg_left (v - y)
    have hvv : ⟪A.toEuclideanLin v, v⟫ = ⟪v, u⟫ := by
      rw [← hsd, hdad]
    have huy : ⟪u, y⟫ = ⟪A.toEuclideanLin v, y⟫ := by rw [hu]
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hvv, hsa y v,
      real_inner_comm (A.toEuclideanLin v) y] at h0
    linarith
  have htrace : (D * (A * T * A)).trace = (A * T).trace := by
    rw [Matrix.trace_mul_comm D, Matrix.mul_assoc (A * T) A D, Matrix.trace_mul_comm (A * T),
      ← Matrix.mul_assoc (A * D) A T, Matrix.mul_covariancePseudoInverse_mul hA]
  have hAY := hY.integrable_inner_toEuclideanLin A
  have hDU := hU.integrable_inner_toEuclideanLin D
  calc ∫ ω, ⟪X ω - m, Y ω⟫ ∂P
      ≤ ∫ ω, (⟪A.toEuclideanLin (Y ω), Y ω⟫ + ⟪D.toEuclideanLin (X ω - m), X ω - m⟫) / 2 ∂P :=
        integral_mono_ae (hU.integrable_inner hY) ((hAY.add hDU).div_const 2) hpt
    _ = (∫ ω, ⟪A.toEuclideanLin (Y ω), Y ω⟫ ∂P + (A * T).trace) / 2 := by
        rw [integral_div, integral_add hAY hDU,
          integral_inner_toEuclideanLin_sub_integral_eq_trace_mul_covMatrix_map hX D, hcov,
          htrace]

end TauCeti
