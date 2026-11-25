/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.IsoperimetricProfile
public import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Checks for the Gaussian isoperimetric function and the orthogonal splitting

Checks of the one-dimensional Gaussian isoperimetric function `I = φ ∘ Φ⁻¹`
(`TauCeti.Probability.gaussianIsoperimetricProfile`) and of the orthogonal splitting of the
standard Gaussian measure:

* `I(1 - Φ(1)) = φ(1)` and `I(1/3) = I(2/3)`;
* the quantile of the standard Gaussian law takes the value `0` at the levels `0` and `1`, where
  `φ` of it would be `φ(0) ≠ 0`, so the separate definition `I(0) = I(1) = 0` is forced;
* `I'(3/10) = -Φ⁻¹(3/10)` and `I''(3/10) = -1/I(3/10)`;
* in `ℝ²`, `γ({x₁ + x₂ < √2}) = Φ(1)`, by projection onto `(e₁ + e₂)/√2`;
* on the plane `{x ∈ ℝ³ | x₁ + x₂ + x₃ = 0}`, the coordinate `√(3/2) x₁` has the standard
  normal law, with the factor `√(q/(q-1))` at `q = 3`;
* the splittings along `F = {0}` and `F = E`, where the standard Gaussian on the zero factor is
  the Dirac mass `δ₀`;
* the standard Gaussian on `ℝ²` has the density `multivariateGaussianPDF 0 1`, whose value at the
  origin is `(2π)⁻¹`.
-/

open MeasureTheory ProbabilityTheory Real Set TauCeti.Probability
open scoped RealInnerProductSpace

public noncomputable section

namespace TauCeti.Examples.GaussianIsoperimetry

/-- `I(1 - Φ(1)) = φ(1)`. -/
example : gaussianIsoperimetricProfile (1 - cdf (gaussianReal 0 1) 1) = gaussianPDFReal 0 1 1 := by
  rw [← cdf_gaussianReal_zero_one_neg, gaussianIsoperimetricProfile_cdf, gaussianPDFReal_zero_neg]

/-- `I(1/3) = I(2/3)`. -/
example : gaussianIsoperimetricProfile (1 / 3) = gaussianIsoperimetricProfile (2 / 3) := by
  rw [← gaussianIsoperimetricProfile_one_sub (2 / 3)]
  norm_num

/-- The quantile of the standard Gaussian law is `0` at the level `0`. -/
example : (gaussianReal 0 1).quantile 0 = 0 :=
  Measure.quantile_of_nonpos _ le_rfl

/-- The quantile of the standard Gaussian law is `0` at the level `1`, since `Φ < 1`. -/
example : (gaussianReal 0 1).quantile 1 = 0 := by
  have : {x : ℝ | 1 ≤ cdf (gaussianReal 0 1) x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦
      (cdf_gaussianReal_lt_one 0 one_ne_zero x).not_ge hx
  rw [Measure.quantile_def, this, Real.sInf_empty]

/-- `φ` of the quantile at the levels `0` and `1` would be `φ(0) ≠ 0 = I(0) = I(1)`. -/
example : gaussianPDFReal 0 1 0 ≠ gaussianIsoperimetricProfile 0 ∧
    gaussianIsoperimetricProfile 0 = gaussianIsoperimetricProfile 1 := by
  rw [gaussianIsoperimetricProfile_zero, gaussianIsoperimetricProfile_one]
  exact ⟨(gaussianPDFReal_pos 0 1 0 one_ne_zero).ne', rfl⟩

/-- `I'(3/10) = -Φ⁻¹(3/10)`. -/
example : deriv gaussianIsoperimetricProfile (3 / 10) = -(gaussianReal 0 1).quantile (3 / 10) :=
  (hasDerivAt_gaussianIsoperimetricProfile (by norm_num)).deriv

/-- `I''(3/10) = -1/I(3/10)`. -/
example : deriv (deriv gaussianIsoperimetricProfile) (3 / 10) =
    -1 / gaussianIsoperimetricProfile (3 / 10) := by
  rw [(hasDerivAt_deriv_gaussianIsoperimetricProfile (by norm_num)).deriv, neg_div, one_div]

/-- In `ℝ²`, projecting onto the unit vector `(e₁ + e₂)/√2` gives `γ({x₁ + x₂ < √2}) = Φ(1)`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 2))).real {x | x 0 + x 1 < √2} =
    cdf (gaussianReal 0 1) 1 := by
  set ν : EuclideanSpace ℝ (Fin 2) := (√2)⁻¹ • (EuclideanSpace.single 0 1 +
    EuclideanSpace.single 1 1) with hν
  have h2 : (0 : ℝ) < √2 := by positivity
  have hnorm : ‖ν‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    norm_num [hν, Real.sq_sqrt]
  rw [← measureReal_stdGaussian_setOf_inner_lt hnorm 1]
  congr 1
  ext x
  simp only [mem_ofPred_eq, hν, inner_smul_right, inner_add_right,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rw [inv_mul_lt_iff₀ h2, mul_one]

/-- The plane `{x ∈ ℝ³ | x₁ + x₂ + x₃ = 0}`, the orthogonal complement of `(1, 1, 1)`. -/
abbrev sumZeroPlane : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (ℝ ∙ (!₂[1, 1, 1] : EuclideanSpace ℝ (Fin 3)))ᗮ

/-- The projection `(2/3, -1/3, -1/3)` of `e₁` to the plane, rescaled to a unit vector. -/
private noncomputable def unitVec : sumZeroPlane :=
  ⟨√(3 / 2) • !₂[2 / 3, -1 / 3, -1 / 3], by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    ring⟩

/-- On the plane `{x₁ + x₂ + x₃ = 0}` of `ℝ³`, the coordinate `√(3/2) x₁` has the standard normal
law: the projection of `e₁` to the plane has squared norm `2/3`. -/
example : (stdGaussian sumZeroPlane).map
      (fun x : sumZeroPlane ↦ √(3 / 2) * (x : EuclideanSpace ℝ (Fin 3)) 0) =
    gaussianReal 0 1 := by
  have hnorm : ‖unitVec‖ = 1 := by
    rw [← Submodule.norm_coe, unitVec, EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_three, div_pow, mul_pow]
  rw [← map_inner_stdGaussian_of_norm_eq_one hnorm]
  congr 1
  funext x
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.1 x.property
  simp only [unitVec, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    PiLp.smul_apply, smul_eq_mul, mul_one] at hx ⊢
  linear_combination (√(3 / 2) / 3) * hx

/-- The splitting along `F = {0}`: `γ_E = δ₀ ⊗ γ_E`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ((Measure.dirac (0 : (⊥ : Submodule ℝ E))).prod (stdGaussian (⊥ : Submodule ℝ E)ᗮ)).map
      (fun p ↦ (p.1 : E) + p.2) = stdGaussian E := by
  rw [← Measure.eq_dirac_of_subsingleton (stdGaussian (⊥ : Submodule ℝ E))]
  exact Submodule.map_add_prod_stdGaussian ⊥

/-- The splitting along `F = E`: `γ_E = γ_E ⊗ δ₀`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ((stdGaussian (⊤ : Submodule ℝ E)).prod (Measure.dirac (0 : (⊤ : Submodule ℝ E)ᗮ))).map
      (fun p ↦ (p.1 : E) + p.2) = stdGaussian E := by
  have : Subsingleton (⊤ : Submodule ℝ E)ᗮ := by
    rw [Submodule.top_orthogonal_eq_bot]
    infer_instance
  rw [← Measure.eq_dirac_of_subsingleton (stdGaussian (⊤ : Submodule ℝ E)ᗮ)]
  exact Submodule.map_add_prod_stdGaussian ⊤

/-- The standard Gaussian on `ℝ²` has the density `multivariateGaussianPDF 0 1`, and that density
takes the value `(2π)⁻¹` at the origin. -/
example :
    stdGaussian (EuclideanSpace ℝ (Fin 2)) = volume.withDensity (multivariateGaussianPDF 0 1) ∧
    multivariateGaussianPDFReal (0 : EuclideanSpace ℝ (Fin 2)) 1 0 = (2 * π)⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [← multivariateGaussian_eq_withDensity Matrix.PosDef.one, multivariateGaussian_zero_one]
  · norm_num [multivariateGaussianPDFReal_def, Real.rpow_neg_one]

end TauCeti.Examples.GaussianIsoperimetry
