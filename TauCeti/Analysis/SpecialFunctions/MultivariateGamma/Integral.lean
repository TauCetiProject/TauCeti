/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Cholesky
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef

/-!
# The multivariate Gamma function as a cone integral

The multivariate Gamma function `TauCeti.multivariateGamma p a` is the value of the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of positive-definite symmetric
`p × p` matrices, taken against `TauCeti.symmetricLebesgue p`. This file proves that identity,
for `(p - 1) / 2 < a` in every dimension and for every `a` in dimension zero, where the cone is a
single point and both sides are `1`.

The normalization of the reference measure is part of the identity, not a convention that can be
changed afterwards, which is why this file, unlike the elementary theory of `multivariateGamma`,
depends on the measure theory of the symmetric matrices: the same integral against a differently
scaled reference measure has a different value, and it is this one that the Wishart normalizing
constant uses.

The proof is the Cholesky change of variables, which turns the cone integral into the integral
over the positive-diagonal lower-triangular coordinates, where the integrand factorizes into
one-dimensional Gamma and Gaussian integrals. Both the lower-integral and the Bochner form are
recorded, together with the integrability of the integrand on the cone: a density defined by
`MeasureTheory.Measure.withDensity` is normalized by the first and integrated against by the
others.

## Main results

* `TauCeti.integral_posDef_multivariateGamma` — the cone integral;
* `TauCeti.lintegral_posDef_multivariateGamma` — its lower-integral form;
* `TauCeti.integrableOn_posDef_det_rpow_mul_exp_neg_trace` — integrability on the cone;
* `TauCeti.integral_posDef_multivariateGamma_zero` — the cone integral in dimension zero, where
  no hypothesis on the shape parameter is needed.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 5.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory Real

open scoped Matrix

namespace TauCeti

variable {p : ℕ} {a : ℝ}

/-- The cone integral that characterizes `Γ_p`, in dimension zero: the symmetric `0 × 0` matrices
form a single point, which is positive definite and has determinant `1` and trace `0`, and
`symmetricLebesgue 0` is the Dirac measure there. Both sides are `1`, so unlike the
positive-dimensional identity this one needs no hypothesis on the shape parameter. -/
theorem integral_posDef_multivariateGamma_zero (a : ℝ) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
        (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef},
      (A : Matrix (Fin 0) (Fin 0) ℝ).det ^ (a - 1 / 2) *
        exp (-(A : Matrix (Fin 0) (Fin 0) ℝ).trace) ∂symmetricLebesgue 0 =
      multivariateGamma 0 a := by
  have hset : {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
      (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef} = Set.univ :=
    Set.eq_univ_of_forall fun A =>
      ⟨selfAdjoint.isHermitian_coe A, fun x hx => absurd (by ext i; exact i.elim0) hx⟩
  rw [hset, Measure.restrict_univ, symmetricLebesgue_zero, integral_dirac]
  simp [Matrix.det_fin_zero]

/-- Pulled back along the Cholesky parametrization the integrand is nonnegative everywhere, not
only over the positive-diagonal region: a Gram determinant is a square. -/
private theorem det_rpow_mul_exp_neg_trace_nonneg (x : lowerTriangle p → ℝ) (c : ℝ) :
    0 ≤ (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ c *
      exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace) := by
  refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.exp_nonneg _)
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact mul_self_nonneg _

/-- **The multivariate Gamma integral**, in lower-integral form: the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the positive-definite cone against
`TauCeti.symmetricLebesgue p` is `Γ_p(a)`. This is the form that normalizes a density defined by
`MeasureTheory.Measure.withDensity`. -/
theorem lintegral_posDef_multivariateGamma (ha : ((p : ℝ) - 1) / 2 < a) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)) ∂symmetricLebesgue p =
      ENNReal.ofReal (multivariateGamma p a) := by
  -- In the Cholesky coordinates the Jacobian weight joins the integrand as a second factor.
  have hpt : ∀ x : lowerTriangle p → ℝ,
      choleskyJacobianDensity p x *
          ENNReal.ofReal ((lowerTriangleGram p x : Matrix (Fin p) (Fin p) ℝ).det ^
              (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleGram p x : Matrix (Fin p) (Fin p) ℝ).trace)) =
        ENNReal.ofReal
          (((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
              exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
            (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ)))) := fun x => by
    rw [ENNReal.ofReal_mul (det_rpow_mul_exp_neg_trace_nonneg x _), choleskyJacobianDensity_def,
      coe_lowerTriangleGram, mul_comm]
  have hnonneg : 0 ≤ᵐ[volume.restrict
      {x : lowerTriangle p → ℝ | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩}]
      fun x : lowerTriangle p → ℝ =>
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
          (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ))) := by
    rw [← posDiagLowerRegion_def]
    filter_upwards [ae_restrict_mem (measurableSet_posDiagLowerRegion p)] with x hx
    exact mul_nonneg (det_rpow_mul_exp_neg_trace_nonneg x _) (mul_nonneg (by positivity)
      (Finset.prod_nonneg fun i _ => pow_nonneg ((mem_posDiagLowerRegion p).mp hx i).le _))
  rw [setLIntegral_posDef_symmetricLebesgue p (by fun_prop)]
  simp_rw [hpt]
  rw [posDiagLowerRegion_def, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_lowerTriangle_det_rpow_mul_exp_neg_trace ha) hnonneg,
    integral_lowerTriangle_det_rpow_mul_exp_neg_trace ha]

/-- For `((p : ℝ) - 1) / 2 < a` the integrand `(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` is
integrable over the positive-definite cone against `TauCeti.symmetricLebesgue p`. -/
theorem integrableOn_posDef_det_rpow_mul_exp_neg_trace (ha : ((p : ℝ) - 1) / 2 < a) :
    IntegrableOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
          exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace))
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} (symmetricLebesgue p) := by
  refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
  -- On the cone the determinant is positive, so the integrand is its own norm.
  have henorm : ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ‖(A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)‖ₑ ∂symmetricLebesgue p =
      ENNReal.ofReal (multivariateGamma p a) := by
    rw [← lintegral_posDef_multivariateGamma ha]
    refine setLIntegral_congr_fun (measurableSet_posDefMatrix p) fun A hA => ?_
    exact Real.enorm_eq_ofReal
      (mul_nonneg (Real.rpow_nonneg hA.det_pos.le _) (Real.exp_nonneg _))
  rw [hasFiniteIntegral_iff_enorm, henorm]
  exact ENNReal.ofReal_lt_top

/-- **The multivariate Gamma integral.** For `((p : ℝ) - 1) / 2 < a`, the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of positive-definite symmetric
`p × p` matrices, against `TauCeti.symmetricLebesgue p`, is `Γ_p(a)`. -/
theorem integral_posDef_multivariateGamma (ha : ((p : ℝ) - 1) / 2 < a) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace) ∂symmetricLebesgue p =
      multivariateGamma p a := by
  rw [integral_posDef_symmetricLebesgue p (Measurable.aestronglyMeasurable (by fun_prop)),
    ← integral_lowerTriangle_det_rpow_mul_exp_neg_trace ha, ← posDiagLowerRegion_def]
  refine setIntegral_congr_fun (measurableSet_posDiagLowerRegion p) fun x _ => ?_
  simp only [coe_lowerTriangleGram, smul_eq_mul]
  ring

end TauCeti
