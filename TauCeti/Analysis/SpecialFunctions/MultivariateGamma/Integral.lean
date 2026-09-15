/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence

/-!
# The multivariate Gamma function as a cone integral

For `(p - 1) / 2 < a`, the range in which the integral converges, the multivariate Gamma function
is the integral of `(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of
positive-definite symmetric `p × p` matrices, taken against `TauCeti.symmetricLebesgue p`. This
file proves that identity in dimension zero, where the cone is a single point and the condition
on `a` is vacuous, and computes how the integral depends on a scale matrix: weighting the
exponential by an inverse positive-definite scale `T`, so that the integrand becomes
`(det A) ^ (a - (p + 1) / 2) * exp (-trace (T⁻¹ * A))`, multiplies the integral by `(det T) ^ a`.

The scale identity is a congruence change of variables: writing `T = C * Cᵀ`, the map
`A ↦ C * A * Cᵀ` preserves the cone, carries the plain exponential weight to the weighted one,
and contributes the Jacobian `|det C| ^ (p + 1)`; the two determinant powers combine to
`(det T) ^ a`. It is proved for every real `a`, with no convergence hypothesis on either side.
Together with the unscaled integral it fixes the normalizing constant of a Wishart density with
scale matrix `S`, whose exponential weight is `exp (-trace (S⁻¹ * A) / 2)` and hence has scale
`2 • S`.

The normalization of the reference measure is part of these identities, not a convention that can
be changed afterwards, which is why this file, unlike the elementary theory in
`TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Basic.lean`, depends on the measure theory
of the symmetric matrices.

## Main results

* `TauCeti.integral_posDef_multivariateGamma_zero` — the cone integral in dimension zero;
* `Matrix.PosDef.lintegral_det_rpow_mul_exp_neg_trace_inv_mul` and
  `Matrix.PosDef.integral_det_rpow_mul_exp_neg_trace_inv_mul` — an inverse positive-definite
  scale `T` in the exponential weight multiplies the cone integral by `(det T) ^ a`;
* `Matrix.PosDef.lintegral_det_rpow_mul_exp_neg_trace_inv_mul_div_two` and
  `Matrix.PosDef.integral_det_rpow_mul_exp_neg_trace_inv_mul_div_two` — the same statement in
  the halved form `exp (-trace (S⁻¹ * A) / 2)` used by the Wishart densities, where the factor
  is `2 ^ (p * a) * (det S) ^ a`.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 5.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Section 2.1.
* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 3 (the cone integral
  characterizing `multivariateGamma`) and item 4, whose nonsingular real-degree Wishart density
  is normalized by `2 ^ (n * p / 2) * (det S) ^ (n / 2) * multivariateGamma p (n / 2)`; the scale
  identities below are exactly how that constant depends on `S`.
-/

public section

noncomputable section

open MeasureTheory Real

namespace TauCeti

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

end TauCeti

/-! ### The scale matrix in the cone integral -/

namespace Matrix.PosDef

variable {p : ℕ} {S T : Matrix (Fin p) (Fin p) ℝ}

open TauCeti

open scoped ENNReal Matrix

/-- Congruence by `C` multiplies the determinant of a symmetric matrix by `det (C * Cᵀ)`. -/
private theorem det_coe_symmetricCongruence {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = T)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ((Matrix.GeneralLinearGroup.symmetricCongruence C A :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ).det = T.det * (A : Matrix (Fin p) (Fin p) ℝ).det := by
  rw [Matrix.GeneralLinearGroup.det_symmetricCongruence_apply, ← hC, Matrix.det_mul,
    Matrix.det_transpose, sq]

/-- Congruence by `C` turns the trace against the inverse scale `(C * Cᵀ)⁻¹` into the plain
trace: the two copies of `C` cancel against the inverse. -/
private theorem trace_inv_mul_coe_symmetricCongruence
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = T)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (T⁻¹ * ((Matrix.GeneralLinearGroup.symmetricCongruence C A :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ)).trace = (A : Matrix (Fin p) (Fin p) ℝ).trace := by
  have hdetC : IsUnit (C : Matrix (Fin p) (Fin p) ℝ).det :=
    isUnit_iff_ne_zero.2 (Matrix.GeneralLinearGroup.det_ne_zero C)
  have hdetCt : IsUnit ((C : Matrix (Fin p) (Fin p) ℝ)ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hsandwich :
      (C : Matrix (Fin p) (Fin p) ℝ)ᵀ * T⁻¹ * (C : Matrix (Fin p) (Fin p) ℝ) = 1 := by
    rw [← hC, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetCt,
      Matrix.one_mul, Matrix.nonsing_inv_mul _ hdetC]
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hsandwich, Matrix.one_mul]

/-- The Jacobian `|det C| ^ (p + 1)` of the congruence combines with the determinant factor
`(det T) ^ (a - (p + 1) / 2)` picked up by the integrand to give `(det T) ^ a`. -/
private theorem abs_det_pow_mul_det_rpow {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = T)
    (hT : T.PosDef) (a : ℝ) :
    |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) * T.det ^ (a - ((p : ℝ) + 1) / 2) =
      T.det ^ a := by
  have hdetT : (0 : ℝ) < T.det := hT.det_pos
  have hsq : (C : Matrix (Fin p) (Fin p) ℝ).det ^ 2 = T.det := by
    rw [← hC, Matrix.det_mul, Matrix.det_transpose, sq]
  have habs : |(C : Matrix (Fin p) (Fin p) ℝ).det| = T.det ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_eq_rpow]
  rw [habs, ← Real.rpow_natCast (T.det ^ ((1 : ℝ) / 2)) (p + 1), ← Real.rpow_mul hdetT.le,
    ← Real.rpow_add hdetT]
  push_cast
  ring_nf

/-- The integrand with scale `T` at a congruence image, on the positive-definite cone. -/
private theorem integrand_symmetricCongruence {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = T)
    (hT : T.PosDef) (a : ℝ) {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    ((Matrix.GeneralLinearGroup.symmetricCongruence C A :
            selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(T⁻¹ * ((Matrix.GeneralLinearGroup.symmetricCongruence C A :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
            Matrix (Fin p) (Fin p) ℝ)).trace) =
      T.det ^ (a - ((p : ℝ) + 1) / 2) *
        ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
          exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)) := by
  rw [det_coe_symmetricCongruence hC, trace_inv_mul_coe_symmetricCongruence hC,
    Real.mul_rpow hT.det_pos.le hA.det_pos.le, mul_assoc]

/-- Doubling the scale halves the trace against its inverse. -/
private theorem trace_two_smul_inv_mul (hS : S.PosDef)
    {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    ((((2 : ℝ) • S)⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace) =
      (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2 := by
  rw [Matrix.inv_smul S 2 (isUnit_iff_ne_zero.2 hS.det_pos.ne'), invOf_eq_inv, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- Doubling the scale multiplies the determinant power by `2 ^ (p * a)`. -/
private theorem det_two_smul_rpow (hS : S.PosDef) (a : ℝ) :
    ((2 : ℝ) • S).det ^ a = 2 ^ ((p : ℝ) * a) * S.det ^ a := by
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.mul_rpow (by positivity) hS.det_pos.le, ← Real.rpow_natCast (2 : ℝ) p,
    ← Real.rpow_mul (by norm_num)]

/-- **The scale matrix in the cone integral.** For a positive-definite `T`, weighting the
exponential in the cone integral by the inverse scale `T⁻¹` multiplies the integral by
`(det T) ^ a`. Lower integration is defined for every real `a`, so the identity carries no
convergence hypothesis. -/
theorem lintegral_det_rpow_mul_exp_neg_trace_inv_mul (hT : T.PosDef) (a : ℝ) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(T⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) ∂symmetricLebesgue p =
      ENNReal.ofReal (T.det ^ a) *
        ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
          ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)) ∂symmetricLebesgue p := by
  obtain ⟨C, hC⟩ := hT.exists_generalLinearGroup_mul_transpose_eq
  have hJne : ENNReal.ofReal |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) ≠ 0 :=
    pow_ne_zero _
      (ENNReal.ofReal_pos.2 (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C))).ne'
  have hJtop : ENNReal.ofReal |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hJmul : ENNReal.ofReal |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) *
      ENNReal.ofReal (T.det ^ (a - ((p : ℝ) + 1) / 2)) = ENNReal.ofReal (T.det ^ a) := by
    rw [← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _), abs_det_pow_mul_det_rpow hC hT a]
  have key := Matrix.GeneralLinearGroup.lintegral_posDef_symmetricCongruence C
    (fun A => ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
      exp (-(T⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace)))
  rw [setLIntegral_congr_fun (measurableSet_posDefMatrix p) fun A hA => by
      rw [integrand_symmetricCongruence hC hT a hA,
        ENNReal.ofReal_mul (Real.rpow_nonneg hT.det_pos.le _)],
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at key
  symm
  rw [← hJmul, mul_assoc, key, ← mul_assoc, ENNReal.mul_inv_cancel hJne hJtop, one_mul]

/-- The Bochner form of `Matrix.PosDef.lintegral_det_rpow_mul_exp_neg_trace_inv_mul`: an inverse
positive-definite scale `T` in the exponential weight multiplies the cone integral by
`(det T) ^ a`. -/
theorem integral_det_rpow_mul_exp_neg_trace_inv_mul (hT : T.PosDef) (a : ℝ) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(T⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace) ∂symmetricLebesgue p =
      T.det ^ a *
        ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace) ∂symmetricLebesgue p := by
  obtain ⟨C, hC⟩ := hT.exists_generalLinearGroup_mul_transpose_eq
  have hJpos : (0 : ℝ) < |(C : Matrix (Fin p) (Fin p) ℝ).det| ^ (p + 1) :=
    pow_pos (abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)) _
  have key := Matrix.GeneralLinearGroup.integral_posDef_symmetricCongruence C
    (fun A => (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
      exp (-(T⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace))
  rw [setIntegral_congr_fun (measurableSet_posDefMatrix p)
      fun A hA => integrand_symmetricCongruence hC hT a hA,
    integral_const_mul, smul_eq_mul] at key
  symm
  rw [← abs_det_pow_mul_det_rpow hC hT a, mul_assoc, key, ← mul_assoc,
    mul_inv_cancel₀ hJpos.ne', one_mul]

/-- The halved form of `Matrix.PosDef.lintegral_det_rpow_mul_exp_neg_trace_inv_mul` used by the
Wishart densities, whose exponential weight is `exp (-trace (S⁻¹ * A) / 2)`: the scale is then
`2 • S` and the factor is `2 ^ (p * a) * (det S) ^ a`. -/
theorem lintegral_det_rpow_mul_exp_neg_trace_inv_mul_div_two (hS : S.PosDef) (a : ℝ) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2)) ∂symmetricLebesgue p =
      ENNReal.ofReal (2 ^ ((p : ℝ) * a) * S.det ^ a) *
        ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
          ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace)) ∂symmetricLebesgue p := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h := lintegral_det_rpow_mul_exp_neg_trace_inv_mul (hS.smul h2) a
  rw [det_two_smul_rpow hS a] at h
  rw [← h]
  exact setLIntegral_congr_fun (measurableSet_posDefMatrix p)
    fun A _ => by rw [trace_two_smul_inv_mul hS, neg_div]

/-- The Bochner form of
`Matrix.PosDef.lintegral_det_rpow_mul_exp_neg_trace_inv_mul_div_two`. -/
theorem integral_det_rpow_mul_exp_neg_trace_inv_mul_div_two (hS : S.PosDef) (a : ℝ) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2) ∂symmetricLebesgue p =
      2 ^ ((p : ℝ) * a) * S.det ^ a *
        ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace) ∂symmetricLebesgue p := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h := integral_det_rpow_mul_exp_neg_trace_inv_mul (hS.smul h2) a
  rw [det_two_smul_rpow hS a] at h
  rw [← h]
  exact setIntegral_congr_fun (measurableSet_posDefMatrix p)
    fun A _ => by rw [trace_two_smul_inv_mul hS, neg_div]

end Matrix.PosDef
