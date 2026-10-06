/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of the norm away from the origin

Mathlib computes the derivative of `x ↦ ‖x‖ ^ p` on the whole inner-product space when
`1 < p`.  Negative powers, which occur in the Newtonian kernel, are smooth only away from the
origin.  This file supplies the corresponding local derivative, Hessian, and Laplacian formulas
under the explicit hypothesis `x ≠ 0`, together with the Laplacian of the dipole-type product
`x ↦ ⟪a, x⟫ ‖x‖^p`.  The critical exponents give the functions `‖x‖^(2 - dim E)` and
`⟪a, x⟫ ‖x‖^(-dim E)`, harmonic away from the origin, from which the Poisson kernel of a ball is
assembled.

The first derivative proof adapts Mathlib's `hasFDerivAt_norm_rpow`, retaining its norm-square
chain-rule argument while replacing the global exponent hypothesis with the local condition
`x ≠ 0`.

## Main declarations

* `norm_rpow_eq_norm_sq_rpow`: a real power of the norm as a power of the squared norm.
* `hasFDerivAt_norm_rpow_of_ne`: the derivative of an arbitrary real power away from zero.
* `iteratedFDeriv_two_norm_rpow_apply`: the Hessian of an arbitrary real power away from zero.
* `laplacian_norm_rpow_of_ne`: the radial Laplacian formula
  `Δ ‖x‖^p = p (p + dim E - 2) ‖x‖^(p-2)` away from zero.
* `laplacian_inner_mul_norm_rpow_of_ne`: the dipole formula
  `Δ (⟪a, x⟫ ‖x‖^p) = p (p + dim E) ⟪a, x⟫ ‖x‖^(p-2)` away from zero.
* `harmonicAt_norm_rpow_two_sub_finrank`, `harmonicAt_inner_mul_norm_rpow_neg_finrank`: the
  harmonic radial and dipole powers.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A real power of the norm, written as a power of the squared norm. -/
theorem norm_rpow_eq_norm_sq_rpow (x : E) (p : ℝ) : ‖x‖ ^ p = (‖x‖ ^ 2) ^ (p / 2) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  congr 1
  push_cast
  ring

/-- Away from the origin, the derivative of `x ↦ ‖x‖ ^ p` is
`p ‖x‖ ^ (p - 2) ⟨x, ·⟩`.  Unlike Mathlib's `hasFDerivAt_norm_rpow`, this local form
allows every real exponent. -/
theorem hasFDerivAt_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- The Fréchet derivative of an arbitrary real power of the norm away from the origin. -/
theorem fderiv_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖ ^ p) x = (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x :=
  (hasFDerivAt_norm_rpow_of_ne p hx).fderiv

/-- The Hessian of `x ↦ ‖x‖ ^ p` away from the origin, evaluated on two directions. -/
theorem iteratedFDeriv_two_norm_rpow_apply (p : ℝ) {x : E} (hx : x ≠ 0) (v w : E) :
    iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ p) x ![v, w] =
      p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ +
        p * ‖x‖ ^ (p - 2) * ⟪v, w⟫_ℝ := by
  have hne : ∀ᶠ y in nhds x, y ≠ 0 := eventually_ne_nhds hx
  have hfd : fderiv ℝ (fun y : E ↦ ‖y‖ ^ p) =ᶠ[nhds x]
      fun y ↦ (p * ‖y‖ ^ (p - 2)) • innerSL ℝ y := by
    filter_upwards [hne] with y hy
    exact fderiv_norm_rpow_of_ne p hy
  have hc : DifferentiableAt ℝ (fun y : E ↦ p * ‖y‖ ^ (p - 2)) x :=
    (hasFDerivAt_norm_rpow_of_ne (p - 2) hx).const_mul p |>.differentiableAt
  have hi : DifferentiableAt ℝ (innerSL ℝ : E → E →L[ℝ] ℝ) x :=
    (innerSL ℝ).differentiableAt
  rw [iteratedFDeriv_two_apply, hfd.fderiv_eq, fderiv_fun_smul hc hi]
  rw [((hasFDerivAt_norm_rpow_of_ne (p - 2) hx).const_mul p).fderiv]
  rw [(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv]
  -- `innerSL ℝ` is bundled as a conjugate-linear map, so this evaluation is not syntactically
  -- an instance of `innerSL_apply_apply`; it is stated separately rather than proved by `rfl`.
  have hinner : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) v w = ⟪v, w⟫_ℝ := innerSL_apply_apply (𝕜 := ℝ) v w
  simp only [Fin.isValue, Matrix.cons_val_zero, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, coe_innerSL_apply, smul_eq_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hinner]
  ring_nf

variable [FiniteDimensional ℝ E]

/-- The Laplacian of a real power of the norm away from the origin is
`p (p + dim E - 2) ‖x‖ ^ (p - 2)`. -/
theorem laplacian_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ ‖y‖ ^ p) x =
      p * (p + Module.finrank ℝ E - 2) * ‖x‖ ^ (p - 2) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : E ↦ ‖y‖ ^ p) (stdOrthonormalBasis ℝ E)) x]
  simp_rw [iteratedFDeriv_two_norm_rpow_apply p hx]
  rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ i, p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, stdOrthonormalBasis ℝ E i⟫_ℝ *
          ⟪x, stdOrthonormalBasis ℝ E i⟫_ℝ =
        p * (p - 2) * ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst]
  simp_rw [real_inner_self_eq_norm_sq,
    (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one, one_pow]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrpow : ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 2) := by
    calc
      ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 4) * ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two]
      _ = ‖x‖ ^ ((p - 4) + 2) := (Real.rpow_add hnorm _ _).symm
      _ = ‖x‖ ^ (p - 2) := by ring_nf
  rw [mul_assoc (p * (p - 2)), hrpow]
  ring

/-- The Laplacian of the dipole-type product `x ↦ ⟪a, x⟫ ‖x‖ ^ p` away from the origin is
`p (p + dim E) ⟪a, x⟫ ‖x‖ ^ (p - 2)`. -/
theorem laplacian_inner_mul_norm_rpow_of_ne (a : E) (p : ℝ) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ ⟪a, y⟫_ℝ * ‖y‖ ^ p) x =
      p * (p + Module.finrank ℝ E) * ⟪a, x⟫_ℝ * ‖x‖ ^ (p - 2) := by
  have hℓd : ∀ y, HasFDerivAt (fun y : E ↦ ⟪a, y⟫_ℝ) (toDual ℝ E a) y :=
    fun y ↦ (toDual ℝ E a).hasFDerivAt
  have hℓ : ContDiffAt ℝ 2 (fun y : E ↦ ⟪a, y⟫_ℝ) x := (toDual ℝ E a).contDiff.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ p) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  -- The linear factor has constant derivative, hence vanishing Laplacian.
  have hΔℓ : Δ (fun y : E ↦ ⟪a, y⟫_ℝ) x = 0 := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)) x]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, funext fun y ↦ (hℓd y).fderiv]
    simp
  rw [hℓ.laplacian_fun_mul hg, laplacian_norm_rpow_of_ne p hx, hΔℓ,
    (hasGradientAt_iff_hasFDerivAt.mpr (hℓd x)).gradient, inner_gradient_right, conj_trivial,
    fderiv_norm_rpow_of_ne p hx]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm x a]
  ring

/-- Away from the origin, `x ↦ ‖x‖ ^ (2 - dim E)` is harmonic. -/
theorem harmonicAt_norm_rpow_two_sub_finrank {x : E} (hx : x ≠ 0) :
    HarmonicAt (fun y : E ↦ ‖y‖ ^ (2 - Module.finrank ℝ E : ℝ)) x := by
  refine ⟨(contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_norm_rpow_of_ne _ hy, Pi.zero_apply]
  ring

/-- Away from the origin, the dipole `x ↦ ⟪a, x⟫ ‖x‖ ^ (-dim E)` is harmonic. -/
theorem harmonicAt_inner_mul_norm_rpow_neg_finrank (a : E) {x : E} (hx : x ≠ 0) :
    HarmonicAt (fun y : E ↦ ⟪a, y⟫_ℝ * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ))) x := by
  refine ⟨(toDual ℝ E a).contDiff.contDiffAt.mul
    ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_inner_mul_norm_rpow_of_ne a _ hy, Pi.zero_apply]
  ring

end TauCeti

end
