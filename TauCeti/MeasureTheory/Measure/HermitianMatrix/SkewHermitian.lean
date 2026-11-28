/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Jacobian
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import TauCeti.Algebra.Star.SelfAdjoint.BaseChange

/-!
# Lebesgue measure on skew-Hermitian matrices

`TauCeti.skewHermitianLebesgue p` is the image of the coordinate Lebesgue measure
`TauCeti.hermitianLebesgue p` on the Hermitian matrices of size `p` under `S ↦ i S`. In
coordinates it is the Lebesgue measure of the entries `Im S_aa` and `Re S_ab`, `Im S_ab` (`a < b`)
of a skew-Hermitian matrix `S`; divided by the volume of `U(p)` it is the measure that gives the
compact-dual normalisation of the Cayley measure (`Matrix.unitaryGroupOf.cayleyMeasure`).

## Main results

* `TauCeti.skewHermitianLebesgue`, with `TauCeti.lintegral_skewHermitianLebesgue`:
  `∫⁻ S, g S ∂skewHermitianLebesgue p = ∫⁻ H, g (i H) ∂hermitianLebesgue p`.
* `TauCeti.lintegral_eq_inv_two_pow_mul_lintegral_lintegral_add`: writing a square complex matrix
  as `Z = S + T / 2` with `S` skew-Hermitian and `T` Hermitian, `dZ = 2 ^ (-p) dS dT`. This is
  `TauCeti.lintegral_eq_inv_two_pow_mul_lintegral_lintegral_I_smul_add` with `S = i H`.
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped ENNReal

namespace TauCeti

variable (p : ℕ)

/-- **Lebesgue measure on the skew-Hermitian matrices** of size `p`: the image of
`TauCeti.hermitianLebesgue p` under `H ↦ i H`, that is, the Lebesgue measure of the coordinates
`Im S_aa` and `Re S_ab`, `Im S_ab` (`a < b`). The map `H ↦ i H` is the inverse of
`TauCeti.skewAdjointEquivSelfAdjoint` for the skew-adjoint unit `-i`. -/
def skewHermitianLebesgue : Measure (skewAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (hermitianLebesgue p).map (skewAdjointEquivSelfAdjoint (-Units.mk0 I I_ne_zero)
    (neg_mem Complex.val_mk0_I_mem_skewAdjoint)).symm

/-- Defining formula for `TauCeti.skewHermitianLebesgue`: the image of
`TauCeti.hermitianLebesgue p` under `H ↦ i H`. -/
theorem skewHermitianLebesgue_def :
    skewHermitianLebesgue p =
      (hermitianLebesgue p).map (skewAdjointEquivSelfAdjoint (-Units.mk0 I I_ne_zero)
        (neg_mem Complex.val_mk0_I_mem_skewAdjoint)).symm := (rfl)

instance isAddHaarMeasure_skewHermitianLebesgue : (skewHermitianLebesgue p).IsAddHaarMeasure :=
  (skewAdjointEquivSelfAdjoint _ _).symm.toContinuousLinearEquiv.isAddHaarMeasure_map _

/-- Integrals for `TauCeti.skewHermitianLebesgue` are integrals of `H ↦ g (i H)` for
`TauCeti.hermitianLebesgue`. -/
theorem lintegral_skewHermitianLebesgue (g : Matrix (Fin p) (Fin p) ℂ → ℝ≥0∞) :
    ∫⁻ S, g S ∂skewHermitianLebesgue p =
      ∫⁻ H, g (I • (H : Matrix (Fin p) (Fin p) ℂ)) ∂hermitianLebesgue p := by
  refine ((skewAdjointEquivSelfAdjoint (-Units.mk0 I I_ne_zero)
    (neg_mem Complex.val_mk0_I_mem_skewAdjoint)).symm.toContinuousLinearEquiv.toHomeomorph
      |>.measurableEmbedding.lintegral_map (μ := hermitianLebesgue p) fun S ↦ g S).trans ?_
  simp

variable {p} in
/-- **Lebesgue measure on square matrices in skew-Hermitian and Hermitian coordinates.** Writing a
complex matrix of size `p` as `Z = S + T / 2`, with `S` skew-Hermitian and `T` Hermitian,
`dZ = 2 ^ (-p) dS dT` for `TauCeti.skewHermitianLebesgue p` and `TauCeti.hermitianLebesgue p`. -/
theorem lintegral_eq_inv_two_pow_mul_lintegral_lintegral_add
    {g : Matrix (Fin p) (Fin p) ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ Z, g Z = (2 ^ p)⁻¹ * ∫⁻ T, ∫⁻ S, g ((S : Matrix (Fin p) (Fin p) ℂ) +
      (2⁻¹ : ℝ) • (T : Matrix (Fin p) (Fin p) ℂ))
        ∂skewHermitianLebesgue p ∂hermitianLebesgue p := by
  rw [lintegral_eq_inv_two_pow_mul_lintegral_lintegral_I_smul_add hg]
  congr 1
  exact lintegral_congr fun T ↦ (lintegral_skewHermitianLebesgue p
    fun M ↦ g (M + (2⁻¹ : ℝ) • (T : Matrix (Fin p) (Fin p) ℂ))).symm

end TauCeti
