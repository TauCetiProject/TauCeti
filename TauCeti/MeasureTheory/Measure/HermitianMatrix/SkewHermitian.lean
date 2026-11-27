/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Jacobian
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

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

/-- Multiplication by `i`, as a real linear equivalence from the Hermitian onto the
skew-Hermitian matrices of size `p`. -/
def iSMulHermitian :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃L[ℝ]
      skewAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun H := ⟨I • (H : Matrix (Fin p) (Fin p) ℂ),
        I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr H.property⟩
      invFun S := ⟨-I • (S : Matrix (Fin p) (Fin p) ℂ),
        (skewAdjoint.negISMul (⟨S, S.property⟩ : skewAdjoint (Matrix (Fin p) (Fin p) ℂ))).property⟩
      map_add' H H' := Subtype.ext (smul_add _ _ _)
      map_smul' c H := Subtype.ext (smul_comm _ _ _)
      left_inv H := Subtype.ext (by simp [smul_smul])
      right_inv S := Subtype.ext (by simp [smul_smul]) }

@[simp]
theorem coe_iSMulHermitian_apply (H : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (iSMulHermitian p H : Matrix (Fin p) (Fin p) ℂ) = I • (H : Matrix (Fin p) (Fin p) ℂ) :=
  (rfl)

/-- **Lebesgue measure on the skew-Hermitian matrices** of size `p`: the image of
`TauCeti.hermitianLebesgue p` under `H ↦ i H`, that is, the Lebesgue measure of the coordinates
`Im S_aa` and `Re S_ab`, `Im S_ab` (`a < b`). -/
def skewHermitianLebesgue : Measure (skewAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (hermitianLebesgue p).map (iSMulHermitian p)

instance isAddHaarMeasure_skewHermitianLebesgue : (skewHermitianLebesgue p).IsAddHaarMeasure :=
  (iSMulHermitian p).isAddHaarMeasure_map _

/-- Integrals for `TauCeti.skewHermitianLebesgue` are integrals of `H ↦ g (i H)` for
`TauCeti.hermitianLebesgue`. -/
theorem lintegral_skewHermitianLebesgue
    (g : skewAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) → ℝ≥0∞) :
    ∫⁻ S, g S ∂skewHermitianLebesgue p = ∫⁻ H, g (iSMulHermitian p H) ∂hermitianLebesgue p :=
  (iSMulHermitian p).toHomeomorph.measurableEmbedding.lintegral_map g

variable {p} in
/-- **Lebesgue measure on square matrices in skew-Hermitian and Hermitian coordinates.** Writing a
complex matrix of size `p` as `Z = S + T / 2`, with `S` skew-Hermitian and `T` Hermitian,
`dZ = 2 ^ (-p) dS dT` for `TauCeti.skewHermitianLebesgue p` and `TauCeti.hermitianLebesgue p`. -/
theorem lintegral_eq_inv_two_pow_mul_lintegral_lintegral_add
    {g : Matrix (Fin p) (Fin p) ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ Z, g Z = (2 ^ p)⁻¹ * ∫⁻ T, ∫⁻ S, g ((S : Matrix (Fin p) (Fin p) ℂ) +
      (2⁻¹ : ℝ) • (T : Matrix (Fin p) (Fin p) ℂ))
        ∂skewHermitianLebesgue p ∂hermitianLebesgue p := by
  simp only [lintegral_skewHermitianLebesgue, coe_iSMulHermitian_apply]
  exact lintegral_eq_inv_two_pow_mul_lintegral_lintegral_I_smul_add hg

end TauCeti
