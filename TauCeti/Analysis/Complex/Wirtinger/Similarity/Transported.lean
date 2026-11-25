/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Conformal

/-!
# A non-constant complex structure for the similarity principle

For a family `Φ : ℂ → V ≃L[ℝ] V` of real-linear automorphisms of a complex normed space,
`J = Φ i Φ⁻¹` is a complex structure with `J Φ = Φ i`, and with `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`
every `ξ = Φ σ` with `σ` holomorphic solves `∂_s ξ + J ∂_t ξ + C ξ = 0`. So the similarity
principle for `∂_s ξ + J ∂_t ξ + C ξ = 0` must allow a non-constant `J`. For families `C¹` on an
open set with continuous inverse there, `C` is continuous on that set, hence locally `Lᵖ`. The
opposite normalization is excluded: if `J' Φ = -Φ i` at `z₀`, then `ξ w = Φ w ((w - z₀) v)`,
`v ≠ 0`, fails `∂_s ξ + J' ∂_t ξ + C' ξ = 0` at `z₀` for every `C'`.

## Main declarations

* `TauCeti.transportedComplexStructure`: the complex structure `J = Φ i Φ⁻¹`.
* `TauCeti.transportedCoeff`: the coefficient `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`, for a field of
  derivatives of `Φ`.
* `TauCeti.add_transportedComplexStructure_add_transportedCoeff_eq_zero`: the pointwise identity
  behind the transport, shared with the Sobolev version.
* `TauCeti.fderiv_apply_add_transportedComplexStructure_add_eq_zero`: `Φ σ` solves the equation
  for `J = Φ i Φ⁻¹`.
* `TauCeti.fderiv_apply_smul_add_ne_zero`: the normalization `J' Φ = -Φ i` fails.
* `TauCeti.memLpLoc_transportedCoeff`: the coefficient is locally `Lᵖ` for a `C¹` family.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5, the Carleman similarity principle).
-/

public noncomputable section

open Complex ContinuousLinearMap

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The complex structure `J = Φ i Φ⁻¹` transported from multiplication by `i` along
real-linear automorphisms `Φ z`. -/
def transportedComplexStructure (Φ : ℂ → V ≃L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  (Φ z).conjContinuousAlgEquiv (I • ContinuousLinearMap.id ℝ V)

/-- The coefficient `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹` that absorbs the derivative of `Φ`, for a field
`DΦ` of derivatives of `Φ`, with `∂_s Φ = DΦ · 1` and `∂_t Φ = DΦ · I`. For `C¹` families
`DΦ` is `fderiv`; for Sobolev families it is a weak derivative. -/
def transportedCoeff (Φ : ℂ → V ≃L[ℝ] V) (DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  -((DΦ z 1 + transportedComplexStructure Φ z ∘L DΦ z I) ∘L ((Φ z).symm : V →L[ℝ] V))

variable {Φ : ℂ → V ≃L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- `J v = Φ (i Φ⁻¹ v)`. -/
theorem transportedComplexStructure_apply (z : ℂ) (v : V) :
    transportedComplexStructure Φ z v = Φ z (I • (Φ z).symm v) := (rfl)

/-- `C v = -(∂_s Φ (Φ⁻¹ v) + J ∂_t Φ (Φ⁻¹ v))`. -/
theorem transportedCoeff_apply (z : ℂ) (v : V) :
    transportedCoeff Φ DΦ z v =
      -(DΦ z 1 ((Φ z).symm v) + transportedComplexStructure Φ z (DΦ z I ((Φ z).symm v))) :=
  (rfl)

/-- `J Φ = Φ i`. -/
@[simp]
theorem transportedComplexStructure_apply_apply (z : ℂ) (v : V) :
    transportedComplexStructure Φ z (Φ z v) = Φ z (I • v) := by
  rw [transportedComplexStructure_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- `J² = -1`. -/
theorem transportedComplexStructure_comp_self (z : ℂ) :
    transportedComplexStructure Φ z ∘L transportedComplexStructure Φ z =
      -ContinuousLinearMap.id ℝ V := by
  rw [transportedComplexStructure, ← ContinuousLinearMap.mul_def, ← map_mul,
    ContinuousLinearMap.mul_def]
  ext v
  simp [smul_smul]

/-- For `Φ` and `Φ⁻¹` continuous on `U`, the structure `J = Φ i Φ⁻¹` is continuous on `U`. -/
theorem continuousOn_transportedComplexStructure {U : Set ℂ}
    (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) U)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) U) :
    ContinuousOn (transportedComplexStructure Φ) U :=
  hΦ.clm_comp (continuousOn_const.clm_comp hΨ)

/-- **The pointwise identity behind the transport.** For a value `σ z = v`, a complex-linear
derivative `σ'` of `σ` (so `σ' I = I • σ' 1`) and the Leibniz derivative
`D(Φ σ) = DΦ · σ + Φ σ'`, the expression `∂_s(Φ σ) + J ∂_t(Φ σ) + C (Φ σ)` vanishes, because
`J Φ = Φ i`. -/
theorem add_transportedComplexStructure_add_transportedCoeff_eq_zero (z : ℂ) (v : V)
    {σ' : ℂ →L[ℝ] V} (hσ' : σ' I = I • σ' 1) :
    DΦ z 1 v + Φ z (σ' 1) + transportedComplexStructure Φ z (DΦ z I v + Φ z (σ' I)) +
      transportedCoeff Φ DΦ z (Φ z v) = 0 := by
  simp only [hσ', transportedComplexStructure_apply, transportedCoeff_apply, map_add,
    ContinuousLinearEquiv.symm_apply_apply, smul_smul, I_mul_I, neg_smul, one_smul, map_neg]
  abel

/-- For `J = Φ i Φ⁻¹` and `C = -(∂_s Φ + J ∂_t Φ) Φ⁻¹`, every `ξ = Φ σ` with `σ` holomorphic
solves `∂_s ξ + J ∂_t ξ + C ξ = 0`. -/
theorem fderiv_apply_add_transportedComplexStructure_add_eq_zero {σ : ℂ → V} {z : ℂ}
    (hΦ : DifferentiableAt ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z) (hσ : DifferentiableAt ℂ σ z) :
    fderiv ℝ (fun w ↦ Φ w (σ w)) z 1 +
        transportedComplexStructure Φ z (fderiv ℝ (fun w ↦ Φ w (σ w)) z I) +
      transportedCoeff Φ (fderiv ℝ fun w ↦ (Φ w : V →L[ℝ] V)) z (Φ z (σ z)) = 0 := by
  have hD := hΦ.hasFDerivAt.clm_apply (hσ.restrictScalars ℝ).hasFDerivAt
  simp only [ContinuousLinearEquiv.coe_coe] at hD
  rw [hD.fderiv]
  simpa only [add_apply, comp_apply, ContinuousLinearEquiv.coe_coe, flip_apply, add_comm] using
    add_transportedComplexStructure_add_transportedCoeff_eq_zero
      (DΦ := fderiv ℝ fun w ↦ (Φ w : V →L[ℝ] V)) z (σ z)
      (differentiableAt_complex_iff_differentiableAt_real.1 hσ).2

/-- The normalization `Φ⁻¹ J' Φ = -i` is wrong: if `J' Φ = -Φ i` at `z₀` and `v ≠ 0`, then
`ξ w = Φ w ((w - z₀) v)` fails `∂_s ξ + J' ∂_t ξ + C' ξ = 0` at its zero `z₀`, whatever `C'`. -/
theorem fderiv_apply_smul_add_ne_zero {z₀ : ℂ}
    (hΦ : DifferentiableAt ℝ (fun w ↦ (Φ w : V →L[ℝ] V)) z₀) {J' C' : V →L[ℝ] V}
    (hJ' : ∀ v, J' (Φ z₀ v) = -Φ z₀ (I • v)) {v : V} (hv : v ≠ 0) :
    fderiv ℝ (fun w ↦ Φ w ((w - z₀) • v)) z₀ 1 +
        J' (fderiv ℝ (fun w ↦ Φ w ((w - z₀) • v)) z₀ I) +
      C' (Φ z₀ ((z₀ - z₀) • v)) ≠ 0 := by
  have hσ : HasFDerivAt (fun w : ℂ ↦ (w - z₀) • v) ((ContinuousLinearMap.id ℝ ℂ).smulRight v) z₀ :=
    ((hasFDerivAt_id z₀).sub_const z₀).smul_const v
  have hD := hΦ.hasFDerivAt.clm_apply hσ
  simp only [ContinuousLinearEquiv.coe_coe] at hD
  rw [hD.fderiv]
  simp only [sub_self, zero_smul, map_zero, add_zero, comp_apply, smulRight_apply, id_apply,
    one_smul, ContinuousLinearEquiv.coe_coe, hJ', smul_smul, I_mul_I, neg_smul, map_neg, neg_neg,
    ne_eq]
  rw [← two_smul ℝ]
  exact smul_ne_zero two_ne_zero ((Φ z₀).map_ne_zero_iff.mpr hv)

/-- For a family `Φ` and its inverse continuous on `U` and a derivative field `DΦ` continuous on
`U`, the coefficient `C` is continuous on `U`. -/
theorem continuousOn_transportedCoeff {U : Set ℂ}
    (hΦ : ContinuousOn (fun w ↦ (Φ w : V →L[ℝ] V)) U)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) U) (hD : ContinuousOn DΦ U) :
    ContinuousOn (transportedCoeff Φ DΦ) U :=
  (((hD.clm_apply continuousOn_const).add ((continuousOn_transportedComplexStructure hΦ hΨ).clm_comp
    (hD.clm_apply continuousOn_const))).clm_comp hΨ).neg

/-- For a family `C¹` on an open set `U` with inverse continuous on `U`, the coefficient `C` for
the derivative `fderiv` is locally `Lᵖ` on `U`. -/
theorem memLpLoc_transportedCoeff {U : Set ℂ} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ 1 (fun w ↦ (Φ w : V →L[ℝ] V)) U)
    (hΨ : ContinuousOn (fun w ↦ ((Φ w).symm : V →L[ℝ] V)) U) (p : ENNReal) :
    MemLpLoc p U (transportedCoeff Φ (fderiv ℝ fun w ↦ (Φ w : V →L[ℝ] V))) :=
  (continuousOn_transportedCoeff hΦ.continuousOn hΨ
    (hΦ.continuousOn_fderiv_of_isOpen hU le_rfl)).memLpLoc

end TauCeti
