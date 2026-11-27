/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Invariant
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Real
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import TauCeti.NumberTheory.LocalField.Units.Haar

/-!
# Eigendistributions on the multiplicative group of a nonarchimedean local field

Let `F` be a nonarchimedean local field. Its multiplicative group acts on the test functions
`C_c^∞(F^×)`, the locally constant compactly supported functions `F^× → ℂ`, by dilation
`(r(a) f)(x) = f(x a)`, and on their algebraic dual by `r′(a) λ = λ ∘ r(a⁻¹)`. For a quasi-character
`ω : F^× → ℂ^×`, the `ω`-eigendistributions on `C_c^∞(F^×)` are the functionals `λ` with
`r′(a) λ = ω(a) λ` for every `a`; they form the space `C_c^∞(F^×)′(ω)` of Tate's local theory.
This file shows that it is the line spanned by `f ↦ ∫ f(x) ω(x) d^×x`, for the Haar measure `d^×x`
giving `𝒪_F^×` volume one (`TauCeti.unitsHaar`).

Since `F^×` is commutative, `r(a⁻¹)` is the left translation `f ↦ f(a⁻¹ ·)` of
`TauCeti.compactlySupportedRep`, so `r′(a)` is the contragredient of left translation at `a⁻¹`, and
`C_c^∞(F^×)′(ω)` is the `ω⁻¹`-eigensubmodule of that contragredient: by
`Representation.mem_charEigenspace_dual_iff` its elements are the `λ` with
`λ(f(a⁻¹ ·)) = ω(a) λ(f)`. A quasi-character has open kernel, so it is locally constant
(`TauCeti.ClassFieldTheory.isLocallyConstant_character`), and multiplying by it turns
eigendistributions into invariant functionals (`TauCeti.dual_charEigenspace_compactlySupportedRep`).
The integral is the one of the volumes `d^×x(K)` of compact open sets `K`
(`TauCeti.HaarMeasureWithValues.ofMeasure`), with values in `ℂ`.

## Main results

* `TauCeti.dual_charEigenspace_inv_compactlySupportedRep_units`: `C_c^∞(F^×)′(ω)` is spanned by
  `f ↦ ∫ f(x) ω(x) d^×x`.
* `TauCeti.finrank_dual_charEigenspace_inv_compactlySupportedRep_units`: `C_c^∞(F^×)′(ω)` is
  one-dimensional.

## References

* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, Birkhäuser, 2003, §3.
-/

public section

noncomputable section

open LocallyConstant Module

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The units `𝒪[K]ˣ = U(K, 0)`, as an open subgroup of `Kˣ`. -/
private def unitsIntegerOpenSubgroup : OpenSubgroup Kˣ :=
  ⟨unitFiltration K 0, isOpen_unitFiltration 0⟩

private theorem isCompact_unitsIntegerOpenSubgroup :
    IsCompact (unitsIntegerOpenSubgroup K : Set Kˣ) :=
  isCompact_unitFiltration 0

private theorem hasUnitProOrder_unitsIntegerOpenSubgroup :
    HasUnitProOrder ℂ (unitsIntegerOpenSubgroup K) :=
  have := isCompact_iff_compactSpace.1 (isCompact_unitsIntegerOpenSubgroup K)
  hasUnitProOrder_of_algebra ℚ

/-- The `ℂ`-valued volumes of `d^×x` are those of the Haar measure normalised on `𝒪[K]ˣ`. -/
private theorem map_ofMeasure_unitsHaar [MeasurableSpace K] [BorelSpace K] :
    (HaarMeasureWithValues.ofMeasure (unitsHaar K)).map Complex.ofRealHom.toAddMonoidHom =
      HaarMeasureWithValues.normalized ℂ (unitsIntegerOpenSubgroup K)
        (isCompact_unitsIntegerOpenSubgroup K) (hasUnitProOrder_unitsIntegerOpenSubgroup K) := by
  refine (HaarMeasureWithValues.eq_normalized_iff _ _).2 ?_
  rw [HaarMeasureWithValues.map_apply, HaarMeasureWithValues.ofMeasure_apply,
    OpenSubgroup.coe_toCompactOpens, MeasureTheory.measureReal_def]
  change Complex.ofRealHom.toAddMonoidHom (unitsHaar K (unitFiltration K 0)).toReal = 1
  rw [unitsHaar_unitFiltration_zero, ENNReal.toReal_one]
  exact Complex.ofReal_one

/-- The inverse of a quasi-character of `Kˣ` is locally constant. -/
private theorem isLocallyConstant_inv_character (ω : Kˣ →ₜ* ℂˣ) :
    IsLocallyConstant ⇑ω.toMonoidHom⁻¹ :=
  (ClassFieldTheory.isLocallyConstant_character K ω).comp fun u ↦ u⁻¹

/-- **The `ω`-eigendistributions on `C_c^∞(F^×)` are the multiples of `ω(x) d^×x`.** For a
quasi-character `ω` of the multiplicative group of a nonarchimedean local field `K`, the
functionals `λ` on `C_c^∞(Kˣ)` with `λ(f(a⁻¹ ·)) = ω(a) λ(f)`, which form the `ω⁻¹`-eigensubmodule
of the contragredient of left translation, are the multiples of `f ↦ ∫ f(x) ω(x) d^×x`, where
`d^×x` is the Haar measure giving `𝒪[K]ˣ` volume one. -/
theorem dual_charEigenspace_inv_compactlySupportedRep_units [MeasurableSpace K] [BorelSpace K]
    (ω : Kˣ →ₜ* ℂˣ) :
    (compactlySupportedRep ℂ Kˣ Kˣ ℂ).dual.charEigenspace ω.toMonoidHom⁻¹ =
      ℂ ∙ (((HaarMeasureWithValues.ofMeasure (unitsHaar K)).map
          Complex.ofRealHom.toAddMonoidHom).integral ∘ₗ
        compactlySupported.mulLeft
          ((⟨ω, ClassFieldTheory.isLocallyConstant_character K ω⟩ :
            LocallyConstant Kˣ ℂˣ).map (↑))) := by
  rw [dual_charEigenspace_compactlySupportedRep (isCompact_unitsIntegerOpenSubgroup K)
    (hasUnitProOrder_unitsIntegerOpenSubgroup K) _ (isLocallyConstant_inv_character K ω),
    map_ofMeasure_unitsHaar]
  congr 3

/-- **`C_c^∞(F^×)′(ω)` is one-dimensional.** For a quasi-character `ω` of the multiplicative group
of a nonarchimedean local field `K`, the functionals `λ` on `C_c^∞(Kˣ)` with
`λ(f(a⁻¹ ·)) = ω(a) λ(f)` form a line. -/
theorem finrank_dual_charEigenspace_inv_compactlySupportedRep_units (ω : Kˣ →ₜ* ℂˣ) :
    finrank ℂ ((compactlySupportedRep ℂ Kˣ Kˣ ℂ).dual.charEigenspace ω.toMonoidHom⁻¹) = 1 :=
  finrank_dual_charEigenspace_compactlySupportedRep (isCompact_unitsIntegerOpenSubgroup K)
    (hasUnitProOrder_unitsIntegerOpenSubgroup K) _ (isLocallyConstant_inv_character K ω)

end TauCeti
