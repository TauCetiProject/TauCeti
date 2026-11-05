/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space

/-!
# Restriction of BV functions

Restriction to an open subset preserves integrability and decreases total variation.
`TauCeti.BV.restrictL` implements this operation on almost-everywhere classes as a
contractive continuous linear map for the BV norm, not merely for the weaker `L¹` norm.
Its representative agrees with the original function almost everywhere on the smaller
domain. Restriction commutes with forming a BV class and is functorial.

These maps allow BV convergence to be localized without choosing compatible pointwise
representatives. Equality can also be checked after restriction to a countable open cover.
No finiteness or boundary regularity of the domains is required.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω U V : Opens E}

variable [OpensMeasurableSpace E]

namespace BV

/-- Restriction of BV classes to an open subset, as a continuous linear contraction
for the sum of the `L¹` norm and total variation. -/
def restrictL (hU : U ≤ Ω) : BV μ Ω →L[ℝ] BV μ U :=
  let r : BV μ Ω →ₗ[ℝ] BV μ U := {
    toFun u := ofFunction u (u.memBV.mono hU)
    map_add' u v := by
      apply ext
      filter_upwards [coeFn_ofFunction (u + v) ((u + v).memBV.mono hU),
        coeFn_add (ofFunction u (u.memBV.mono hU)) (ofFunction v (v.memBV.mono hU)),
        coeFn_ofFunction u (u.memBV.mono hU), coeFn_ofFunction v (v.memBV.mono hU),
        ae_restrict_of_ae_restrict_of_subset hU (coeFn_add u v)] with x h₁ h₂ h₃ h₄ h₅
      simp_all
    map_smul' c u := by
      apply ext
      filter_upwards [coeFn_ofFunction (c • u) ((c • u).memBV.mono hU),
        coeFn_smul c (ofFunction u (u.memBV.mono hU)),
        coeFn_ofFunction u (u.memBV.mono hU),
        ae_restrict_of_ae_restrict_of_subset hU (coeFn_smul c u)] with x h₁ h₂ h₃ h₄
      simp_all }
  r.mkContinuous 1 fun u => by
    dsimp only [r, LinearMap.coe_mk, AddHom.coe_mk]
    rw [one_mul, norm_def, norm_def]
    apply add_le_add
    · rw [Lp.norm_def, Lp.norm_def,
        eLpNorm_congr_ae (coeFn_ofFunction u (u.memBV.mono hU))]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u.toL1)
        (eLpNorm_mono_measure _ (Measure.restrict_mono hU le_rfl))
    · rw [totalVariationOn_ofFunction]
      exact ENNReal.toReal_mono u.totalVariationOn_lt_top.ne (totalVariationOn_mono hU)

/-- The restricted class is represented by the original function almost everywhere
on the smaller domain. -/
theorem coeFn_restrictL (hU : U ≤ Ω) (u : BV μ Ω) :
    (restrictL hU u : E → ℝ) =ᵐ[μ.restrict U] u :=
  coeFn_ofFunction u (u.memBV.mono hU)

/-- Characterization of restriction, without a choice of pointwise representatives. -/
theorem restrictL_eq_iff (hU : U ≤ Ω) (u : BV μ Ω) (v : BV μ U) :
    restrictL hU u = v ↔ (u : E → ℝ) =ᵐ[μ.restrict U] v := by
  constructor
  · intro h
    exact (coeFn_restrictL hU u).symm.trans (h ▸ Filter.EventuallyEq.rfl)
  · intro h
    exact ext ((coeFn_restrictL hU u).trans h)

/-- The underlying `L¹` class of a restriction is the class of the original
representative on the smaller domain. -/
theorem toL1_restrictL (hU : U ≤ Ω) (u : BV μ Ω) :
    (restrictL hU u).toL1 = (u.integrableOn.mono_set hU).toL1 u := by
  apply Lp.ext
  exact (coeFn_restrictL hU u).trans (u.integrableOn.mono_set hU).coeFn_toL1.symm

/-- Restriction preserves total variation on the smaller open set. -/
@[simp]
theorem totalVariationOn_restrictL (hU : U ≤ Ω) (u : BV μ Ω) :
    totalVariationOn μ U (restrictL hU u) = totalVariationOn μ U u :=
  totalVariationOn_congr_ae (coeFn_restrictL hU u)

/-- The restriction operator has norm at most one. -/
theorem norm_restrictL_le_one (hU : U ≤ Ω) :
    ‖restrictL (μ := μ) hU‖ ≤ 1 := by
  unfold restrictL
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Restriction decreases the BV norm. -/
theorem norm_restrictL_le (hU : U ≤ Ω) (u : BV μ Ω) :
    ‖restrictL hU u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using (restrictL hU).le_of_opNorm_le (norm_restrictL_le_one hU) u

/-- Forming a BV class commutes with restriction. -/
@[simp]
theorem restrictL_ofFunction (hU : U ≤ Ω) (u : E → ℝ) (hu : MemBV μ Ω u) :
    restrictL hU (ofFunction u hu) = ofFunction u (hu.mono hU) := by
  apply ext
  exact ((coeFn_restrictL hU _).trans
    (ae_restrict_of_ae_restrict_of_subset hU (coeFn_ofFunction u hu))).trans
      (coeFn_ofFunction u (hu.mono hU)).symm

/-- Restriction to the same domain is the identity. -/
@[simp]
theorem restrictL_self (u : BV μ Ω) : restrictL le_rfl u = u :=
  ext (coeFn_restrictL le_rfl u)

/-- Successive restrictions agree with direct restriction. -/
@[simp]
theorem restrictL_restrictL (hU : U ≤ Ω) (hV : V ≤ U) (u : BV μ Ω) :
    restrictL hV (restrictL hU u) = restrictL (hV.trans hU) u := by
  apply ext
  exact ((coeFn_restrictL hV _).trans
    (ae_restrict_of_ae_restrict_of_subset hV (coeFn_restrictL hU u))).trans
      (coeFn_restrictL (hV.trans hU) u).symm

/-- BV classes agreeing on every member of a countable open cover are equal. -/
theorem eq_of_restrictL_eq {ι : Type*} [Countable ι] {U : ι → Opens E}
    (hU : ∀ i, U i ≤ Ω) (hcover : ⨆ i, U i = Ω) {u v : BV μ Ω}
    (h : ∀ i, restrictL (hU i) u = restrictL (hU i) v) : u = v := by
  apply ext
  have hlocal (i : ι) : (u : E → ℝ) =ᵐ[μ.restrict (U i)] v :=
    (coeFn_restrictL (hU i) u).symm.trans
      ((h i) ▸ coeFn_restrictL (hU i) v)
  have hglobal := (ae_eq_restrict_iUnion_iff (fun i => (U i : Set E))
    (u : E → ℝ) v).mpr hlocal
  simpa only [← Opens.coe_iSup, hcover] using hglobal

end BV

end TauCeti
