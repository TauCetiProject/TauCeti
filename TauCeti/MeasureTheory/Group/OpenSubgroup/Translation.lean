/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.RightTranslation
public import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic

/-!
# Subgroup equivariance of `Lᵖ` restriction and extension by zero

This file shows that subtype restriction `MeasureTheory.Lp.restrictComapCLM` (for *all*
`f ∈ Lᵖ(G, μ)`, with no support assumption) and extension by zero
`MeasureTheory.Lp.extendByZeroComapₗᵢ` (for `f₀ ∈ Lᵖ(H, μ.comap (↑))`) intertwine ambient and
subgroup `Lᵖ` translations by elements `u : H`:

* **Left translation (`LeftTranslation`):** Stated for any measurable `SubgroupClass` `H` carrying
  `[(μ.comap ((↑) : H → G)).IsMulLeftInvariant]` — synthesized automatically for
  `H : OpenSubgroup G` by `OpenSubgroup.instIsMulLeftInvariantComap`, and obtained for an arbitrary
  measurable subgroup from `Measure.IsMulLeftInvariant.comap μ (f := SubgroupClass.subtype H)
  (MeasurableEmbedding.subtype_coe hH)`.
* **Right translation (`RightTranslation`):** Stated for `H : OpenSubgroup G` on a locally compact
  group with a regular Haar measure `μ`, using `OpenSubgroup.modularCharacter_eq` to match the
  modular-character weights on `H` and on `G`.

## Main statements

* `MeasureTheory.Lp.restrictComapCLM_leftTranslation`,
  `MeasureTheory.Lp.leftTranslation_extendByZeroComapₗᵢ`: equivariance of subtype restriction and
  extension by zero under subgroup left translations.
* `MeasureTheory.Lp.restrictComapCLM_rightTranslation`,
  `MeasureTheory.Lp.rightTranslation_extendByZeroComapₗᵢ`: equivariance of subtype restriction and
  extension by zero under open-subgroup right translations.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §§2.4–2.5.
-/

public section

noncomputable section

open Filter Set
open scoped ENNReal

namespace MeasureTheory.Lp

section LeftTranslation

variable {G S E 𝕜 : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant] [SetLike S G] [SubgroupClass S G] {H : S}
  [(μ.comap ((↑) : H → G)).IsMulLeftInvariant]
  [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Restricting any `f ∈ Lᵖ(G, μ)` to a measurable subgroup `H` commutes with left translation by
elements `u : H`. For `H : OpenSubgroup G` the `IsMulLeftInvariant` instance on `μ.comap (↑)` is
synthesized automatically; for a general measurable subgroup it is given by
`Measure.IsMulLeftInvariant.comap μ (f := SubgroupClass.subtype H)
(MeasurableEmbedding.subtype_coe hH)`. -/
theorem restrictComapCLM_leftTranslation (hH : MeasurableSet (H : Set G)) (u : H)
    (f : Lp E p μ) :
    restrictComapCLM 𝕜 μ p hH (leftTranslation μ p 𝕜 (u : G) f) =
      leftTranslation (μ.comap ((↑) : H → G)) p 𝕜 u (restrictComapCLM 𝕜 μ p hH f) := by
  set ν : Measure H := μ.comap ((↑) : H → G)
  refine Lp.ext ?_
  have h1 := coeFn_restrictComapCLM (𝕜 := 𝕜) hH (leftTranslation μ p 𝕜 (u : G) f)
  have h2 := (ae_restrict_iff_subtype hH).1
    (ae_restrict_of_ae (coeFn_leftTranslation (𝕜 := 𝕜) (u : G) f))
  have h3 := coeFn_leftTranslation (μ := ν) (𝕜 := 𝕜) u (restrictComapCLM 𝕜 μ p hH f)
  have h4 := (measurePreserving_mul_left ν u⁻¹).quasiMeasurePreserving.ae
    (coeFn_restrictComapCLM (𝕜 := 𝕜) hH f)
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  simp only [Function.comp_apply] at hv1 hv4
  rw [hv1, hv2, hv3, hv4, MulMemClass.coe_mul, InvMemClass.coe_inv]

/-- Extending `f₀ ∈ Lᵖ(H, μ.comap (↑))` by zero to `G` commutes with left translation by elements
`u : H`. -/
theorem leftTranslation_extendByZeroComapₗᵢ (hH : MeasurableSet (H : Set G)) (u : H)
    (f₀ : Lp E p (μ.comap ((↑) : H → G))) :
    leftTranslation μ p 𝕜 (u : G) (extendByZeroComapₗᵢ 𝕜 μ hH f₀) =
      extendByZeroComapₗᵢ 𝕜 μ hH (leftTranslation (μ.comap ((↑) : H → G)) p 𝕜 u f₀) := by
  have hoff : (leftTranslation μ p 𝕜 (u : G) (extendByZeroComapₗᵢ 𝕜 μ hH f₀) : G → E) =ᵐ[
      μ.restrict (H : Set G)ᶜ] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hH.compl]
    have h0 := (ae_restrict_iff' hH.compl).1
      (coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hH f₀)
    filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) (u : G) (extendByZeroComapₗᵢ 𝕜 μ hH f₀),
      (measurePreserving_mul_left μ (u : G)⁻¹).quasiMeasurePreserving.ae h0] with x hx1 hx2 hxH
    refine hx1.trans (hx2 fun hmem ↦ hxH ?_)
    simpa [mul_inv_cancel_left] using mul_mem u.2 hmem
  rw [← extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero (𝕜 := 𝕜) hH hoff,
    restrictComapCLM_leftTranslation, restrictComapCLM_extendByZeroComapₗᵢ]

end LeftTranslation

section RightTranslation

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [SMulCommClass ℝ 𝕜 E]

/-- Restricting any `f ∈ Lᵖ(G, μ)` to an open subgroup `H` commutes with right translation by
elements `u : H`. -/
theorem restrictComapCLM_rightTranslation (H : OpenSubgroup G) (u : H) (f : Lp E p μ) :
    restrictComapCLM 𝕜 μ p H.isOpen.measurableSet (rightTranslation μ p 𝕜 (u : G) f) =
      rightTranslation (μ.comap ((↑) : H → G)) p 𝕜 u
        (restrictComapCLM 𝕜 μ p H.isOpen.measurableSet f) := by
  set ν : Measure H := μ.comap ((↑) : H → G)
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  refine Lp.ext ?_
  have h1 := coeFn_restrictComapCLM (𝕜 := 𝕜) hH (rightTranslation μ p 𝕜 (u : G) f)
  have h2 := (ae_restrict_iff_subtype hH).1
    (ae_restrict_of_ae (coeFn_rightTranslation (𝕜 := 𝕜) (u : G) f))
  have h3 := coeFn_rightTranslation (μ := ν) (𝕜 := 𝕜) u (restrictComapCLM 𝕜 μ p hH f)
  have h4 := (Measure.quasiMeasurePreserving_mul_right_of_regular ν u).ae
    (coeFn_restrictComapCLM (𝕜 := 𝕜) hH f)
  have hmod : Measure.modularCharacter u⁻¹ = Measure.modularCharacter (u : G)⁻¹ :=
    (H.modularCharacter_eq u⁻¹).trans (by rw [InvMemClass.coe_inv])
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  simp only [Function.comp_apply] at hv1 hv4
  rw [hv1, hv2, hv3, hv4, hmod, MulMemClass.coe_mul]

/-- Extending `f₀ ∈ Lᵖ(H, μ.comap (↑))` by zero from an open subgroup `H` to `G` commutes with right
translation by elements `u : H`. -/
theorem rightTranslation_extendByZeroComapₗᵢ (H : OpenSubgroup G) (u : H)
    (f₀ : Lp E p (μ.comap ((↑) : H → G))) :
    rightTranslation μ p 𝕜 (u : G) (extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet f₀) =
      extendByZeroComapₗᵢ 𝕜 μ H.isOpen.measurableSet
        (rightTranslation (μ.comap ((↑) : H → G)) p 𝕜 u f₀) := by
  have hH : MeasurableSet (H : Set G) := H.isOpen.measurableSet
  have hoff : (rightTranslation μ p 𝕜 (u : G) (extendByZeroComapₗᵢ 𝕜 μ hH f₀) : G → E) =ᵐ[
      μ.restrict (H : Set G)ᶜ] 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hH.compl]
    have h0 := (ae_restrict_iff' hH.compl).1
      (coeFn_extendByZeroComapₗᵢ_restrict_compl (𝕜 := 𝕜) hH f₀)
    filter_upwards [coeFn_rightTranslation (𝕜 := 𝕜) (u : G) (extendByZeroComapₗᵢ 𝕜 μ hH f₀),
      (Measure.quasiMeasurePreserving_mul_right_of_regular μ (u : G)).ae h0] with x hx1 hx2 hxH
    have hzero : extendByZeroComapₗᵢ 𝕜 μ hH f₀ (x * (u : G)) = 0 :=
      hx2 fun hmem ↦ hxH (by simpa [mul_inv_cancel_right] using mul_mem hmem (inv_mem u.2))
    simp [hx1, hzero]
  rw [← extendByZeroComapₗᵢ_restrictComapCLM_of_ae_restrict_compl_eq_zero (𝕜 := 𝕜) hH hoff,
    restrictComapCLM_rightTranslation, restrictComapCLM_extendByZeroComapₗᵢ]

end RightTranslation

end MeasureTheory.Lp
