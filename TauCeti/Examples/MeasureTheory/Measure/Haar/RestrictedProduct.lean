/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic

import TauCeti.Algebra.BigOperators.Finprod

/-!
# Checks for normalized restricted Haar products

Three instances of `TauCeti.restrictedHaar_eq_finprod_smul`, which rescales the normalized
restricted Haar product `restrictedHaar B μ` when the local Haar measures are rescaled by
`c i • μ i`:

* unit local scalars preserve the measure (`TauCeti.restrictedHaar_eq_of_eq_one_smul`);
* rescaling one local factor by `2` rescales the restricted product by `2`
  (`TauCeti.restrictedHaar_eq_two_smul_of_mulSingle`);
* rescaling two local factors by `2` and `1 / 2` preserves the restricted product
  (`TauCeti.restrictedHaar_eq_of_mulSingle_two_mul_mulSingle_inv`).

Two instances of the functoriality `TauCeti.map_restrictedProductCongrRight_restrictedHaar`:

* the identity family preserves the restricted Haar product, so every box mass
  (`TauCeti.map_restrictedProductCongrRight_refl_restrictedHaar`);
* on one copy of the additive group `ℝ` with Lebesgue measure and reference subgroup `ℝ`,
  `x ↦ 2x` sends the restricted Haar product to the one of `(x ↦ 2x)_* vol = vol / 2`: the box
  `[0, 2]` has pushforward mass `1` (`TauCeti.map_addRestrictedProductCongrRight_two_mul_box`).
-/

public section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct
open scoped NNReal RestrictedProduct

namespace TauCeti

section Normalization

variable {ι : Type*} [Countable ι] [DecidableEq ι]
  {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]
  (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
  (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
  (μ' : ∀ i, Measure (G i)) [∀ i, (μ' i).IsHaarMeasure] (hμ'B : ∀ᶠ i in cofinite, μ' i (B i) = 1)

omit [DecidableEq ι] in
/-- Unit local scalars preserve the restricted Haar product. -/
theorem restrictedHaar_eq_of_eq_one_smul (hμ' : ∀ i, μ' i = (1 : ℝ≥0) • μ i) :
    restrictedHaar B μ' hμ'B = restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B 1 hμ', Pi.one_def, finprod_one, one_smul]

/-- Rescaling the local Haar measure at one index by `2` rescales the restricted Haar product
by `2`. -/
theorem restrictedHaar_eq_two_smul_of_mulSingle (j : ι)
    (hμ' : ∀ i, μ' i = (Pi.mulSingle j 2 : ι → ℝ≥0) i • μ i) :
    restrictedHaar B μ' hμ'B = (2 : ℝ≥0) • restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B _ hμ', finprod_mulSingle]

/-- Rescaling the local Haar measures at two indices by `2` and `1 / 2` preserves the restricted
Haar product. -/
theorem restrictedHaar_eq_of_mulSingle_two_mul_mulSingle_inv (j k : ι)
    (hμ' : ∀ i, μ' i = ((Pi.mulSingle j 2 : ι → ℝ≥0) i * (Pi.mulSingle k 2⁻¹ : ι → ℝ≥0) i) • μ i) :
    restrictedHaar B μ' hμ'B = restrictedHaar B μ hμB := by
  rw [restrictedHaar_eq_finprod_smul B μ hμB μ' hμ'B _ hμ',
    finprod_mul_distrib ((Set.finite_singleton j).subset Pi.mulSupport_mulSingle_subset)
      ((Set.finite_singleton k).subset Pi.mulSupport_mulSingle_subset),
    finprod_mulSingle, finprod_mulSingle, mul_inv_cancel₀ two_ne_zero, one_smul]

end Normalization

section Refl

variable {ι : Type*} [Countable ι]
  {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  (U : ∀ i, Subgroup (G i)) [Fact (∀ i, IsOpen (U i : Set (G i)))]
  (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1)

/-- The identity family preserves the restricted Haar product. -/
theorem map_restrictedProductCongrRight_refl_restrictedHaar :
    (restrictedHaar U μ hμU).map (restrictedProductCongrRight U U
        (fun i ↦ (ContinuousMulEquiv.refl (G i)).toMulEquiv) (.of_forall fun _ ↦ Set.bijOn_id _)) =
      restrictedHaar U μ hμU := by
  rw [map_restrictedProductCongrRight_restrictedHaar]
  congr 1
  funext i
  simp only [ContinuousMulEquiv.coe_refl, Measure.map_id]

end Refl

section Real

/-- The reference subgroup `ℝ` of `ℝ` is open. -/
local instance : Fact (∀ _ : Unit, IsOpen ((⊤ : AddSubgroup ℝ) : Set ℝ)) :=
  ⟨fun _ ↦ isOpen_univ⟩

/-- On one copy of `ℝ` with Lebesgue measure, `x ↦ 2x` sends the restricted Haar product to one
under which the box `[0, 2]` has mass `1`. -/
theorem map_addRestrictedProductCongrRight_two_mul_box :
    (restrictedAddHaar (fun _ : Unit ↦ (⊤ : AddSubgroup ℝ)) (fun _ ↦ volume)
        (by simp [Filter.cofinite_eq_bot])).map
      (addRestrictedProductCongrRight (fun _ : Unit ↦ (⊤ : AddSubgroup ℝ))
        (fun _ ↦ (⊤ : AddSubgroup ℝ)) (fun _ ↦ (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
          (Units.mk0 (2 : ℝ) two_ne_zero)).toContinuousAddEquiv.toAddEquiv)
        (by simp [Filter.cofinite_eq_bot]))
      (box fun _ ↦ Set.Icc 0 2) = 1 := by
  set e : ℝ ≃ₜ+ ℝ :=
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 (2 : ℝ) two_ne_zero)).toContinuousAddEquiv
  have he : ⇑e = (2 * ·) := by
    ext x
    simp [e, Units.smul_def]
  rw [map_addRestrictedProductCongrRight_restrictedAddHaar _ _ (fun _ ↦ e),
    restrictedAddHaar_box_eq_finprod _ _ _ (by simp [Filter.cofinite_eq_bot]), finprod_unique,
    map_apply (map_continuous e).measurable measurableSet_Icc, he,
    Real.volume_preimage_mul_left two_ne_zero, Real.volume_Icc, ← ENNReal.ofReal_mul (by simp)]
  norm_num

end Real

end TauCeti
