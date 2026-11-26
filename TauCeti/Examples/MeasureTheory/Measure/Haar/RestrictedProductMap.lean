/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Map

/-!
# Checks for the functoriality of restricted Haar products

Two instances of `TauCeti.map_restrictedProductCongrRight_restrictedHaar`:

* the identity family preserves the restricted Haar product, so every box mass
  (`TauCeti.map_restrictedProductCongrRight_refl_restrictedHaar`);
* on one copy of the additive group `ℝ` with Lebesgue measure and reference subgroup `ℝ`,
  `x ↦ 2x` sends the restricted Haar product to the one of `(x ↦ 2x)_* vol = vol / 2`: the box
  `[0, 2]` has pushforward mass `1` (`TauCeti.map_addRestrictedProductCongrRight_two_mul_box`).
-/

public section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct
open scoped RestrictedProduct

namespace TauCeti

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
  exact Measure.map_id

end Refl

section Real

/-- Multiplication by `2` on `ℝ`, as an isomorphism of topological additive groups. -/
noncomputable def twoMulContinuousAddEquiv : ℝ ≃ₜ+ ℝ where
  toFun x := 2 * x
  invFun x := 2⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := mul_add 2 x y
  continuous_toFun := continuous_const_mul 2
  continuous_invFun := continuous_const_mul 2⁻¹

/-- The reference subgroup `ℝ` of `ℝ` is open. -/
instance instFactIsOpenTopAddSubgroupReal :
    Fact (∀ _ : Unit, IsOpen ((⊤ : AddSubgroup ℝ) : Set ℝ)) :=
  ⟨fun _ ↦ isOpen_univ⟩

/-- On one copy of `ℝ` with Lebesgue measure, `x ↦ 2x` sends the restricted Haar product to one
under which the box `[0, 2]` has mass `1`. -/
theorem map_addRestrictedProductCongrRight_two_mul_box :
    (restrictedAddHaar (fun _ : Unit ↦ (⊤ : AddSubgroup ℝ)) (fun _ ↦ volume)
        (by simp [Filter.cofinite_eq_bot])).map
      (addRestrictedProductCongrRight (fun _ : Unit ↦ (⊤ : AddSubgroup ℝ))
        (fun _ ↦ (⊤ : AddSubgroup ℝ)) (fun _ ↦ twoMulContinuousAddEquiv.toAddEquiv)
        (by simp [Filter.cofinite_eq_bot]))
      (box fun _ ↦ Set.Icc 0 2) = 1 := by
  rw [map_addRestrictedProductCongrRight_restrictedAddHaar _ _
      (fun _ ↦ twoMulContinuousAddEquiv),
    restrictedAddHaar_box_eq_finprod _ _ _ (by simp [Filter.cofinite_eq_bot]), finprod_unique,
    map_apply (map_continuous twoMulContinuousAddEquiv).measurable measurableSet_Icc]
  have : twoMulContinuousAddEquiv ⁻¹' Set.Icc 0 2 = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    change 0 ≤ 2 * x ∧ 2 * x ≤ 2 ↔ _
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [this, Real.volume_Icc]
  simp

end Real

end TauCeti
