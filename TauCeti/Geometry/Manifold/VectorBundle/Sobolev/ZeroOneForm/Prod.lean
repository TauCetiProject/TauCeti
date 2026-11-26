/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic

/-!
# Sobolev `(0,1)`-forms with values in a product bundle

Let `M` be a complex curve without boundary and `V`, `V'` complex vector bundles over `M`, with a
finite bundle atlas `A` of `V` whose chart domains have closures inside the base sets of the
preferred trivializations of `V'`. The Sobolev space `W^{k,p}` of one-forms with values in
`V ×ᵇ V'` is the product of those with values in `V` and in `V'`
(`TauCeti.SobolevSection.tangentHomProdEquiv`), and a one-form with values in `V ×ᵇ V'` is a
`(0,1)`-form exactly when both components are. This file restricts the isomorphism to the
`(0,1)`-forms:

`W^{k,p}(Σ, Λ^{0,1} ⊗ (V ×ᵇ V')) ≃ W^{k,p}(Σ, Λ^{0,1} ⊗ V) × W^{k,p}(Σ, Λ^{0,1} ⊗ V')`.

## Main definitions

* `TauCeti.zeroOneSobolevSectionsProdEquiv`: the isomorphism of Sobolev `(0,1)`-forms.

## Main results

* `TauCeti.mem_zeroOneSobolevSections_prod_iff`: a one-form with values in `V ×ᵇ V'` is a Sobolev
  `(0,1)`-form exactly when both of its components are.
* `TauCeti.coe_zeroOneSobolevSectionsProdEquiv_fst`,
  `TauCeti.coe_zeroOneSobolevSectionsProdEquiv_snd`,
  `TauCeti.coe_zeroOneSobolevSectionsProdEquiv_symm`: the isomorphism is the restriction of
  `TauCeti.SobolevSection.tangentHomProdEquiv`.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace ℂ F']
  [IsScalarTower ℝ ℂ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')] [∀ x, AddCommGroup (V' x)]
  [∀ x, Module ℝ (V' x)] [∀ x, Module ℂ (V' x)] [∀ x, IsScalarTower ℝ ℂ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [FiberBundle F' V'] [VectorBundle ℂ F' V']

local instance instVectorBundleRealZeroOneFormProdLeft : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

local instance instVectorBundleRealZeroOneFormProdRight : VectorBundle ℝ F' V' :=
  VectorBundle.restrictScalars ℝ ℂ F' V'

variable {A : FiniteBundleAtlas ℂ M F V}
  {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet}
  {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- A one-form with values in `V ×ᵇ V'` is a Sobolev `(0,1)`-form exactly when both of its
components are. -/
theorem mem_zeroOneSobolevSections_prod_iff {w : SobolevSection (A.prod h).tangentHom μ p k} :
    w ∈ zeroOneSobolevSections (A.prod h) μ p k ↔
      (SobolevSection.tangentHomProdEquiv A h μ p k w).1 ∈ zeroOneSobolevSections A μ p k ∧
        (SobolevSection.tangentHomProdEquiv A h μ p k w).2 ∈
          zeroOneSobolevSections (A.ofBaseSet h) μ p k := by
  simp only [mem_zeroOneSobolevSections_iff]
  refine ⟨fun hw ↦ ⟨fun i ↦ (A.ae_image_tangentHom_iff μ i).2 ?_,
    fun i ↦ (A.ae_image_tangentHom_ofBaseSet_iff μ h i).2 ?_⟩, fun hw i ↦
      (A.ae_image_tangentHom_ofBaseSet_iff μ _ i).2 ?_⟩
  · filter_upwards [(A.ae_image_tangentHom_ofBaseSet_iff μ _ i).1 (hw i),
      SobolevSection.chartValueL_tangentHomProdEquiv_fst_ae w i] with y h₁ h₂ v
    rw [h₂, ContinuousLinearMap.comp_apply, h₁ v]
    simp
  · filter_upwards [(A.ae_image_tangentHom_ofBaseSet_iff μ _ i).1 (hw i),
      SobolevSection.chartValueL_tangentHomProdEquiv_snd_ae w i] with y h₁ h₂ v
    rw [h₂, ContinuousLinearMap.comp_apply, h₁ v]
    simp
  · have hs := SobolevSection.chartValueL_tangentHomProdEquiv_symm_ae
      (SobolevSection.tangentHomProdEquiv A h μ p k w).1
      (SobolevSection.tangentHomProdEquiv A h μ p k w).2 i
    rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at hs
    filter_upwards [(A.ae_image_tangentHom_iff μ i).1 (hw.1 i),
      (A.ae_image_tangentHom_ofBaseSet_iff μ h i).1 (hw.2 i), hs]
      with y h₁ h₂ h₃ v
    rw [h₃, ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply, h₁ v, h₂ v]
    simp

variable (A h μ p k)

/-- The first component of `TauCeti.zeroOneSobolevSectionsProdEquiv`. -/
private def zeroOneFstL :
    zeroOneSobolevSections (A.prod h) μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  ((ContinuousLinearMap.fst ℝ _ _).comp
      ((SobolevSection.tangentHomProdEquiv A h μ p k).toContinuousLinearMap.comp
        (zeroOneSobolevSections (A.prod h) μ p k).subtypeL)).codRestrict _
    fun w ↦ by simpa using (mem_zeroOneSobolevSections_prod_iff.1 w.property).1

/-- The second component of `TauCeti.zeroOneSobolevSectionsProdEquiv`. -/
private def zeroOneSndL :
    zeroOneSobolevSections (A.prod h) μ p k →L[ℝ] zeroOneSobolevSections (A.ofBaseSet h) μ p k :=
  ((ContinuousLinearMap.snd ℝ _ _).comp
      ((SobolevSection.tangentHomProdEquiv A h μ p k).toContinuousLinearMap.comp
        (zeroOneSobolevSections (A.prod h) μ p k).subtypeL)).codRestrict _
    fun w ↦ by simpa using (mem_zeroOneSobolevSections_prod_iff.1 w.property).2

/-- The inverse of `TauCeti.zeroOneSobolevSectionsProdEquiv`. -/
private def zeroOnePairL :
    zeroOneSobolevSections A μ p k × zeroOneSobolevSections (A.ofBaseSet h) μ p k →L[ℝ]
      zeroOneSobolevSections (A.prod h) μ p k :=
  ((SobolevSection.tangentHomProdEquiv A h μ p k).symm.toContinuousLinearMap.comp
      ((zeroOneSobolevSections A μ p k).subtypeL.prodMap
        (zeroOneSobolevSections (A.ofBaseSet h) μ p k).subtypeL)).codRestrict _
    fun w ↦ mem_zeroOneSobolevSections_prod_iff.2 <| by
      simp

/-- **Sobolev `(0,1)`-forms with values in a product bundle.** The Sobolev `(0,1)`-forms with
values in `V ×ᵇ V'`, on the charts of `A.prod h`, are isomorphic to the product of the Sobolev
`(0,1)`-forms with values in `V` on the charts of `A` and with values in `V'` on the charts of
`A.ofBaseSet h`. It is the restriction of `TauCeti.SobolevSection.tangentHomProdEquiv`
(`TauCeti.coe_zeroOneSobolevSectionsProdEquiv_fst`,
`TauCeti.coe_zeroOneSobolevSectionsProdEquiv_snd`,
`TauCeti.coe_zeroOneSobolevSectionsProdEquiv_symm`). -/
def zeroOneSobolevSectionsProdEquiv :
    zeroOneSobolevSections (A.prod h) μ p k ≃L[ℝ]
      zeroOneSobolevSections A μ p k × zeroOneSobolevSections (A.ofBaseSet h) μ p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap ((zeroOneFstL A h μ p k).prod (zeroOneSndL A h μ p k))
    (zeroOnePairL A h μ p k)
    (h₁ := ContinuousLinearMap.ext fun w ↦ by
      ext1 <;> refine Subtype.ext ?_ <;>
        simp [zeroOneFstL, zeroOneSndL, zeroOnePairL])
    (h₂ := ContinuousLinearMap.ext fun w ↦ Subtype.ext <| by
      simp [zeroOneFstL, zeroOneSndL, zeroOnePairL])

variable {A h μ p k}

/-- The first component of `TauCeti.zeroOneSobolevSectionsProdEquiv` is the first component of
`TauCeti.SobolevSection.tangentHomProdEquiv`. -/
@[simp]
theorem coe_zeroOneSobolevSectionsProdEquiv_fst (w : zeroOneSobolevSections (A.prod h) μ p k) :
    ((zeroOneSobolevSectionsProdEquiv A h μ p k w).1 : SobolevSection A.tangentHom μ p k) =
      (SobolevSection.tangentHomProdEquiv A h μ p k w).1 := by
  simp [zeroOneSobolevSectionsProdEquiv, zeroOneFstL]

/-- The second component of `TauCeti.zeroOneSobolevSectionsProdEquiv` is the second component of
`TauCeti.SobolevSection.tangentHomProdEquiv`. -/
@[simp]
theorem coe_zeroOneSobolevSectionsProdEquiv_snd (w : zeroOneSobolevSections (A.prod h) μ p k) :
    ((zeroOneSobolevSectionsProdEquiv A h μ p k w).2 :
        SobolevSection (A.ofBaseSet h).tangentHom μ p k) =
      (SobolevSection.tangentHomProdEquiv A h μ p k w).2 := by
  simp [zeroOneSobolevSectionsProdEquiv, zeroOneSndL]

/-- The inverse of `TauCeti.zeroOneSobolevSectionsProdEquiv` is the inverse of
`TauCeti.SobolevSection.tangentHomProdEquiv`. -/
@[simp]
theorem coe_zeroOneSobolevSectionsProdEquiv_symm
    (w : zeroOneSobolevSections A μ p k × zeroOneSobolevSections (A.ofBaseSet h) μ p k) :
    ((zeroOneSobolevSectionsProdEquiv A h μ p k).symm w :
        SobolevSection (A.prod h).tangentHom μ p k) =
      (SobolevSection.tangentHomProdEquiv A h μ p k).symm (w.1, w.2) := by
  simp [zeroOneSobolevSectionsProdEquiv, zeroOnePairL, Prod.map]

end TauCeti
