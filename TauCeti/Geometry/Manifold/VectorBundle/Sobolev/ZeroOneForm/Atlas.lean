/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Equiv
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic

/-!
# Independence of the Sobolev `(0,1)`-forms from the bundle atlas

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle, with two finite
bundle atlases `A` and `A'`. The Sobolev space `W^{k,p}(Σ, Λ^{0,1} ⊗ V)` of
`TauCeti.zeroOneSobolevSections A μ p k` is a closed subspace of the Sobolev space of `V`-valued
one-forms built on the charts of `A`. Whenever one-forms transfer from the atlas `A.tangentHom` to
`A'.tangentHom` (`TauCeti.SobolevSection.TransfersTo`), the change of atlas
`TauCeti.SobolevSection.changeAtlas` commutes with the `(0,1)`-projections of the two atlases, both
lifting the pointwise `(0,1)`-projection of one-forms. So it sends `(0,1)`-forms to `(0,1)`-forms
(`TauCeti.zeroOneChangeAtlas`), and when one-forms transfer in both directions the two spaces of
`(0,1)`-forms are isomorphic Banach spaces (`TauCeti.zeroOneAtlasEquiv`), a `(0,1)`-form
corresponding to the one with the same underlying one-form. For a smooth bundle over a Hausdorff
curve the transfer holds in both directions for every order and exponent
(`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`).

## Main definitions

* `TauCeti.zeroOneChangeAtlas`: the change of atlas on Sobolev `(0,1)`-forms.
* `TauCeti.zeroOneAtlasEquiv`: the isomorphism of Sobolev `(0,1)`-forms of two atlases.

## Main results

* `TauCeti.zeroOnePartSobolevL_changeAtlas`: the change of atlas commutes with the
  `(0,1)`-projections.
* `TauCeti.changeAtlas_mem_zeroOneSobolevSections`: the change of atlas preserves `(0,1)`-forms.
* `TauCeti.zeroOneChangeAtlas_comp`, `TauCeti.zeroOneAtlasEquiv_trans`,
  `TauCeti.zeroOneAtlasEquiv_refl`: changes of atlas compose, and the trivial one is the identity.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneFormAtlas : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable {A A' : FiniteBundleAtlas ℂ M F V} {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {k : ℕ}

/-- **The change of atlas commutes with the `(0,1)`-projections.** Both sides have as chart data
the readings of the `(0,1)`-part of any one-form representing `w`. -/
theorem zeroOnePartSobolevL_changeAtlas
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (w : SobolevSection A.tangentHom μ p k) :
    (zeroOnePartSobolevL A' μ p k (SobolevSection.changeAtlas h w) :
        SobolevSection A'.tangentHom μ p k) =
      SobolevSection.changeAtlas h (zeroOnePartSobolevL A μ p k w : _) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  obtain ⟨θ, hθ⟩ := SobolevSection.exists_ae_eq_coord w
  have hθ' := SobolevSection.chartValueL_changeAtlas_ae h hθ
  refine SobolevSection.eq_of_ae_eq_coord
    (s := fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) (fun i ↦ ?_)
    (SobolevSection.chartValueL_changeAtlas_ae h fun i ↦ ?_)
  · exact chartValueL_zeroOnePartSobolevL_ae_coord (hθ' i)
  · exact chartValueL_zeroOnePartSobolevL_ae_coord (hθ i)

/-- The change of atlas sends Sobolev `(0,1)`-forms to `(0,1)`-forms. -/
theorem changeAtlas_mem_zeroOneSobolevSections
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    {w : SobolevSection A.tangentHom μ p k} (hw : w ∈ zeroOneSobolevSections A μ p k) :
    SobolevSection.changeAtlas h w ∈ zeroOneSobolevSections A' μ p k := by
  rw [← coe_zeroOnePartSobolevL_eq_self_iff, zeroOnePartSobolevL_changeAtlas,
    coe_zeroOnePartSobolevL_eq_self_iff.2 hw]

/-- **Change of atlas on `(0,1)`-forms.** Given the transfer of one-forms from `A.tangentHom` to
`A'.tangentHom`, the continuous linear map between the Sobolev `(0,1)`-forms of the two atlases
sending a `(0,1)`-form to the one with the same underlying one-form. It is the restriction of
`TauCeti.SobolevSection.changeAtlas`. -/
def zeroOneChangeAtlas (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k) :
    zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A' μ p k :=
  ((SobolevSection.changeAtlas h).comp (zeroOneSobolevSections A μ p k).subtypeL).codRestrict _
    fun w ↦ changeAtlas_mem_zeroOneSobolevSections h w.property

@[simp]
theorem coe_zeroOneChangeAtlas_apply
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (w : zeroOneSobolevSections A μ p k) :
    (zeroOneChangeAtlas h w : SobolevSection A'.tangentHom μ p k) =
      SobolevSection.changeAtlas h (w : SobolevSection A.tangentHom μ p k) :=
  (rfl)

@[simp]
theorem zeroOneChangeAtlas_zeroOneChangeAtlas {A'' : FiniteBundleAtlas ℂ M F V}
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A''.tangentHom μ p k)
    (w : zeroOneSobolevSections A μ p k) :
    zeroOneChangeAtlas h' (zeroOneChangeAtlas h w) = zeroOneChangeAtlas (h.trans h') w :=
  Subtype.ext <| by simp

/-- Not `@[simp]`: `zeroOneChangeAtlas_refl` and `ContinuousLinearMap.id_apply` prove it. -/
theorem zeroOneChangeAtlas_refl_apply (w : zeroOneSobolevSections A μ p k) :
    zeroOneChangeAtlas SobolevSection.transfersTo_refl w = w :=
  Subtype.ext <| by simp

@[simp]
theorem zeroOneChangeAtlas_refl :
    zeroOneChangeAtlas (SobolevSection.transfersTo_refl (A := A.tangentHom) (μ := μ) (p := p)
      (k := k)) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext zeroOneChangeAtlas_refl_apply

@[simp]
theorem zeroOneChangeAtlas_comp {A'' : FiniteBundleAtlas ℂ M F V}
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A''.tangentHom μ p k) :
    (zeroOneChangeAtlas h').comp (zeroOneChangeAtlas h) = zeroOneChangeAtlas (h.trans h') :=
  ContinuousLinearMap.ext (zeroOneChangeAtlas_zeroOneChangeAtlas h h')

/-- **Independence of the atlas for `(0,1)`-forms.** If one-forms transfer between `A.tangentHom`
and `A'.tangentHom` in both directions, the Sobolev `(0,1)`-forms of the two atlases are isomorphic
Banach spaces, a `(0,1)`-form corresponding to the one with the same underlying one-form. It is the
restriction of `TauCeti.SobolevSection.atlasEquiv`. -/
def zeroOneAtlasEquiv (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k) :
    zeroOneSobolevSections A μ p k ≃L[ℝ] zeroOneSobolevSections A' μ p k :=
  .ofContinuousLinearMap (zeroOneChangeAtlas h) (zeroOneChangeAtlas h')
    (ContinuousLinearMap.ext fun w ↦ by
      simp)
    (ContinuousLinearMap.ext fun w ↦ by
      simp)

@[simp]
theorem toContinuousLinearMap_zeroOneAtlasEquiv
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k) :
    (zeroOneAtlasEquiv h h' :
        zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A' μ p k) =
      zeroOneChangeAtlas h :=
  (rfl)

@[simp]
theorem zeroOneAtlasEquiv_apply (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k)
    (w : zeroOneSobolevSections A μ p k) :
    zeroOneAtlasEquiv h h' w = zeroOneChangeAtlas h w :=
  (rfl)

theorem zeroOneAtlasEquiv_symm_apply
    (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k)
    (w : zeroOneSobolevSections A' μ p k) :
    (zeroOneAtlasEquiv h h').symm w = zeroOneChangeAtlas h' w :=
  (rfl)

@[simp]
theorem zeroOneAtlasEquiv_symm (h : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k) :
    (zeroOneAtlasEquiv h h').symm = zeroOneAtlasEquiv h' h :=
  (rfl)

@[simp]
theorem zeroOneAtlasEquiv_refl :
    zeroOneAtlasEquiv (SobolevSection.transfersTo_refl (A := A.tangentHom) (μ := μ) (p := p)
      (k := k)) SobolevSection.transfersTo_refl = ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext <| funext zeroOneChangeAtlas_refl_apply

@[simp]
theorem zeroOneAtlasEquiv_trans {A'' : FiniteBundleAtlas ℂ M F V}
    (h₁ : SobolevSection.TransfersTo A.tangentHom A'.tangentHom μ p k)
    (h₁' : SobolevSection.TransfersTo A'.tangentHom A.tangentHom μ p k)
    (h₂ : SobolevSection.TransfersTo A'.tangentHom A''.tangentHom μ p k)
    (h₂' : SobolevSection.TransfersTo A''.tangentHom A'.tangentHom μ p k) :
    (zeroOneAtlasEquiv h₁ h₁').trans (zeroOneAtlasEquiv h₂ h₂') =
      zeroOneAtlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  ContinuousLinearEquiv.ext <| funext <| zeroOneChangeAtlas_zeroOneChangeAtlas h₁ h₂

end TauCeti
