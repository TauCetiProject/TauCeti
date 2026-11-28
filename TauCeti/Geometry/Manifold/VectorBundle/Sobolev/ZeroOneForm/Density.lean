/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOne.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density

/-!
# Density in the Sobolev `(0,1)`-forms

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`,
and `1 ≤ p < ∞`.

* The inclusion `W^{k+d,p}(Σ, Λ^{0,1} ⊗ V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)` forgetting `d` weak
  derivatives (`TauCeti.zeroOneLowerOrdersL`) has dense range
  (`TauCeti.denseRange_zeroOneLowerOrdersL`): the `(0,1)`-projection is onto and commutes with
  lowering the order, and lowering the order of one-forms has dense range
  (`TauCeti.SobolevSection.denseRange_lowerOrdersL`).
* The Sobolev forms of `C^∞` `(0,1)`-forms are dense in `W^{k,p}(Σ, Λ^{0,1} ⊗ V)`
  (`TauCeti.dense_ofContMDiffSection_zeroOneSobolevSections`): the `(0,1)`-projection of the
  Sobolev form of a smooth one-form `σ` is the Sobolev form of its pointwise `(0,1)`-part
  `x ↦ (σ x)^{0,1}` (`TauCeti.zeroOnePartSobolevL_ofContMDiffSection`), a `Cᵏ` section by
  `ContMDiffSection.map` since the projection is smooth on the total space
  (`TauCeti.SmoothAlmostComplexStructure.contMDiff_totalSpace_zeroOnePart`, `k ≤ ∞`), and smooth
  one-forms are dense. With `Continuous.ext_on`, continuous maps out of the Sobolev
  `(0,1)`-forms are determined by their values on smooth `(0,1)`-forms, as used for extending
  identities such as Green's formula from smooth forms.
-/


public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneDensity : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ)
  [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ)

/-- **Lowering the order of `(0,1)`-forms has dense range.** For `1 ≤ p < ∞`, the `W^{k+d,p}`
`(0,1)`-forms are dense in the `W^{k,p}` `(0,1)`-forms. -/
theorem denseRange_zeroOneLowerOrdersL (hp : p ≠ ⊤) (d : ℕ) :
    DenseRange (zeroOneLowerOrdersL A μ p k d) := by
  have h := (zeroOnePartSobolevL_surjective (A := A) (μ := μ) (p := p) (k := k)).denseRange.comp
    (SobolevSection.denseRange_lowerOrdersL A.tangentHom μ p k hp d)
    (zeroOnePartSobolevL A μ p k).continuous
  refine h.mono ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨_, zeroOneLowerOrdersL_zeroOnePartSobolevL d w⟩

/-! ### Smooth `(0,1)`-forms are dense -/

open SmoothAlmostComplexStructure

variable [∀ x, ContinuousSMul ℂ (V x)]

omit [T2Space M] in
/-- **The `(0,1)`-projection of a `Cᵏ` one-form** is the Sobolev form of its pointwise
`(0,1)`-part. -/
theorem zeroOnePartSobolevL_ofContMDiffSection
    (σ : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯) :
    (zeroOnePartSobolevL A μ p k (SobolevSection.ofContMDiffSection A.tangentHom μ p k σ) :
        SobolevSection A.tangentHom μ p k) =
      SobolevSection.ofContMDiffSection A.tangentHom μ p k
        (ContMDiffSection.map (fun _ ↦ (ofComplexManifold ℂ M).zeroOnePart)
          ((ofComplexManifold ℂ M).contMDiff_totalSpace_zeroOnePart (mod_cast le_top)) σ) := by
  refine SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_
  -- The chart data of a smooth form are almost everywhere on `A.image i`, which is the image of
  -- chart `i` of the one-form atlas.
  have hσ (τ : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯) :=
    (SobolevSection.chartValueL_ofContMDiffSection_ae A.tangentHom μ p k τ i).filter_mono
      (ae_mono (Measure.restrict_mono (A.tangentHom.sectionChartData_image i).le le_rfl))
  have h := hσ (ContMDiffSection.map (fun _ ↦ (ofComplexManifold ℂ M).zeroOnePart)
    ((ofComplexManifold ℂ M).contMDiff_totalSpace_zeroOnePart (mod_cast le_top)) σ)
  -- The mapped section is pointwise the `(0,1)`-part of `σ`.
  rw [show ⇑(ContMDiffSection.map (fun _ ↦ (ofComplexManifold ℂ M).zeroOnePart)
      ((ofComplexManifold ℂ M).contMDiff_totalSpace_zeroOnePart (mod_cast le_top)) σ) =
      fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (σ x) from
    funext (ContMDiffSection.map_apply _ _ σ)] at h
  exact (chartValueL_zeroOnePartSobolevL_ae_coord (hσ σ)).trans h.symm

/-- **Smooth `(0,1)`-forms are dense in the Sobolev `(0,1)`-forms.** For `1 ≤ p < ∞` and every
order `k`, the Sobolev forms of `C^∞` `(0,1)`-forms are dense in `W^{k,p}(Σ, Λ^{0,1} ⊗ V)`. -/
theorem dense_ofContMDiffSection_zeroOneSobolevSections (hp : p ≠ ⊤) :
    Dense {w : zeroOneSobolevSections A μ p k |
      ∃ σ : Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯,
        (∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (σ x)) ∧
          (w : SobolevSection A.tangentHom μ p k) =
            SobolevSection.ofContMDiffSection A.tangentHom μ p k
              (ContMDiffSection.ofLE ENat.LEInfty.out σ)} := by
  have h := (zeroOnePartSobolevL_surjective (A := A) (μ := μ) (p := p) (k := k)).denseRange.comp
    (SobolevSection.denseRange_ofContMDiffSection_comp_ofLE A.tangentHom μ p k hp)
    (zeroOnePartSobolevL A μ p k).continuous
  refine h.mono ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨ContMDiffSection.map (fun _ ↦ (ofComplexManifold ℂ M).zeroOnePart)
      ((ofComplexManifold ℂ M).contMDiff_totalSpace_zeroOnePart le_rfl) σ,
    fun x ↦ by
      rw [ContMDiffSection.map_apply]
      exact (ofComplexManifold ℂ M).isZeroOneForm_zeroOnePart (σ x), ?_⟩
  rw [Function.comp_apply, LinearMap.comp_apply, zeroOnePartSobolevL_ofContMDiffSection]
  exact congrArg _ (ContMDiffSection.ext fun x ↦ by simp)

end TauCeti
