/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt

/-!
# The `L²` pairing of Sobolev `(0,1)`-forms

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, with a finite bundle atlas `A`, continuous metrics on `TM` and
`V`, and a positive continuous density measure `ν` on `M`. For a continuous `V`-valued one-form
`η`, the Hilbert–Schmidt covector field `⟪η x, ·⟫` is continuous in the trivializations of the
bundle of one-forms (`Bundle.Trivialization.continuousOn_hilbertSchmidtInnerL_comp_symmL`), so
integration against it is a continuous linear functional on the Sobolev `(0,1)`-forms
`W^{k,p}(M, Λ^{0,1} ⊗ V)`, `w ↦ ∫ ⟪η, w⟫ dν` (`TauCeti.zeroOneHilbertSchmidtL`). This is the
`L²` pairing of McDuff–Salamon's duality (C.1.3).

## Main definitions

* `TauCeti.zeroOneHilbertSchmidtL`: the `L²` pairing `w ↦ ∫ ⟪η, w⟫ dν`.

## Main results

* `TauCeti.zeroOneHilbertSchmidtL_apply_eq_integralL`: the pairing is
  `TauCeti.SobolevSection.integralL` of the covector field `⟪η x, ·⟫`.
* `TauCeti.zeroOneHilbertSchmidtL_apply`: its value `∫ ⟪η x, θ x⟫ dν`, for any one-form `θ` with
  the chart data of `w`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, the duality (C.1.3).
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOnePairing : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  [MeasurableSpace M] [BorelSpace M]

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) 0 F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) 0 ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  (A : FiniteBundleAtlas ℂ M F V) (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ) {ν : Measure M}

/-- **The `L²` pairing of `(0,1)`-forms.** For a positive continuous density measure `ν`, metrics
on `TM` and `V` and a continuous `V`-valued one-form `η`, the continuous linear functional
`w ↦ ∫ ⟪η x, θ x⟫ dν` on the Sobolev `(0,1)`-forms `W^{k,p}(M, Λ^{0,1} ⊗ V)`, where `θ` is any
one-form with the chart data of `w` and `⟪·, ·⟫` is the Hilbert–Schmidt inner product
(`TauCeti.zeroOneHilbertSchmidtL_apply`). It is `TauCeti.SobolevSection.integralL` for the
covector field `⟪η x, ·⟫`, restricted to the `(0,1)`-forms. -/
def zeroOneHilbertSchmidtL (hν : IsPositiveDensityMeasure 𝓘(ℝ, ℂ) ν)
    (η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x)
    (hη : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x)) :
    zeroOneSobolevSections A μ p k →L[ℝ] ℝ :=
  ContinuousLinearMap.comp
    (SobolevSection.integralL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hν
      (L := fun x ↦ (η x).hilbertSchmidtInnerL)
      (fun x₀ ↦ Bundle.Trivialization.continuousOn_hilbertSchmidtInnerL_comp_symmL _
        (trivializationAt _ _ x₀).open_baseSet subset_rfl hη.continuousOn))
    (zeroOneSobolevSections A μ p k).subtypeL

variable {A μ p k}

/-- The pairing `TauCeti.zeroOneHilbertSchmidtL` is the integral
`TauCeti.SobolevSection.integralL` of the Hilbert–Schmidt covector field `⟪η x, ·⟫` against the
underlying Sobolev one-form. -/
theorem zeroOneHilbertSchmidtL_apply_eq_integralL (hν : IsPositiveDensityMeasure 𝓘(ℝ, ℂ) ν)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (w : zeroOneSobolevSections A μ p k) :
    zeroOneHilbertSchmidtL A μ p k hν η hη w =
      SobolevSection.integralL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hν
        (L := fun x ↦ (η x).hilbertSchmidtInnerL)
        (fun x₀ ↦ Bundle.Trivialization.continuousOn_hilbertSchmidtInnerL_comp_symmL _
          (trivializationAt _ _ x₀).open_baseSet subset_rfl hη.continuousOn)
        (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) := by
  rw [zeroOneHilbertSchmidtL, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- **The value of the pairing.** For every one-form `θ` with the chart data of the `(0,1)`-form
`w`, `TauCeti.zeroOneHilbertSchmidtL` takes the value `∫ ⟪η x, θ x⟫ dν` at `w`. -/
theorem zeroOneHilbertSchmidtL_apply (hν : IsPositiveDensityMeasure 𝓘(ℝ, ℂ) ν)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : Continuous fun x ↦ TotalSpace.mk' (ℂ →L[ℝ] F)
      (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    {w : zeroOneSobolevSections A μ p k} {θ : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hθ : ∀ i, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i
      ((w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ p k)
        =ᵐ[μ.restrict (A.image i)] (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    zeroOneHilbertSchmidtL A μ p k hν η hη w = ∫ x, (η x).hilbertSchmidtInner (θ x) ∂ν := by
  rw [zeroOneHilbertSchmidtL_apply_eq_integralL,
    SobolevSection.integralL_apply (A := A.tangentHom 𝓘(ℝ, ℂ)) hν _ fun i ↦
      (ae_image_tangentHom_iff A μ i).2 (hθ i)]
  simp only [ContinuousLinearMap.hilbertSchmidtInnerL_apply]

end TauCeti
