/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Adjoint
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Pairing
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Green's formula for Sobolev sections

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V`, realized as the
bounded operator `D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`), and let `ν` be a positive continuous density
measure on `M`.

* *Green's formula extends to Sobolev sections.* If continuous covector fields `L` on `V`-valued
  one-forms and `L'` on `V` satisfy `∫ L (D σ) dν = ∫ L' σ dν` for every smooth section `σ`, then
  the same identity holds for the realization on every `w ∈ W^{1,p}`, `1 ≤ p < ∞`
  (`TauCeti.IsRealCauchyRiemannOperator.integralL_sobolevL`). Both sides are continuous linear
  functionals of `w` (`TauCeti.SobolevSection.integralL`), and smooth sections are dense.
* *Green's formula.* For compatible metrics, a smooth metric connection, the Riemannian volume and a
  smooth `(0,1)`-form `η`, `∫ ⟪η, D w⟫ dV = ∫ ⟪D* η, w⟫ dV` for every `w ∈ W^{1,p}`, where the
  left side is the `L²` pairing of `(0,1)`-forms (`TauCeti.zeroOneHilbertSchmidtL`)
  (`TauCeti.IsRealCauchyRiemannOperator.zeroOneHilbertSchmidtL_sobolevL`), extending Green's
  formula for smooth sections
  (`TauCeti.IsRealCauchyRiemannOperator.integral_inner_formalAdjoint_of_compactSpace`). Hence
  every `(0,1)`-form in the range of `D` is `L²`-orthogonal to every smooth `η` with `D* η = 0`
  (`TauCeti.IsRealCauchyRiemannOperator.range_sobolevL_le_ker_zeroOneHilbertSchmidtL`): one
  inclusion of McDuff–Salamon's duality (C.1.3).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.integralL_sobolevL`: Green's formula for Sobolev sections,
  for any continuous covector fields satisfying it on smooth sections.
* `TauCeti.IsRealCauchyRiemannOperator.continuousOn_innerSL_formalAdjoint_comp_symmL`: the
  covector field `⟪D* η, ·⟫` of a smooth `(0,1)`-form `η` can be integrated against Sobolev
  sections.
* `TauCeti.IsRealCauchyRiemannOperator.zeroOneHilbertSchmidtL_sobolevL`: Green's formula
  `∫ ⟪η, D w⟫ dV = ∫ ⟪D* η, w⟫ dV` for `w ∈ W^{1,p}`.
* `TauCeti.IsRealCauchyRiemannOperator.range_sobolevL_le_ker_zeroOneHilbertSchmidtL`: the range of
  `D` is `L²`-orthogonal to the smooth `(0,1)`-forms `η` with `D* η = 0`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Lemma C.1.9 and the duality (C.1.3).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold RealInnerProductSpace

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

/-! ### Green's formula for Sobolev sections -/

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannGreen : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [MeasurableSpace M] [BorelSpace M] {ν : Measure M}

namespace IsRealCauchyRiemannOperator

/-- **Green's formula for Sobolev sections.** Let `L` be a continuous covector field on `V`-valued
one-forms and `L'` one on `V`, with `∫ L x (D σ x) dν = ∫ L' x (σ x) dν` for every smooth section
`σ`. Then for every `w ∈ W^{1,p}(M, V)`, `1 ≤ p < ∞`, the integral of `L` against the realization
`D w` is the integral of `L'` against `w`. -/
theorem integralL_sobolevL (hp_top : p ≠ ⊤) (hν : IsPositiveDensityMeasure 𝓘(ℝ, ℂ) ν)
    {L : ∀ x, (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) →L[ℝ] ℝ}
    (hL : ∀ x₀ : M, ContinuousOn (fun x ↦ L x ∘L
      (trivializationAt (ℂ →L[ℝ] F) (fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x₀).symmL ℝ x)
      (trivializationAt (ℂ →L[ℝ] F) (fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) x₀).baseSet)
    {L' : ∀ x, V x →L[ℝ] ℝ}
    (hL' : ∀ x₀ : M, ContinuousOn (fun x ↦ L' x ∘L (trivializationAt F V x₀).symmL ℝ x)
      (trivializationAt F V x₀).baseSet)
    (h : ∀ σ : Cₛ^∞⟮𝓘(ℝ, ℂ); F, V⟯, ∫ x, L x (D σ x) ∂ν = ∫ x, L' x (σ x) ∂ν)
    (w : SobolevSection A μ p 1) :
    SobolevSection.integralL A.tangentHom μ p 0 hν hL
        (hD.sobolevL A hDs μ p w : SobolevSection A.tangentHom μ p 0) =
      SobolevSection.integralL A μ p 1 hν hL' w := by
  let T : SobolevSection A μ p 1 →L[ℝ] ℝ := (SobolevSection.integralL A.tangentHom μ p 0 hν hL).comp
    ((zeroOneSobolevSections A μ p 0).subtypeL.comp (hD.sobolevL A hDs μ p))
  -- Both sides are continuous in `w` and agree on smooth sections, which are dense.
  have hT : (T : SobolevSection A μ p 1 → ℝ) = SobolevSection.integralL A μ p 1 hν hL' :=
    (SobolevSection.denseRange_ofContMDiffSection_comp_ofLE A μ p 1 hp_top).equalizer T.continuous
      (ContinuousLinearMap.continuous _) <| funext fun σ ↦ by
        simp only [Function.comp_apply, LinearMap.comp_apply, T, ContinuousLinearMap.comp_apply,
          Submodule.subtypeL_apply]
        rw [SobolevSection.integralL_ofContMDiffSection,
          SobolevSection.integralL_apply (A := A.tangentHom) hν hL
          (s := D (ContMDiffSection.ofLE (m := ((1 : ℕ) : ℕ∞ω)) ENat.LEInfty.out σ)) fun i ↦
            (ae_image_tangentHom_iff A μ i).2
              (hD.chartValueL_sobolevL_ofContMDiffSection_ae A hDs μ p _ i)]
        simpa only [ContMDiffSection.coe_ofLE] using h σ
  exact congrFun hT w

end IsRealCauchyRiemannOperator

end General

/-! ### Green's formula with the formal adjoint -/

section Pairing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannPairing : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [RiemannianBundle V] [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  [MeasurableSpace M] [BorelSpace M]

section Green

variable [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ F V]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℂ) ∞ ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x)]
  {A : FiniteBundleAtlas ℂ M F V} {μ : Measure ℂ} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (cov : _root_.CovariantDerivative 𝓘(ℝ, ℂ) F V)
  [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
  [∀ x, ContinuousSMul ℂ (V x)] [LindelofSpace M]

local instance instIsContinuousRiemannianBundleCauchyRiemannPairing :
    IsContinuousRiemannianBundle F V :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, ℂ)) (n := ∞)

local instance instIsContinuousRiemannianBundleTangentCauchyRiemannPairing :
    IsContinuousRiemannianBundle ℂ (fun x : M ↦ TangentSpace 𝓘(ℝ, ℂ) x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, ℂ)) (n := ∞)

namespace IsRealCauchyRiemannOperator

include hDs in
omit [MeasurableSpace M] [BorelSpace M] [LindelofSpace M] in
/-- The covector field `⟪D* η x, ·⟫` of the formal adjoint of a smooth `(0,1)`-form is continuous
in the preferred trivializations of `V`, so it can be integrated against Sobolev sections
(`TauCeti.SobolevSection.integralL`). -/
theorem continuousOn_innerSL_formalAdjoint_comp_symmL
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (hη01 : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) (x₀ : M) :
    ContinuousOn (fun x ↦ innerSL ℝ (hD.formalAdjoint cov η x) ∘L
      (trivializationAt F V x₀).symmL ℝ x) (trivializationAt F V x₀).baseSet :=
  (trivializationAt F V x₀).continuousOn_innerSL_comp_symmL subset_rfl
    (hD.contMDiff_formalAdjoint cov hDs hJ hV hη hη01).continuous.continuousOn

/-- **Green's formula for Sobolev sections** (McDuff–Salamon, Lemma C.1.9, on a closed surface).
For compatible metrics, a smooth metric connection, the Riemannian volume `dV` and a smooth
`(0,1)`-form `η`, `∫ ⟪η, D w⟫ dV = ∫ ⟪D* η, w⟫ dV` for every `w ∈ W^{1,p}(M, V)`, `1 ≤ p < ∞`.
The left side is the `L²` pairing of `(0,1)`-forms (`TauCeti.zeroOneHilbertSchmidtL`) and the
right side the integral of the covector field `⟪D* η, ·⟫` against `w`
(`TauCeti.SobolevSection.integralL`). -/
theorem zeroOneHilbertSchmidtL_sobolevL (hp_top : p ≠ ⊤) (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (hη01 : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x)) (w : SobolevSection A μ p 1) :
    zeroOneHilbertSchmidtL A μ p 0 isPositiveDensityMeasure_riemannianVolume η hη.continuous
        (hD.sobolevL A hDs μ p w) =
      SobolevSection.integralL A μ p 1 isPositiveDensityMeasure_riemannianVolume
        (L := fun x ↦ innerSL ℝ (hD.formalAdjoint cov η x))
        (continuousOn_innerSL_formalAdjoint_comp_symmL hD hDs cov hJ hV hη hη01) w := by
  have := A.compactSpace
  rw [zeroOneHilbertSchmidtL_apply_eq_integralL]
  refine hD.integralL_sobolevL A hDs hp_top _ _ _ (fun σ ↦ ?_) w
  simp only [ContinuousLinearMap.hilbertSchmidtInnerL_apply, innerSL_apply_apply]
  exact (hD.integral_inner_formalAdjoint_of_compactSpace cov hcov hDs hJ hV hη hη01
    σ.contMDiff).symm

/-- **The range of `D` is orthogonal to the kernel of `D*`.** For compatible metrics, a smooth
metric connection and the Riemannian volume, every `(0,1)`-form in the range of the realization
`D : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`, `1 ≤ p < ∞`, is `L²`-orthogonal to every smooth
`(0,1)`-form `η` with `D* η = 0`. This is one inclusion of McDuff–Salamon's duality (C.1.3). -/
theorem range_sobolevL_le_ker_zeroOneHilbertSchmidtL (hp_top : p ≠ ⊤)
    (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x (u v : TangentSpace 𝓘(ℝ, ℂ) x),
      ⟪ofComplexManifold ℂ M x u, ofComplexManifold ℂ M x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    {η : Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hη : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] F)) ∞ fun x ↦
      TotalSpace.mk' (ℂ →L[ℝ] F) (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] V y) x (η x))
    (hη01 : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (η x))
    (hDη : ∀ x, hD.formalAdjoint cov η x = 0) :
    (hD.sobolevL A hDs μ p).range ≤
      (zeroOneHilbertSchmidtL A μ p 0 isPositiveDensityMeasure_riemannianVolume η
        hη.continuous).ker := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
    hD.zeroOneHilbertSchmidtL_sobolevL hDs cov hp_top hcov hJ hV hη hη01 w,
    SobolevSection.integralL_apply _ _ (SobolevSection.exists_ae_eq_coord w).choose_spec]
  simp [hDη]

end IsRealCauchyRiemannOperator

end Green

end Pairing

end TauCeti
