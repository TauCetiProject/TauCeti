/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.HomMultiplication

/-!
# Real Cauchy–Riemann operators with rough zeroth-order terms

Let `M` be a closed complex curve and `V → M` a complex vector bundle with a finite bundle atlas
`A`. A real Cauchy–Riemann operator of class `W^{0,p}` is `D = D₀ + α`, where `D₀` is a smooth real
Cauchy–Riemann operator and `α` is a zeroth-order term of class `L^p`, `p > 2`, with values in
`(0,1)`-forms (McDuff–Salamon, Definition C.1.5). This file realizes such operators as bounded
operators `W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` for every finite `1 ≤ q ≤ p`, the exponents
`ℓ = k = 1` used in McDuff–Salamon Theorem C.1.10, and shows that `D - D₀` is compact
(McDuff–Salamon Lemma C.2.2 at `ℓ = k = 1`).

The coefficient `α` is an order-zero Sobolev section of the real hom bundle
`x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, that is a `V`-valued one-form with coefficients in `End_ℝ V`,
on the charts of `A`, whose atlas is `A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet`.
Multiplication by `α` is `TauCeti.SobolevSection.homMulL`, which lands in the `L^q` one-forms
`TauCeti.SobolevSection A.tangentHom μ q 0`; its `(0,1)`-part is taken with
`TauCeti.zeroOnePartSobolevL`, which does not change `α ξ` when `α` takes values in
`(0,1)`-forms (`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevL_ae_of_zeroOne`).

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.perturbationL`: for a fixed `L^p` coefficient `α`, the
  bounded operator `ξ ↦ (α ξ)^{0,1}` from `W^{1,q}` sections to `L^q` `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL`: the realization of `D₀ + α` as a
  bounded operator `W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbationL`: for a fixed coefficient,
  the perturbation is compact.
* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbedSobolevL_sub`: the realizations
  of `D₀ + α` and of `D₀` differ by a compact operator.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevL_ae`: in chart `i`, the
  realization is `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevL_ae_of_zeroOne`: in chart `i`,
  the realization is `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ` for a coefficient with values in `(0,1)`-forms.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Definition C.1.5, Theorem C.1.10 and Lemma C.2.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_eq_self_iff)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannPerturbation : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
  [Fact (1 ≤ (q : ℝ≥0∞))]

namespace IsRealCauchyRiemannOperator

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
private theorem finrank_lt (hp : 2 < p) : (finrank ℝ ℂ : ℝ≥0) < p := by
  rwa [Complex.finrank_real_complex, Nat.cast_ofNat]

/-- Multiplication by an `L^p` section of the real hom bundle from `V` to the `V`-valued one-forms,
from `W^{1,q}` sections of `V` to `L^q` one-forms. -/
private def homMulTangentL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0) :
    SobolevSection A μ q 1 →L[ℝ] SobolevSection A.tangentHom μ q 0 :=
  SobolevSection.homMulL A A.tangentHom.closure_dom_subset_baseSet μ (finrank_lt hp) hqp α

/-- **The rough zeroth-order term.** For `p > 2`, `1 ≤ q ≤ p` and an `L^p` section `α` of the real
hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, the bounded operator sending a `W^{1,q}` section `ξ`
of `V` to the `(0,1)`-part of the one-form `α ξ`, an `L^q` `(0,1)`-form
(`TauCeti.IsRealCauchyRiemannOperator.perturbationL_apply`). In chart `i` it is the complex
antilinear part of `αᵢ uᵢ` (`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbationL_ae`). -/
def perturbationL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  (zeroOnePartSobolevL A μ q 0).comp (homMulTangentL A μ hp hqp α)

@[simp]
theorem perturbationL_apply (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (ξ : SobolevSection A μ q 1) :
    perturbationL A μ hp hqp α ξ = zeroOnePartSobolevL A μ q 0
      (SobolevSection.homMulL A A.tangentHom.closure_dom_subset_baseSet μ (by simpa using hp) hqp
        α ξ) :=
  (rfl)

/-- **Compact perturbation** (McDuff–Salamon, Lemma C.2.2, at `ℓ = k = 1`). For a fixed `L^p`
coefficient with `p > 2`, the rough zeroth-order term is compact from `W^{1,q}` to `L^q`, for every
finite `1 ≤ q ≤ p`. -/
theorem isCompactOperator_perturbationL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0) :
    IsCompactOperator (perturbationL A μ hp hqp α) :=
  (SobolevSection.isCompactOperator_homMulL A A.tangentHom.closure_dom_subset_baseSet μ
    (finrank_lt hp) hqp α).continuous_comp (zeroOnePartSobolevL A μ q 0).continuous

/-- In chart `i`, the rough zeroth-order term is the complex antilinear part of the pointwise
application of the chart data `αᵢ` of the coefficient to the chart data `uᵢ` of the section. -/
theorem chartValueL_perturbationL_ae (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (ξ : SobolevSection A μ q 1) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((perturbationL A μ hp hqp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 0 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  have h₁ := chartValueL_zeroOnePartSobolevL_ae (homMulTangentL A μ hp hqp α ξ) i
  have h₂ := SobolevSection.chartValueL_homMulL_ae A A.tangentHom.closure_dom_subset_baseSet μ
    (finrank_lt hp) hqp α ξ i
  rw [FiniteBundleAtlas.image_ofBaseSet (A := A)
    (h := A.tangentHom.closure_dom_subset_baseSet)] at h₂
  filter_upwards [(FiniteBundleAtlas.ae_image_tangentHom_iff A μ i).1 h₁, h₂] with y hy₁ hy₂
  rw [perturbationL, ContinuousLinearMap.comp_apply, hy₁]
  exact congrArg complexAntilinearPartL hy₂

include hD in
/-- **The realization of `D₀ + α`.** For a smooth real Cauchy–Riemann operator `D₀`, `p > 2`,
`1 ≤ q ≤ p` and an `L^p` zeroth-order term `α`, the bounded operator
`W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` sending `ξ` to `D₀ ξ + (α ξ)^{0,1}`
(`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL_apply`). For a coefficient with values in
`(0,1)`-forms it is `D₀ + α` in every chart
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevL_ae_of_zeroOne`). -/
def perturbedSobolevL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  -- Instance search for this `ContinuousAdd` instance exceeds the default heartbeat limit.
  haveI : ContinuousAdd (zeroOneSobolevSections A μ q 0) :=
    AddSubmonoid.continuousAdd (zeroOneSobolevSections A μ q 0).toAddSubmonoid
  hD.sobolevL A hDs μ q + perturbationL A μ hp hqp α

@[simp]
theorem perturbedSobolevL_apply (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (ξ : SobolevSection A μ q 1) :
    hD.perturbedSobolevL A hDs μ hp hqp α ξ =
      hD.sobolevL A hDs μ q ξ + perturbationL A μ hp hqp α ξ :=
  (rfl)

/-- The realizations of `D₀ + α` and of `D₀` differ by a compact operator, the rough zeroth-order
term. -/
theorem isCompactOperator_perturbedSobolevL_sub (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0) :
    IsCompactOperator fun ξ ↦
      hD.perturbedSobolevL A hDs μ hp hqp α ξ - hD.sobolevL A hDs μ q ξ := by
  convert isCompactOperator_perturbationL A μ hp hqp α using 1
  funext ξ
  rw [perturbedSobolevL_apply]
  -- The `AddCommGroup` structure of the `(0,1)`-forms is only found once the type is given.
  exact add_sub_cancel_left (G := zeroOneSobolevSections A μ q 0) _ _

/-- **The chart formula.** In chart `i`, the realization of `D₀ + α` sends a section with chart data
`uᵢ` to `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, where `∂bar uᵢ` is the complex antilinear part of any
weak derivative `Du` of `uᵢ` and `Zᵢ` is the zeroth-order term of `D₀` in chart `i`. -/
theorem chartValueL_perturbedSobolevL_ae (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((hD.perturbedSobolevL A hDs μ hp hqp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        complexAntilinearPartL
          ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 0 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  have h₃ := (FiniteBundleAtlas.ae_image_tangentHom_iff A μ i).1 (Lp.coeFn_add
    (A.tangentHom.sectionChartData.chartValueL μ q 0 i
      ((hD.sobolevL A hDs μ q ξ : SobolevSection A.tangentHom μ q 0) :
        A.tangentHom.sectionChartData.SobolevData μ q 0))
    (A.tangentHom.sectionChartData.chartValueL μ q 0 i
      ((perturbationL A μ hp hqp α ξ : SobolevSection A.tangentHom μ q 0) :
        A.tangentHom.sectionChartData.SobolevData μ q 0)))
  filter_upwards [chartValueL_sobolevL_ae A hD hDs μ q ξ hDu,
    chartValueL_perturbationL_ae A μ hp hqp α ξ i, h₃] with y h₁ h₂ h₃
  rw [perturbedSobolevL_apply, Submodule.coe_add, Submodule.coe_add, map_add, h₃, Pi.add_apply,
    h₁, h₂]

/-- **The chart formula for a `(0,1)`-valued coefficient.** If the chart data of `α` take values in
complex antilinear maps almost everywhere, that is `α` is a zeroth-order term in
`Λ^{0,1} ⊗ End_ℝ V`, then in chart `i` the realization of `D₀ + α` is `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`. -/
theorem chartValueL_perturbedSobolevL_ae_of_zeroOne (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 0)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du)
    (hα : ∀ᵐ y ∂μ.restrict (A.image i), ∀ (u : F) (v : ℂ),
      (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 0 i α y u (Complex.I • v) =
        -(Complex.I •
          (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 0 i α y u v)) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((hD.perturbedSobolevL A hDs μ hp hqp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 0 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y) := by
  filter_upwards [hD.chartValueL_perturbedSobolevL_ae A hDs μ hp hqp α ξ hDu, hα] with y h hy
  rw [h, complexAntilinearPartL_eq_self_iff.2 (hy _)]

end IsRealCauchyRiemannOperator

end TauCeti
