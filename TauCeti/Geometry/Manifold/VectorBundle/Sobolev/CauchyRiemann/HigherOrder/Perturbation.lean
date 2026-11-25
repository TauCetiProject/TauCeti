/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.HomMultiplication.Higher
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich

/-!
# Real Cauchy–Riemann operators with higher-order Sobolev zeroth-order terms

Let `M` be a closed complex curve and `V → M` a complex vector bundle with a finite bundle atlas
`A`. A real Cauchy–Riemann operator of class `W^{ℓ-1,p}` is `D = D₀ + α`, where `D₀` is a smooth
real Cauchy–Riemann operator and `α` is a zeroth-order term of class `W^{ℓ-1,p}`, `p > 2`, with
values in `(0,1)`-forms (McDuff–Salamon, Definition C.1.5). This file realizes such operators for
`ℓ ≥ 2` at the top Sobolev order `m = ℓ` of McDuff–Salamon Theorem C.1.10, as bounded operators

`W^{ℓ,q}(Σ, V) → W^{ℓ-1,q}(Σ, Λ^{0,1} ⊗ V)`

for every `1 < q ≤ p`, and shows that `D - D₀` is compact (McDuff–Salamon Lemma C.2.2). At the
top order `m = ℓ`, the admissibility condition `m - 2/q ≤ ℓ - 2/p` of Theorem C.1.10 is `q ≤ p`.
In the declarations `ℓ = k + 2`: the coefficient is in `W^{k+1,p}` and the realization goes from
`W^{k+2,q}` to `W^{k+1,q}`. The case `ℓ = 1` is
`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL`.

The Sobolev spaces are those of the Lebesgue measure `volume` on the charts, in which the local
Sobolev classes behind multiplication by `W^{k+1,p}` coefficients are stated.

## The argument

Since `k + 1 ≥ 1` and `p > 2`, a `W^{k+1,p}` coefficient multiplies `W^{k+1,q}` into itself
(`TauCeti.SobolevSection.homMulSuccL`). The perturbation `ξ ↦ (α ξ)^{0,1}` is this multiplication
after the inclusion `W^{k+2,q} → W^{k+1,q}`, which is compact by Rellich's theorem
(`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`). So the perturbation is compact, with no
need to approximate the coefficient.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.perturbationSuccL`: for a fixed `W^{k+1,p}` coefficient `α`,
  the compact operator `ξ ↦ (α ξ)^{0,1}` from `W^{k+2,q}` sections to `W^{k+1,q}` `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL`: the realization of `D₀ + α` as a
  bounded operator `W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbationSuccL`: the perturbation is
  compact.
* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbedSobolevSuccL_sub`: the
  realizations of `D₀ + α` and of `D₀` differ by a compact operator.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevSuccL_ae`,
  `TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevSuccL_ae_of_zeroOne`: in chart
  `i`, the realization is `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, and `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ` for a
  coefficient with values in `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_perturbedSobolevSuccL`: the
  realizations at consecutive orders commute with forgetting the highest weak derivative.

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

local instance instVectorBundleRealCauchyRiemannPerturbationSucc : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (k : ℕ)

namespace IsRealCauchyRiemannOperator

/-- Multiplication by a `W^{k+1,p}` section of the real hom bundle from `V` to the `V`-valued
one-forms, on `W^{k+1,q}` sections of `V`. -/
private def homMulTangentSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    SobolevSection A volume q (k + 1) →L[ℝ] SobolevSection A.tangentHom volume q (k + 1) :=
  SobolevSection.homMulSuccL A A.tangentHom.closure_dom_subset_baseSet ENat.LEInfty.out hp hq hqp
    α

/-- **The zeroth-order term of class `W^{k+1,p}`.** For `p > 2`, `1 < q ≤ p` and a `W^{k+1,p}`
section `α` of the real hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, the bounded operator sending
a `W^{k+2,q}` section `ξ` of `V` to the `(0,1)`-part of the one-form `α ξ`, a `W^{k+1,q}`
`(0,1)`-form (`TauCeti.IsRealCauchyRiemannOperator.perturbationSuccL_apply`). In chart `i` it is
the complex antilinear part of `αᵢ uᵢ`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbationSuccL_ae`). -/
def perturbationSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    SobolevSection A volume q (k + 1 + 1) →L[ℝ] zeroOneSobolevSections A volume q (k + 1) :=
  (zeroOnePartSobolevL A volume q (k + 1)).comp
    ((homMulTangentSuccL A k hp hq hqp α).comp (A.sectionChartData.lowerOrderL volume q (k + 1)))

omit [T2Space M] in
@[simp]
theorem perturbationSuccL_apply (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) :
    perturbationSuccL A k hp hq hqp α ξ = zeroOnePartSobolevL A volume q (k + 1)
      (SobolevSection.homMulSuccL A A.tangentHom.closure_dom_subset_baseSet ENat.LEInfty.out hp hq
        hqp α (A.sectionChartData.lowerOrderL volume q (k + 1) ξ)) :=
  (rfl)

/-- **Compact perturbation** (McDuff–Salamon, Lemma C.2.2, at the top order `ℓ = k + 2 ≥ 2`).
For a fixed `W^{k+1,p}` coefficient with `p > 2`, the zeroth-order term is compact from
`W^{k+2,q}` to `W^{k+1,q}`, for every `1 < q ≤ p`: it factors through the compact inclusion
`W^{k+2,q} → W^{k+1,q}`. -/
theorem isCompactOperator_perturbationSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    IsCompactOperator (perturbationSuccL A k hp hq hqp α) :=
  (SobolevSection.isCompactOperator_lowerOrderL A volume q (k + 1)).clm_comp
    ((zeroOnePartSobolevL A volume q (k + 1)).comp (homMulTangentSuccL A k hp hq hqp α))

omit [T2Space M] in
/-- In chart `i`, the zeroth-order term is the complex antilinear part of the pointwise application
of the chart data `αᵢ` of the coefficient to the chart data `uᵢ` of the section. -/
theorem chartValueL_perturbationSuccL_ae (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((perturbationSuccL A k hp hq hqp α ξ : SobolevSection A.tangentHom volume q (k + 1)) :
          A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1) i α y
            (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y)) := by
  have h₁ := chartValueL_zeroOnePartSobolevL_ae
    (homMulTangentSuccL A k hp hq hqp α (A.sectionChartData.lowerOrderL volume q (k + 1) ξ)) i
  have h₂ := SobolevSection.chartValueL_homMulSuccL_ae A A.tangentHom.closure_dom_subset_baseSet
    ENat.LEInfty.out hp hq hqp α (A.sectionChartData.lowerOrderL volume q (k + 1) ξ) i
  filter_upwards [(FiniteBundleAtlas.ae_image_tangentHom_iff A volume i).1 h₁, h₂] with y hy₁ hy₂
  rw [perturbationSuccL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hy₁]
  refine congrArg complexAntilinearPartL (hy₂.trans ?_)
  rw [A.sectionChartData.chartValueL_coe_lowerOrderL volume q (k + 1) ξ i]

omit [T2Space M] in
/-- **Compatibility with the order.** Forgetting the highest weak derivative of the zeroth-order
term of a `W^{k+2,p}` coefficient on a `W^{k+3,q}` section gives the zeroth-order term at order
`k + 2`, of the coefficient and the section regarded as one order rougher. -/
theorem zeroOneLowerOrdersL_perturbationSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1 + 1)) :
    zeroOneLowerOrdersL A volume q (k + 1) 1 (perturbationSuccL A (k + 1) hp hq hqp α ξ) =
      perturbationSuccL A k hp hq hqp
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
          volume p (k + 1) α)
        (A.sectionChartData.lowerOrderL volume q (k + 1 + 1) ξ) := by
  rw [perturbationSuccL_apply, perturbationSuccL_apply]
  -- `rw` does not find these patterns through the hom atlas of the one-form bundle, so the steps
  -- are chained as terms.
  exact (zeroOneLowerOrdersL_zeroOnePartSobolevL 1 _).trans
    (congrArg (zeroOnePartSobolevL A volume q (k + 1))
      ((DFunLike.congr_fun
        (A.tangentHom.sectionChartData.lowerOrdersL_one volume q (k + 1)) _).trans
        (SobolevSection.lowerOrderL_homMulSuccL A A.tangentHom.closure_dom_subset_baseSet
          ENat.LEInfty.out hp hq hqp α _)))

include hD in
/-- **The realization of `D₀ + α` at order `k + 2`.** For a smooth real Cauchy–Riemann operator
`D₀`, `p > 2`, `1 < q ≤ p` and a `W^{k+1,p}` zeroth-order term `α`, the bounded operator
`W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)` sending `ξ` to `D₀ ξ + (α ξ)^{0,1}`
(`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL_apply`). For a coefficient with values
in `(0,1)`-forms it is `D₀ + α` in every chart
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_perturbedSobolevSuccL_ae_of_zeroOne`). -/
def perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    SobolevSection A volume q (k + 1 + 1) →L[ℝ] zeroOneSobolevSections A volume q (k + 1) :=
  -- Instance search for this `ContinuousAdd` instance exceeds the default heartbeat limit.
  haveI : ContinuousAdd (zeroOneSobolevSections A volume q (k + 1)) :=
    AddSubmonoid.continuousAdd (zeroOneSobolevSections A volume q (k + 1)).toAddSubmonoid
  hD.sobolevSuccL A hDs volume q (k + 1) + perturbationSuccL A k hp hq hqp α

@[simp]
theorem perturbedSobolevSuccL_apply (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) :
    hD.perturbedSobolevSuccL A hDs k hp hq hqp α ξ =
      hD.sobolevSuccL A hDs volume q (k + 1) ξ + perturbationSuccL A k hp hq hqp α ξ :=
  (rfl)

/-- The realizations of `D₀ + α` and of `D₀` at order `k + 2` differ by a compact operator, the
zeroth-order term. -/
theorem isCompactOperator_perturbedSobolevSuccL_sub (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    IsCompactOperator fun ξ ↦
      hD.perturbedSobolevSuccL A hDs k hp hq hqp α ξ -
        hD.sobolevSuccL A hDs volume q (k + 1) ξ := by
  convert isCompactOperator_perturbationSuccL A k hp hq hqp α using 1
  funext ξ
  rw [perturbedSobolevSuccL_apply]
  -- The `AddCommGroup` structure of the `(0,1)`-forms is only found once the type is given.
  exact add_sub_cancel_left (G := zeroOneSobolevSections A volume q (k + 1)) _ _

/-- **Compatibility with the order.** Forgetting the highest weak derivative of the realization of
`D₀ + α` at order `k + 3`, for a `W^{k+2,p}` coefficient `α`, gives the realization at order `k + 2`
of `D₀ + α`, with `α` and the section regarded as one order rougher. -/
theorem zeroOneLowerOrdersL_perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1 + 1)) :
    zeroOneLowerOrdersL A volume q (k + 1) 1
        (hD.perturbedSobolevSuccL A hDs (k + 1) hp hq hqp α ξ) =
      hD.perturbedSobolevSuccL A hDs k hp hq hqp
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
          volume p (k + 1) α)
        (A.sectionChartData.lowerOrderL volume q (k + 1 + 1) ξ) := by
  rw [perturbedSobolevSuccL_apply, perturbedSobolevSuccL_apply, map_add,
    zeroOneLowerOrdersL_sobolevSuccL, zeroOneLowerOrdersL_perturbationSuccL]

/-- **The chart formula.** In chart `i`, the realization of `D₀ + α` at order `k + 2` sends a
section with chart data `uᵢ` to `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, where `∂bar uᵢ` is the complex
antilinear part of any weak derivative `Du` of `uᵢ` and `Zᵢ` is the zeroth-order term of `D₀` in
chart `i`. -/
theorem chartValueL_perturbedSobolevSuccL_ae (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn volume (A.image i)
      (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ) Du) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((hD.perturbedSobolevSuccL A hDs k hp hq hqp α ξ :
          SobolevSection A.tangentHom volume q (k + 1)) :
            A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) +
        complexAntilinearPartL
          ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            volume p (k + 1) i α y
              (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y)) := by
  have h₃ := (FiniteBundleAtlas.ae_image_tangentHom_iff A volume i).1 (Lp.coeFn_add
    (A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
      ((hD.sobolevSuccL A hDs volume q (k + 1) ξ : SobolevSection A.tangentHom volume q (k + 1)) :
        A.tangentHom.sectionChartData.SobolevData volume q (k + 1)))
    (A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
      ((perturbationSuccL A k hp hq hqp α ξ : SobolevSection A.tangentHom volume q (k + 1)) :
        A.tangentHom.sectionChartData.SobolevData volume q (k + 1))))
  filter_upwards [chartValueL_sobolevSuccL_ae A hD hDs volume q (k + 1) ξ hDu,
    chartValueL_perturbationSuccL_ae A k hp hq hqp α ξ i, h₃] with y h₁ h₂ h₃
  rw [perturbedSobolevSuccL_apply, Submodule.coe_add, Submodule.coe_add, map_add, h₃,
    Pi.add_apply, h₁, h₂]

/-- **The chart formula for a `(0,1)`-valued coefficient.** If the chart data of `α` take values in
complex antilinear maps almost everywhere, that is `α` is a zeroth-order term in
`Λ^{0,1} ⊗ End_ℝ V`, then in chart `i` the realization of `D₀ + α` at order `k + 2` is
`∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`. -/
theorem chartValueL_perturbedSobolevSuccL_ae_of_zeroOne (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn volume (A.image i)
      (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ) Du)
    (hα : ∀ᵐ y ∂volume.restrict (A.image i), ∀ (u : F) (v : ℂ),
      (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1) i α y u (Complex.I • v) =
        -(Complex.I •
          (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            volume p (k + 1) i α y u v)) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((hD.perturbedSobolevSuccL A hDs k hp hq hqp α ξ :
          SobolevSection A.tangentHom volume q (k + 1)) :
            A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) +
        (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1) i α y (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) := by
  filter_upwards [hD.chartValueL_perturbedSobolevSuccL_ae A hDs k hp hq hqp α ξ hDu, hα]
    with y h hy
  rw [h, complexAntilinearPartL_eq_self_iff.2 (hy _)]

end IsRealCauchyRiemannOperator

end TauCeti
