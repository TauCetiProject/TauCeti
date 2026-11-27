/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation.Basic

/-!
# Real Cauchy–Riemann operators with zeroth-order terms of class `W^{1,p}`

Let `M` be a closed complex curve and `V → M` a complex vector bundle with a finite bundle atlas
`A`. A real Cauchy–Riemann operator of class `W^{1,p}` is `D = D₀ + α`, where `D₀` is a smooth real
Cauchy–Riemann operator and `α` is a zeroth-order term of class `W^{1,p}`, `p > 2`, with values in
`(0,1)`-forms (McDuff–Salamon, Definition C.1.5, with `ℓ = 2`). This file realizes such operators
as bounded operators `W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` for every finite `q ≥ 1`, the exponents
`ℓ = 2`, `k = 1` of McDuff–Salamon Theorem C.1.10, and shows that `D - D₀` is compact
(McDuff–Salamon Lemma C.2.2 at `ℓ = 2`, `k = 1`).

The admissible exponents of Theorem C.1.10 are `k - 2/q ≤ ℓ - 2/p`. For `ℓ = 2` and `k = 1` this is
`2/p - 1 ≤ 2/q`, which holds for every `q` since `p > 2`. So, unlike the `L^p` coefficients of
`TauCeti.IsRealCauchyRiemannOperator.perturbationL`, which need `q ≤ p`, a `W^{1,p}` coefficient
gives a realization at every exponent `q`, including `q > p`. The construction works for `p ≥ 2`,
so the results are stated for `p ≥ 2`, including the endpoint `p = 2` outside Definition C.1.5.

## The argument

A `W^{1,p}` section of the real hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)` lies in `L^r` for every
finite `r`: since `1/p ≤ 1/2 < 1/r + 1/2`, the Rellich–Kondrachov theorem
`TauCeti.SobolevSection.exists_isCompactOperator_of_finrank_le` gives a bounded operator
`W^{1,p} → W^{0,r}` keeping the chart data. With `r = p + q`, the coefficient is then an `L^r`
coefficient with `2 < r` and `q ≤ r`, and the realization is
`TauCeti.IsRealCauchyRiemannOperator.perturbationL` at the exponent `r`, which is compact.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbationL`: for a fixed `W^{1,p}` coefficient
  `α`, the compact operator `ξ ↦ (α ξ)^{0,1}` from `W^{1,q}` sections to `L^q` `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL`: the realization of `D₀ + α`
  as a bounded operator `W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_sobolevCoeffPerturbationL`: the
  perturbation is compact.
* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_sobolevCoeffPerturbedSobolevL_sub`: the
  realizations of `D₀ + α` and of `D₀` differ by a compact operator.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevL_ae`,
  `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevL_ae_of_zeroOne`: in
  chart `i`, the realization is `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, and `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`
  for a coefficient with values in `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL_eq_perturbedSobolevL`: for
  `p > 2` and `q ≤ p` the realization is that of `α` as an `L^p` coefficient.

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

local instance instVectorBundleRealCauchyRiemannPerturbationSobolevCoeff : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
  [Fact (1 ≤ (q : ℝ≥0∞))]

namespace IsRealCauchyRiemannOperator

/-- The exponent `p + q` at which a `W^{1,p}` coefficient acts on `W^{1,q}` is at least `1`. -/
local instance instFactOneLeAdd : Fact (1 ≤ ((p + q : ℝ≥0) : ℝ≥0∞)) :=
  ⟨(Fact.out : (1 : ℝ≥0∞) ≤ q).trans (ENNReal.coe_le_coe.2 le_add_self)⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- For `p ≥ 2` and `q ≥ 1`, the exponent `p + q` lies above `2`, as multiplication by `L^{p+q}`
coefficients on a surface requires. -/
private theorem two_lt_add (hp : 2 ≤ p) : 2 < p + q :=
  hp.trans_lt (lt_add_of_pos_right p
    (ENNReal.coe_pos.1 (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))))

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- For `p ≥ 2`, the exponent `p` is at least the real dimension of the base. -/
private theorem finrank_le (hp : 2 ≤ p) : (finrank ℝ ℂ : ℝ≥0∞) ≤ p := by
  rw [Complex.finrank_real_complex]
  exact_mod_cast hp

/-- The `W^{1,p}` coefficient as an `L^r` coefficient, `p ≥ 2`, through the Rellich–Kondrachov
embedding `TauCeti.SobolevSection.exists_isCompactOperator_of_finrank_le` of the hom bundle. -/
private def coefficientL (hp : 2 ≤ p) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))] :
    SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1 →L[ℝ]
      SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ r 0 :=
  (SobolevSection.exists_isCompactOperator_of_finrank_le (q := r)
    (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ 0
    (by simp [Complex.finrank_real_complex]) (finrank_le hp) ENNReal.coe_ne_top).choose

omit [Fact (1 ≤ (q : ℝ≥0∞))] in
/-- The coefficient embedding keeps the chart data. -/
private theorem chartValueL_coefficientL_ae (hp : 2 ≤ p) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1)
    (i : Fin A.n) :
    (A.hom (𝕜 := ℝ)
        (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
        μ r 0 i (coefficientL A μ hp r α) =ᵐ[μ.restrict (A.image i)]
      (A.hom (𝕜 := ℝ)
          (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
        μ p 1 i α := by
  rw [← FiniteBundleAtlas.image_hom (A := A)
    (h := (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) (𝕜 := ℝ) i]
  -- `coefficientL` is the operator chosen from the Rellich–Kondrachov embedding.
  exact (SobolevSection.exists_isCompactOperator_of_finrank_le (q := r)
    (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ 0
    (by simp [Complex.finrank_real_complex]) (finrank_le hp) ENNReal.coe_ne_top).choose_spec.2 α i

/-- **The zeroth-order term of class `W^{1,p}`.** For `p ≥ 2`, every finite `q ≥ 1` and a `W^{1,p}`
section `α` of the real hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, the bounded operator sending
a `W^{1,q}` section `ξ` of `V` to the `(0,1)`-part of the one-form `α ξ`, an `L^q` `(0,1)`-form.
In chart `i` it is the complex antilinear part of `αᵢ uᵢ`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbationL_ae`). It is
`TauCeti.IsRealCauchyRiemannOperator.perturbationL` for `α` as an `L^r` coefficient, `r = p + q`.
-/
def sobolevCoeffPerturbationL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  perturbationL A μ (two_lt_add hp) le_add_self
    (coefficientL A μ hp (p + q) α)

/-- **Compact perturbation** (McDuff–Salamon, Lemma C.2.2, at `ℓ = 2`, `k = 1`). For a fixed
`W^{1,p}` coefficient with `p ≥ 2`, the zeroth-order term is compact from `W^{1,q}` to `L^q`, for
every finite `q ≥ 1`. -/
theorem isCompactOperator_sobolevCoeffPerturbationL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    IsCompactOperator (sobolevCoeffPerturbationL (q := q) A μ hp α) :=
  -- `sobolevCoeffPerturbationL` is `perturbationL` of `coefficientL α` by definition.
  isCompactOperator_perturbationL A μ _ _ _

/-- In chart `i`, the zeroth-order term is the complex antilinear part of the pointwise
application of the chart data `αᵢ` of the coefficient to the chart data `uᵢ` of the section. -/
theorem chartValueL_sobolevCoeffPerturbationL_ae (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) (i : Fin A.n) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ q 0 i
        ((sobolevCoeffPerturbationL A μ hp α ξ : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q 0) :
          (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL
        ((A.hom (𝕜 := ℝ)
            (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  filter_upwards [chartValueL_perturbationL_ae A μ (two_lt_add hp)
      le_add_self (coefficientL A μ hp (p + q) α) ξ i,
    chartValueL_coefficientL_ae A μ hp (p + q) α i] with y h₁ h₂
  -- `sobolevCoeffPerturbationL` is `perturbationL` of `coefficientL α` by definition.
  rw [← h₂]
  exact h₁

include hD in
/-- **The realization of `D₀ + α`.** For a smooth real Cauchy–Riemann operator `D₀`, `p ≥ 2`,
every finite `q ≥ 1` and a `W^{1,p}` zeroth-order term `α`, the bounded operator
`W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` sending `ξ` to `D₀ ξ + (α ξ)^{0,1}`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL_apply`). For a coefficient with
values in `(0,1)`-forms it is `D₀ + α` in every chart
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevL_ae_of_zeroOne`).
It is `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL` for `α` as an `L^r` coefficient,
`r = p + q`. -/
def sobolevCoeffPerturbedSobolevL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  hD.perturbedSobolevL A hDs μ (two_lt_add hp) le_add_self
    (coefficientL A μ hp (p + q) α)

/-- The realization of `D₀ + α` is the realization of `D₀` plus the zeroth-order term. -/
@[simp]
theorem sobolevCoeffPerturbedSobolevL_apply (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) :
    hD.sobolevCoeffPerturbedSobolevL A hDs μ hp α ξ =
      hD.sobolevL A hDs μ q ξ + sobolevCoeffPerturbationL A μ hp α ξ := by
  rw [sobolevCoeffPerturbedSobolevL, perturbedSobolevL_apply, sobolevCoeffPerturbationL]

/-- The realizations of `D₀ + α` and of `D₀` differ by a compact operator, the zeroth-order term
of class `W^{1,p}`. -/
theorem isCompactOperator_sobolevCoeffPerturbedSobolevL_sub (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    IsCompactOperator fun ξ : SobolevSection A μ q 1 ↦
      hD.sobolevCoeffPerturbedSobolevL A hDs μ hp α ξ - hD.sobolevL A hDs μ q ξ :=
  -- `sobolevCoeffPerturbedSobolevL` is `perturbedSobolevL` of `coefficientL α` by definition.
  isCompactOperator_perturbedSobolevL_sub A hD hDs μ _ _ _

/-- **The chart formula.** In chart `i`, the realization of `D₀ + α` sends a section with chart data
`uᵢ` to `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, where `∂bar uᵢ` is the complex antilinear part of any
weak derivative `Du` of `uᵢ` and `Zᵢ` is the zeroth-order term of `D₀` in chart `i`. -/
theorem chartValueL_sobolevCoeffPerturbedSobolevL_ae (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ q 0 i
        ((hD.sobolevCoeffPerturbedSobolevL A hDs μ hp α ξ :
          SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q 0) :
            (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        complexAntilinearPartL
          ((A.hom (𝕜 := ℝ)
              (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  filter_upwards [hD.chartValueL_perturbedSobolevL_ae A hDs μ (two_lt_add hp)
      le_add_self (coefficientL A μ hp (p + q) α) ξ hDu,
    chartValueL_coefficientL_ae A μ hp (p + q) α i] with y h₁ h₂
  -- `sobolevCoeffPerturbedSobolevL` is `perturbedSobolevL` of `coefficientL α` by definition.
  rw [← h₂]
  exact h₁

/-- **The chart formula for a `(0,1)`-valued coefficient.** If the chart data of `α` take values in
complex antilinear maps almost everywhere, that is `α` is a zeroth-order term in
`Λ^{0,1} ⊗ End_ℝ V`, then in chart `i` the realization of `D₀ + α` is `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`. -/
theorem chartValueL_sobolevCoeffPerturbedSobolevL_ae_of_zeroOne (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du)
    (hα : ∀ᵐ y ∂μ.restrict (A.image i), ∀ (u : F) (v : ℂ),
      (A.hom (𝕜 := ℝ)
          (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y u (Complex.I • v) =
        -(Complex.I •
          (A.hom (𝕜 := ℝ)
              (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 1 i α y u v)) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ q 0 i
        ((hD.sobolevCoeffPerturbedSobolevL A hDs μ hp α ξ :
          SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q 0) :
            (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        (A.hom (𝕜 := ℝ)
            (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y) := by
  filter_upwards [hD.chartValueL_sobolevCoeffPerturbedSobolevL_ae A hDs μ hp α ξ hDu, hα]
    with y h hy
  rw [h, complexAntilinearPartL_eq_self_iff.2 (hy _)]

/-- **Agreement with the `L^p` realization.** For `p > 2` and `q ≤ p`, the zeroth-order term of a
`W^{1,p}` coefficient `α` is that of `α` as an `L^p` coefficient. -/
theorem sobolevCoeffPerturbationL_eq_perturbationL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    sobolevCoeffPerturbationL A μ hp.le α = perturbationL A μ hp hqp
      ((A.hom (𝕜 := ℝ)
          (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        μ p 0 α) := by
  refine ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <|
    SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (FiniteBundleAtlas.ae_image_tangentHom_iff A μ i).2 ?_
  filter_upwards [chartValueL_sobolevCoeffPerturbationL_ae A μ hp.le α ξ i,
    chartValueL_perturbationL_ae A μ hp hqp _ ξ i] with y h₁ h₂
  rw [h₁, h₂, SectionChartData.chartValueL_coe_lowerOrderL
    (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData μ p 0 α i]

/-- **Agreement with the `L^p` realization.** For `p > 2` and `q ≤ p`, the realization of `D₀ + α`
for a `W^{1,p}` coefficient `α` is the realization for `α` as an `L^p` coefficient. -/
theorem sobolevCoeffPerturbedSobolevL_eq_perturbedSobolevL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ p 1) :
    hD.sobolevCoeffPerturbedSobolevL A hDs μ hp.le α = hD.perturbedSobolevL A hDs μ hp hqp
      ((A.hom (𝕜 := ℝ)
          (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        μ p 0 α) :=
  ContinuousLinearMap.ext fun ξ ↦ by
    rw [sobolevCoeffPerturbedSobolevL_apply, perturbedSobolevL_apply,
      sobolevCoeffPerturbationL_eq_perturbationL A μ hp hqp]

/-- **Check.** A zeroth-order term of class `W^{1,3}` is realized from `W^{1,4}` to `L^4`, an
exponent above `3` excluded for `L^3` coefficients, and from `W^{1,3/2}` to `L^{3/2}`, below `2`; in
both cases it is compact. -/
example [Fact (1 ≤ ((3 : ℝ≥0) : ℝ≥0∞))] [Fact (1 ≤ ((4 : ℝ≥0) : ℝ≥0∞))]
    [Fact (1 ≤ ((3 / 2 : ℝ≥0) : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ
      ((3 : ℝ≥0) : ℝ≥0∞) 1) :
    IsCompactOperator (sobolevCoeffPerturbationL (q := 4) A μ (by norm_num) α) ∧
      IsCompactOperator (sobolevCoeffPerturbationL (q := 3 / 2) A μ (by norm_num) α) :=
  ⟨isCompactOperator_sobolevCoeffPerturbationL A μ _ α,
    isCompactOperator_sobolevCoeffPerturbationL A μ _ α⟩

/-- **Check.** The endpoint `p = 2`, below the range `p > 2` of McDuff–Salamon Definition C.1.5 and
of `TauCeti.IsRealCauchyRiemannOperator.perturbationL`: a `W^{1,2}` coefficient lies in every `L^r`,
`r < ∞`, so it still gives a compact zeroth-order term from `W^{1,q}` to `L^q`. -/
example [Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) μ
      ((2 : ℝ≥0) : ℝ≥0∞) 1) :
    IsCompactOperator (sobolevCoeffPerturbationL (q := q) A μ le_rfl α) :=
  isCompactOperator_sobolevCoeffPerturbationL A μ _ α

end IsRealCauchyRiemannOperator

end TauCeti
