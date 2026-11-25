/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation

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
`TauCeti.SobolevSection.exists_isCompactOperator_of_inv_lt_inv_add` gives a bounded operator
`W^{1,p} → W^{0,r}` keeping the chart data. With `r = p + q`, the coefficient is then an `L^r`
coefficient with `2 < r` and `q ≤ r`, and the realization is
`TauCeti.IsRealCauchyRiemannOperator.perturbationL` at the exponent `r`, which is compact.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.orderOnePerturbationL`: for a fixed `W^{1,p}` coefficient
  `α`, the compact operator `ξ ↦ (α ξ)^{0,1}` from `W^{1,q}` sections to `L^q` `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.orderOnePerturbedSobolevL`: the realization of `D₀ + α` as a
  bounded operator `W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_orderOnePerturbationL`: the perturbation
  is compact.
* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_orderOnePerturbedSobolevL_sub`: the
  realizations of `D₀ + α` and of `D₀` differ by a compact operator.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_orderOnePerturbedSobolevL_ae`,
  `TauCeti.IsRealCauchyRiemannOperator.chartValueL_orderOnePerturbedSobolevL_ae_of_zeroOne`: in
  chart `i`, the realization is `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, and `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`
  for a coefficient with values in `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.orderOnePerturbedSobolevL_eq_perturbedSobolevL`: for
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

local instance instVectorBundleRealCauchyRiemannPerturbationOrderOne : VectorBundle ℝ F V :=
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

/-- For `p ≥ 2`, the Rellich–Kondrachov exponent condition `1/p < 1/r + 1/2` for one derivative
on a surface holds for every finite exponent `r`. -/
private theorem inv_lt_inv_add {p : ℝ≥0} (hp : 2 ≤ p) {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    (p : ℝ≥0∞)⁻¹ < r⁻¹ + (1 : ℕ) * (finrank ℝ ℂ : ℝ≥0∞)⁻¹ := by
  rw [Complex.finrank_real_complex, Nat.cast_one, one_mul, Nat.cast_ofNat, add_comm]
  refine (ENNReal.inv_le_inv.2 ?_).trans_lt (ENNReal.lt_add_right (by simp) (by simpa using hr))
  rw [← ENNReal.coe_ofNat]
  exact ENNReal.coe_le_coe.2 hp

omit [Fact (1 ≤ (q : ℝ≥0∞))] in
/-- For `p ≥ 2`, a `W^{1,p}` section of the real hom bundle from `V` to the `V`-valued one-forms
is an `L^r` section for every finite `r`, by a bounded operator keeping the chart data. -/
private theorem exists_coefficientL (hp : 2 ≤ p) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))] :
    ∃ T : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1 →L[ℝ]
      SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ r 0,
      ∀ α (i : Fin A.n),
        (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ r 0 i (T α) =ᵐ[μ.restrict (A.image i)]
          (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 1 i α := by
  obtain ⟨T, -, hT⟩ := SobolevSection.exists_isCompactOperator_of_inv_lt_inv_add (q := r)
    (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ 0 (by simp) one_ne_zero
    ENNReal.coe_ne_top (inv_lt_inv_add hp ENNReal.coe_ne_top)
  refine ⟨T, fun α i ↦ ?_⟩
  rw [← FiniteBundleAtlas.image_hom (A := A) (h := A.tangentHom.closure_dom_subset_baseSet)
    (𝕜 := ℝ) i]
  exact hT α i

/-- The `W^{1,p}` coefficient as an `L^r` coefficient, `p ≥ 2`. -/
private def coefficientL (hp : 2 ≤ p) (r : ℝ≥0) [Fact (1 ≤ (r : ℝ≥0∞))] :
    SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1 →L[ℝ]
      SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ r 0 :=
  (exists_coefficientL A μ hp r).choose

/-- **The zeroth-order term of class `W^{1,p}`.** For `p ≥ 2`, every finite `q ≥ 1` and a `W^{1,p}`
section `α` of the real hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, the bounded operator sending
a `W^{1,q}` section `ξ` of `V` to the `(0,1)`-part of the one-form `α ξ`, an `L^q` `(0,1)`-form.
In chart `i` it is the complex antilinear part of `αᵢ uᵢ`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_orderOnePerturbationL_ae`). It is
`TauCeti.IsRealCauchyRiemannOperator.perturbationL` for `α` as an `L^r` coefficient, `r = p + q`.
-/
def orderOnePerturbationL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  perturbationL A μ (two_lt_add hp) le_add_self
    (coefficientL A μ hp (p + q) α)

/-- **Compact perturbation** (McDuff–Salamon, Lemma C.2.2, at `ℓ = 2`, `k = 1`). For a fixed
`W^{1,p}` coefficient with `p ≥ 2`, the zeroth-order term is compact from `W^{1,q}` to `L^q`, for
every finite `q ≥ 1`. -/
theorem isCompactOperator_orderOnePerturbationL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    IsCompactOperator (orderOnePerturbationL (q := q) A μ hp α) :=
  -- `orderOnePerturbationL` is `perturbationL` of `coefficientL α` by definition.
  isCompactOperator_perturbationL A μ _ _ _

/-- In chart `i`, the zeroth-order term is the complex antilinear part of the pointwise
application of the chart data `αᵢ` of the coefficient to the chart data `uᵢ` of the section. -/
theorem chartValueL_orderOnePerturbationL_ae (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((orderOnePerturbationL A μ hp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  filter_upwards [chartValueL_perturbationL_ae A μ (two_lt_add hp)
      le_add_self (coefficientL A μ hp (p + q) α) ξ i,
    (exists_coefficientL A μ hp (p + q)).choose_spec α i] with y h₁ h₂
  -- `orderOnePerturbationL` is `perturbationL` of `coefficientL α` by definition.
  rw [← h₂]
  exact h₁

include hD in
/-- **The realization of `D₀ + α`.** For a smooth real Cauchy–Riemann operator `D₀`, `p ≥ 2`,
every finite `q ≥ 1` and a `W^{1,p}` zeroth-order term `α`, the bounded operator
`W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` sending `ξ` to `D₀ ξ + (α ξ)^{0,1}`
(`TauCeti.IsRealCauchyRiemannOperator.orderOnePerturbedSobolevL_apply`). For a coefficient with
values in `(0,1)`-forms it is `D₀ + α` in every chart
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_orderOnePerturbedSobolevL_ae_of_zeroOne`). It is
`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL` for `α` as an `L^r` coefficient,
`r = p + q`. -/
def orderOnePerturbedSobolevL (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    SobolevSection A μ q 1 →L[ℝ] zeroOneSobolevSections A μ q 0 :=
  hD.perturbedSobolevL A hDs μ (two_lt_add hp) le_add_self
    (coefficientL A μ hp (p + q) α)

/-- The realization of `D₀ + α` is the realization of `D₀` plus the zeroth-order term. -/
@[simp]
theorem orderOnePerturbedSobolevL_apply (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) :
    hD.orderOnePerturbedSobolevL A hDs μ hp α ξ =
      hD.sobolevL A hDs μ q ξ + orderOnePerturbationL A μ hp α ξ := by
  rw [orderOnePerturbedSobolevL, perturbedSobolevL_apply, orderOnePerturbationL]

/-- The realizations of `D₀ + α` and of `D₀` differ by a compact operator, the zeroth-order term
of class `W^{1,p}`. -/
theorem isCompactOperator_orderOnePerturbedSobolevL_sub (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    IsCompactOperator fun ξ : SobolevSection A μ q 1 ↦
      hD.orderOnePerturbedSobolevL A hDs μ hp α ξ - hD.sobolevL A hDs μ q ξ :=
  -- `orderOnePerturbedSobolevL` is `perturbedSobolevL` of `coefficientL α` by definition.
  isCompactOperator_perturbedSobolevL_sub A hD hDs μ _ _ _

/-- **The chart formula.** In chart `i`, the realization of `D₀ + α` sends a section with chart data
`uᵢ` to `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, where `∂bar uᵢ` is the complex antilinear part of any
weak derivative `Du` of `uᵢ` and `Zᵢ` is the zeroth-order term of `D₀` in chart `i`. -/
theorem chartValueL_orderOnePerturbedSobolevL_ae (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((hD.orderOnePerturbedSobolevL A hDs μ hp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        complexAntilinearPartL
          ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y)) := by
  filter_upwards [hD.chartValueL_perturbedSobolevL_ae A hDs μ (two_lt_add hp)
      le_add_self (coefficientL A μ hp (p + q) α) ξ hDu,
    (exists_coefficientL A μ hp (p + q)).choose_spec α i] with y h₁ h₂
  -- `orderOnePerturbedSobolevL` is `perturbedSobolevL` of `coefficientL α` by definition.
  rw [← h₂]
  exact h₁

/-- **The chart formula for a `(0,1)`-valued coefficient.** If the chart data of `α` take values in
complex antilinear maps almost everywhere, that is `α` is a zeroth-order term in
`Λ^{0,1} ⊗ End_ℝ V`, then in chart `i` the realization of `D₀ + α` is `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`. -/
theorem chartValueL_orderOnePerturbedSobolevL_ae_of_zeroOne (hp : 2 ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1)
    (ξ : SobolevSection A μ q 1) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn μ (A.image i) (A.sectionChartData.chartValueL μ q 1 i ξ) Du)
    (hα : ∀ᵐ y ∂μ.restrict (A.image i), ∀ (u : F) (v : ℂ),
      (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y u (Complex.I • v) =
        -(Complex.I •
          (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            μ p 1 i α y u v)) :
    A.tangentHom.sectionChartData.chartValueL μ q 0 i
        ((hD.orderOnePerturbedSobolevL A hDs μ hp α ξ : SobolevSection A.tangentHom μ q 0) :
          A.tangentHom.sectionChartData.SobolevData μ q 0)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL μ q 1 i ξ y) +
        (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          μ p 1 i α y (A.sectionChartData.chartValueL μ q 1 i ξ y) := by
  filter_upwards [hD.chartValueL_orderOnePerturbedSobolevL_ae A hDs μ hp α ξ hDu, hα] with y h hy
  rw [h, complexAntilinearPartL_eq_self_iff.2 (hy _)]

/-- **Agreement with the `L^p` realization.** For `p > 2` and `q ≤ p`, the zeroth-order term of a
`W^{1,p}` coefficient `α` is that of `α` as an `L^p` coefficient. -/
theorem orderOnePerturbationL_eq_perturbationL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    orderOnePerturbationL A μ hp.le α = perturbationL A μ hp hqp
      ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        μ p 0 α) := by
  refine ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <|
    SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (FiniteBundleAtlas.ae_image_tangentHom_iff A μ i).2 ?_
  filter_upwards [chartValueL_orderOnePerturbationL_ae A μ hp.le α ξ i,
    chartValueL_perturbationL_ae A μ hp hqp _ ξ i] with y h₁ h₂
  rw [h₁, h₂, SectionChartData.chartValueL_coe_lowerOrderL
    (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData μ p 0 α i]

/-- **Agreement with the `L^p` realization.** For `p > 2` and `q ≤ p`, the realization of `D₀ + α`
for a `W^{1,p}` coefficient `α` is the realization for `α` as an `L^p` coefficient. -/
theorem orderOnePerturbedSobolevL_eq_perturbedSobolevL (hp : 2 < p) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ p 1) :
    hD.orderOnePerturbedSobolevL A hDs μ hp.le α = hD.perturbedSobolevL A hDs μ hp hqp
      ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        μ p 0 α) :=
  ContinuousLinearMap.ext fun ξ ↦ by
    rw [orderOnePerturbedSobolevL_apply, perturbedSobolevL_apply,
      orderOnePerturbationL_eq_perturbationL A μ hp hqp]

/-- **Check.** A zeroth-order term of class `W^{1,3}` is realized from `W^{1,4}` to `L^4`, an
exponent above `3` excluded for `L^3` coefficients, and from `W^{1,3/2}` to `L^{3/2}`, below `2`; in
both cases it is compact. -/
example [Fact (1 ≤ ((3 : ℝ≥0) : ℝ≥0∞))] [Fact (1 ≤ ((4 : ℝ≥0) : ℝ≥0∞))]
    [Fact (1 ≤ ((3 / 2 : ℝ≥0) : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ
      ((3 : ℝ≥0) : ℝ≥0∞) 1) :
    IsCompactOperator (orderOnePerturbationL (q := 4) A μ (by norm_num) α) ∧
      IsCompactOperator (orderOnePerturbationL (q := 3 / 2) A μ (by norm_num) α) :=
  ⟨isCompactOperator_orderOnePerturbationL A μ _ α,
    isCompactOperator_orderOnePerturbationL A μ _ α⟩

/-- **Check.** The endpoint `p = 2`, below the range `p > 2` of McDuff–Salamon Definition C.1.5 and
of `TauCeti.IsRealCauchyRiemannOperator.perturbationL`: a `W^{1,2}` coefficient lies in every `L^r`,
`r < ∞`, so it still gives a compact zeroth-order term from `W^{1,q}` to `L^q`. -/
example [Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ
      ((2 : ℝ≥0) : ℝ≥0∞) 1) :
    IsCompactOperator (orderOnePerturbationL (q := q) A μ le_rfl α) :=
  isCompactOperator_orderOnePerturbationL A μ _ α

end IsRealCauchyRiemannOperator

end TauCeti
