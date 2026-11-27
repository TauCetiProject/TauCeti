/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Estimate
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Perturbation
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation.SobolevCoeff
import TauCeti.Analysis.Normed.Operator.Compact.Estimate

/-!
# Real Cauchy–Riemann operators below the top Sobolev order

Let `M` be a closed complex curve and `V → M` a complex vector bundle with a finite bundle atlas
`A`. A real Cauchy–Riemann operator of class `W^{ℓ-1,p}` is `D = D₀ + α`, where `D₀` is a smooth
real Cauchy–Riemann operator and `α` is a zeroth-order term of class `W^{ℓ-1,p}`, `p > 2`, with
values in `(0,1)`-forms (McDuff–Salamon, Definition C.1.5). This file realizes such operators at
the Sobolev orders `2 ≤ m < ℓ` of McDuff–Salamon Theorem C.1.10, as bounded operators

`W^{m,q}(Σ, V) → W^{m-1,q}(Σ, Λ^{0,1} ⊗ V)`

for every `q > 1`, shows that `D - D₀` is compact (McDuff–Salamon Lemma C.2.2) and proves the
elliptic estimate `‖ξ‖_{W^{m,q}} ≤ C (‖D ξ‖_{W^{m-1,q}} + ‖ξ‖_{L^q})`.

Below the top order the admissibility condition `m - 2/q ≤ ℓ - 2/p` of Theorem C.1.10 holds for
every `q`, since `m - 2/q < m ≤ ℓ - 1 < ℓ - 2/p`. So, unlike the top order `m = ℓ` of
`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL`, which needs `q ≤ p`, the realization
exists at every exponent `q > 1`, including `q > p`. The declarations take a coefficient of order
`m` itself, that is `ℓ = m + 1`, with `m = k + 2`: the coefficient is in `W^{k+2,p}` and the
realization goes from `W^{k+2,q}` to `W^{k+1,q}`. A coefficient of a higher order `ℓ - 1 > m`
enters through the inclusion `SectionChartData.lowerOrdersL` into `W^{m,p}`. The order `m = 1` is
`TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL`. The construction works for
`p ≥ 2`, so the results are stated for `p ≥ 2`, including the endpoint `p = 2` outside
Definition C.1.5.

## The argument

Since `p ≥ 2` is at least the dimension of the base, the coefficient embedding
`TauCeti.IsRealCauchyRiemannOperator.coefficientL` maps `W^{k+2,p}` into `W^{k+1,r}` keeping the
chart data, for every finite `r`. With `r = p + q`, the coefficient is a `W^{k+1,r}` coefficient
with `2 < r` and `q ≤ r`, and the realization is the top-order realization
`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL` at the exponent `r`, whose zeroth-order
term is compact. The elliptic estimate of `D₀`,
`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`, has the compact
error `‖ξ‖_{L^q}` (Rellich), so it survives the compact perturbation, and the compact error is
replaced by the `L^q` norm, which is injective (the abstract estimates of
`TauCeti.Analysis.Normed.Operator.Compact.Estimate`).

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbationSuccL`: for a fixed `W^{k+2,p}`
  coefficient `α`, the compact operator `ξ ↦ (α ξ)^{0,1}` from `W^{k+2,q}` sections to `W^{k+1,q}`
  `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevSuccL`: the realization of
  `D₀ + α` as a bounded operator `W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_sobolevCoeffPerturbationSuccL`,
  `TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_sobolevCoeffPerturbedSobolevSuccL_sub`:
  the perturbation is compact, so the realizations of `D₀ + α` and of `D₀` differ by a compact
  operator.
* `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae`,
  `TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae_of_zeroOne`:
  in chart `i`, the realization is `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, and `∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`
  for a coefficient with values in `(0,1)`-forms.
* `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevSuccL_eq_perturbedSobolevSuccL`:
  for `p > 2` and `q ≤ p` the realization is the top-order realization of `α` as a `W^{k+1,p}`
  coefficient.
* `IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevCoeffPerturbedSobolevSuccL_add_norm`:
  the elliptic estimate.

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

local instance instVectorBundleRealCauchyRiemannSobolevCoeffSucc : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (k : ℕ)

namespace IsRealCauchyRiemannOperator

/-- The exponent `p + q` at which a `W^{k+2,p}` coefficient acts on `W^{k+2,q}` is at least `1`. -/
local instance instFactOneLeAddSucc : Fact (1 ≤ ((p + q : ℝ≥0) : ℝ≥0∞)) :=
  ⟨(Fact.out : (1 : ℝ≥0∞) ≤ q).trans (ENNReal.coe_le_coe.2 le_add_self)⟩

omit [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] in
/-- For `p ≥ 2` and `q > 1`, the exponent `p + q` lies above `2`, as multiplication by `W^{k+1,p+q}`
coefficients requires. -/
private theorem two_lt_add (hp : 2 ≤ p) (hq : 1 < q) : 2 < p + q :=
  hp.trans_lt (lt_add_of_pos_right p (zero_lt_one.trans hq))

/-- **The zeroth-order term of class `W^{k+2,p}`.** For `p ≥ 2`, every finite `q > 1` and a
`W^{k+2,p}` section `α` of the real hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`, the bounded
operator sending a `W^{k+2,q}` section `ξ` of `V` to the `(0,1)`-part of the one-form `α ξ`, a
`W^{k+1,q}` `(0,1)`-form. In chart `i` it is the complex antilinear part of `αᵢ uᵢ`
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbationSuccL_ae`). It is
`TauCeti.IsRealCauchyRiemannOperator.perturbationSuccL` for `α` as a `W^{k+1,r}` coefficient,
`r = p + q`. -/
def sobolevCoeffPerturbationSuccL (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    SobolevSection A volume q (k + 1 + 1) →L[ℝ] zeroOneSobolevSections A volume q (k + 1) :=
  perturbationSuccL A k (two_lt_add hp hq) hq le_add_self
    (coefficientL A volume hp (p + q) (k + 1) α)

/-- **Compact perturbation** (McDuff–Salamon, Lemma C.2.2, below the top order). For a fixed
`W^{k+2,p}` coefficient with `p ≥ 2`, the zeroth-order term is compact from `W^{k+2,q}` to
`W^{k+1,q}`, for every finite `q > 1`. -/
theorem isCompactOperator_sobolevCoeffPerturbationSuccL (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    IsCompactOperator (sobolevCoeffPerturbationSuccL A k hp hq α) :=
  -- `sobolevCoeffPerturbationSuccL` is `perturbationSuccL` of `coefficientL α` by definition.
  isCompactOperator_perturbationSuccL A k _ _ _ _

/-- In chart `i`, the zeroth-order term is the complex antilinear part of the pointwise
application of the chart data `αᵢ` of the coefficient to the chart data `uᵢ` of the section. -/
theorem chartValueL_sobolevCoeffPerturbationSuccL_ae (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((sobolevCoeffPerturbationSuccL A k hp hq α ξ :
          SobolevSection A.tangentHom volume q (k + 1)) :
            A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1 + 1) i α y
            (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y)) := by
  filter_upwards [chartValueL_perturbationSuccL_ae A k (two_lt_add hp hq) hq le_add_self
      (coefficientL A volume hp (p + q) (k + 1) α) ξ i,
    chartValueL_coefficientL_ae A volume hp (p + q) (k + 1) α i] with y h₁ h₂
  -- `sobolevCoeffPerturbationSuccL` is `perturbationSuccL` of `coefficientL α` by definition.
  rw [← h₂]
  exact h₁

include hD in
/-- **The realization of `D₀ + α` below the top order.** For a smooth real Cauchy–Riemann operator
`D₀`, `p ≥ 2`, every finite `q > 1` and a `W^{k+2,p}` zeroth-order term `α`, the bounded operator
`W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)` sending `ξ` to `D₀ ξ + (α ξ)^{0,1}`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevSuccL_apply`). For a coefficient
with values in `(0,1)`-forms it is `D₀ + α` in every chart
(`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae_of_zeroOne`).
It is `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL` for `α` as a `W^{k+1,r}`
coefficient, `r = p + q`. -/
def sobolevCoeffPerturbedSobolevSuccL (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    SobolevSection A volume q (k + 1 + 1) →L[ℝ] zeroOneSobolevSections A volume q (k + 1) :=
  hD.perturbedSobolevSuccL A hDs k (two_lt_add hp hq) hq le_add_self
    (coefficientL A volume hp (p + q) (k + 1) α)

/-- The realization of `D₀ + α` is the realization of `D₀` plus the zeroth-order term. -/
@[simp]
theorem sobolevCoeffPerturbedSobolevSuccL_apply (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) :
    hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α ξ =
      hD.sobolevSuccL A hDs volume q (k + 1) ξ + sobolevCoeffPerturbationSuccL A k hp hq α ξ := by
  rw [sobolevCoeffPerturbedSobolevSuccL, perturbedSobolevSuccL_apply,
    sobolevCoeffPerturbationSuccL]

/-- The realizations of `D₀ + α` and of `D₀` below the top order differ by a compact operator, the
zeroth-order term of class `W^{k+2,p}`. -/
theorem isCompactOperator_sobolevCoeffPerturbedSobolevSuccL_sub (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    IsCompactOperator fun ξ ↦
      hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α ξ -
        hD.sobolevSuccL A hDs volume q (k + 1) ξ :=
  -- `sobolevCoeffPerturbedSobolevSuccL` is `perturbedSobolevSuccL` of `coefficientL α` by
  -- definition.
  isCompactOperator_perturbedSobolevSuccL_sub A hD hDs k _ _ _ _

/-- **The chart formula.** In chart `i`, the realization of `D₀ + α` below the top order sends a
section with chart data `uᵢ` to `∂bar uᵢ + Zᵢ uᵢ + (αᵢ uᵢ)^{0,1}`, where `∂bar uᵢ` is the complex
antilinear part of any weak derivative `Du` of `uᵢ` and `Zᵢ` is the zeroth-order term of `D₀` in
chart `i`. -/
theorem chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn volume (A.image i)
      (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ) Du) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α ξ :
          SobolevSection A.tangentHom volume q (k + 1)) :
            A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) +
        complexAntilinearPartL
          ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            volume p (k + 1 + 1) i α y
              (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y)) := by
  filter_upwards [hD.chartValueL_perturbedSobolevSuccL_ae A hDs k (two_lt_add hp hq) hq
      le_add_self (coefficientL A volume hp (p + q) (k + 1) α) ξ hDu,
    chartValueL_coefficientL_ae A volume hp (p + q) (k + 1) α i] with y h₁ h₂
  -- `sobolevCoeffPerturbedSobolevSuccL` is `perturbedSobolevSuccL` of `coefficientL α` by
  -- definition.
  rw [← h₂]
  exact h₁

/-- **The chart formula for a `(0,1)`-valued coefficient.** If the chart data of `α` take values in
complex antilinear maps almost everywhere, that is `α` is a zeroth-order term in
`Λ^{0,1} ⊗ End_ℝ V`, then in chart `i` the realization of `D₀ + α` below the top order is
`∂bar uᵢ + Zᵢ uᵢ + αᵢ uᵢ`. -/
theorem chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae_of_zeroOne (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1))
    (ξ : SobolevSection A volume q (k + 1 + 1)) {i : Fin A.n} {Du : ℂ → ℂ →L[ℝ] F}
    (hDu : HasWeakFDerivOn volume (A.image i)
      (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ) Du)
    (hα : ∀ᵐ y ∂volume.restrict (A.image i), ∀ (u : F) (v : ℂ),
      (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1 + 1) i α y u (Complex.I • v) =
        -(Complex.I •
          (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
            volume p (k + 1 + 1) i α y u v)) :
    A.tangentHom.sectionChartData.chartValueL volume q (k + 1) i
        ((hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α ξ :
          SobolevSection A.tangentHom volume q (k + 1)) :
            A.tangentHom.sectionChartData.SobolevData volume q (k + 1))
      =ᵐ[volume.restrict (A.image i)] fun y ↦ complexAntilinearPartL (Du y) +
        A.chartZeroOrder D i y (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) +
        (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.chartValueL
          volume p (k + 1 + 1) i α y
            (A.sectionChartData.chartValueL volume q (k + 1 + 1) i ξ y) := by
  filter_upwards [hD.chartValueL_sobolevCoeffPerturbedSobolevSuccL_ae A hDs k hp hq α ξ hDu, hα]
    with y h hy
  rw [h, complexAntilinearPartL_eq_self_iff.2 (hy _)]

/-- **Agreement with the top-order realization.** For `p > 2` and `q ≤ p`, the zeroth-order term
of a `W^{k+2,p}` coefficient `α` is that of `α` as a `W^{k+1,p}` coefficient. -/
theorem sobolevCoeffPerturbationSuccL_eq_perturbationSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    sobolevCoeffPerturbationSuccL A k hp.le hq α = perturbationSuccL A k hp hq hqp
      ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        volume p (k + 1) α) := by
  refine ContinuousLinearMap.ext fun ξ ↦ Subtype.ext <|
    SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (FiniteBundleAtlas.ae_image_tangentHom_iff A volume i).2 ?_
  filter_upwards [chartValueL_sobolevCoeffPerturbationSuccL_ae A k hp.le hq α ξ i,
    chartValueL_perturbationSuccL_ae A k hp hq hqp
      ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
        volume p (k + 1) α) ξ i] with y h₁ h₂
  rw [h₁, h₂, SectionChartData.chartValueL_coe_lowerOrderL
    (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData volume p (k + 1) α i]

/-- **Agreement with the top-order realization.** For `p > 2` and `q ≤ p`, the realization of
`D₀ + α` for a `W^{k+2,p}` coefficient `α` is the realization for `α` as a `W^{k+1,p}`
coefficient. -/
theorem sobolevCoeffPerturbedSobolevSuccL_eq_perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp.le hq α =
      hD.perturbedSobolevSuccL A hDs k hp hq hqp
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
          volume p (k + 1) α) :=
  ContinuousLinearMap.ext fun ξ ↦ by
    rw [sobolevCoeffPerturbedSobolevSuccL_apply, perturbedSobolevSuccL_apply,
      sobolevCoeffPerturbationSuccL_eq_perturbationSuccL A k hp hq hqp]

include hD hDs in
/-- **The elliptic estimate below the top order.** Let `D = D₀ + α` be a real Cauchy–Riemann
operator with a `W^{k+2,p}` zeroth-order term, `p ≥ 2`, on a complex vector bundle `V` over a
compact boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < q < ∞`. There is
a constant `C` such that every `ξ ∈ W^{k+2,q}(Σ, V)` satisfies
`‖ξ‖_{W^{k+2,q}} ≤ C (‖D ξ‖_{W^{k+1,q}} + ‖ξ‖_{L^q})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevSuccL` and `‖ξ‖_{L^q}` is the norm
of `ξ` in `W^{0,q}(Σ, V)` (`TauCeti.SectionChartData.lowerToZeroL`). -/
theorem exists_norm_le_norm_sobolevCoeffPerturbedSobolevSuccL_add_norm (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1 + 1)) :
    ∃ C : ℝ, ∀ ξ : SobolevSection A volume q (k + 1 + 1),
      ‖ξ‖ ≤ C * (‖hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α ξ‖ +
        ‖A.sectionChartData.lowerToZeroL volume q (k + 1 + 1) ξ‖) := by
  obtain ⟨C, hC⟩ := exists_norm_le_norm_sobolevSuccL_add_norm A hD hDs
    (by exact_mod_cast hq) ENNReal.coe_ne_top (k + 1)
  set L := A.sectionChartData.lowerToZeroL volume q (k + 1 + 1)
  -- `L` forgets the highest derivative first, which is compact by Rellich's theorem.
  have hL : IsCompactOperator L := by
    convert (SobolevSection.isCompactOperator_lowerOrderL A volume q (k + 1)).clm_comp
      (A.sectionChartData.lowerToZeroL volume q (k + 1)) using 1
    funext ξ
    exact (SectionChartData.lowerToZeroL_lowerOrderL (w := ξ)).symm
  -- The estimate for `D₀` with its error term written as the compact operator `|C| • L`.
  have hbound (ξ : SobolevSection A volume q (k + 1 + 1)) :
      ‖ξ‖ ≤ |C| * ‖hD.sobolevSuccL A hDs volume q (k + 1) ξ‖ + ‖(|C| • L) ξ‖ := by
    simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_abs, ← mul_add]
    exact (hC ξ).trans (by gcongr; exact le_abs_self C)
  have hST := isCompactOperator_sobolevCoeffPerturbedSobolevSuccL_sub A hD hDs k hp hq α
  -- The abstract estimates are applied with their type arguments named, so that instance search on
  -- the Sobolev section spaces runs first (see `CauchyRiemann/SemiFredholm.lean`).
  have h₁ := ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := SobolevSection A volume q 0) (C := |C|) (T := hD.sobolevSuccL A hDs volume q (k + 1))
    (S := hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α) (K := |C| • L)
  obtain ⟨C', K', hK', hC'⟩ :=
    h₁ (hL.smul |C|) hbound (by simpa only [FunLike.coe_sub, Pi.sub_def] using hST)
  -- `L` is injective: it keeps the chart data, which determine the section.
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.2 fun ξ ξ' h ↦
    A.sectionChartData.chartValuesL_injective volume q (k + 1 + 1) (by
      rw [← SectionChartData.chartValuesL_lowerToZeroL,
        ← SectionChartData.chartValuesL_lowerToZeroL (w := ξ')]
      exact congrArg _ h)
  have h₂ := ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := zeroOneSobolevSections A volume q (k + 1) × SobolevSection A volume q 0)
    (Z := SobolevSection A volume q 0) (C := C')
    (hD.sobolevCoeffPerturbedSobolevSuccL A hDs k hp hq α) (K := K') (j := L)
  obtain ⟨C'', -, hC''⟩ := h₂ hK' hC' (by rw [hker]; exact disjoint_bot_right)
  exact ⟨C'', hC''⟩

/-- **Check.** The zeroth-order term of a `W^{2,3}` coefficient (`ℓ = 3`) is compact from `W^{2,4}`
to `W^{1,4}`, an exponent above `3` excluded at the top order, and from `W^{2,3/2}` to `W^{1,3/2}`,
below `2`; that of a `W^{3,3}` coefficient (`ℓ = 4`) is compact from `W^{2,4}` to `W^{1,4}` after
forgetting the highest derivative of the coefficient. -/
example [Fact (1 ≤ ((3 : ℝ≥0) : ℝ≥0∞))] [Fact (1 ≤ ((4 : ℝ≥0) : ℝ≥0∞))]
    [Fact (1 ≤ ((3 / 2 : ℝ≥0) : ℝ≥0∞))]
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume
      ((3 : ℝ≥0) : ℝ≥0∞) 2)
    (β : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume
      ((3 : ℝ≥0) : ℝ≥0∞) 3) :
    IsCompactOperator (sobolevCoeffPerturbationSuccL (q := 4) A 0 (by norm_num) (by norm_num) α) ∧
      IsCompactOperator
        (sobolevCoeffPerturbationSuccL (q := 3 / 2) A 0 (by norm_num) (by norm_num) α) ∧
      IsCompactOperator (sobolevCoeffPerturbationSuccL (q := 4) A 0 (by norm_num) (by norm_num)
        ((A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).sectionChartData.lowerOrderL
          volume _ 2 β)) :=
  ⟨isCompactOperator_sobolevCoeffPerturbationSuccL A 0 _ _ α,
    isCompactOperator_sobolevCoeffPerturbationSuccL A 0 _ _ α,
    isCompactOperator_sobolevCoeffPerturbationSuccL A 0 _ _ _⟩

end IsRealCauchyRiemannOperator

end TauCeti
