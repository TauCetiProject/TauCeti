/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Integral.AddContent
public import TauCeti.MeasureTheory.SetAlgebra

/-!
# Functionals on `L∞` and finitely additive set functions on measurable sets

Let `μ` be a measure on a measurable space `α`. Evaluating a linear functional `M` on `L∞(α, μ)`
at the classes `[1_s]` of indicator functions of measurable sets gives a finitely additive real
set function `s ↦ M [1_s]` on the measurable sets (`LinearMap.toAddContentLpTop`). It vanishes on
`μ`-null sets, since their indicators vanish in `L∞`, and it is nonnegative when `M` is positive.

Conversely, every nonnegative real content `ν` on the measurable sets that vanishes on `μ`-null
sets arises in this way from exactly one positive linear functional on `L∞(α, μ)`
(`PositiveLinearMap.ofAddContentLpTop`). A real simple function `f` is integrated by the finite
sum `∑ c, c * ν {x | f x = c}` (`MeasureTheory.AddContent.integralSimple`). Null annihilation
makes this sum depend only on the class of `f` in `L∞`, and bounds it by `ν univ` times the
essential supremum of `|f|`. Simple functions are uniformly dense among essentially bounded
functions (`MeasureTheory.SimpleFunc.denseRange_toLpTop`), so the integral extends uniquely by
continuity, and the extension is positive because its norm is at most its value `ν univ` at the
constant one. The values of a content on nonmeasurable sets
play no role: the inverse laws hold on measurable sets.

For a left-invariant measure on a group, left translation of a class in `L∞` translates the
indicators, and a positive functional is invariant under left translation exactly when its
content is invariant under translation of measurable sets
(`PositiveLinearMap.forall_apply_leftTranslation_eq_iff`). Thus left-invariant means on Haar
`L∞` are the same as left-invariant finitely additive probabilities on the Borel sets vanishing on
Haar-null sets.

The construction follows the discrete case in
`TauCeti/Topology/ContinuousMap/Bounded/AddContent.lean`, and shares its finite sums
`MeasureTheory.AddContent.integralSimple`; the extension is `LinearMap.extendOfNorm`. The classes
`TauCeti.linftyIndicator μ s hs` of indicators and `MeasureTheory.SimpleFunc.toLpTop μ 𝕜` of
simple functions in `L∞` come from `TauCeti/MeasureTheory/Function/Lp/Indicator.lean` and
`TauCeti/MeasureTheory/Function/SimpleFunc/Dense.lean`.

## Main definitions

* `LinearMap.toAddContentLpTop`: the content `s ↦ M [1_s]` of a linear functional on `L∞`.
* `PositiveLinearMap.ofAddContentLpTop`: integration against a nonnegative content vanishing on
  null sets, as a positive linear functional on `L∞`.

## Main results

* `PositiveLinearMap.ext_linftyIndicator`: a positive functional on `L∞` is determined by its
  values at indicators.
* `PositiveLinearMap.ofAddContentLpTop_linftyIndicator` and
  `PositiveLinearMap.ofAddContentLpTop_toAddContentLpTop`: the two constructions are inverse.
* `PositiveLinearMap.forall_apply_leftTranslation_eq_iff`: invariance of a functional under left
  translation is invariance of its content.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, Theorem G.3.1, for
  the correspondence between means on `L∞` and finitely additive probabilities.
* N. Dunford, J. T. Schwartz, *Linear Operators, Part I*, §IV.8, Theorem 16, for the dual of
  `L∞` as the space of bounded finitely additive set functions vanishing on null sets.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ENNReal Pointwise

namespace LinearMap

open MeasureTheory TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous linear map out of real `L∞` is determined by its values at the indicators of
measurable sets. -/
theorem ext_linftyIndicator {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] {f g : Lp ℝ ∞ μ →ₗ[ℝ] E} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ s (hs : MeasurableSet s), f (linftyIndicator μ s hs) = g (linftyIndicator μ s hs)) :
    f = g := by
  have hsimple : f ∘ₗ SimpleFunc.toLpTop μ ℝ = g ∘ₗ SimpleFunc.toLpTop μ ℝ := by
    ext φ
    induction φ using SimpleFunc.induction with
    | const c hs => simp [h]
    | add _ hφ hψ => simp_all
  exact LinearMap.coe_injective <|
    SimpleFunc.denseRange_toLpTop.equalizer hf hg (congrArg DFunLike.coe hsimple)

open Classical in
/-- The real content `s ↦ m [1_s]` of a linear functional `m` on `L∞(μ)`, on the measurable sets.
Its value at a nonmeasurable set is zero. -/
def toAddContentLpTop (m : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) : AddContent ℝ {s : Set α | MeasurableSet s} :=
  isSetRing_measurableSet.addContent_of_union
    (fun s => if hs : MeasurableSet s then m (linftyIndicator μ s hs) else 0)
    (by simp) fun {s t} hs ht hst => by
      rw [mem_ofPred_eq] at hs ht
      simp only [dite_eq_left (hs.union ht), dite_eq_left hs, dite_eq_left ht,
        linftyIndicator_union hs ht hst, map_add]

/-- On a measurable set `s`, the content of `m` is its value at the indicator of `s`. -/
theorem toAddContentLpTop_apply (m : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α} (hs : MeasurableSet s) :
    m.toAddContentLpTop s = m (linftyIndicator μ s hs) := by
  unfold toAddContentLpTop
  exact dite_eq_left hs

/-- The content of a functional on `L∞` is zero at nonmeasurable sets, by convention. -/
theorem toAddContentLpTop_of_not_measurableSet (m : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α}
    (hs : ¬MeasurableSet s) : m.toAddContentLpTop s = 0 := by
  unfold toAddContentLpTop
  exact dite_eq_right hs

/-- The total mass of the content of `m` is its value at the constant one. -/
@[simp]
theorem toAddContentLpTop_univ (m : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) : m.toAddContentLpTop univ = m linftyOne := by
  rw [toAddContentLpTop_apply m MeasurableSet.univ, linftyIndicator_univ]

/-- The content of a functional on `L∞(μ)` vanishes on `μ`-null sets. -/
theorem toAddContentLpTop_of_measure_eq_zero (m : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (h : μ s = 0) : m.toAddContentLpTop s = 0 := by
  rw [toAddContentLpTop_apply m hs, linftyIndicator_of_measure_eq_zero hs h, map_zero]

/-- Composing a functional on `L∞` of a left-invariant measure with left translation by `g`
translates its content by `g`. -/
theorem toAddContentLpTop_comp_leftTranslation {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {ν : Measure G} [ν.IsMulLeftInvariant] (m : Lp ℝ ∞ ν →ₗ[ℝ] ℝ) (g : G)
    {s : Set G} (hs : MeasurableSet s) :
    (m ∘ₗ (Lp.leftTranslation ν ∞ ℝ g).toLinearEquiv.toLinearMap).toAddContentLpTop s =
      m.toAddContentLpTop (g • s) := by
  simp [toAddContentLpTop_apply _ hs, toAddContentLpTop_apply _ (hs.const_smul g),
    Lp.leftTranslation_linftyIndicator]

end LinearMap

namespace PositiveLinearMap

open MeasureTheory TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A positive linear functional on real `L∞` is continuous. -/
theorem continuous_lpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) : Continuous M :=
  continuous_of_forall_le_norm_smul M Lp.le_norm_smul_linftyOne

/-- A positive linear functional on real `L∞` is determined by its values at the indicators of
measurable sets. -/
theorem ext_linftyIndicator {M N : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s), M (linftyIndicator μ s hs) = N (linftyIndicator μ s hs)) :
    M = N := by
  have := LinearMap.ext_linftyIndicator (f := M.toLinearMap) (g := N.toLinearMap)
    M.continuous_lpTop N.continuous_lpTop h
  ext φ
  exact LinearMap.congr_fun this φ

/-- The content of a positive functional is nonnegative. -/
theorem toAddContentLpTop_nonneg (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (s : Set α) :
    0 ≤ M.toLinearMap.toAddContentLpTop s := by
  by_cases hs : MeasurableSet s
  · rw [LinearMap.toAddContentLpTop_apply _ hs]
    exact M.map_nonneg (linftyIndicator_nonneg hs)
  · exact (M.toLinearMap.toAddContentLpTop_of_not_measurableSet hs).ge

section ofAddContent

/-! ### Integration against a nonnegative content

A nonnegative real content `ν` on the measurable sets is integrated first on simple functions,
by `∑ c, c * ν {x | f x = c}` (`AddContent.integralSimple`), and then on all of `L∞` by uniform
approximation. Null annihilation makes the finite sums depend only on the `L∞` class. -/

variable (ν : AddContent ℝ {s : Set α | MeasurableSet s})

variable (μ) in
/-- The integral of essentially bounded functions against `ν`, extending
`AddContent.integralSimple` by continuity. It is meaningful when `ν` is nonnegative and vanishes
on `μ`-null sets. -/
private def integral : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (ν.integralSimple isSetRing_measurableSet fun _ hs => hs).extendOfNorm (SimpleFunc.toLpTop μ ℝ)

variable {ν}

variable (hν₀ : ∀ s, MeasurableSet s → 0 ≤ ν s) (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)
include hν₀ hνμ

private theorem norm_integralSimple_le (g : SimpleFunc α ℝ) :
    ‖ν.integralSimple isSetRing_measurableSet (fun _ hs => hs) g‖ ≤
      ν univ * ‖SimpleFunc.toLpTop μ ℝ g‖ := by
  set C := ‖SimpleFunc.toLpTop μ ℝ g‖ with hC
  -- Truncating `g` at its essential supremum changes it only on a null set.
  set g' := g.map fun y => max (-C) (min y C)
  have hgg' : g =ᵐ[μ] g' := by
    filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) (𝕜 := ℝ) g,
      Lp.ae_norm_le_norm_top (SimpleFunc.toLpTop μ ℝ g)] with x h hx
    rw [h, Real.norm_eq_abs, abs_le, ← hC] at hx
    simp only [g', SimpleFunc.map_apply]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have h x : |g' x| ≤ C := by
    have : 0 ≤ C := norm_nonneg _
    simp only [g', SimpleFunc.map_apply, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  rw [AddContent.integralSimple_congr_ae _ _ hνμ hgg', Real.norm_eq_abs, mul_comm]
  exact AddContent.abs_integralSimple_le _ _ hν₀ h

private theorem integral_toLpTop (g : SimpleFunc α ℝ) :
    integral μ ν (SimpleFunc.toLpTop μ ℝ g) =
      ν.integralSimple isSetRing_measurableSet (fun _ hs => hs) g :=
  LinearMap.extendOfNorm_eq SimpleFunc.denseRange_toLpTop ⟨_, norm_integralSimple_le hν₀ hνμ⟩ g

private theorem norm_integral_apply_le (φ : Lp ℝ ∞ μ) : ‖integral μ ν φ‖ ≤ ν univ * ‖φ‖ :=
  LinearMap.norm_extendOfNorm_apply_le SimpleFunc.denseRange_toLpTop _
    (norm_integralSimple_le hν₀ hνμ) φ

private theorem integral_linftyIndicator {s : Set α} (hs : MeasurableSet s) :
    integral μ ν (linftyIndicator μ s hs) = ν s := by
  have := integral_toLpTop hν₀ hνμ
    (SimpleFunc.piecewise s hs (SimpleFunc.const α 1) (SimpleFunc.const α 0))
  rwa [AddContent.integralSimple_piecewise, one_mul, SimpleFunc.const_zero,
    SimpleFunc.toLpTop_piecewise_const_zero, one_smul] at this

/-- The integral against a nonnegative content vanishing on null sets is positive. -/
private theorem integral_nonneg {φ : Lp ℝ ∞ μ} (hφ : 0 ≤ φ) : 0 ≤ integral μ ν φ := by
  -- For `0 ≤ φ`, the class `‖φ‖ • 1 - φ` has norm at most `‖φ‖`, so applying the bound
  -- `|integral ψ| ≤ ν univ * ‖ψ‖` to it gives `‖φ‖ * ν univ - integral φ ≤ ‖φ‖ * ν univ`.
  have hbound := norm_integral_apply_le hν₀ hνμ (‖φ‖ • linftyOne - φ)
  have hnorm : ‖‖φ‖ • (linftyOne : Lp ℝ ∞ μ) - φ‖ ≤ ‖φ‖ := by
    refine Lp.norm_top_le_of_ae_bound (norm_nonneg φ) ?_
    filter_upwards [Lp.coeFn_sub (‖φ‖ • (linftyOne : Lp ℝ ∞ μ)) φ,
      Lp.coeFn_smul ‖φ‖ (linftyOne : Lp ℝ ∞ μ), coeFn_linftyOne (μ := μ),
      (Lp.coeFn_nonneg φ).2 hφ, Lp.ae_norm_le_norm_top φ] with x hsub hsmul h1 h0 hx
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    rw [Real.norm_eq_abs, abs_le] at hx ⊢
    have := h0
    simp only [Pi.zero_apply] at this
    constructor <;> linarith
  have h₁ : integral μ ν linftyOne = ν univ := by
    simpa using integral_linftyIndicator hν₀ hνμ MeasurableSet.univ
  rw [map_sub, map_smul, h₁, smul_eq_mul, Real.norm_eq_abs] at hbound
  have := (le_abs_self _).trans hbound
  nlinarith [mul_le_mul_of_nonneg_left hnorm (hν₀ univ MeasurableSet.univ)]

variable (ν) in
/-- Integration against a nonnegative real content `ν` on the measurable sets which vanishes on
`μ`-null sets, as a positive linear functional on `L∞(μ)`. It takes the value `ν s` at the class
of the indicator of a measurable set `s`. -/
def ofAddContentLpTop : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
  mk₀ (integral μ ν).toLinearMap fun _ hφ => integral_nonneg hν₀ hνμ hφ

/-- The functional associated to a content takes the value `ν s` at the indicator of `s`. -/
@[simp]
theorem ofAddContentLpTop_linftyIndicator {s : Set α} (hs : MeasurableSet s) :
    ofAddContentLpTop ν hν₀ hνμ (linftyIndicator μ s hs) = ν s :=
  integral_linftyIndicator hν₀ hνμ hs

/-- The functional associated to a content takes its total mass at the constant one. -/
@[simp]
theorem ofAddContentLpTop_linftyOne : ofAddContentLpTop ν hν₀ hνμ linftyOne = ν univ := by
  simpa using ofAddContentLpTop_linftyIndicator hν₀ hνμ MeasurableSet.univ

/-- The content of the functional associated to `ν` is `ν`, on measurable sets. -/
@[simp]
theorem toAddContentLpTop_ofAddContentLpTop_apply {s : Set α} (hs : MeasurableSet s) :
    (ofAddContentLpTop ν hν₀ hνμ).toLinearMap.toAddContentLpTop s = ν s :=
  (LinearMap.toAddContentLpTop_apply _ hs).trans (ofAddContentLpTop_linftyIndicator hν₀ hνμ hs)

end ofAddContent

/-- A positive functional on `L∞(μ)` is the integral against its content. -/
@[simp]
theorem ofAddContentLpTop_toAddContentLpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    ofAddContentLpTop M.toLinearMap.toAddContentLpTop (fun s _ => M.toAddContentLpTop_nonneg s)
      (fun _ hs h => M.toLinearMap.toAddContentLpTop_of_measure_eq_zero hs h) = M :=
  ext_linftyIndicator fun s hs => by
    rw [ofAddContentLpTop_linftyIndicator, LinearMap.toAddContentLpTop_apply _ hs, coe_toLinearMap]

section Group

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {ν : Measure G}
  [ν.IsMulLeftInvariant]

/-- A positive functional on `L∞` of a left-invariant measure is invariant under left translation
exactly when its content is invariant under left translation of measurable sets. -/
theorem forall_apply_leftTranslation_eq_iff (M : Lp ℝ ∞ ν →ₚ[ℝ] ℝ) :
    (∀ (g : G) φ, M (Lp.leftTranslation ν ∞ ℝ g φ) = M φ) ↔
      ∀ (g : G) s, MeasurableSet s →
        M.toLinearMap.toAddContentLpTop (g • s) = M.toLinearMap.toAddContentLpTop s := by
  refine ⟨fun h g s hs => ?_, fun h g => ?_⟩
  · have hM : M.toLinearMap ∘ₗ (Lp.leftTranslation ν ∞ ℝ g).toLinearEquiv.toLinearMap =
        M.toLinearMap := LinearMap.ext fun φ => by simpa using h g φ
    rw [← LinearMap.toAddContentLpTop_comp_leftTranslation _ g hs, hM]
  · -- Both `M ∘ L_g` and `M` are continuous and have the same content.
    have := LinearMap.ext_linftyIndicator
      (f := M.toLinearMap ∘ₗ (Lp.leftTranslation ν ∞ ℝ g).toLinearEquiv.toLinearMap)
      (g := M.toLinearMap)
      (M.continuous_lpTop.comp (Lp.leftTranslation ν ∞ ℝ g).continuous) M.continuous_lpTop
      fun s hs => by
        rw [← LinearMap.toAddContentLpTop_apply _ hs, ← LinearMap.toAddContentLpTop_apply _ hs,
          LinearMap.toAddContentLpTop_comp_leftTranslation _ g hs, h g s hs]
    exact fun φ => LinearMap.congr_fun this φ

end Group

end PositiveLinearMap
