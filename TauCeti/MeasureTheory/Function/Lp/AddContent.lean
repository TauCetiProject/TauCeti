/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.SimpleFunc.AddContent
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# Functionals on `L∞` and contents on measurable sets

Let `μ` be a measure on a measurable space `α`. A positive linear functional `M` on real
`L∞(α, μ)` gives a finitely additive set function on measurable sets by evaluating indicator
classes, `ν s = M [1_s]`. It is nonnegative, and it vanishes on `μ`-null sets because their
indicator classes are zero.

Conversely, every nonnegative real content `ν` on the measurable sets which vanishes on `μ`-null
sets arises in this way from exactly one positive linear functional on `L∞(α, μ)`. A simple
function `g` is integrated by the finite sum `∑ c, c * ν {x | g x = c}`. Since `ν` annihilates
null sets this sum only depends on the almost-everywhere class of `g`, and it is bounded by
`ν univ` times the essential supremum of `g`. Classes of simple functions are dense in `L∞`, so
the integral extends uniquely by continuity, and the extension is positive because it has norm at
most its value `ν univ` at the constant one. Neither side involves countable additivity; no
finiteness or σ-finiteness of `μ` is assumed.

Values of a content outside the measurable sets play no role in this correspondence. The content
`LinearMap.toMeasurableAddContent` of a functional is taken to be zero there, and the inverse laws
are stated on measurable sets.

The finite sums are `MeasureTheory.SimpleFunc.integralAddContent`, uniform approximation by
simple functions is `MeasureTheory.SimpleFunc.tendstoUniformly_approxOn`, and the extension is
`LinearMap.extendOfNorm`. The discrete counterpart, for bounded functions on a discrete space and
contents on all subsets, is `PositiveLinearMap.addContentEquiv`.

## Main definitions

* `MeasureTheory.SimpleFunc.toLpTop μ`: the class in `L∞(μ)` of a simple function, as a linear
  map; its range is dense (`MeasureTheory.SimpleFunc.denseRange_toLpTop`).
* `LinearMap.toMeasurableAddContent`: the content `s ↦ M [1_s]` of a functional `M` on `L∞`.
* `PositiveLinearMap.ofMeasurableAddContent`: the positive functional on `L∞` given by
  integration against a nonnegative content which vanishes on null sets.

## Main results

* `PositiveLinearMap.ext_linftyIndicator`: a positive functional on `L∞` is determined by its
  values at indicator classes of measurable sets.
* `PositiveLinearMap.ofMeasurableAddContent_linftyIndicator` and
  `PositiveLinearMap.ofMeasurableAddContent_toMeasurableAddContent`: the two constructions are
  inverse to each other.
* `PositiveLinearMap.existsUnique_apply_linftyIndicator_eq`: every nonnegative content vanishing
  on null sets is the content of exactly one positive functional on `L∞`.
* `PositiveLinearMap.forall_apply_leftTranslation_eq_iff`: for a left-invariant measure on a
  group, a positive functional on `L∞` is invariant under left translation exactly when its
  content is invariant under translation of measurable sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, in particular the
  correspondence between invariant means on `L∞` and invariant finitely additive measures in
  Theorem G.3.1.
-/

public section

noncomputable section

open Set Filter TauCeti
open scoped ENNReal Pointwise

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

namespace SimpleFunc

/-- The class in `L∞(μ)` of a simple function, as a linear map. -/
def toLpTop : SimpleFunc α ℝ →ₗ[ℝ] Lp ℝ ∞ μ where
  toFun g := (g.memLp_top μ).toLp g
  map_add' f g := MemLp.toLp_add (f.memLp_top μ) (g.memLp_top μ)
  map_smul' c g := MemLp.toLp_const_smul c (g.memLp_top μ)

variable {μ}

/-- The representative of the class of a simple function is almost everywhere the function. -/
theorem coeFn_toLpTop (g : SimpleFunc α ℝ) : toLpTop μ g =ᵐ[μ] g :=
  MemLp.coeFn_toLp (g.memLp_top μ)

/-- The class of a simple function equal to `c` on `s` and to `0` off `s` is `c` times the
indicator class of `s`. -/
theorem toLpTop_piecewise_const {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    toLpTop μ (piecewise s hs (const α c) (const α 0)) = c • linftyIndicator μ hs := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toLpTop (μ := μ) (piecewise s hs (const α c) (const α 0)),
    Lp.coeFn_smul c (linftyIndicator μ hs), coeFn_linftyIndicator (μ := μ) hs] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

variable (μ) in
/-- Classes of simple functions are dense in real `L∞`: every essentially bounded function is,
after modification on a null set, a uniform limit of simple functions. -/
theorem denseRange_toLpTop : DenseRange (toLpTop μ) := by
  refine Metric.denseRange_iff.2 fun φ ε hε => ?_
  set c := ‖φ‖
  have hc : 0 ≤ c := norm_nonneg φ
  -- a measurable representative of `φ` with values in `[-c, c]`
  have hφ := Lp.aestronglyMeasurable φ
  set f : α → ℝ := fun x => max (-c) (min c (hφ.mk φ x))
  have hfm : Measurable f :=
    measurable_const.max (measurable_const.min hφ.stronglyMeasurable_mk.measurable)
  have hf (x : α) : f x ∈ Icc (-c) c :=
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfφ : f =ᵐ[μ] φ := by
    filter_upwards [hφ.ae_eq_mk, Lp.ae_norm_le_norm_top φ] with x hx hb
    have hb' : |φ x| ≤ c := by rwa [← Real.norm_eq_abs]
    simp only [f, ← hx, min_eq_right (abs_le.1 hb').2, max_eq_right (abs_le.1 hb').1]
  have h₀ : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith, hc⟩
  have hu := tendstoUniformly_approxOn hfm h₀ isCompact_Icc.totallyBounded
    fun x => subset_closure (hf x)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 hu (ε / 2) (half_pos hε)).exists
  refine ⟨approxOn f hfm (Icc (-c) c) 0 h₀ n, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rw [dist_eq_norm]
  refine Lp.norm_le_of_ae_bound_top (half_pos hε).le ?_
  filter_upwards [Lp.coeFn_sub φ (toLpTop μ (approxOn f hfm (Icc (-c) c) 0 h₀ n)),
    coeFn_toLpTop (μ := μ) (approxOn f hfm (Icc (-c) c) 0 h₀ n), hfφ] with x h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, ← h₃, ← dist_eq_norm]
  exact (hn x).le

end SimpleFunc

end MeasureTheory

namespace LinearMap

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

open Classical in
/-- The real content `s ↦ M [1_s]` on the measurable sets of a linear functional `M` on
`L∞(μ)`, where `[1_s]` is the indicator class of `s`. It is taken to be zero on nonmeasurable
sets. -/
def toMeasurableAddContent (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) :
    AddContent ℝ {s : Set α | MeasurableSet s} :=
  isSetRing_measurableSet.addContent_of_union
    (fun s => if hs : MeasurableSet s then M (linftyIndicator μ hs) else 0)
    (by simp) (by
      intro s t (hs : MeasurableSet s) (ht : MeasurableSet t) hst
      simp only [hs, ht, hs.union ht, dite_true]
      rw [linftyIndicator_union hs ht hst, map_add])

open Classical in
private theorem coe_toMeasurableAddContent (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) :
    ⇑M.toMeasurableAddContent =
      fun s => if hs : MeasurableSet s then M (linftyIndicator μ hs) else 0 :=
  (rfl)

theorem toMeasurableAddContent_apply (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α} (hs : MeasurableSet s) :
    M.toMeasurableAddContent s = M (linftyIndicator μ hs) := by
  simp [coe_toMeasurableAddContent, hs]

theorem toMeasurableAddContent_of_not_measurableSet (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α}
    (hs : ¬MeasurableSet s) : M.toMeasurableAddContent s = 0 := by
  simp [coe_toMeasurableAddContent, hs]

@[simp]
theorem toMeasurableAddContent_univ (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) :
    M.toMeasurableAddContent univ = M linftyOne := by
  rw [toMeasurableAddContent_apply M MeasurableSet.univ, linftyIndicator_univ]

/-- The content of a functional on `L∞(μ)` vanishes on `μ`-null sets. -/
theorem toMeasurableAddContent_of_null (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) {s : Set α} (hμs : μ s = 0) :
    M.toMeasurableAddContent s = 0 := by
  by_cases hs : MeasurableSet s
  · rw [toMeasurableAddContent_apply M hs, linftyIndicator_of_null hs hμs, map_zero]
  · exact toMeasurableAddContent_of_not_measurableSet M hs

end LinearMap

namespace PositiveLinearMap

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The content of a positive functional on `L∞` is nonnegative. -/
theorem toMeasurableAddContent_nonneg (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (s : Set α) :
    0 ≤ M.toLinearMap.toMeasurableAddContent s := by
  by_cases hs : MeasurableSet s
  · rw [LinearMap.toMeasurableAddContent_apply _ hs]
    exact M.map_nonneg (linftyIndicator_nonneg hs)
  · rw [LinearMap.toMeasurableAddContent_of_not_measurableSet _ hs]

/-- A positive functional on `L∞(μ)` is determined by its values at the indicator classes of
measurable sets. -/
theorem ext_linftyIndicator {M M' : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s), M (linftyIndicator μ hs) = M' (linftyIndicator μ hs)) :
    M = M' := by
  have hsimple (g : SimpleFunc α ℝ) : M (SimpleFunc.toLpTop μ g) = M' (SimpleFunc.toLpTop μ g) := by
    induction g using SimpleFunc.induction with
    | const c hs => rw [SimpleFunc.toLpTop_piecewise_const, map_smul, map_smul, h]
    | add _ hf hg => rw [map_add, map_add, map_add, hf, hg]
  ext φ
  exact congrFun ((SimpleFunc.denseRange_toLpTop μ).equalizer
    (continuous_of_forall_le_norm_smul M le_norm_smul_linftyOne)
    (continuous_of_forall_le_norm_smul M' le_norm_smul_linftyOne) (funext hsimple)) φ

section ofMeasurableAddContent

/-! ### Integration against a nonnegative content

A nonnegative real content `ν` on the measurable sets of `α` is integrated first on simple
functions, by `MeasureTheory.SimpleFunc.integralAddContent`, and then on all of `L∞(μ)` by uniform
approximation. -/

variable (ν : AddContent ℝ {s : Set α | MeasurableSet s})

/-- The integral of simple functions against `ν`. -/
private abbrev integralSimple : SimpleFunc α ℝ →ₗ[ℝ] ℝ :=
  SimpleFunc.integralAddContent ν fun _ hs => hs

variable (μ) in
/-- The integral of `L∞(μ)` classes against `ν`, extending `integralSimple ν` by continuity. It
is meaningful when `ν` is nonnegative and vanishes on `μ`-null sets. -/
private def integral : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (integralSimple ν).extendOfNorm (SimpleFunc.toLpTop μ)

section Bounds

variable {ν} (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
  (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)

include hν hνμ in
private theorem norm_integralSimple_le (g : SimpleFunc α ℝ) :
    ‖integralSimple ν g‖ ≤ ν univ * ‖SimpleFunc.toLpTop μ g‖ := by
  -- Clamp `g` to `[-c, c]`, where `c` is its essential supremum; this changes `g` only on a
  -- null set, hence does not change its integral.
  set c := ‖SimpleFunc.toLpTop μ g‖
  set g' := g.map fun y => max (-c) (min c y)
  have hg' : g' =ᵐ[μ] g := by
    filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) g,
      Lp.ae_norm_le_norm_top (SimpleFunc.toLpTop μ g)] with x hx hb
    have hb' : |g x| ≤ c := by rwa [hx, Real.norm_eq_abs] at hb
    simp only [g', SimpleFunc.map_apply, min_eq_right (abs_le.1 hb').2,
      max_eq_right (abs_le.1 hb').1]
  have hle (x : α) : |g' x| ≤ c := by
    simp only [g', SimpleFunc.map_apply]
    exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith [norm_nonneg (SimpleFunc.toLpTop μ g)])
      (min_le_left _ _)⟩
  rw [← SimpleFunc.integralAddContent_congr hνμ hg', Real.norm_eq_abs, abs_le, mul_comm]
  refine ⟨?_, SimpleFunc.integralAddContent_le hν fun x => (le_abs_self _).trans (hle x)⟩
  have := SimpleFunc.integralAddContent_le (hC := fun _ hs => hs) hν (g := -g') fun x =>
    (neg_le_abs _).trans (hle x)
  rw [map_neg] at this
  linarith

include hν hνμ

private theorem integral_toLpTop (g : SimpleFunc α ℝ) :
    integral μ ν (SimpleFunc.toLpTop μ g) = integralSimple ν g :=
  LinearMap.extendOfNorm_eq (SimpleFunc.denseRange_toLpTop μ) ⟨_, norm_integralSimple_le hν hνμ⟩ g

private theorem norm_integral_apply_le (φ : Lp ℝ ∞ μ) : ‖integral μ ν φ‖ ≤ ν univ * ‖φ‖ :=
  LinearMap.norm_extendOfNorm_apply_le (SimpleFunc.denseRange_toLpTop μ) _
    (norm_integralSimple_le hν hνμ) φ

private theorem integral_linftyIndicator {s : Set α} (hs : MeasurableSet s) :
    integral μ ν (linftyIndicator μ hs) = ν s := by
  have := integral_toLpTop hν hνμ (SimpleFunc.piecewise s hs
    (SimpleFunc.const α 1) (SimpleFunc.const α 0))
  rwa [SimpleFunc.toLpTop_piecewise_const, SimpleFunc.integralAddContent_piecewise_const,
    one_smul, one_mul] at this

/-- The integral against a nonnegative content is positive. -/
private theorem integral_nonneg {φ : Lp ℝ ∞ μ} (hφ : 0 ≤ φ) : 0 ≤ integral μ ν φ := by
  -- For `0 ≤ φ`, the class `‖φ‖ • 1 - φ` has norm at most `‖φ‖`, so applying the bound
  -- `|integral ψ| ≤ ν univ * ‖ψ‖` to it gives `‖φ‖ * ν univ - integral φ ≤ ‖φ‖ * ν univ`.
  have hbound := norm_integral_apply_le hν hνμ (‖φ‖ • linftyOne - φ)
  have hnorm : ‖‖φ‖ • (linftyOne : Lp ℝ ∞ μ) - φ‖ ≤ ‖φ‖ := by
    refine Lp.norm_le_of_ae_bound_top (norm_nonneg φ) ?_
    filter_upwards [Lp.coeFn_sub (‖φ‖ • linftyOne) φ, Lp.coeFn_smul ‖φ‖ (linftyOne : Lp ℝ ∞ μ),
      coeFn_linftyOne, Lp.ae_norm_le_norm_top φ, (Lp.coeFn_nonneg φ).2 hφ]
      with x h₁ h₂ h₃ hb h₀
    rw [Pi.zero_apply] at h₀
    rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, smul_eq_mul, mul_one, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [Real.le_norm_self (φ x)], by linarith⟩
  have h₁ : integral μ ν linftyOne = ν univ := by
    simpa using integral_linftyIndicator hν hνμ MeasurableSet.univ
  rw [map_sub, map_smul, h₁, smul_eq_mul, Real.norm_eq_abs] at hbound
  have := (le_abs_self _).trans hbound
  nlinarith [mul_le_mul_of_nonneg_left hnorm (hν univ MeasurableSet.univ)]

end Bounds

variable (μ) in
/-- The positive linear functional on `L∞(μ)` given by integration against a nonnegative content
`ν` on the measurable sets which vanishes on `μ`-null sets. It is the unique positive functional
taking the value `ν s` at the indicator class of every measurable set `s`. -/
def ofMeasurableAddContent (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
    (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
  mk₀ (integral μ ν).toLinearMap fun _ hφ => integral_nonneg hν hνμ hφ

variable {ν} (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
  (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)

/-- The functional associated to a content takes the value `ν s` at the indicator class of a
measurable set `s`. -/
@[simp]
theorem ofMeasurableAddContent_linftyIndicator {s : Set α} (hs : MeasurableSet s) :
    ofMeasurableAddContent μ ν hν hνμ (linftyIndicator μ hs) = ν s :=
  integral_linftyIndicator hν hνμ hs

/-- The functional associated to a content takes its total mass at the constant one. -/
@[simp]
theorem ofMeasurableAddContent_linftyOne :
    ofMeasurableAddContent μ ν hν hνμ linftyOne = ν univ := by
  simpa using ofMeasurableAddContent_linftyIndicator hν hνμ MeasurableSet.univ

/-- The content of the functional associated to a content `ν` agrees with `ν` on measurable
sets. -/
theorem toMeasurableAddContent_ofMeasurableAddContent {s : Set α} (hs : MeasurableSet s) :
    (ofMeasurableAddContent μ ν hν hνμ).toLinearMap.toMeasurableAddContent s = ν s := by
  rw [LinearMap.toMeasurableAddContent_apply _ hs]
  exact ofMeasurableAddContent_linftyIndicator hν hνμ hs

end ofMeasurableAddContent

/-- A positive functional on `L∞` is the integral against its content. -/
@[simp]
theorem ofMeasurableAddContent_toMeasurableAddContent (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    ofMeasurableAddContent μ M.toLinearMap.toMeasurableAddContent
      (fun s _ => M.toMeasurableAddContent_nonneg s)
      (fun _ _ hμs => M.toLinearMap.toMeasurableAddContent_of_null hμs) = M :=
  ext_linftyIndicator fun _ hs => by
    rw [ofMeasurableAddContent_linftyIndicator, LinearMap.toMeasurableAddContent_apply _ hs]
    rfl

/-- **Functionals on `L∞` and contents.** A nonnegative real content `ν` on the measurable sets
which vanishes on `μ`-null sets is given by evaluating exactly one positive functional on
`L∞(μ)` at indicator classes. -/
theorem existsUnique_apply_linftyIndicator_eq (ν : AddContent ℝ {s : Set α | MeasurableSet s})
    (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) :
    ∃! M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, ∀ s (hs : MeasurableSet s), M (linftyIndicator μ hs) = ν s :=
  ⟨ofMeasurableAddContent μ ν hν hνμ, fun _ hs => ofMeasurableAddContent_linftyIndicator hν hνμ hs,
    fun _ hM => ext_linftyIndicator fun s hs => by
      rw [hM s hs, ofMeasurableAddContent_linftyIndicator]⟩

section LeftTranslation

/-! ### Invariance under left translation

For a left-invariant measure on a group, left translation of `L∞` classes corresponds to
translation of measurable sets, so the correspondence matches invariant functionals with
invariant contents. -/

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- A positive functional on `L∞(μ)` of a left-invariant measure is invariant under left
translation exactly when its content is invariant under translation of measurable sets. -/
theorem forall_apply_leftTranslation_eq_iff (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    (∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∀ (g : G) s, MeasurableSet s → M.toLinearMap.toMeasurableAddContent (g • s) =
        M.toLinearMap.toMeasurableAddContent s := by
  refine ⟨fun h g s hs => ?_, fun h g => ?_⟩
  · rw [LinearMap.toMeasurableAddContent_apply _ (hs.const_smul g),
      LinearMap.toMeasurableAddContent_apply _ hs, ← Lp.leftTranslation_linftyIndicator]
    exact h g _
  · -- `M ∘ L_g` is again a positive functional, with the same values at indicator classes.
    let L : Lp ℝ ∞ μ →ₚ[ℝ] Lp ℝ ∞ μ :=
      { toLinearMap := (Lp.leftTranslation μ ∞ ℝ g).toLinearEquiv.toLinearMap
        monotone' := fun _ _ => Lp.leftTranslation_mono g }
    have hL : M.comp L = M := ext_linftyIndicator fun s hs => by
      have := h g s hs
      rw [LinearMap.toMeasurableAddContent_apply _ (hs.const_smul g),
        LinearMap.toMeasurableAddContent_apply _ hs, ← Lp.leftTranslation_linftyIndicator] at this
      exact this
    exact fun φ => congrArg (· φ) hL

/-- Integration against a content which is invariant under translation of measurable sets is
invariant under left translation. -/
theorem ofMeasurableAddContent_leftTranslation {ν : AddContent ℝ {s : Set G | MeasurableSet s}}
    (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)
    (hinv : ∀ (g : G) s, MeasurableSet s → ν (g • s) = ν s) (g : G) (φ : Lp ℝ ∞ μ) :
    ofMeasurableAddContent μ ν hν hνμ (Lp.leftTranslation μ ∞ ℝ g φ) =
      ofMeasurableAddContent μ ν hν hνμ φ := by
  refine (forall_apply_leftTranslation_eq_iff _).2 (fun g s hs => ?_) g φ
  rw [toMeasurableAddContent_ofMeasurableAddContent hν hνμ (hs.const_smul g),
    toMeasurableAddContent_ofMeasurableAddContent hν hνμ hs, hinv g s hs]

end LeftTranslation

end PositiveLinearMap
