/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Integral.AddContent
public import TauCeti.MeasureTheory.Measure.AddContent

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Normed.Order.PositiveLinearMap
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Positive functionals on `L∞` and finitely additive set functions

Let `μ` be a measure on `α`. A positive linear functional `M` on real `L∞(α, μ)` gives the set
function `s ↦ M [1_s]` on the measurable sets, where `[1_s]` is the class of the indicator function
(`LinearMap.linftyContent`). It is nonnegative, finitely additive, and vanishes on `μ`-null sets.
Conversely, every nonnegative finitely additive set function `ν` on the measurable sets which
vanishes on `μ`-null sets is `s ↦ M [1_s]` for exactly one positive linear functional `M`
(`MeasureTheory.AddContent.linftyIntegral`): integrate simple functions against `ν`, and extend by
uniform continuity. Neither side involves countable additivity, and `μ` need not be finite or
σ-finite.

The extension uses that simple functions are dense in real `L∞`
(`MeasureTheory.SimpleFunc.denseRange_toLinfty`): rounding an essentially bounded representative
down to a multiple of `δ` gives a simple function within `δ` of it. The integral of a simple
function `f` against `ν` only depends on the class of `f` in `L∞`, because `ν` vanishes on
`μ`-null sets, and it is bounded by `ν univ` times the essential supremum of `|f|`.

The values of a set function on nonmeasurable sets play no role. Accordingly the inverse laws are
stated on measurable sets (`LinearMap.linftyContent_linftyIntegral`) and for functionals
(`PositiveLinearMap.linftyIntegral_linftyContent`). A positive functional on `L∞` is determined by
its values on indicator classes (`PositiveLinearMap.ext_linftyIndicator`).

## Main definitions

* `MeasureTheory.SimpleFunc.toLinfty μ`: the class in `L∞(μ)` of a real simple function, as a linear
  map.
* `LinearMap.linftyContent M`: the finitely additive set function `s ↦ M [1_s]` on the measurable
  sets.
* `MeasureTheory.AddContent.linftyIntegral ν hν hνμ`: the positive functional on `L∞(μ)` obtained
  by integrating against a nonnegative finitely additive set function `ν` vanishing on `μ`-null
  sets.

## Main results

* `MeasureTheory.SimpleFunc.denseRange_toLinfty`: simple functions are dense in real `L∞`.
* `PositiveLinearMap.ext_linftyIndicator`: positive functionals on `L∞` that agree on indicator
  classes are equal.
* `MeasureTheory.AddContent.linftyIntegral_linftyIndicator`: the integral of `[1_s]` against `ν` is
  `ν s`.
* `PositiveLinearMap.linftyIntegral_linftyContent`: a positive functional on `L∞` is the integral
  against its set function.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, for means on `L∞`
  of a locally compact group.
-/

public section

noncomputable section

open Set TauCeti
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

namespace SimpleFunc

variable (μ) in
/-- The class in `L∞(μ)` of a real simple function, as a linear map. -/
def toLinfty : SimpleFunc α ℝ →ₗ[ℝ] Lp ℝ ∞ μ where
  toFun f := (f.memLp_top μ).toLp f
  map_add' f g := MemLp.toLp_add (f.memLp_top μ) (g.memLp_top μ)
  map_smul' c f := MemLp.toLp_const_smul c (f.memLp_top μ)

/-- The class of a simple function is almost everywhere equal to it. -/
theorem coeFn_toLinfty (f : SimpleFunc α ℝ) : toLinfty μ f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.memLp_top μ)

/-- The class of the indicator function of a measurable set, as a simple function, is its
indicator class. -/
theorem toLinfty_piecewise_one_zero (hs : MeasurableSet s) :
    toLinfty μ (piecewise s hs (const α 1) (const α 0)) = linftyIndicator hs := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toLinfty (μ := μ) (piecewise s hs (const α 1) (const α 0)),
    coeFn_linftyIndicator (μ := μ) hs] with x hx hx'
  rw [hx, hx']
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Real simple functions are dense in `L∞`. -/
theorem denseRange_toLinfty : DenseRange (toLinfty μ) := by
  refine Metric.denseRange_iff.2 fun φ ε hε => ?_
  set C := ‖φ‖
  set δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  -- `r y` clamps `y` to `[-C, C]` and rounds it down to a multiple of `δ`.
  let r : ℝ → ℝ := fun y => δ * ⌊max (-C) (min C y) / δ⌋
  have hrm : Measurable r := by
    have : Measurable fun y : ℝ => max (-C) (min C y) / δ := by fun_prop
    exact (measurable_from_top.comp this.floor).const_mul δ
  have hrf : (range r).Finite := by
    refine ((finite_Icc ⌊-C / δ⌋ ⌊C / δ⌋).image fun n : ℤ => δ * n).subset
      (range_subset_iff.2 fun y => mem_image_of_mem _ ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩)
    · exact div_le_div_of_nonneg_right (le_max_left _ _) hδ.le
    · exact div_le_div_of_nonneg_right
        (max_le (by linarith [norm_nonneg φ]) (min_le_left _ _)) hδ.le
  let g : SimpleFunc ℝ ℝ := ⟨r, fun y => hrm (measurableSet_singleton y), hrf⟩
  refine ⟨g.comp φ (Lp.stronglyMeasurable φ).measurable, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rw [dist_eq_norm]
  refine Lp.norm_le_of_ae_bound_top hδ.le ?_
  filter_upwards [ae_le_lpNorm_exponent_top (Lp.memLp φ), Lp.coeFn_sub φ (toLinfty μ _),
    coeFn_toLinfty (μ := μ) (g.comp φ (Lp.stronglyMeasurable φ).measurable)] with x hx hsub hg
  have hφx : |φ x| ≤ C := hx
  rw [hsub, Pi.sub_apply, hg, coe_comp, Function.comp_apply, Real.norm_eq_abs]
  have hclamp : max (-C) (min C (φ x)) = φ x := by
    rw [min_eq_right (abs_le.1 hφx).2, max_eq_right (abs_le.1 hφx).1]
  have h : φ x - δ * ⌊φ x / δ⌋ = δ * Int.fract (φ x / δ) := by
    rw [Int.fract, mul_sub, mul_div_cancel₀ _ hδ.ne']
  simp only [g, r, SimpleFunc.coe_mk]
  rw [hclamp, h, abs_of_nonneg (mul_nonneg hδ.le (Int.fract_nonneg _))]
  exact mul_le_of_le_one_right hδ.le (Int.fract_lt_one _).le

end SimpleFunc

/-- Positive linear functionals on `L∞` which agree on the indicator classes of measurable sets
are equal. -/
theorem _root_.PositiveLinearMap.ext_linftyIndicator {M N : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s), M (linftyIndicator hs) = N (linftyIndicator hs)) :
    M = N := by
  have hc (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) : Continuous M :=
    PositiveLinearMap.continuous_of_forall_le_norm_smul M le_norm_smul_linftyOne
  -- Both functionals agree on the dense set of classes of simple functions.
  have hsimple (f : SimpleFunc α ℝ) :
      M (SimpleFunc.toLinfty μ f) = N (SimpleFunc.toLinfty μ f) := by
    induction f using SimpleFunc.induction with
    | @const c s hs =>
      have : SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0) =
          c • SimpleFunc.piecewise s hs (SimpleFunc.const α 1) (SimpleFunc.const α 0) := by
        ext x
        by_cases hx : x ∈ s <;> simp [hx]
      rw [this, map_smul, SimpleFunc.toLinfty_piecewise_one_zero, map_smul, map_smul, h]
    | add _ hf hg => rw [map_add, map_add, map_add, hf, hg]
  ext φ
  exact congrFun ((SimpleFunc.denseRange_toLinfty.equalizer (hc M) (hc N))
    (funext hsimple)) φ

end MeasureTheory

namespace LinearMap

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

open scoped Classical in
/-- The finitely additive set function `s ↦ M [1_s]` on the measurable sets, for a linear functional
`M` on `L∞(μ)`. It vanishes on nonmeasurable sets, which play no role. -/
def linftyContent (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) : AddContent ℝ {s : Set α | MeasurableSet s} :=
  isSetRing_setOf_measurableSet.addContent_of_union
    (fun s => if hs : MeasurableSet s then M (linftyIndicator hs) else 0)
    (by simp) fun {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) hst => by
      rw [dite_eq_left (hs.union ht), dite_eq_left hs, dite_eq_left ht,
        linftyIndicator_union hs ht hst, map_add]

variable (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ)

/-- At a measurable set `s`, the set function of `M` is `M [1_s]`. -/
theorem linftyContent_apply (hs : MeasurableSet s) :
    M.linftyContent s = M (linftyIndicator hs) :=
  dite_eq_left hs

@[simp]
theorem linftyContent_univ : M.linftyContent univ = M linftyOne := by
  rw [linftyContent_apply M MeasurableSet.univ, linftyIndicator_univ]

/-- The set function of a functional on `L∞(μ)` vanishes on `μ`-null sets. -/
theorem linftyContent_of_measure_eq_zero (hs : MeasurableSet s) (hμs : μ s = 0) :
    M.linftyContent s = 0 := by
  rw [linftyContent_apply M hs, linftyIndicator_of_measure_eq_zero hs hμs, map_zero]

end LinearMap

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- The set function of a positive functional on `L∞` is nonnegative. -/
theorem _root_.PositiveLinearMap.linftyContent_nonneg (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ)
    (hs : MeasurableSet s) : 0 ≤ M.toLinearMap.linftyContent s := by
  rw [LinearMap.linftyContent_apply _ hs]
  exact M.map_nonneg (linftyIndicator_nonneg hs)

namespace AddContent

/-! ### Integration against a finitely additive set function vanishing on null sets -/

variable {ν : AddContent ℝ {s : Set α | MeasurableSet s}} (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
  (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)

include hν hνμ in
/-- A simple function bounded by `c` almost everywhere has integral at most `c * ν univ`. -/
private theorem integralSimple_le_of_ae_le {f : SimpleFunc α ℝ} {c : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≤ c) : ν.integralSimple (fun _ => id) f ≤ c * ν univ := by
  -- Truncating `f` at `c` changes it only on a `μ`-null set.
  let f' := f.map fun y => min y c
  have hf' : f =ᵐ[μ] f' := by
    filter_upwards [hf] with x hx
    simp [f', hx]
  rw [integralSimple_congr_ae hνμ hf', ← integralSimple_const]
  exact integralSimple_mono hν fun x => by simp [f']

include hν hνμ in
private theorem norm_integralSimple_le (f : SimpleFunc α ℝ) :
    ‖ν.integralSimple (fun _ => id) f‖ ≤ ν univ * ‖SimpleFunc.toLinfty μ f‖ := by
  have h : ∀ᵐ x ∂μ, |f x| ≤ ‖SimpleFunc.toLinfty μ f‖ := by
    filter_upwards [ae_le_lpNorm_exponent_top (Lp.memLp (SimpleFunc.toLinfty μ f)),
      SimpleFunc.coeFn_toLinfty (μ := μ) f] with x hx hfx
    rw [← hfx]
    exact hx
  rw [Real.norm_eq_abs, abs_le, mul_comm]
  refine ⟨?_, integralSimple_le_of_ae_le hν hνμ (h.mono fun x hx => (le_abs_self _).trans hx)⟩
  have := integralSimple_le_of_ae_le hν hνμ (f := -f)
    (h.mono fun x hx => (neg_le_abs _).trans hx)
  rw [map_neg] at this
  linarith

variable (ν) in
/-- The integral against `ν` on `L∞(μ)`, extending the integral of simple functions by
continuity. It is meaningful when `ν` is nonnegative and vanishes on `μ`-null sets. -/
private def linftyIntegralCLM : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (ν.integralSimple fun _ => id).extendOfNorm (SimpleFunc.toLinfty μ)

include hν hνμ

private theorem linftyIntegralCLM_toLinfty (f : SimpleFunc α ℝ) :
    linftyIntegralCLM (μ := μ) ν (SimpleFunc.toLinfty μ f) = ν.integralSimple (fun _ => id) f :=
  LinearMap.extendOfNorm_eq SimpleFunc.denseRange_toLinfty ⟨_, norm_integralSimple_le hν hνμ⟩ f

private theorem linftyIntegralCLM_linftyIndicator (hs : MeasurableSet s) :
    linftyIntegralCLM (μ := μ) ν (linftyIndicator hs) = ν s := by
  rw [← SimpleFunc.toLinfty_piecewise_one_zero, linftyIntegralCLM_toLinfty hν hνμ,
    integralSimple_piecewise_const, one_mul]

private theorem linftyIntegralCLM_nonneg {φ : Lp ℝ ∞ μ} (hφ : 0 ≤ φ) :
    0 ≤ linftyIntegralCLM (μ := μ) ν φ := by
  -- For `0 ≤ φ`, the class `‖φ‖ • 1 - φ` has norm at most `‖φ‖`, so the bound
  -- `|∫ ψ| ≤ ν univ * ‖ψ‖` at `ψ = ‖φ‖ • 1 - φ` gives `‖φ‖ * ν univ - ∫ φ ≤ ‖φ‖ * ν univ`.
  have hbound : ‖linftyIntegralCLM ν (‖φ‖ • linftyOne - φ)‖ ≤ ν univ * ‖‖φ‖ • linftyOne - φ‖ :=
    LinearMap.norm_extendOfNorm_apply_le SimpleFunc.denseRange_toLinfty _
      (norm_integralSimple_le hν hνμ) _
  have hnorm : ‖‖φ‖ • linftyOne - φ‖ ≤ ‖φ‖ := by
    refine Lp.norm_le_of_ae_bound_top (norm_nonneg φ) ?_
    filter_upwards [(Lp.coeFn_nonneg φ).2 hφ, ae_le_lpNorm_exponent_top (Lp.memLp φ),
      Lp.coeFn_sub (‖φ‖ • linftyOne) φ, Lp.coeFn_smul ‖φ‖ (linftyOne (μ := μ)),
      coeFn_linftyOne (μ := μ)] with x h0 hx hsub hsmul h1
    have h0' : 0 ≤ φ x := h0
    have hx' : |φ x| ≤ ‖φ‖ := hx
    rw [abs_of_nonneg h0'] at hx'
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, h1, smul_eq_mul, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have h1 : linftyIntegralCLM (μ := μ) ν linftyOne = ν univ := by
    simpa using linftyIntegralCLM_linftyIndicator hν hνμ MeasurableSet.univ
  rw [map_sub, map_smul, h1, smul_eq_mul, Real.norm_eq_abs] at hbound
  have := (le_abs_self _).trans hbound
  nlinarith [mul_le_mul_of_nonneg_left hnorm (hν univ MeasurableSet.univ)]

omit hν hνμ in
/-- The positive linear functional on `L∞(μ)` obtained by integrating against a nonnegative finitely
additive set function `ν` on the measurable sets which vanishes on `μ`-null sets. -/
def linftyIntegral (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
    (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (linftyIntegralCLM ν).toLinearMap fun _ hφ =>
    linftyIntegralCLM_nonneg hν hνμ hφ

/-- The integral of the indicator class of a measurable set `s` against `ν` is `ν s`. -/
@[simp]
theorem linftyIntegral_linftyIndicator (hs : MeasurableSet s) :
    linftyIntegral hν hνμ (linftyIndicator hs) = ν s :=
  -- `linftyIntegral` evaluates as `linftyIntegralCLM` by definition; Mathlib has no evaluation
  -- lemma for `PositiveLinearMap.mk₀`.
  linftyIntegralCLM_linftyIndicator hν hνμ hs

/-- The integral of the constant class one against `ν` is the total mass of `ν`. -/
@[simp]
theorem linftyIntegral_linftyOne : linftyIntegral hν hνμ linftyOne = ν univ := by
  simpa using linftyIntegral_linftyIndicator hν hνμ MeasurableSet.univ

/-- The set function of the integral against `ν` is `ν` on measurable sets. -/
theorem _root_.LinearMap.linftyContent_linftyIntegral (hs : MeasurableSet s) :
    (linftyIntegral hν hνμ).toLinearMap.linftyContent s = ν s := by
  rw [LinearMap.linftyContent_apply _ hs, PositiveLinearMap.coe_toLinearMap]
  exact linftyIntegral_linftyIndicator hν hνμ hs

end AddContent

/-- A positive linear functional on `L∞(μ)` is the integral against its set function. -/
@[simp]
theorem _root_.PositiveLinearMap.linftyIntegral_linftyContent (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    AddContent.linftyIntegral (fun _ => M.linftyContent_nonneg)
      (fun _ hs => M.toLinearMap.linftyContent_of_measure_eq_zero hs) = M :=
  PositiveLinearMap.ext_linftyIndicator fun s hs => by
    rw [AddContent.linftyIntegral_linftyIndicator, LinearMap.linftyContent_apply _ hs]
    exact congrFun M.coe_toLinearMap _

end MeasureTheory
