/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# Simple functions and indicator classes in `L∞`

Every simple function is essentially bounded, so, unlike in `Lᵖ` for finite `p`, taking
almost-everywhere classes is a linear map `MeasureTheory.SimpleFunc.toLpTop` from all simple
functions to `L∞(μ)`, with no finiteness condition on the measure of their supports. For
real-valued functions its range is dense: an element of `L∞` has a measurable representative with
values in the interval `[-‖f‖, ‖f‖]`, which is a uniform limit of simple functions.

Likewise `MeasureTheory.indicatorConstLpTop μ hs c` is the class in `L∞` of the indicator function
of a measurable set `s` with value `c`, for sets of arbitrary measure; Mathlib's
`MeasureTheory.indicatorConstLp` requires `μ s ≠ ∞`.

These are the tools for describing functionals on `L∞` by their values on indicator classes, as in
the correspondence between positive functionals on `L∞` and finitely additive set functions.

## Main definitions

* `MeasureTheory.SimpleFunc.toLpTop`: the class in `L∞` of a simple function, as a linear map.
* `MeasureTheory.indicatorConstLpTop`: the class in `L∞` of `s.indicator fun _ ↦ c`.

## Main results

* `MeasureTheory.Lp.ae_norm_le_norm_top`, `MeasureTheory.Lp.norm_le_of_ae_bound_top`: an element
  of `L∞` is almost everywhere bounded by its norm, which is its least almost-everywhere bound.
* `MeasureTheory.Lp.le_norm_smul_linftyOne`: `f ≤ ‖f‖ • 1` in real `L∞`.
* `MeasureTheory.SimpleFunc.denseRange_toLpTop`: simple functions are dense in real `L∞`.
-/

public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

namespace Lp

/-- An element of `L∞` is almost everywhere bounded by its norm. -/
theorem ae_norm_le_norm_top (f : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := f)] with x hx
  rw [norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← toReal_enorm]
  exact ENNReal.toReal_mono
    (by simpa [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using eLpNorm_ne_top f) hx

/-- The norm of an element of `L∞` is at most any almost-everywhere bound. Unlike
`MeasureTheory.Lp.norm_le_of_ae_bound`, the measure need not be finite. -/
theorem norm_le_of_ae_bound_top {f : Lp E ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound h)

/-- In real `L∞`, every element lies below its norm times the constant one. -/
theorem le_norm_smul_linftyOne (f : Lp ℝ ∞ μ) : f ≤ ‖f‖ • TauCeti.linftyOne := by
  rw [← coeFn_le]
  filter_upwards [ae_norm_le_norm_top f, coeFn_smul ‖f‖ (TauCeti.linftyOne (μ := μ)),
    TauCeti.coeFn_linftyOne] with x hx hs h1
  rw [hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact (le_abs_self _).trans hx

end Lp

section Indicator

variable (μ) {s : Set α}

/-- The class in `L∞` of the indicator function of a measurable set `s` with value `c`. Unlike
`MeasureTheory.indicatorConstLp`, no finiteness of `μ s` is needed. -/
def indicatorConstLpTop (hs : MeasurableSet s) (c : E) : Lp E ∞ μ :=
  ((memLp_top_const c).indicator hs.nullMeasurableSet).toLp (s.indicator fun _ => c)

/-- The indicator class of `s` with value `c` is represented by `s.indicator fun _ ↦ c`. -/
theorem indicatorConstLpTop_coeFn (hs : MeasurableSet s) (c : E) :
    indicatorConstLpTop μ hs c =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp _

/-- The indicator class of the whole space is the constant one. -/
@[simp]
theorem indicatorConstLpTop_univ : indicatorConstLpTop μ MeasurableSet.univ (1 : ℝ) =
    TauCeti.linftyOne := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ MeasurableSet.univ (1 : ℝ), TauCeti.coeFn_linftyOne]
    with x h h1
  rw [h, h1, indicator_univ]

/-- The indicator class of a null set vanishes. -/
theorem indicatorConstLpTop_eq_zero (hs : MeasurableSet s) (hμs : μ s = 0) (c : E) :
    indicatorConstLpTop μ hs c = 0 := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ hs c, Lp.coeFn_zero E ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 hμs] with x h h0 hx
  rw [h, h0, indicator_of_notMem hx, Pi.zero_apply]

/-- Indicator classes add on disjoint sets. -/
theorem indicatorConstLpTop_union {t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (c : E) :
    indicatorConstLpTop μ (hs.union ht) c =
      indicatorConstLpTop μ hs c + indicatorConstLpTop μ ht c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ (hs.union ht) c, indicatorConstLpTop_coeFn μ hs c,
    indicatorConstLpTop_coeFn μ ht c, Lp.coeFn_add (indicatorConstLpTop μ hs c)
      (indicatorConstLpTop μ ht c)] with x h hs' ht' hadd
  rw [hadd, Pi.add_apply, h, hs', ht', indicator_union_of_disjoint hst]

/-- A version of `Set.indicator_const_smul` for `MeasureTheory.indicatorConstLpTop`. -/
theorem indicatorConstLpTop_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (hs : MeasurableSet s) (a : 𝕜) (c : E) :
    indicatorConstLpTop μ hs (a • c) = a • indicatorConstLpTop μ hs c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ hs (a • c), indicatorConstLpTop_coeFn μ hs c,
    Lp.coeFn_smul a (indicatorConstLpTop μ hs c)] with x h h' hsmul
  rw [hsmul, Pi.smul_apply, h, h', indicator_const_smul_apply]

/-- A real indicator class is nonnegative when its value is. -/
theorem indicatorConstLpTop_nonneg (hs : MeasurableSet s) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ indicatorConstLpTop μ hs c := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [indicatorConstLpTop_coeFn μ hs c] with x h
  rw [h]
  exact indicator_nonneg (fun _ _ => hc) x

end Indicator

namespace SimpleFunc

variable (μ) (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The class in `L∞` of a simple function, as a linear map. Every simple function is essentially
bounded, whatever the measure of its support. -/
def toLpTop : (SimpleFunc α E) →ₗ[𝕜] Lp E ∞ μ where
  toFun g := (g.memLp_top μ).toLp g
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp ((f + g).memLp_top μ), MemLp.coeFn_toLp (f.memLp_top μ),
      MemLp.coeFn_toLp (g.memLp_top μ), Lp.coeFn_add ((f.memLp_top μ).toLp f)
        ((g.memLp_top μ).toLp g)] with x h hf hg hadd
    rw [hadd, Pi.add_apply, h, hf, hg, coe_add, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp ((c • f).memLp_top μ), MemLp.coeFn_toLp (f.memLp_top μ),
      Lp.coeFn_smul c ((f.memLp_top μ).toLp f)] with x h hf hs
    rw [RingHom.id_apply, hs, Pi.smul_apply, h, hf, coe_smul, Pi.smul_apply]

variable {μ 𝕜}

/-- The class of a simple function `g` is represented by `g`. -/
theorem coeFn_toLpTop (g : SimpleFunc α E) : toLpTop μ 𝕜 g =ᵐ[μ] g :=
  MemLp.coeFn_toLp (g.memLp_top μ)

/-- The class of a simple function equal to `c` on `s` and to `0` off `s` is an indicator
class. -/
theorem toLpTop_piecewise_const {s : Set α} (hs : MeasurableSet s) (c : E) :
    toLpTop μ 𝕜 (piecewise s hs (const α c) (const α 0)) = indicatorConstLpTop μ hs c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_toLpTop (μ := μ) (𝕜 := 𝕜) (piecewise s hs (const α c) (const α 0)),
    indicatorConstLpTop_coeFn μ hs c] with x h hi
  rw [h, hi]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Simple functions are dense in real `L∞`: every element is within any `ε > 0` of the class of
a simple function. -/
theorem denseRange_toLpTop : DenseRange (toLpTop μ ℝ : (SimpleFunc α ℝ) → Lp ℝ ∞ μ) := by
  refine Metric.denseRange_iff.2 fun f ε hε => ?_
  set C := ‖f‖
  -- A strongly measurable representative of `f`, clamped to `[-C, C]`, is a representative of
  -- `f` with values in `[-C, C]` everywhere.
  obtain ⟨h, hh, hfh⟩ := Lp.aestronglyMeasurable f
  have hm : Measurable fun x => max (-C) (min C (h x)) :=
    measurable_const.max (measurable_const.min hh.measurable)
  have hmem (x : α) : max (-C) (min C (h x)) ∈ Icc (-C) C :=
    ⟨le_max_left _ _, max_le (neg_le_self (norm_nonneg f)) (min_le_left _ _)⟩
  have hae : (fun x => max (-C) (min C (h x))) =ᵐ[μ] f := by
    filter_upwards [hfh, Lp.ae_norm_le_norm_top f] with x hx hle
    rw [← hx, min_eq_right (le_of_abs_le hle), max_eq_right (neg_le_of_abs_le hle)]
  -- The simple approximants with values in `[-C, C]` converge to it uniformly.
  have hu := tendstoUniformly_approxOn hm (s := Icc (-C) C) (y₀ := -C)
    ⟨le_rfl, neg_le_self (norm_nonneg f)⟩ (totallyBounded_Icc _ _)
    (fun x => subset_closure (hmem x))
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 hu (ε / 2) (half_pos hε)).exists
  refine ⟨approxOn _ hm (Icc (-C) C) (-C) ⟨le_rfl, neg_le_self (norm_nonneg f)⟩ n, ?_⟩
  rw [dist_eq_norm]
  refine (Lp.norm_le_of_ae_bound_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  filter_upwards [Lp.coeFn_sub f (toLpTop μ ℝ (approxOn _ hm (Icc (-C) C) (-C)
      ⟨le_rfl, neg_le_self (norm_nonneg f)⟩ n)), hae, coeFn_toLpTop (μ := μ) (𝕜 := ℝ)
      (approxOn _ hm (Icc (-C) C) (-C) ⟨le_rfl, neg_le_self (norm_nonneg f)⟩ n)]
    with x hsub hx happ
  rw [hsub, Pi.sub_apply, happ, ← hx, ← dist_eq_norm]
  exact (hn x).le

end SimpleFunc

end MeasureTheory
