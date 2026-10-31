/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.Indicator
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# Simple functions in `L∞`

Every simple function is essentially bounded, so, unlike in `Lᵖ` for finite `p`, taking
almost-everywhere classes is a linear map `MeasureTheory.SimpleFunc.toLpTop` from all simple
functions to `L∞(μ)`, with no finiteness condition on the measure of their supports. For
real-valued functions its range is dense: an element of `L∞` has a measurable representative with
values in the interval `[-‖f‖, ‖f‖]`, which is a uniform limit of simple functions.

Together with the indicator classes `MeasureTheory.indicatorConstLpTop`, these are the tools for
describing functionals on `L∞` by their values on indicator classes, as in the correspondence
between positive functionals on `L∞` and finitely additive set functions.

## Main definitions

* `MeasureTheory.SimpleFunc.toLpTop`: the class in `L∞` of a simple function, as a linear map.

## Main results

* `MeasureTheory.SimpleFunc.toLpTop_piecewise_const`: the class of a simple function equal to `c`
  on `s` and to `0` off `s` is an indicator class.
* `MeasureTheory.SimpleFunc.denseRange_toLpTop`: simple functions are dense in real `L∞`.
-/

public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

namespace SimpleFunc

variable (μ) (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The class in `L∞` of a simple function, as a linear map. Every simple function is essentially
bounded, whatever the measure of its support. -/
def toLpTop : (SimpleFunc α E) →ₗ[𝕜] Lp E ∞ μ where
  toFun g := (g.memLp_top μ).toLp g
  map_add' f g := MemLp.toLp_add (f.memLp_top μ) (g.memLp_top μ)
  map_smul' c f := MemLp.toLp_const_smul c (f.memLp_top μ)

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
  have hae : (fun x => max (-C) (min C (h x))) =ᵐ[μ] f :=
    (Lp.ae_eq_max_min_norm_top hfh).symm.trans hfh.symm
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
