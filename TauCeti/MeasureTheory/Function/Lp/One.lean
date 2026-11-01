/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The constant one and indicator classes in `L∞`

This file defines the constant-one element of `L∞` on an arbitrary measure space, and the class
in `L∞` of the indicator function of a measurable set. Unlike `MeasureTheory.Lp.const` and
`MeasureTheory.indicatorConstLp`, the constructions need no finiteness hypothesis on the measure,
because the essential supremum of a bounded function is always finite.

The norm of a class in `L∞` is the least almost-everywhere bound of its representative
(`MeasureTheory.Lp.ae_norm_le_norm_top`, `MeasureTheory.Lp.norm_le_of_ae_bound_top`, with no
finiteness assumption on the measure). Hence the constant one is an order unit of real `L∞`:
every class `φ` satisfies `φ ≤ ‖φ‖ • 1` (`TauCeti.le_norm_smul_linftyOne`).

Indicator classes are additive on disjoint sets and vanish exactly on null sets, so a linear
functional on `L∞` restricts to a finitely additive set function on measurable sets which
vanishes on null sets.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Lp

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]

/-- The representative of a class in `L∞` is bounded by its norm almost everywhere. -/
theorem ae_norm_le_norm_top (φ : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖φ x‖ ≤ ‖φ‖ := by
  rw [norm_def, toReal_eLpNorm]
  exact ae_le_lpNorm_exponent_top (Lp.memLp φ)

/-- A class in `L∞` whose representative is bounded by `C` almost everywhere has norm at most
`C`. Unlike `MeasureTheory.Lp.norm_le_of_ae_bound`, no finiteness of the measure is needed. -/
theorem norm_le_of_ae_bound_top {φ : Lp E ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) : ‖φ‖ ≤ C := by
  rw [norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable φ)]
  exact ENNReal.toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound h)

end MeasureTheory.Lp

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The constant-one element of `L∞(μ)`. -/
noncomputable def linftyOne : Lp ℝ ∞ μ :=
  (memLp_top_const (1 : ℝ)).toLp fun _ => 1

/-- The representative of `linftyOne` is almost everywhere the constant function one. -/
theorem coeFn_linftyOne :
    (linftyOne (Ω := Ω) (μ := μ) : Ω → ℝ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))

/-- The constant one is an order unit of real `L∞`: every class is at most its norm times one. -/
theorem le_norm_smul_linftyOne (φ : Lp ℝ ∞ μ) : φ ≤ ‖φ‖ • linftyOne := by
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.ae_norm_le_norm_top φ, Lp.coeFn_smul ‖φ‖ linftyOne,
    coeFn_linftyOne] with x hx hs h1
  rw [hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact (Real.le_norm_self _).trans hx

variable (μ) in
/-- The class in `L∞(μ)` of the indicator function of a measurable set `s`. -/
noncomputable def linftyIndicator {s : Set Ω} (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  ((memLp_top_const (1 : ℝ)).indicator hs.nullMeasurableSet).toLp (s.indicator fun _ => 1)

/-- The representative of `linftyIndicator μ hs` is almost everywhere the indicator of `s`. -/
theorem coeFn_linftyIndicator {s : Set Ω} (hs : MeasurableSet s) :
    (linftyIndicator μ hs : Ω → ℝ) =ᵐ[μ] s.indicator fun _ => 1 :=
  MemLp.coeFn_toLp _

/-- The indicator class of a set vanishes exactly when the set is null. -/
@[simp]
theorem linftyIndicator_eq_zero_iff {s : Set Ω} (hs : MeasurableSet s) :
    linftyIndicator μ hs = 0 ↔ μ s = 0 := by
  have h := indicator_ae_eq_zero (μ := μ) (s := s) (f := fun _ : Ω => (1 : ℝ))
  rw [Function.support_const one_ne_zero, inter_univ] at h
  rw [Lp.eq_zero_iff_ae_eq_zero, ← h]
  exact ⟨(coeFn_linftyIndicator hs).symm.trans, (coeFn_linftyIndicator hs).trans⟩

/-- The indicator class of a null set is zero. -/
theorem linftyIndicator_of_null {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s = 0) :
    linftyIndicator μ hs = 0 :=
  (linftyIndicator_eq_zero_iff hs).2 hμs

@[simp]
theorem linftyIndicator_empty : linftyIndicator μ MeasurableSet.empty = 0 :=
  linftyIndicator_of_null _ measure_empty

@[simp]
theorem linftyIndicator_univ : linftyIndicator μ MeasurableSet.univ = linftyOne := by
  rw [linftyIndicator, linftyOne, MemLp.toLp_eq_toLp_iff]
  simp

/-- Indicator classes are additive on disjoint sets. -/
theorem linftyIndicator_union {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    linftyIndicator μ (hs.union ht) = linftyIndicator μ hs + linftyIndicator μ ht := by
  rw [linftyIndicator, linftyIndicator, linftyIndicator, ← MemLp.toLp_add,
    MemLp.toLp_eq_toLp_iff]
  exact .of_forall fun x => congrFun (indicator_union_of_disjoint hst _) x

/-- An indicator class is nonnegative. -/
theorem linftyIndicator_nonneg {s : Set Ω} (hs : MeasurableSet s) : 0 ≤ linftyIndicator μ hs := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_linftyIndicator hs] with x hx
  rw [hx]
  exact indicator_nonneg (fun _ _ => zero_le_one) x

end TauCeti
