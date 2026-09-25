/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Rigidity of measure-preserving real maps

A finite measure determines the distribution of a real-valued function on it: two measurable
real-valued functions with the same pushforward measure, one of which lies below the other almost
everywhere, agree almost everywhere. In the endomap case this says that a measure-preserving real
endomap lying below the identity almost everywhere is the identity almost everywhere.

## Main results

* `MeasureTheory.Measure.ae_eq_of_measurePreserving_of_le` is the general form, for two
  measurable real-valued functions on a finite measure space;
* `MeasureTheory.Measure.ae_eq_id_of_measurePreserving_of_le` is the endomap case. It turns a
  domination hypothesis on a real-valued coordinate into an equality almost everywhere, so it is
  useful whenever one has to rule out a measure-preserving map that moves points downwards.
-/

public section

noncomputable section

open Filter MeasureTheory

namespace MeasureTheory.Measure

/-- Two measurable real-valued functions with the same pushforward measure, where the first lies
below the second almost everywhere, are equal almost everywhere. -/
theorem ae_eq_of_measurePreserving_of_le {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    {μ : Measure α} (hf : Measurable f) (hg : Measurable g) [IsFiniteMeasure μ]
    (hmap : Measure.map f μ = Measure.map g μ) (hle : f ≤ᵐ[μ] g) : f =ᵐ[μ] g := by
  have habs : ∀ y : ℝ, ‖Real.arctan y‖ ≤ Real.pi / 2 := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan y),
      le_of_lt (Real.arctan_lt_pi_div_two y)⟩
  have hfint : Integrable (fun x => Real.arctan (f x)) μ :=
    Integrable.of_bound
      ((Real.continuous_arctan.measurable.comp hf).aestronglyMeasurable)
      (Real.pi / 2) (Filter.Eventually.of_forall (fun x => habs _))
  have hgint : Integrable (fun x => Real.arctan (g x)) μ :=
    Integrable.of_bound
      ((Real.continuous_arctan.measurable.comp hg).aestronglyMeasurable)
      (Real.pi / 2) (Filter.Eventually.of_forall (fun x => habs _))
  have hint : ∫ x, Real.arctan (f x) ∂μ = ∫ x, Real.arctan (g x) ∂μ := by
    have hm := integral_map (μ := μ) (φ := f) (f := fun x => Real.arctan x) hf.aemeasurable
      Real.continuous_arctan.aestronglyMeasurable
    have hm' := integral_map (μ := μ) (φ := g) (f := fun x => Real.arctan x) hg.aemeasurable
      Real.continuous_arctan.aestronglyMeasurable
    calc ∫ x, Real.arctan (f x) ∂μ = ∫ x, Real.arctan x ∂Measure.map f μ := hm.symm
      _ = ∫ x, Real.arctan x ∂Measure.map g μ := by rw [hmap]
      _ = ∫ x, Real.arctan (g x) ∂μ := hm'
  have hmono : ∀ᵐ x ∂μ, Real.arctan (f x) ≤ Real.arctan (g x) := by
    filter_upwards [hle] with x hx
    exact Real.arctan_strictMono.monotone hx
  have hnonneg : 0 ≤ᵐ[μ] (fun x => Real.arctan (g x) - Real.arctan (f x)) := by
    filter_upwards [hmono] with x hx
    simp only [Pi.zero_apply]
    linarith
  have hzero : ∫ x, (Real.arctan (g x) - Real.arctan (f x)) ∂μ = 0 := by
    rw [integral_sub hgint hfint, hint, sub_self]
  have hvanish := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hgint.sub hfint)).mp hzero
  filter_upwards [hvanish] with x hx
  have heq : Real.arctan (f x) = Real.arctan (g x) := by
    simp only [Pi.zero_apply] at hx
    linarith
  exact Real.arctan_injective heq

/-- A measure-preserving real endomap bounded above by the identity is almost everywhere the
identity. -/
theorem ae_eq_id_of_measurePreserving_of_le {f : ℝ → ℝ} {μ : Measure ℝ}
    (hf : Measurable f) [IsFiniteMeasure μ] (hmap : Measure.map f μ = μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ x) : f =ᵐ[μ] id := by
  refine ae_eq_of_measurePreserving_of_le hf measurable_id (μ := μ) ?_ hle
  rw [hmap, Measure.map_id]

end MeasureTheory.Measure
