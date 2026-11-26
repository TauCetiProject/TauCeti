/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Bochner integrals with respect to counting measure

Mathlib's `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure` evaluates Bochner integrals against
`Measure.count` only on finite types (`MeasureTheory.integral_count`) and against general measures
only on countable spaces with measurable singletons (`MeasureTheory.integral_countable`).

This file provides `MeasureTheory.hasSum_integral_count` and `MeasureTheory.integral_count_eq_tsum`
for any `Measure.count`-integrable Banach-space-valued function on an arbitrary measurable space,
with no countability or `MeasurableSingletonClass` assumption (used for counting-measure `L²`
Parseval identities and uncountable discrete group von Neumann algebras).

For a function `(x, z) ↦ k z x` integrable for `m × count`, the inner integral over `z` is the sum
`∑' z, k z x` for almost every `x` (`MeasureTheory.integral_count_ae_eq_tsum_of_integrable_prod`),
so the sum is integrable (`MeasureTheory.integrable_tsum_of_integrable_prod_count`) and the
integral over the product is the integral of the sum
(`MeasureTheory.integral_prod_count_eq_integral_tsum`).
-/

public section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : α → E}

/-- If `f` is integrable with respect to `Measure.count`, then `f` is unconditionally summable with
sum `∫ a, f a ∂Measure.count`. No countability or `MeasurableSingletonClass` assumption on `α` is
required. -/
theorem hasSum_integral_count (hf : Integrable f (Measure.count : Measure α)) :
    HasSum f (∫ a, f a ∂(Measure.count : Measure α)) := by
  have hmk : f = hf.aestronglyMeasurable.mk f :=
    funext (Measure.ae_count_iff.1 hf.aestronglyMeasurable.ae_eq_mk)
  have hsm : StronglyMeasurable f := by
    rw [hmk]
    exact hf.aestronglyMeasurable.stronglyMeasurable_mk
  rw [Measure.count] at hf ⊢
  exact (hasSum_integral_measure hf).congr_fun fun a => (integral_dirac' _ a hsm).symm

/-- The Bochner integral of a `Measure.count`-integrable function equals its `tsum`, with no
countability or `MeasurableSingletonClass` assumption on `α`. -/
theorem integral_count_eq_tsum (hf : Integrable f (Measure.count : Measure α)) :
    ∫ a, f a ∂(Measure.count : Measure α) = ∑' a, f a :=
  (hasSum_integral_count hf).tsum_eq.symm

section Prod

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z] {m : Measure X}
  [SFinite (Measure.count : Measure Z)] {k : Z → X → E}

/-- For `(x, z) ↦ k z x` integrable for `m × count`, the integral of `z ↦ k z x` for counting
measure is the sum `∑' z, k z x` for `m`-almost every `x`. -/
theorem integral_count_ae_eq_tsum_of_integrable_prod
    (h_int : Integrable (fun p : X × Z ↦ k p.2 p.1) (m.prod Measure.count)) :
    (fun x ↦ ∫ z, k z x ∂Measure.count) =ᵐ[m] fun x ↦ ∑' z, k z x := by
  filter_upwards [((integrable_prod_iff h_int.aestronglyMeasurable).mp h_int).1] with x hx
    using integral_count_eq_tsum hx

/-- For `(x, z) ↦ k z x` integrable for `m × count`, the sum `x ↦ ∑' z, k z x` is
`m`-integrable. -/
theorem integrable_tsum_of_integrable_prod_count
    (h_int : Integrable (fun p : X × Z ↦ k p.2 p.1) (m.prod Measure.count)) :
    Integrable (fun x ↦ ∑' z, k z x) m :=
  h_int.integral_prod_left.congr (integral_count_ae_eq_tsum_of_integrable_prod h_int)

/-- For `(x, z) ↦ k z x` integrable for `m × count`, its integral is the integral of
`x ↦ ∑' z, k z x`. -/
theorem integral_prod_count_eq_integral_tsum [SFinite m]
    (h_int : Integrable (fun p : X × Z ↦ k p.2 p.1) (m.prod Measure.count)) :
    ∫ p : X × Z, k p.2 p.1 ∂m.prod Measure.count = ∫ x, ∑' z, k z x ∂m := by
  rw [integral_prod _ h_int]
  exact integral_congr_ae (integral_count_ae_eq_tsum_of_integrable_prod h_int)

end Prod

end MeasureTheory
