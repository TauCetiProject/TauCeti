/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import TauCeti.Topology.Algebra.InfiniteSum.Automorphize

/-!
# Weil's formula for nonnegative functions

Let `μ` be a right-invariant measure on a group `G`, let the right action of a countable
subgroup `Γ` on `G` have a fundamental domain, and let `ν` be the quotient measure on `G ⧸ Γ`.
**Weil's formula** unfolds an integral over `G` into an integral over `G ⧸ Γ` of the sum over
each coset: `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`.

Mathlib proves this for integrable functions with values in a normed space
(`QuotientGroup.integral_eq_integral_automorphize`). This file gives the companion statement
for nonnegative measurable functions with values in `ℝ≥0∞`, which needs no integrability
hypothesis.

## Main results

* `MulAction.lintegral_eq_lintegral_automorphize`: Weil's formula for nonnegative measurable
  functions, for an invariant measure under a countable group action with a fundamental domain.
* `QuotientGroup.lintegral_eq_lintegral_automorphize`: Weil's formula for nonnegative measurable
  functions on a group and its quotient `G ⧸ Γ`.
-/

public section

open MeasureTheory

open scoped ENNReal

/-- **Weil's formula** for nonnegative measurable functions on a space with a group action. Let `μ`
be a measure on `α` invariant under a countable group `G` whose action has a fundamental domain,
and let `ν` be the quotient measure on the orbit space. Then the integral of `f` over `α` is the
integral over the orbit space of the sum of `f` over each orbit, `MulAction.automorphize f`. -/
@[to_additive /-- **Weil's formula** for nonnegative measurable functions on a space with an
additive group action. Let `μ` be a measure on `α` invariant under a countable additive group `G`
whose action has a fundamental domain, and let `ν` be the quotient measure on the orbit space.
Then the integral of `f` over `α` is the integral over the orbit space of the sum of `f` over each
orbit, `AddAction.automorphize f`. -/]
theorem MulAction.lintegral_eq_lintegral_automorphize {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [Countable G] [MeasurableConstSMul G α] {μ : Measure α}
    [SMulInvariantMeasure G α μ] [HasFundamentalDomain G α μ]
    (ν : Measure (Quotient (orbitRel G α))) [QuotientMeasureEqMeasurePreimage μ ν]
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  obtain ⟨s, hs⟩ := ‹HasFundamentalDomain G α μ›.ExistsIsFundamentalDomain
  have hmeas : Measurable (automorphize f : Quotient (orbitRel G α) → ℝ≥0∞) := by
    refine measurable_from_quotient.mpr ?_
    simp only [Function.comp_def, Quotient.mk''_eq_mk, automorphize_mk]
    exact Measurable.tsum fun g ↦ hf.comp (measurable_const_smul g)
  rw [← (hs.measurePreserving_quotient_mk ν).lintegral_comp hmeas, hs.lintegral_eq_tsum'' f]
  simp only [automorphize_mk]
  exact (lintegral_tsum fun g ↦ (hf.comp (measurable_const_smul g)).aemeasurable).symm

/-- **Weil's formula** for nonnegative measurable functions. Let `μ` be a right-invariant measure
on `G`, let the right action of a countable subgroup `Γ` on `G` have a fundamental domain, and let
`ν` be the quotient measure on `G ⧸ Γ`. Then `∫ f dμ = ∫_{G ⧸ Γ} ∑_{γ ∈ Γ} f (g γ) dν(g Γ)`; the
inner sum is `QuotientGroup.automorphize f`, which is constant on each left coset `g Γ`. This is
the nonnegative companion of Mathlib's `QuotientGroup.integral_eq_integral_automorphize`. -/
@[to_additive /-- **Weil's formula** for nonnegative measurable functions on an additive group.
Let `μ` be a right-invariant measure on `G`, let the action of a countable subgroup `Γ` on `G` by
right addition have a fundamental domain, and let `ν` be the quotient measure on `G ⧸ Γ`. Then the
integral of `f` over `G` is the integral over `G ⧸ Γ` of `QuotientAddGroup.automorphize f`. This
is the nonnegative companion of Mathlib's `QuotientAddGroup.integral_eq_integral_automorphize`. -/]
theorem QuotientGroup.lintegral_eq_lintegral_automorphize {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableConstSMul Gᵐᵒᵖ G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulRightInvariant] [HasFundamentalDomain Γ.op G μ]
    (ν : Measure (G ⧸ Γ)) [QuotientMeasureEqMeasurePreimage μ ν] {f : G → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ g, f g ∂μ = ∫⁻ x, automorphize f x ∂ν := by
  -- `QuotientGroup.automorphize` is by definition `MulAction.automorphize` for the right action
  -- of `Γ.op`, and `G ⧸ Γ` is by definition the orbit quotient of that action.
  exact MulAction.lintegral_eq_lintegral_automorphize (G := Γ.op) ν hf
