/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Derivatives on countably many levels

A nonzero derivative isolates a real function's level-set point. Consequently the derivative
vanishes almost everywhere on the preimage of any countable set of levels, even when that
preimage is uncountable.
-/

public section

open MeasureTheory Set
open scoped Topology

/-- Points of a real level set with nonzero derivative form a countable set. -/
theorem countable_level_nonzero_deriv (θ : ℝ → ℝ) (c : ℝ) :
    {t | θ t = c ∧ deriv θ t ≠ 0}.Countable := by
  apply (countable_setOfPred_isolated_right_within (s := {t | θ t = c})).mono
  intro t ht
  refine ⟨ht.1, ?_⟩
  apply Filter.eventually_false_iff_eq_bot.mp
  have he : ∀ᶠ u in nhdsWithin t {t}ᶜ, θ u ≠ c :=
    (differentiableAt_of_deriv_ne_zero ht.2).hasDerivAt.eventually_ne ht.2
  have hm : nhdsWithin t ({u | θ u = c} ∩ Ioi t) ≤ nhdsWithin t {t}ᶜ := by
    apply nhdsWithin_mono
    intro u hu
    exact hu.2.ne'
  filter_upwards [he.filter_mono hm, self_mem_nhdsWithin] with u hne hu
  exact hne hu.1

/-- On countably many real levels there are only countably many points with nonzero derivative. -/
theorem countable_preimage_nonzero_deriv (θ : ℝ → ℝ) {S : Set ℝ} (hS : S.Countable) :
    {t | θ t ∈ S ∧ deriv θ t ≠ 0}.Countable := by
  apply (hS.biUnion (fun c _ ↦ countable_level_nonzero_deriv θ c)).mono
  intro t ht
  exact mem_iUnion.mpr ⟨θ t, mem_iUnion.mpr ⟨ht.1, ⟨rfl, ht.2⟩⟩⟩

/-- The derivative vanishes almost everywhere on the preimage of countably many levels for any
measure vanishing on singletons. No differentiability assumption or countability of the preimage
is required. -/
theorem Set.Countable.ae_deriv_eq_zero_on_preimage [MeasurableSpace ℝ]
    {S : Set ℝ} (hS : S.Countable)
    (θ : ℝ → ℝ) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, θ t ∈ S → deriv θ t = 0 := by
  filter_upwards [(countable_preimage_nonzero_deriv θ hS).ae_notMem μ] with t ht hmem
  by_contra h
  exact ht ⟨hmem, h⟩
