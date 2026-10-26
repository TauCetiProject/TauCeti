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

namespace TauCeti

/-- The points of a level set with nonzero derivative are countable, for any real normed
space as codomain. -/
theorem countable_setOf_eq_and_deriv_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (c : E) :
    {t | f t = c ∧ deriv f t ≠ 0}.Countable := by
  refine (countable_setOfPred_isolated_left_within (s := {t | f t = c})).mono ?_
  rintro t ⟨ht, hderiv⟩
  refine ⟨ht, ?_⟩
  have hne : ∀ᶠ u in 𝓝[≠] t, f u ≠ c := by
    rw [← Filter.not_frequently]
    exact fun h ↦ hderiv (deriv_zero_of_frequently_const h)
  have hc : {u | f u = c}ᶜ ∈ 𝓝[Iio t] t :=
    nhdsWithin_mono t (fun _ hu ↦ ne_of_lt hu) hne
  rw [Set.inter_comm, nhdsWithin_inter']
  exact Filter.inf_principal_eq_bot.mpr hc

/-- On countably many levels there are only countably many points with nonzero derivative. -/
theorem countable_setOf_mem_and_deriv_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (θ : ℝ → E) {S : Set E} (hS : S.Countable) :
    {t | θ t ∈ S ∧ deriv θ t ≠ 0}.Countable := by
  refine (hS.biUnion (fun c _ ↦ countable_setOf_eq_and_deriv_ne_zero θ c)).mono fun t ht ↦ ?_
  exact mem_iUnion.mpr ⟨θ t, mem_iUnion.mpr ⟨ht.1, ⟨rfl, ht.2⟩⟩⟩

end TauCeti

/-- The derivative vanishes almost everywhere on the preimage of countably many levels for any
measure vanishing on singletons. No differentiability assumption or countability of the preimage
is required. -/
theorem Set.Countable.ae_deriv_eq_zero_on_preimage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace ℝ] {S : Set E} (hS : S.Countable)
    (θ : ℝ → E) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, θ t ∈ S → deriv θ t = 0 := by
  filter_upwards [(TauCeti.countable_setOf_mem_and_deriv_ne_zero θ hS).ae_notMem μ] with t ht hmem
  exact not_ne_iff.mp fun h ↦ ht ⟨hmem, h⟩
