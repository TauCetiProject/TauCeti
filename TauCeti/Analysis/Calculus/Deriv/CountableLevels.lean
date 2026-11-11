/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Derivatives on countably many levels

A nonzero derivative isolates a point of a level set of a function on a nontrivially normed
field. When the field is second countable, for instance `ℝ` or `ℂ`, the derivative is therefore
nonzero at only countably many points of the preimage of any countable set of levels, so it
vanishes almost everywhere there for any measure vanishing on singletons, even when that preimage
is uncountable.
-/

public section

open MeasureTheory Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [SecondCountableTopology 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace TauCeti

/-- The points of a level set with nonzero derivative are countable, for a function on a second
countable nontrivially normed field with values in any normed space. -/
theorem countable_setOf_eq_and_deriv_ne_zero (f : 𝕜 → E) (c : E) :
    {t | f t = c ∧ deriv f t ≠ 0}.Countable := by
  -- Each such point is isolated in the level set, so the set is discrete, hence countable.
  refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete <|
    isDiscrete_iff_nhdsNE.2 fun t ⟨_, hderiv⟩ ↦ ?_
  have hne : ∀ᶠ u in 𝓝[≠] t, f u ≠ c := by
    rw [← Filter.not_frequently]
    exact fun h ↦ hderiv (deriv_zero_of_frequently_const h)
  exact Filter.inf_principal_eq_bot.2 (hne.mono fun _ hu h ↦ hu h.1)

/-- On countably many levels there are only countably many points with nonzero derivative. -/
theorem countable_setOf_mem_and_deriv_ne_zero (θ : 𝕜 → E) {S : Set E} (hS : S.Countable) :
    {t | θ t ∈ S ∧ deriv θ t ≠ 0}.Countable := by
  refine (hS.biUnion (fun c _ ↦ countable_setOf_eq_and_deriv_ne_zero θ c)).mono fun t ht ↦ ?_
  exact mem_iUnion.mpr ⟨θ t, mem_iUnion.mpr ⟨ht.1, ⟨rfl, ht.2⟩⟩⟩

end TauCeti

/-- The derivative vanishes almost everywhere on the preimage of countably many levels for any
measure vanishing on singletons. No differentiability assumption or countability of the preimage
is required. -/
theorem Set.Countable.ae_deriv_eq_zero_on_preimage [MeasurableSpace 𝕜] {S : Set E}
    (hS : S.Countable) (θ : 𝕜 → E) (μ : Measure 𝕜) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, θ t ∈ S → deriv θ t = 0 := by
  filter_upwards [(TauCeti.countable_setOf_mem_and_deriv_ne_zero θ hS).ae_notMem μ] with t ht hmem
  exact not_ne_iff.mp fun h ↦ ht ⟨hmem, h⟩
