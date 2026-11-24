/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import TauCeti.Analysis.Complex.SlitPlane

/-!
# The identity principle on the principal cut plane

The principal cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, the complex plane cut along
`[1, ∞)`, is open and preconnected (it is star-convex about `0`). So two functions analytic on
it that agree on a nonempty open subset, for instance on the unit disk, agree on the whole cut
plane. This is how identities for Gauss hypergeometric functions proved on the unit disk from
their power series extend to the cut plane.

The statement is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Hypergeometric/Basic/PrincipalBranch.lean`.

## Main results

* `AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eqOn`: two functions analytic on the cut
  plane that agree on a nonempty open subset of it agree on the cut plane.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Identity principle on the principal cut plane.** Two functions analytic on
`{z | 1 - z ∈ slitPlane}` that agree on a nonempty open subset of it agree on the whole cut
plane. -/
theorem AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eqOn {f g : ℂ → E} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f {z | 1 - z ∈ Complex.slitPlane})
    (hg : AnalyticOnNhd ℂ g {z | 1 - z ∈ Complex.slitPlane}) (hU : IsOpen U) (hU₀ : U.Nonempty)
    (hUs : U ⊆ {z | 1 - z ∈ Complex.slitPlane}) (hfg : EqOn f g U) :
    EqOn f g {z | 1 - z ∈ Complex.slitPlane} := by
  obtain ⟨z₀, hz₀⟩ := hU₀
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (hUs hz₀)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hz₀) hfg)
