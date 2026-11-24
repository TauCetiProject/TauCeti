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
it that agree near one point of it, for instance on a neighbourhood of `0`, agree on the whole cut
plane. This is how identities for Gauss hypergeometric functions proved on the unit disk from
their power series extend to the cut plane.

The statement is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Hypergeometric/Basic/PrincipalBranch.lean`.

## Main results

* `AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eventuallyEq`: two functions analytic on the
  cut plane that agree near one point of it agree on the cut plane.
-/

public section

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Identity principle on the principal cut plane.** Two functions analytic on
`{z | 1 - z ∈ slitPlane}` that agree on a neighbourhood of one point of it agree on the whole cut
plane. -/
theorem AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eventuallyEq {f g : ℂ → E} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f {z | 1 - z ∈ Complex.slitPlane})
    (hg : AnalyticOnNhd ℂ g {z | 1 - z ∈ Complex.slitPlane}) (hz₀ : 1 - z₀ ∈ Complex.slitPlane)
    (hfg : f =ᶠ[𝓝 z₀] g) : EqOn f g {z | 1 - z ∈ Complex.slitPlane} :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg Complex.isPreconnected_setOf_one_sub_mem_slitPlane
    hz₀ hfg
