/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
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
* `AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball`: two functions analytic on the
  cut plane that agree on the unit disk agree on the cut plane.
* `AnalyticOnNhd.comp_eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball`: the same along an analytic
  curve `ι : ℂ → X`, for functions `F`, `G` analytic on regions of `X` that contain the image
  of the cut plane under `ι`.
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

/-- **Identity principle on the principal cut plane, disk form.** Two functions analytic on
`{z | 1 - z ∈ slitPlane}` that agree on the unit disk agree on the whole cut plane. -/
theorem AnalyticOnNhd.eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball {f g : ℂ → E}
    (hf : AnalyticOnNhd ℂ f {z | 1 - z ∈ Complex.slitPlane})
    (hg : AnalyticOnNhd ℂ g {z | 1 - z ∈ Complex.slitPlane})
    (hfg : EqOn f g (Metric.ball 0 1)) : EqOn f g {z | 1 - z ∈ Complex.slitPlane} :=
  hf.eqOn_setOf_one_sub_mem_slitPlane_of_eventuallyEq hg (by simp)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 one_pos) hfg)

/-- **Identity principle on the principal cut plane, along a curve.** Let `ι : ℂ → X` be analytic
on the cut plane `{z | 1 - z ∈ slitPlane}` and map it into regions `s` and `t` on which `F` and
`G` are analytic. If `F ∘ ι` and `G ∘ ι` agree on the unit disk, they agree on the cut plane.

For `ι w = (a, b, c, w)` this extends an identity between functions of parameters and argument
from the unit disk to the cut plane, at fixed parameters. -/
theorem AnalyticOnNhd.comp_eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {F G : X → E} {s t : Set X} {ι : ℂ → X}
    (hF : AnalyticOnNhd ℂ F s) (hG : AnalyticOnNhd ℂ G t)
    (hι : AnalyticOnNhd ℂ ι {z | 1 - z ∈ Complex.slitPlane})
    (hs : MapsTo ι {z | 1 - z ∈ Complex.slitPlane} s)
    (ht : MapsTo ι {z | 1 - z ∈ Complex.slitPlane} t)
    (hFG : EqOn (F ∘ ι) (G ∘ ι) (Metric.ball 0 1)) :
    EqOn (F ∘ ι) (G ∘ ι) {z | 1 - z ∈ Complex.slitPlane} :=
  (hF.comp hι hs).eqOn_setOf_one_sub_mem_slitPlane_of_eqOn_ball (hG.comp hι ht) hFG
