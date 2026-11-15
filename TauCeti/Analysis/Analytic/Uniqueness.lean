/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.RCLike.Basic

-- Proof-only: the identity principle
-- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` and its analytic inputs, and
-- `SeparatingDual.exists_continuousLinearEquiv_apply_eq` for the change of coordinates.
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Analytic functions are determined by their restrictions to lines

A function analytic at `p` vanishes on a neighbourhood of `p` exactly when its restriction
`t ↦ f (p + t • v)` to every line through `p` vanishes on a neighbourhood of `0`. The nontrivial
direction is the identity principle along each line: on a ball around `p` where `f` is analytic,
the restriction to the line through `p` and a point `y` of the ball is analytic on a disc
containing `0` and `1`, so it vanishes at `1`, that is at `y`.

In several complex variables this is the first step of putting a nonzero germ in general position:
some direction `v` has a restriction that does not vanish identically, and in linear coordinates
whose last axis is `v` the germ becomes regular in the last variable, as Weierstrass preparation
requires (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`).

The identity principle also shows that an analytic function on a preconnected set which does not
vanish identically does not vanish on a dense subset: otherwise it would vanish on an open set.
Combined with continuity, the nonvanishing set of an entire function such as a polynomial in the
entries of a matrix is open and dense, which is how genericity statements for finitely many
polynomial conditions are proved.

The name follows Mathlib's `Mathlib.Analysis.Analytic.Uniqueness`, where the identity principle
lives.

## Main declarations

* `AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`: an analytic function
  vanishes near `p` exactly when all its restrictions to lines through `p` vanish near `0`.
* `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: after a linear change of
  coordinates, a function on `E × 𝕜` not vanishing near `p` has finite order in the last variable.
* `AnalyticOnNhd.subset_closure_setOf_ne_zero`: on a preconnected set, an analytic function not
  vanishing at some point does not vanish on a dense subset.
* `AnalyticOnNhd.dense_setOf_ne_zero`: the same for a function analytic on the whole space.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
-/

public section

open Filter Metric Topology

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The nontrivial direction of
`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul` for a complete
codomain, where `f` is analytic on a ball around `p`. -/
private theorem AnalyticAt.eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
    [CompleteSpace F] {f : E → F} {p : E} (hf : AnalyticAt 𝕜 f p)
    (h : ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0) : f =ᶠ[𝓝 p] 0 := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [ball_mem_nhds p hr] with y hy
  set v := y - p
  rcases eq_or_ne v 0 with hv | hv
  · -- On the trivial direction the restriction is the constant `f p = f y`.
    simpa [sub_eq_zero.1 hv] using (h 0).self_of_nhds
  -- On the line through `p` and `y`, the restriction is analytic on a disc containing `0` and `1`.
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmem : ∀ t ∈ ball (0 : 𝕜) (r / ‖v‖), p + t • v ∈ ball p r := fun t ht ↦ by
    rw [mem_ball_zero_iff, lt_div_iff₀ hv'] at ht
    simpa [dist_eq_norm, norm_smul] using ht
  have hline (t : 𝕜) : AnalyticAt 𝕜 (fun t : 𝕜 ↦ p + t • v) t := by fun_prop
  have han : AnalyticOnNhd 𝕜 (fun t : 𝕜 ↦ f (p + t • v)) (ball (0 : 𝕜) (r / ‖v‖)) :=
    fun t ht ↦ AnalyticAt.comp (g := f) (hfr _ (hmem t ht)) (hline t)
  have h1 : (1 : 𝕜) ∈ ball (0 : 𝕜) (r / ‖v‖) := by
    rw [mem_ball_zero_iff, norm_one, one_lt_div hv']
    simpa [v, dist_eq_norm] using hy
  simpa [v] using han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : 𝕜) _).isPreconnected (mem_ball_self (div_pos hr hv')) (h v) h1

/-- **An analytic function is determined near a point by its restrictions to lines.** A function
analytic at `p` vanishes on a neighbourhood of `p` exactly when, for every direction `v`, the
restriction `t ↦ f (p + t • v)` vanishes on a neighbourhood of `0`. -/
theorem AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul {f : E → F}
    {p : E} (hf : AnalyticAt 𝕜 f p) :
    f =ᶠ[𝓝 p] 0 ↔ ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0 := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · have hline : Tendsto (fun t : 𝕜 ↦ p + t • v) (𝓝 0) (𝓝 p) := by
      have : Continuous fun t : 𝕜 ↦ p + t • v := by fun_prop
      simpa using this.tendsto (0 : 𝕜)
    exact hline.eventually h
  -- Pass to the completion of `F`, as in Mathlib's identity principle.
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have he : (e ∘ f) =ᶠ[𝓝 p] 0 :=
    ((e.analyticAt _).comp hf).eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
      fun v ↦ (h v).mono fun t ht ↦ by simp [ht]
  exact he.mono fun y hy ↦ UniformSpace.Completion.coe_injective F (by simpa [e] using hy)

/-- **General position in the last variable.** A function analytic at `p` on `E × 𝕜` that does not
vanish near `p` becomes regular in the last variable after a linear change of coordinates: there
are a continuous linear automorphism `L` and a point `q` with `L q = p` such that
`t ↦ f (L (q.1, t))` has finite analytic order at `q.2`. The last axis is sent to a direction along
which the restriction of `f` does not vanish identically. -/
theorem AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top {f : E × 𝕜 → F}
    {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) (hf0 : ¬f =ᶠ[𝓝 p] 0) :
    ∃ (L : (E × 𝕜) ≃L[𝕜] E × 𝕜) (q : E × 𝕜), L q = p ∧
      analyticOrderAt (fun t ↦ f (L (q.1, t))) q.2 ≠ ⊤ := by
  obtain ⟨v, hv⟩ : ∃ v, ¬(fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0 := by
    by_contra! h
    exact hf0 (hf.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 h)
  rcases eq_or_ne v 0 with rfl | hv0
  · -- The trivial direction only occurs when `f p ≠ 0`, and then any coordinates work.
    refine ⟨.refl 𝕜 _, p, rfl, fun h ↦ hv (Eventually.of_forall fun t ↦ ?_)⟩
    simpa using (analyticOrderAt_eq_top.1 h).self_of_nhds
  -- Move to linear coordinates in which `v` is the last axis.
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := 𝕜)
    (x := ((0 : E), (1 : 𝕜))) (by simp) hv0
  obtain ⟨⟨x₀, w₀⟩, rfl⟩ : ∃ q, L q = p := ⟨L.symm p, L.apply_symm_apply p⟩
  refine ⟨L, (x₀, w₀), rfl, ?_⟩
  -- The vertical slice is the restriction of `f` to the line through `p` along `v`.
  rw [Ne, analyticOrderAt_eq_top]
  refine fun h ↦ hv ?_
  have ht : Tendsto (fun t : 𝕜 ↦ w₀ + t) (𝓝 0) (𝓝 w₀) := by
    have : Continuous fun t : 𝕜 ↦ w₀ + t := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [ht.eventually h] with t ht
  have hLt : L (x₀, w₀ + t) = L (x₀, w₀) + t • v := by
    rw [← hL, ← L.map_smul, ← L.map_add]
    simp
  simpa [hLt] using ht

section NonvanishingSet

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The nonvanishing set of an analytic function is dense.** If `f` is analytic on a
preconnected set `U` and does not vanish at some point of `U`, then every point of `U` is a limit
of points where `f` does not vanish. Otherwise `f` would vanish on a neighbourhood of a point of
`U`, hence on all of `U` by the identity principle. -/
theorem AnalyticOnNhd.subset_closure_setOf_ne_zero {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} (hz₀U : z₀ ∈ U)
    (hz₀ : f z₀ ≠ 0) : U ⊆ closure {x | f x ≠ 0} := by
  intro x hx
  by_contra hcl
  have hzero : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with y hy
    by_contra hfy
    exact hy (subset_closure hfy)
  exact hz₀ (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hx hzero hz₀U)

/-- **The nonvanishing set of an entire function is dense.** A function analytic on a preconnected
space that does not vanish at some point does not vanish on a dense set. Preconnectedness holds for
real and complex normed spaces; over a totally disconnected field such as `ℚ_[p]` the indicator
function of a ball is analytic, and the statement fails. -/
theorem AnalyticOnNhd.dense_setOf_ne_zero [PreconnectedSpace E] {f : E → F}
    (hf : AnalyticOnNhd 𝕜 f Set.univ) {z₀ : E} (hz₀ : f z₀ ≠ 0) : Dense {x | f x ≠ 0} := fun x ↦
  hf.subset_closure_setOf_ne_zero isPreconnected_univ (Set.mem_univ z₀) hz₀ (Set.mem_univ x)

end NonvanishingSet

end
