/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Analytic.Polynomial

/-!
# Analytic continuation and exact quotients of Nash germs

A polynomial relation satisfied by an analytic function near one point of a preconnected set holds
throughout that set (`AnalyticOnNhd.eval_map_eval_eq_zero_of_isPreconnected`). Consequently, an
analytic function on a preconnected set that is a Nash germ at one point of the set is a Nash germ
at every interior point (`IsPreconnected.isNashAt_of_mem`).

As an immediate application, if `f` and `g` are Nash germs at `x` with `g` not identically zero
near `x`, and `q` is an analytic germ at `x` satisfying `f =ᶠ[𝓝 x] g * q`, then `q` is itself a
Nash germ at `x` (`TauCeti.IsNashAt.of_eventuallyEq_mul_left`), even when `g x = 0`: on a small
ball around `x`, `g` is nonzero at some point `y₀`, where `q =ᶠ[𝓝 y₀] f / g` is Nash by
`TauCeti.IsNashAt.div`, and its polynomial relation propagates across the ball to `x`.

## Main results

* `IsPreconnected.isNashAt_of_mem`: analytic continuation of the Nash property along a
  preconnected set.
* `TauCeti.IsNashAt.of_eventuallyEq_mul_left`, `TauCeti.IsNashAt.of_eventuallyEq_mul_right`: an
  analytic quotient of Nash germs whose divisor is not identically zero near `x` is a Nash germ
  at `x`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter Metric Set Topology

variable {σ : Type*} [Fintype σ]

/-- **Analytic continuation of Nash germs.** Let `f` be real analytic on a preconnected set `s`.
If `f` is a Nash germ at one point `y ∈ s`, then `f` is a Nash germ at every point `x` for which
`s ∈ 𝓝 x`. -/
theorem IsPreconnected.isNashAt_of_mem {s : Set (σ → ℝ)} (hs : IsPreconnected s)
    {f : (σ → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f s) {y x : σ → ℝ} (hy : y ∈ s) (hx : s ∈ 𝓝 x)
    (hfy : TauCeti.IsNashAt f y) : TauCeti.IsNashAt f x := by
  obtain ⟨-, P, hP0, hP⟩ := TauCeti.isNashAt_iff.1 hfy
  exact TauCeti.isNashAt_iff.2 ⟨hf x (mem_of_mem_nhds hx), P, hP0,
    eventually_of_mem hx (hf.eval_map_eval_eq_zero_of_isPreconnected hs hy hP)⟩

namespace TauCeti

/-- **Exact analytic right-quotient of Nash germs.** If `f` and `g` are Nash germs at `x`, `g` is
not identically zero near `x`, and `q` is real analytic at `x` with `f =ᶠ[𝓝 x] g * q`, then `q`
is a Nash germ at `x`, even when `g x = 0`. -/
@[to_fun]
theorem IsNashAt.of_eventuallyEq_mul_left {f g q : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (hg : IsNashAt g x) (hg0 : ¬ g =ᶠ[𝓝 x] 0) (hq : AnalyticAt ℝ q x)
    (h : f =ᶠ[𝓝 x] g * q) : IsNashAt q x := by
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.1
    (hf.eventually_isNashAt.and <| hg.eventually_isNashAt.and <| hq.eventually_analyticAt.and h)
  -- Since `g` does not vanish identically near `x`, it is nonzero at some point `y₀` of the ball.
  obtain ⟨y₀, hy₀, hgy₀⟩ : ∃ y₀ ∈ ball x r, g y₀ ≠ 0 := by
    by_contra! hall
    exact hg0 (eventually_of_mem (ball_mem_nhds x hr) hall)
  have hqy₀ : IsNashAt q y₀ := by
    refine ((hB hy₀).1.div (hB hy₀).2.1 hgy₀).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hy₀,
      (hB hy₀).2.1.analyticAt.continuousAt.eventually_ne hgy₀] with y hy hgy
    simp only [Pi.div_apply]
    rw [(hB hy).2.2.2, Pi.mul_apply, mul_div_cancel_left₀ _ hgy]
  exact (convex_ball x r).isPreconnected.isNashAt_of_mem (fun y hy ↦ (hB hy).2.2.1) hy₀
    (ball_mem_nhds x hr) hqy₀

/-- **Exact analytic left-quotient of Nash germs.** If `f` and `g` are Nash germs at `x`, `g` is
not identically zero near `x`, and `q` is real analytic at `x` with `f =ᶠ[𝓝 x] q * g`, then `q`
is a Nash germ at `x`, even when `g x = 0`. -/
@[to_fun]
theorem IsNashAt.of_eventuallyEq_mul_right {f g q : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (hg : IsNashAt g x) (hg0 : ¬ g =ᶠ[𝓝 x] 0) (hq : AnalyticAt ℝ q x)
    (h : f =ᶠ[𝓝 x] q * g) : IsNashAt q x :=
  hf.of_eventuallyEq_mul_left hg hg0 hq (mul_comm q g ▸ h)

end TauCeti
