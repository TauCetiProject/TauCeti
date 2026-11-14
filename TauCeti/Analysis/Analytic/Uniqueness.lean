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

The name follows Mathlib's `Mathlib.Analysis.Analytic.Uniqueness`, where the identity principle
lives.

## Main declarations

* `AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`: an analytic function
  vanishes near `p` exactly when all its restrictions to lines through `p` vanish near `0`.
* `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: after a linear change of
  coordinates, a function on `E × 𝕜` not vanishing near `p` has finite order in the last variable.
* `AnalyticAt.smul_eventuallyEq_zero_iff`, `AnalyticAt.mul_eventuallyEq_zero_iff`: analytic germs at
  a point have no zero divisors.

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

/-- **No zero divisors among scalar and vector analytic germs.** For scalar `f : E → 𝕜` and
vector-valued `g : E → F` analytic at `p`, the product `f • g` vanishes near `p` if and only if
`f` vanishes near `p` or `g` vanishes near `p`. -/
theorem AnalyticAt.smul_eventuallyEq_zero_iff {f : E → 𝕜} {g : E → F} {p : E}
    (hf : AnalyticAt 𝕜 f p) (hg : AnalyticAt 𝕜 g p) :
    f • g =ᶠ[𝓝 p] 0 ↔ f =ᶠ[𝓝 p] 0 ∨ g =ᶠ[𝓝 p] 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (fun h₀ ↦ h₀.mono fun x hx ↦ by simp [hx])
    (fun h₀ ↦ h₀.mono fun x hx ↦ by simp [hx])⟩
  rw [or_iff_not_imp_left]
  intro hf0
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  obtain ⟨r₁, hr₁, hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hgr⟩ := ((e.analyticAt _).comp hg).exists_ball_analyticOnNhd
  obtain ⟨r₃, hr₃, h0⟩ := Metric.eventually_nhds_iff_ball.1 h
  set r := min r₁ (min r₂ r₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  have hq_ex : ∃ q ∈ ball p r, f q ≠ 0 := by
    by_contra! hall
    exact hf0 (eventually_of_mem (ball_mem_nhds p hr) hall)
  obtain ⟨q, hq, hfq⟩ := hq_ex
  have hqr₁ : q ∈ ball p r₁ := ball_subset_ball (min_le_left _ _) hq
  have hzero_q : (e ∘ g) =ᶠ[𝓝 q] 0 := by
    filter_upwards [(hfr q hqr₁).continuousAt.eventually_ne hfq,
      isOpen_ball.mem_nhds (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hq)]
      with y hfy hy₃
    have hy0 : e (f y • g y) = 0 := by simpa using congrArg e (h0 y hy₃)
    rw [map_smul] at hy0
    exact (smul_eq_zero.1 hy0).resolve_left hfy
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hr₂ : ball p r ⊆ ball p r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have heq := (hgr.mono hr₂).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball p r).isPreconnected hq hzero_q
  filter_upwards [ball_mem_nhds p hr] with y hy
  exact UniformSpace.Completion.coe_injective F (by simpa [e] using heq hy)

/-- **No zero divisors among scalar analytic germs.** Two scalar functions analytic at `p` have
product vanishing near `p` if and only if one of them vanishes near `p`. -/
theorem AnalyticAt.mul_eventuallyEq_zero_iff {f g : E → 𝕜} {p : E}
    (hf : AnalyticAt 𝕜 f p) (hg : AnalyticAt 𝕜 g p) :
    f * g =ᶠ[𝓝 p] 0 ↔ f =ᶠ[𝓝 p] 0 ∨ g =ᶠ[𝓝 p] 0 := by
  simpa only [smul_eq_mul] using hf.smul_eventuallyEq_zero_iff hg

end
