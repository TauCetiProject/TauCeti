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
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Restrictions to lines and iterated derivatives of analytic functions

A function analytic at `p` vanishes on a neighbourhood of `p` exactly when its restriction
`t ↦ f (p + t • v)` to every line through `p` vanishes on a neighbourhood of `0`. The nontrivial
direction is the identity principle along each line: on a ball around `p` where `f` is analytic,
the restriction to the line through `p` and a point `y` of the ball is analytic on a disc
containing `0` and `1`, so it vanishes at `1`, that is at `y`.

In several complex variables this is the first step of putting a nonzero germ in general position:
some direction `v` has a restriction that does not vanish identically, and in linear coordinates
whose last axis is `v` the germ becomes regular in the last variable, as Weierstrass preparation
requires (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`).

Over a characteristic-zero normed field and into a complete codomain,
`HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` expresses a germ analytic at `p` on a ball around `p`
through the diagonal values of its iterated Fréchet derivatives at `p`. Consequently `f` vanishes
near `p` if and only if `iteratedFDeriv 𝕜 n f p = 0` for every `n : ℕ`, and Mathlib's identity
principle extends this pointwise jet condition along any preconnected set on which `f` is analytic
on neighbourhoods.

The name follows Mathlib's `Mathlib.Analysis.Analytic.Uniqueness`, where the identity principle
lives.

## Main declarations

* `AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`: an analytic function
  vanishes near `p` exactly when all its restrictions to lines through `p` vanish near `0`.
* `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: after a linear change of
  coordinates, a function on `E × 𝕜` not vanishing near `p` has finite order in the last variable.
* `AnalyticAt.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero`,
  `AnalyticAt.eventuallyEq_iff_forall_iteratedFDeriv_eq`: over a characteristic-zero field and into
  a complete space, an analytic germ is determined by its iterated Fréchet derivatives at a single
  point.
* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`: the corresponding identity
  principles on preconnected sets.

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

section IteratedFDeriv

variable {𝕜' E' F' : Type*} [NontriviallyNormedField 𝕜'] [CharZero 𝕜']
  [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] [CompleteSpace F']

/-- Over a characteristic-zero field and into a complete normed space, an analytic germ vanishes
near `p` if and only if all of its iterated Fréchet derivatives at `p` vanish. -/
theorem AnalyticAt.eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero
    {f : E' → F'} {p : E'} (hf : AnalyticAt 𝕜' f p) :
    f =ᶠ[𝓝 p] 0 ↔ ∀ n : ℕ, iteratedFDeriv 𝕜' n f p = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · simpa [iteratedFDeriv_zero] using (h.iteratedFDeriv 𝕜' n).eq_of_nhds
  · obtain ⟨P, r, hP⟩ := hf
    filter_upwards [Metric.eball_mem_nhds p hP.r_pos] with y hy
    have hy' : y - p ∈ Metric.eball 0 r := by
      simpa [eDist_eq_eNorm_sub] using hy
    have hsum := hP.hasSum_iteratedFDeriv hy'
    simp only [h, zero_apply, smul_zero, add_sub_cancel] at hsum
    exact hsum.unique hasSum_zero

/-- Over a characteristic-zero field and into a complete normed space, two germs analytic at `p`
agree near `p` if and only if all of their iterated Fréchet derivatives at `p` agree. -/
theorem AnalyticAt.eventuallyEq_iff_forall_iteratedFDeriv_eq
    {f g : E' → F'} {p : E'} (hf : AnalyticAt 𝕜' f p) (hg : AnalyticAt 𝕜' g p) :
    f =ᶠ[𝓝 p] g ↔ ∀ n : ℕ, iteratedFDeriv 𝕜' n f p = iteratedFDeriv 𝕜' n g p := by
  rw [Filter.eventuallyEq_iff_sub,
    (hf.sub hg).eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero]
  refine forall_congr' fun n ↦ ?_
  rw [iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt, sub_eq_zero]

/-- **Identity principle via iterated derivatives.** If a function into a complete normed space is
analytic on neighbourhoods along a preconnected set `U` over a characteristic-zero field and all of
its iterated Fréchet derivatives vanish at one point `z₀ ∈ U`, then it vanishes on `U`. -/
theorem AnalyticOnNhd.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    {f : E' → F'} {U : Set E'} (hf : AnalyticOnNhd 𝕜' f U) (hU : IsPreconnected U)
    {z₀ : E'} (h₀ : z₀ ∈ U) (hfz₀ : ∀ n : ℕ, iteratedFDeriv 𝕜' n f z₀ = 0) :
    Set.EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).eventuallyEq_zero_iff_forall_iteratedFDeriv_eq_zero.2 hfz₀)

/-- **Identity principle via iterated derivatives.** Two functions into a complete normed space
that are analytic on neighbourhoods along a preconnected set `U` over a characteristic-zero field
and have equal iterated Fréchet derivatives at one point `z₀ ∈ U` agree on `U`. -/
theorem AnalyticOnNhd.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    {f g : E' → F'} {U : Set E'} (hf : AnalyticOnNhd 𝕜' f U) (hg : AnalyticOnNhd 𝕜' g U)
    (hU : IsPreconnected U) {z₀ : E'} (h₀ : z₀ ∈ U)
    (hfg : ∀ n : ℕ, iteratedFDeriv 𝕜' n f z₀ = iteratedFDeriv 𝕜' n g z₀) :
    Set.EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU h₀
    (((hf z₀ h₀).eventuallyEq_iff_forall_iteratedFDeriv_eq (hg z₀ h₀)).2 hfg)

end IteratedFDeriv

end
