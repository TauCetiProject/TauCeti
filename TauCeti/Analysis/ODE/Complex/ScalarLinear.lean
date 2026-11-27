/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Proportionality of holomorphic solutions of first-order linear equations

Two holomorphic functions `u`, `v` on a preconnected open set `U ⊆ ℂ` that satisfy the same
equation `y' = p y` on a dense subset of `U`, with `v` nonzero at one point of `U`, are
proportional on `U` (`IsOpen.exists_eq_const_mul_of_hasDerivAt_mul`). On a ball around that point
where `v` has no zero, the quotient `u / v` is holomorphic with derivative vanishing on a dense
subset, hence everywhere by continuity, so it is constant there; the identity theorem extends
`u = C v` to `U`. The coefficient `p` is arbitrary: the equation is only used where it holds, and
`u` may vanish.

## Main results

* `IsOpen.exists_eq_const_mul_of_hasDerivAt_mul`: proportionality of solutions of `y' = p y`.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-- The case of `IsOpen.exists_eq_const_mul_of_hasDerivAt_mul` where `v` has no zero on `U`: the
quotient `u / v` is holomorphic on `U` with derivative vanishing on `U ∩ S`, hence on `U`. -/
private theorem exists_eq_const_mul_of_hasDerivAt_mul_of_forall_ne_zero {U S : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hS : Dense S) {p u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u U) (hv : DifferentiableOn ℂ v U) (hv₀ : ∀ z ∈ U, v z ≠ 0)
    (hu' : ∀ z ∈ U ∩ S, HasDerivAt u (p z * u z) z)
    (hv' : ∀ z ∈ U ∩ S, HasDerivAt v (p z * v z) z) :
    ∃ C : ℂ, ∀ z ∈ U, u z = C * v z := by
  have hR : DifferentiableOn ℂ (fun z ↦ u z / v z) U := hu.div hv hv₀
  -- On `U ∩ S` the quotient has derivative `(p u v - u p v) / v ^ 2 = 0`.
  have hd : EqOn (deriv fun z ↦ u z / v z) 0 (U ∩ S) := fun z hz ↦
    (((hu' z hz).div (hv' z hz) (hv₀ z hz.1)).congr_deriv
      (by rw [Pi.zero_apply]; ring)).deriv
  -- The derivative of the quotient is continuous on `U`, and `U ∩ S` is dense in `U`.
  have hd' := hd.of_subset_closure (hR.deriv hU).continuousOn continuousOn_const
    inter_subset_left (hS.open_subset_closure_inter hU)
  obtain ⟨C, hC⟩ := hU.exists_is_const_of_deriv_eq_zero hUc hR fun z hz ↦ hd' hz
  exact ⟨C, fun z hz ↦ by rw [← hC z hz, div_mul_cancel₀ _ (hv₀ z hz)]⟩

/-- Two holomorphic functions `u`, `v` on a preconnected open set `U ⊆ ℂ` that satisfy the same
first-order linear equation `y' = p y` at the points of `U ∩ S` for a dense set `S`, with `v`
nonzero at a point `z₀ ∈ U`, are proportional on `U`: `u = C v` for a constant `C`. -/
theorem _root_.IsOpen.exists_eq_const_mul_of_hasDerivAt_mul {U S : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hS : Dense S) {p u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u U)
    (hv : DifferentiableOn ℂ v U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hv₀ : v z₀ ≠ 0)
    (hu' : ∀ z ∈ U ∩ S, HasDerivAt u (p z * u z) z)
    (hv' : ∀ z ∈ U ∩ S, HasDerivAt v (p z * v z) z) :
    ∃ C : ℂ, ∀ z ∈ U, u z = C * v z := by
  -- A ball around `z₀` inside `U` on which `v` has no zero.
  have hV : U ∩ {z | v z ≠ 0} ∈ 𝓝 z₀ := inter_mem (hU.mem_nhds hz₀)
    ((hv.continuousOn.continuousAt (hU.mem_nhds hz₀)).eventually_ne hv₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨C, hC⟩ := exists_eq_const_mul_of_hasDerivAt_mul_of_forall_ne_zero Metric.isOpen_ball
    (convex_ball z₀ ε).isPreconnected hS (hu.mono fun z hz ↦ (hball hz).1)
    (hv.mono fun z hz ↦ (hball hz).1) (fun z hz ↦ (hball hz).2)
    (fun z hz ↦ hu' z ⟨(hball hz.1).1, hz.2⟩) (fun z hz ↦ hv' z ⟨(hball hz.1).1, hz.2⟩)
  -- The identity theorem extends `u = C v` from the ball to `U`.
  refine ⟨C, fun z hz ↦ (hu.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    ((hv.const_mul C).analyticOnNhd hU) hUc hz₀ ?_ hz⟩
  filter_upwards [Metric.ball_mem_nhds z₀ hε] with w hw using hC w hw

end TauCeti
