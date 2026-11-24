/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.ODE.Wronskian

/-!
# Proportional solutions and the span criterion for holomorphic linear equations

Two holomorphic functions `u`, `v` on a preconnected open set `U ⊆ ℂ` that satisfy the same
equation `y' = p y` on a dense subset of `U`, with `v` nonzero at one point of `U`, are
proportional on `U` (`IsOpen.exists_eq_const_mul_of_hasDerivAt_mul`). On a ball around that point
where `v` has no zero, the quotient `u / v` is holomorphic with derivative vanishing on a dense
subset, hence everywhere by continuity, so it is constant there; the identity theorem extends
`u = C v` to `U`. The coefficient `p` is arbitrary: the equation is only used where it holds, and
`u` may vanish.

For the second-order equation `P w'' + Q w' + R w = 0` on `U`, whose leading coefficient `P` is
nonzero on a dense subset of `U`, the Wronskians of any two solutions satisfy Abel's identity
there, so they are proportional. Hence two solutions whose Wronskian is nonzero at one point of
`U` span all solutions on `U` (`IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation`). The
zeros of `P`, such as the singular points `0` and `1` of the hypergeometric equation, may lie
in `U`.

## Main results

* `IsOpen.exists_eq_const_mul_of_hasDerivAt_mul`: proportionality of solutions of `y' = p y`.
* `IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation`: the span criterion for
  `P w'' + Q w' + R w = 0`.
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

/-- **The span criterion** for a second-order linear equation `P w'' + Q w' + R w = 0` on a
preconnected open set `U ⊆ ℂ` whose leading coefficient `P` is nonzero on `U ∩ S` for a dense
set `S`: if `f₁` and `f₂` are holomorphic solutions on `U` whose Wronskian `𝒲{f₁, f₂}` is nonzero
at a point `z₀ ∈ U`, then every holomorphic solution `w` on `U` is `A f₁ + B f₂` with constants
`A`, `B`. The coefficients need not be continuous, and `U` may contain zeros of `P`. -/
theorem _root_.IsOpen.exists_eq_mul_add_mul_of_secondOrderLinearEquation {U S : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hS : Dense S) {P Q R f₁ f₂ w : ℂ → ℂ}
    (hP : ∀ z ∈ U ∩ S, P z ≠ 0)
    (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    (hw : DifferentiableOn ℂ w U)
    (hf₁' : ∀ z ∈ U, P z * deriv (deriv f₁) z + Q z * deriv f₁ z + R z * f₁ z = 0)
    (hf₂' : ∀ z ∈ U, P z * deriv (deriv f₂) z + Q z * deriv f₂ z + R z * f₂ z = 0)
    (hw' : ∀ z ∈ U, P z * deriv (deriv w) z + Q z * deriv w z + R z * w z = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hW : f₁ z₀ * deriv f₂ z₀ - deriv f₁ z₀ * f₂ z₀ ≠ 0) :
    ∃ A B : ℂ, ∀ z ∈ U, w z = A * f₁ z + B * f₂ z := by
  -- On `U ∩ S` every Wronskian of two solutions satisfies Abel's identity, so it is a constant
  -- multiple of `𝒲{f₁, f₂}`, which is nonzero at `z₀`.
  have habel {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U, P z * deriv (deriv g₁) z + Q z * deriv g₁ z + R z * g₁ z = 0)
      (hg₂' : ∀ z ∈ U, P z * deriv (deriv g₂) z + Q z * deriv g₂ z + R z * g₂ z = 0)
      (z : ℂ) (hz : z ∈ U ∩ S) :
      HasDerivAt (fun ζ ↦ g₁ ζ * deriv g₂ ζ - deriv g₁ ζ * g₂ ζ)
        (-(Q z / P z) * (g₁ z * deriv g₂ z - deriv g₁ z * g₂ z)) z :=
    (hg₁.differentiableAt (hU.mem_nhds hz.1)).hasDerivAt_wronskian_of_secondOrderLinearEquation
      (hP z hz) ((hg₁.deriv hU).differentiableAt (hU.mem_nhds hz.1))
      (hg₂.differentiableAt (hU.mem_nhds hz.1))
      ((hg₂.deriv hU).differentiableAt (hU.mem_nhds hz.1)) (hg₁' z hz.1) (hg₂' z hz.1)
  have hW₁₂ := (hf₁.mul (hf₂.deriv hU)).sub ((hf₁.deriv hU).mul hf₂)
  have hratio {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U, P z * deriv (deriv g₁) z + Q z * deriv g₁ z + R z * g₁ z = 0)
      (hg₂' : ∀ z ∈ U, P z * deriv (deriv g₂) z + Q z * deriv g₂ z + R z * g₂ z = 0) :
      ∃ K : ℂ, ∀ z ∈ U, g₁ z * deriv g₂ z - deriv g₁ z * g₂ z =
        K * (f₁ z * deriv f₂ z - deriv f₁ z * f₂ z) :=
    hU.exists_eq_const_mul_of_hasDerivAt_mul hUc hS
      ((hg₁.mul (hg₂.deriv hU)).sub ((hg₁.deriv hU).mul hg₂)) hW₁₂ hz₀ hW
      (habel hg₁ hg₂ hg₁' hg₂') (habel hf₁ hf₂ hf₁' hf₂')
  obtain ⟨A, hA⟩ := hratio hw hf₂ hw' hf₂'
  obtain ⟨B, hB⟩ := hratio hf₁ hw hf₁' hw'
  -- `𝒲{f₁, f₂} w = 𝒲{f₁, f₂} (A f₁ + B f₂)` on `U`, so `w = A f₁ + B f₂` near `z₀`, where
  -- `𝒲{f₁, f₂}` has no zero; the identity theorem extends this to `U`.
  refine ⟨A, B, fun z hz ↦ (hw.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (((hf₁.const_mul A).add (hf₂.const_mul B)).analyticOnNhd hU) hUc hz₀ ?_ hz⟩
  filter_upwards [((hW₁₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt).eventually_ne hW,
    hU.mem_nhds hz₀] with z hWz hz
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply] at hWz ⊢
  apply mul_right_cancel₀ hWz
  linear_combination f₁ z * hA z hz + f₂ z * hB z hz

end TauCeti
