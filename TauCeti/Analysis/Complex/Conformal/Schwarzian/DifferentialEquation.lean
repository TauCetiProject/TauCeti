/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Schwarzian.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The Schwarzian differential equation

A locally univalent holomorphic function `w` is the quotient of two independent solutions of the
second-order linear equation `y'' + S(w) / 2 * y = 0`, where `S(w)` is the Schwarzian derivative.
Explicitly, if `u` is a holomorphic reciprocal square root of `w'`, so that `u ^ 2 * w' = 1`,
then `v₂ = u = 1 / √w'` and `v₁ = w * u = w / √w'` solve this equation, their Wronskian is one
and `v₁ / v₂ = w`.  Conversely, the quotient of two solutions of `y'' + Q * y = 0` with nonzero
Wronskian has Schwarzian derivative `2 * Q`.

Both directions rest on one identity: if `u ^ 2 * w' = c` near `x` for a nonzero constant `c`,
then `S(w) = -2 * u'' / u` at `x`.  This is how the Schwarzian of a local inverse of a covering
map, which does not depend on the branch, turns into a linear differential equation for the
inverse.

All statements are local at a point `x`: hypotheses hold on a neighbourhood of `x`, and
conclusions are evaluated at `x` or hold on a neighbourhood of `x`.  The Wronskian of `(y₂, y₁)`
is written out as `y₂ * y₁' - y₂' * y₁`, the convention of `Polynomial.wronskian`.

## Main results

* `TauCeti.schwarzian_eq_neg_two_mul_iteratedDeriv_two_div` -- if `u ^ 2 * w' = c ≠ 0` near
  `x`, then `S(w) = -2 * u'' / u` at `x`.
* `TauCeti.iteratedDeriv_two_add_schwarzian_div_two_mul_eq_zero` and
  `TauCeti.iteratedDeriv_two_mul_add_schwarzian_div_two_mul_eq_zero` -- `u` and `w * u` solve
  `y'' + S(w) / 2 * y = 0`.
* `TauCeti.mul_deriv_mul_sub_deriv_mul_mul_eq` -- their Wronskian is `c`.
* `TauCeti.exists_schwarzian_differentialEquation` -- a locally univalent holomorphic germ is the
  quotient of two solutions of `y'' + S(w) / 2 * y = 0` with Wronskian one.
* `TauCeti.schwarzian_div_eq_two_mul` -- the quotient of two solutions of `y'' + Q * y = 0` with
  nonzero Wronskian has Schwarzian derivative `2 * Q`.

## References

* O. Lehto, *Univalent Functions and Teichmüller Spaces*, Chapter II, Section 1.
* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), equation (5.1.11).
-/

public section

namespace TauCeti

open Filter Topology

variable {w u : ℂ → ℂ} {c x : ℂ}

/-- A function whose derivative is `c / u ^ 2` near `x`, for a nonzero constant `c`, is
holomorphic at `x`: its derivative does not vanish near `x`. -/
private lemma analyticAt_of_sq_mul_deriv_eq (hc : c ≠ 0)
    (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) : AnalyticAt ℂ w x := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [h] with z hz
  refine differentiableAt_of_deriv_ne_zero fun h0 => hc ?_
  rw [← hz, h0, mul_zero]

/-- If `u ^ 2 * w' = c` near `x` for a nonzero constant `c`, then `u x ≠ 0`. -/
private lemma ne_zero_of_sq_mul_deriv_eq (hc : c ≠ 0)
    (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) : u x ≠ 0 :=
  fun h0 => hc (by simpa [h0] using h.self_of_nhds.symm)

/-- **The Schwarzian through a reciprocal square root of the derivative.**  If `u` is holomorphic
at `x` and `u ^ 2 * w' = c` near `x` for a nonzero constant `c`, then
`S(w) = -2 * u'' / u` at `x`. -/
theorem schwarzian_eq_neg_two_mul_iteratedDeriv_two_div (hu : AnalyticAt ℂ u x) (hc : c ≠ 0)
    (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) :
    schwarzian w x = -2 * iteratedDeriv 2 u x / u x := by
  have hux : u x ≠ 0 := ne_zero_of_sq_mul_deriv_eq hc h
  have hne : ∀ᶠ z in 𝓝 x, u z ≠ 0 := hu.continuousAt.eventually_ne hux
  -- Near `x`, the derivative of `w` is `c / u ^ 2`.
  have hd : deriv w =ᶠ[𝓝 x] fun z => c * (u z ^ 2)⁻¹ := by
    filter_upwards [h, hne] with z hz hz0
    rw [← hz]
    field_simp
  have hd1 : deriv (fun z => c * (u z ^ 2)⁻¹) =ᶠ[𝓝 x]
      fun z => -2 * c * deriv u z / u z ^ 3 := by
    filter_upwards [hu.eventually_analyticAt, hne] with z hz hz0
    rw [(((hz.differentiableAt.hasDerivAt.fun_pow 2).fun_inv (pow_ne_zero 2 hz0)).const_mul
      c).deriv]
    field_simp
    ring
  have hd2 : deriv (fun z => -2 * c * deriv u z / u z ^ 3) x =
      (-2 * c * deriv (deriv u) x * u x ^ 3 -
        -2 * c * deriv u x * (3 * u x ^ 2 * deriv u x)) / (u x ^ 3) ^ 2 := by
    have h3 : HasDerivAt (fun z => u z ^ 3) (3 * u x ^ 2 * deriv u x) x :=
      (hu.differentiableAt.hasDerivAt.fun_pow 3).congr_deriv (by norm_num)
    exact (((hu.deriv.differentiableAt.hasDerivAt).const_mul (-2 * c)).fun_div h3
      (pow_ne_zero 3 hux)).deriv
  have h2w : iteratedDeriv 2 w x = -2 * c * deriv u x / u x ^ 3 := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hd.deriv_eq, hd1.eq_of_nhds]
  have h3w : iteratedDeriv 3 w x = deriv (deriv (fun z => c * (u z ^ 2)⁻¹)) x := by
    rw [iteratedDeriv_succ', hd.iteratedDeriv_eq, iteratedDeriv_succ, iteratedDeriv_one]
  rw [schwarzian_def, h2w, h3w, hd1.deriv_eq, hd2, hd.eq_of_nhds, iteratedDeriv_succ,
    iteratedDeriv_one]
  field_simp
  ring

/-- **The reciprocal square root of the derivative solves the Schwarzian equation.**  If `u` is
holomorphic at `x` and `u ^ 2 * w' = c` near `x` for a nonzero constant `c`, then
`u'' + S(w) / 2 * u = 0` at `x`.  For `c = 1`, `u` is `1 / √w'`. -/
theorem iteratedDeriv_two_add_schwarzian_div_two_mul_eq_zero (hu : AnalyticAt ℂ u x)
    (hc : c ≠ 0) (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) :
    iteratedDeriv 2 u x + schwarzian w x / 2 * u x = 0 := by
  have hux : u x ≠ 0 := ne_zero_of_sq_mul_deriv_eq hc h
  rw [schwarzian_eq_neg_two_mul_iteratedDeriv_two_div hu hc h]
  field_simp
  ring

/-- **The second solution of the Schwarzian equation.**  If `u` is holomorphic at `x` and
`u ^ 2 * w' = c` near `x` for a nonzero constant `c`, then `v = w * u` satisfies
`v'' + S(w) / 2 * v = 0` at `x`.  For `c = 1`, `v` is `w / √w'`. -/
theorem iteratedDeriv_two_mul_add_schwarzian_div_two_mul_eq_zero (hu : AnalyticAt ℂ u x)
    (hc : c ≠ 0) (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) :
    iteratedDeriv 2 (fun z => w z * u z) x + schwarzian w x / 2 * (w x * u x) = 0 := by
  have hw := analyticAt_of_sq_mul_deriv_eq hc h
  have hux : u x ≠ 0 := ne_zero_of_sq_mul_deriv_eq hc h
  -- Differentiating `u ^ 2 * w' = c` gives `2 * u * u' * w' + u ^ 2 * w'' = 0` at `x`.
  have hc' : 2 * u x * deriv u x * deriv w x + u x ^ 2 * deriv (deriv w) x = 0 := by
    have hconst : (fun z => u z ^ 2 * deriv w z) =ᶠ[𝓝 x] fun _ => c := h
    have hder := ((hu.differentiableAt.hasDerivAt.fun_pow 2).fun_mul
      hw.deriv.differentiableAt.hasDerivAt).deriv
    rw [hconst.deriv_eq, deriv_const] at hder
    rw [hder]
    push_cast
    ring
  -- The Leibniz rule for `(w * u)''`.
  have hv : iteratedDeriv 2 (fun z => w z * u z) x =
      deriv (deriv w) x * u x + 2 * deriv w x * deriv u x + w x * deriv (deriv u) x := by
    rw [iteratedDeriv_fun_mul hw.contDiffAt hu.contDiffAt]
    simp [Finset.sum_range_succ, iteratedDeriv_succ]
    ring
  have hsol := iteratedDeriv_two_add_schwarzian_div_two_mul_eq_zero hu hc h
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hsol
  rw [hv]
  have hw2 : deriv (deriv w) x * u x + 2 * deriv w x * deriv u x = 0 := by
    have hmul : u x * (deriv (deriv w) x * u x + 2 * deriv w x * deriv u x) = 0 := by
      linear_combination hc'
    exact (mul_eq_zero.mp hmul).resolve_left hux
  linear_combination hw2 + w x * hsol

/-- **The Wronskian of the two solutions of the Schwarzian equation.**  If `u` is differentiable
at `x` and `u ^ 2 * w' = c` near `x` for a nonzero constant `c`, then the Wronskian
`u * (w * u)' - u' * (w * u)` of `(u, w * u)` equals `c` at `x`. -/
theorem mul_deriv_mul_sub_deriv_mul_mul_eq (hu : DifferentiableAt ℂ u x) (hc : c ≠ 0)
    (h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = c) :
    u x * deriv (fun z => w z * u z) x - deriv u x * (w x * u x) = c := by
  have hw := analyticAt_of_sq_mul_deriv_eq hc h
  rw [(hw.differentiableAt.hasDerivAt.fun_mul hu.hasDerivAt).deriv,
    ← h.self_of_nhds]
  ring

/-- **The Schwarzian differential equation.**  A holomorphic germ `w` with `w' x ≠ 0` is, near
`x`, the quotient `v₁ / v₂` of two holomorphic solutions of `y'' + S(w) / 2 * y = 0` whose
Wronskian `v₂ * v₁' - v₂' * v₁` is one.  One may take `v₂ = 1 / √w'` and `v₁ = w / √w'` for a
holomorphic branch of `√w'` near `x`. -/
theorem exists_schwarzian_differentialEquation (hw : AnalyticAt ℂ w x) (hwx : deriv w x ≠ 0) :
    ∃ v₁ v₂ : ℂ → ℂ, AnalyticAt ℂ v₁ x ∧ AnalyticAt ℂ v₂ x ∧
      (∀ᶠ z in 𝓝 x, iteratedDeriv 2 v₁ z + schwarzian w z / 2 * v₁ z = 0) ∧
      (∀ᶠ z in 𝓝 x, iteratedDeriv 2 v₂ z + schwarzian w z / 2 * v₂ z = 0) ∧
      (∀ᶠ z in 𝓝 x, v₂ z * deriv v₁ z - deriv v₂ z * v₁ z = 1) ∧
      ∀ᶠ z in 𝓝 x, v₁ z / v₂ z = w z := by
  -- A holomorphic square root of `1 / w'` near `x`.
  have hA : AnalyticAt ℂ (fun z => (deriv w z)⁻¹) x := hw.deriv.inv hwx
  obtain ⟨u, hu, hu2⟩ := (exists_eventuallyEq_pow_iff_dvd hA two_ne_zero).2 (by
    rw [hA.analyticOrderAt_eq_zero.2 (inv_ne_zero hwx)]
    exact dvd_zero _)
  have hne : ∀ᶠ z in 𝓝 x, deriv w z ≠ 0 := hw.deriv.continuousAt.eventually_ne hwx
  have h : ∀ᶠ z in 𝓝 x, u z ^ 2 * deriv w z = 1 := by
    filter_upwards [hu2, hne] with z hz hz0
    rw [← hz, inv_mul_cancel₀ hz0]
  -- Each hypothesis is an open condition, so the pointwise results hold near `x`.
  have hloc : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ u z ∧ ∀ᶠ y in 𝓝 z, u y ^ 2 * deriv w y = 1 :=
    hu.eventually_analyticAt.and h.eventually_nhds
  have hw' := analyticAt_of_sq_mul_deriv_eq one_ne_zero h
  refine ⟨fun z => w z * u z, u, hw'.mul hu, hu, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hloc] with z hz
    exact iteratedDeriv_two_mul_add_schwarzian_div_two_mul_eq_zero hz.1 one_ne_zero hz.2
  · filter_upwards [hloc] with z hz
    exact iteratedDeriv_two_add_schwarzian_div_two_mul_eq_zero hz.1 one_ne_zero hz.2
  · filter_upwards [hloc] with z hz
    exact mul_deriv_mul_sub_deriv_mul_mul_eq hz.1.differentiableAt one_ne_zero hz.2
  · filter_upwards [hloc] with z hz
    have hz0 : u z ≠ 0 := ne_zero_of_sq_mul_deriv_eq one_ne_zero hz.2
    field_simp

/-- **Quotients of solutions have Schwarzian `2 * Q`.**  If `y₁` and `y₂` are holomorphic at
`x`, both solve `y'' + Q * y = 0` near `x`, their Wronskian `y₂ * y₁' - y₂' * y₁` is nonzero at
`x` and `y₂ x ≠ 0`, then `S(y₁ / y₂) = 2 * Q` at `x`.  No regularity of `Q` is assumed. -/
theorem schwarzian_div_eq_two_mul {y₁ y₂ Q : ℂ → ℂ} (h₁ : AnalyticAt ℂ y₁ x)
    (h₂ : AnalyticAt ℂ y₂ x) (hy₁ : ∀ᶠ z in 𝓝 x, iteratedDeriv 2 y₁ z + Q z * y₁ z = 0)
    (hy₂ : ∀ᶠ z in 𝓝 x, iteratedDeriv 2 y₂ z + Q z * y₂ z = 0)
    (hW : y₂ x * deriv y₁ x - deriv y₂ x * y₁ x ≠ 0) (hx : y₂ x ≠ 0) :
    schwarzian (fun z => y₁ z / y₂ z) x = 2 * Q x := by
  set W : ℂ → ℂ := fun z => y₂ z * deriv y₁ z - deriv y₂ z * y₁ z
  -- The Wronskian has derivative `y₂ * y₁'' - y₂'' * y₁ = 0` near `x`, so it is constant there.
  have hloc : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ y₁ z ∧ AnalyticAt ℂ y₂ z ∧
      iteratedDeriv 2 y₁ z + Q z * y₁ z = 0 ∧ iteratedDeriv 2 y₂ z + Q z * y₂ z = 0 ∧
      y₂ z ≠ 0 :=
    h₁.eventually_analyticAt.and <| h₂.eventually_analyticAt.and <| hy₁.and <| hy₂.and <|
      h₂.continuousAt.eventually_ne hx
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hloc
  have hWd : ∀ z ∈ Metric.ball x r, HasDerivAt W 0 z := by
    intro z hz
    obtain ⟨h₁z, h₂z, hy₁z, hy₂z, -⟩ := hball z hz
    rw [iteratedDeriv_succ, iteratedDeriv_one] at hy₁z hy₂z
    refine ((h₂z.differentiableAt.hasDerivAt.fun_mul h₁z.deriv.differentiableAt.hasDerivAt).sub
      (h₂z.deriv.differentiableAt.hasDerivAt.fun_mul
        h₁z.differentiableAt.hasDerivAt)).congr_deriv ?_
    linear_combination y₂ z * hy₁z - y₁ z * hy₂z
  have hWc : ∀ z ∈ Metric.ball x r, W z = W x := fun z hz =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
      (fun y hy => (hWd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hWd y hy).deriv) hz (Metric.mem_ball_self hr)
  -- Hence `y₂ ^ 2 * (y₁ / y₂)' = W x` near `x`, and the reciprocal-square-root identity applies.
  have h : ∀ᶠ z in 𝓝 x, y₂ z ^ 2 * deriv (fun z => y₁ z / y₂ z) z = W x := by
    filter_upwards [Metric.ball_mem_nhds x hr] with z hz
    obtain ⟨h₁z, h₂z, -, -, hz0⟩ := hball z hz
    rw [(h₁z.differentiableAt.hasDerivAt.fun_div h₂z.differentiableAt.hasDerivAt hz0).deriv,
      ← hWc z hz]
    field_simp
    ring
  have hQ := hy₂.self_of_nhds
  rw [schwarzian_eq_neg_two_mul_iteratedDeriv_two_div h₂ hW h, div_eq_iff hx]
  linear_combination -2 * hQ

end TauCeti
