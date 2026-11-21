/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Complex.Conformal.Schwarzian
public import TauCeti.Analysis.ODE.Complex.Wronskian
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The Schwarzian differential equation

For a holomorphic function `w` without critical points on an open set `U`, the
**Schwarzian equation** of `w` is the second-order linear equation
`y'' + (1 / 2) * S(w) * y = 0` on `U`, where `S(w)` is the Schwarzian derivative
`TauCeti.schwarzian w`. The two directions of the classical correspondence between this equation
and `w` are:

* if `s` is a holomorphic square root of `w'` on `U`, then `v₁ = w / s` and `v₂ = 1 / s` solve the
  Schwarzian equation of `w`, their Wronskian `v₁ v₂' - v₁' v₂` is `-1`, and `w = v₁ / v₂`;
* conversely, if `y₁, y₂` solve an equation `y'' + Q y = 0` and their Wronskian does not vanish,
  then `S(y₁ / y₂) = 2 Q` wherever `y₂ ≠ 0`.

Since a branch change of the inverse of a holomorphic covering is a Möbius map, and the Schwarzian
is Möbius invariant, these turn an explicit formula for the Schwarzian of such an inverse into a
linear differential equation whose solution quotients recover the inverse.

## Main definitions

* `TauCeti.LinearEquation.ofSchwarzian`: the equation `y'' + (1 / 2) * S(w) * y = 0`.

## Main results

* `TauCeti.LinearEquation.IsSolution.schwarzian_div`: the Schwarzian of `y₁ / y₂` is `2 Q` at each
  point where the Wronskian of the solutions `y₁, y₂` of `y'' + Q y = 0` is nonzero and `y₂ ≠ 0`.
* `TauCeti.LinearEquation.isSolution_ofSchwarzian_inv` and
  `TauCeti.LinearEquation.isSolution_ofSchwarzian_div`: `1 / s` and `w / s` solve the Schwarzian
  equation of `w` when `s ^ 2 = w'`.
* `TauCeti.LinearEquation.exists_isSolution_ofSchwarzian`: on a simply connected domain, `w` is the
  quotient of two solutions of its Schwarzian equation with Wronskian `-1`.

## References

* O. Lehto, *Univalent Functions and Teichmüller Spaces*, Chapter II, Section 1.
* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), equation (5.1.11).
-/

public noncomputable section

open Set TopologicalSpace Filter Topology

namespace TauCeti

namespace LinearEquation

variable {U : Opens ℂ}

/-! ### Quotients of solutions of `y'' + Q y = 0` -/

section Quotient

variable {E : LinearEquation U 2} {y₁ y₂ : ℂ → ℂ} {z : ℂ}

/-- **The Schwarzian of a quotient of solutions.** Let `y₁, y₂` solve a second-order equation
`y'' + Q y = 0` without first-derivative term. If their Wronskian `y₁ y₂' - y₁' y₂` is nonzero at
`z` and `y₂ z ≠ 0`, then the Schwarzian derivative of `y₁ / y₂` at `z` is `2 Q(z)`. -/
theorem IsSolution.schwarzian_div (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂)
    (hE : E.coeff 1 = 0) (hz : z ∈ U) (hW : y₁ z * deriv y₂ z - deriv y₁ z * y₂ z ≠ 0)
    (h₂ : y₂ z ≠ 0) :
    schwarzian (fun x ↦ y₁ x / y₂ x) z = 2 * HolomorphicFunctions.extend (E.coeff 0) z := by
  set W := fun x ↦ y₁ x * deriv y₂ x - deriv y₁ x * y₂ x with hWdef
  have hy₂z := hy₂.analyticOnNhd z hz
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball z r, x ∈ U ∧ y₂ x ≠ 0 :=
    Metric.eventually_nhds_iff_ball.mp
      ((U.isOpen.eventually_mem hz).and (hy₂z.continuousAt.eventually_ne h₂))
  have hrz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hW' (x : ℂ) (hx : x ∈ U) : HasDerivAt W 0 x := by
    simpa [hE] using hy₁.hasDerivAt_wronskian hy₂ hx
  -- By Abel's identity the Wronskian is constant near `z`.
  have hWc (x : ℂ) (hx : x ∈ Metric.ball z r) : W x = W z :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
      (fun x hx ↦ (hW' x (hball x hx).1).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hW' x (hball x hx).1).deriv) hx hrz
  -- Hence `(y₁ / y₂)' = -W(z) / y₂ ^ 2` near `z`.
  have hd₁ : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x ↦ y₁ x / y₂ x) (-W z / y₂ x ^ 2) x := by
    filter_upwards [Metric.ball_mem_nhds z hr] with x hx
    have hxU := (hball x hx).1
    have h₁x := hy₁.analyticOnNhd x hxU
    have h₂x := hy₂.analyticOnNhd x hxU
    convert h₁x.differentiableAt.hasDerivAt.div h₂x.differentiableAt.hasDerivAt (hball x hx).2
      using 1
    rw [← hWc x hx, hWdef]
    ring
  have hd₂ : ∀ᶠ x in 𝓝 z, HasDerivAt (fun x ↦ -W z / y₂ x ^ 2)
      (2 * W z * deriv y₂ x / y₂ x ^ 3) x := by
    filter_upwards [Metric.ball_mem_nhds z hr] with x hx
    have h₂x := (hy₂.analyticOnNhd x (hball x hx).1).differentiableAt.hasDerivAt
    convert (hasDerivAt_const x (-W z)).div (h₂x.pow 2) (pow_ne_zero 2 (hball x hx).2) using 1
    simp only [Pi.pow_apply]
    field_simp [(hball x hx).2]
    ring
  have hd₃ : HasDerivAt (fun x ↦ 2 * W z * deriv y₂ x / y₂ x ^ 3)
      (2 * W z * (deriv (deriv y₂) z * y₂ z ^ 3 - deriv y₂ z * (3 * y₂ z ^ 2 * deriv y₂ z)) /
        (y₂ z ^ 3) ^ 2) z := by
    convert (hy₂z.deriv.differentiableAt.hasDerivAt.const_mul (2 * W z)).div
      (hy₂z.differentiableAt.hasDerivAt.pow 3) (pow_ne_zero 3 h₂) using 1
    simp only [Pi.pow_apply]
    push_cast
    ring
  rw [schwarzian_eq_of_deriv_eventuallyEq (hd₁.mono fun x hx ↦ hx.deriv),
    Filter.EventuallyEq.deriv_eq (hd₂.mono fun x hx ↦ hx.deriv), hd₃.deriv, hd₂.self_of_nhds.deriv,
    hy₂.deriv_deriv_eq hz, hE]
  simp only [HolomorphicFunctions.extend_zero, Pi.zero_apply]
  have hWz : W z ≠ 0 := hW
  field_simp
  ring

end Quotient

/-! ### The Schwarzian equation -/

section Schwarzian

variable {w s y y₁ y₂ : ℂ → ℂ} {z : ℂ}

/-- The **Schwarzian equation** `y'' + (1 / 2) * S(w) * y = 0` of a function `w` holomorphic and
without critical points on `U`, where `S(w)` is the Schwarzian derivative `TauCeti.schwarzian w`. -/
def ofSchwarzian (w : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w U) (hw' : ∀ z ∈ U, deriv w z ≠ 0) :
    LinearEquation U 2 where
  order_pos := two_pos
  coeff := ![HolomorphicFunctions.of U (fun z ↦ schwarzian w z / 2)
    ((hw.schwarzian hw').differentiableOn.div_const 2), 0]

/-- A square root of `w'` does not vanish where `w'` does not. -/
private theorem ne_zero_of_sq_eq_deriv (hw' : ∀ z ∈ U, deriv w z ≠ 0)
    (hsw : EqOn (fun z ↦ s z ^ 2) (deriv w) U) (hz : z ∈ U) : s z ≠ 0 :=
  fun h ↦ hw' z hz (by simp [← hsw hz, h])

private theorem eventually_hasDerivAt_inv (hw' : ∀ z ∈ U, deriv w z ≠ 0)
    (hs : AnalyticOnNhd ℂ s U) (hsw : EqOn (fun z ↦ s z ^ 2) (deriv w) U) (hz : z ∈ U) :
    ∀ᶠ x in 𝓝 z, HasDerivAt (fun x ↦ (s x)⁻¹) (-deriv s x / s x ^ 2) x :=
  (U.isOpen.eventually_mem hz).mono fun x hx ↦
    (hs x hx).differentiableAt.hasDerivAt.inv (ne_zero_of_sq_eq_deriv hw' hsw hx)

private theorem eventually_hasDerivAt_div (hw : AnalyticOnNhd ℂ w U)
    (hw' : ∀ z ∈ U, deriv w z ≠ 0) (hs : AnalyticOnNhd ℂ s U)
    (hsw : EqOn (fun z ↦ s z ^ 2) (deriv w) U) (hz : z ∈ U) :
    ∀ᶠ x in 𝓝 z, HasDerivAt (fun x ↦ w x / s x) ((s x ^ 3 - w x * deriv s x) / s x ^ 2) x :=
  (U.isOpen.eventually_mem hz).mono fun x hx ↦ by
    convert (hw x hx).differentiableAt.hasDerivAt.div (hs x hx).differentiableAt.hasDerivAt
      (ne_zero_of_sq_eq_deriv hw' hsw hx) using 1
    rw [← hsw hx]
    ring

variable {hw : AnalyticOnNhd ℂ w U} {hw' : ∀ z ∈ U, deriv w z ≠ 0}

/-- The Schwarzian equation has no first-derivative term. -/
@[simp]
theorem ofSchwarzian_coeff_one : (ofSchwarzian w hw hw').coeff 1 = 0 := (rfl)

/-- The zeroth-order coefficient of the Schwarzian equation of `w` is `S(w) / 2` on the
domain. -/
theorem extend_ofSchwarzian_coeff_zero (hz : z ∈ U) :
    HolomorphicFunctions.extend ((ofSchwarzian w hw hw').coeff 0) z = schwarzian w z / 2 :=
  HolomorphicFunctions.extend_of _ hz

/-- Solutions of the Schwarzian equation of `w` are the functions analytic on the domain that
satisfy `y'' + (1 / 2) * S(w) * y = 0` there. -/
theorem isSolution_ofSchwarzian_iff :
    (ofSchwarzian w hw hw').IsSolution y ↔
      AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U, deriv (deriv y) z + schwarzian w z / 2 * y z = 0 := by
  rw [isSolution_iff_deriv_deriv]
  refine and_congr_right fun _ ↦ forall₂_congr fun z hz ↦ ?_
  simp only [extend_ofSchwarzian_coeff_zero hz, ofSchwarzian_coeff_one,
    HolomorphicFunctions.extend_zero, Pi.zero_apply, zero_mul, add_zero]

/-- The quotient of two solutions of the Schwarzian equation of `w` with nonvanishing Wronskian
has the same Schwarzian derivative as `w`, wherever its denominator does not vanish. -/
theorem IsSolution.schwarzian_div_ofSchwarzian (hy₁ : (ofSchwarzian w hw hw').IsSolution y₁)
    (hy₂ : (ofSchwarzian w hw hw').IsSolution y₂) (hz : z ∈ U)
    (hW : y₁ z * deriv y₂ z - deriv y₁ z * y₂ z ≠ 0) (h₂ : y₂ z ≠ 0) :
    schwarzian (fun x ↦ y₁ x / y₂ x) z = schwarzian w z := by
  rw [hy₁.schwarzian_div hy₂ ofSchwarzian_coeff_one hz hW h₂, extend_ofSchwarzian_coeff_zero hz]
  ring

/-- **The reciprocal square root of `w'` solves the Schwarzian equation.** If `s` is holomorphic
on `U` with `s ^ 2 = w'` there, then `1 / s` solves `y'' + (1 / 2) * S(w) * y = 0` on `U`. -/
theorem isSolution_ofSchwarzian_inv (hs : AnalyticOnNhd ℂ s U)
    (hsw : EqOn (fun z ↦ s z ^ 2) (deriv w) U) :
    (ofSchwarzian w hw hw').IsSolution fun z ↦ (s z)⁻¹ := by
  rw [isSolution_ofSchwarzian_iff]
  refine ⟨fun z hz ↦ (hs z hz).inv (ne_zero_of_sq_eq_deriv hw' hsw hz),
    fun z hz ↦ ?_⟩
  have hs0 := ne_zero_of_sq_eq_deriv hw' hsw hz
  have hsz := hs z hz
  have hd₂ : HasDerivAt (fun x ↦ -deriv s x / s x ^ 2)
      ((-deriv (deriv s) z * s z ^ 2 - -deriv s z * (2 * s z * deriv s z)) / (s z ^ 2) ^ 2) z := by
    convert hsz.deriv.differentiableAt.hasDerivAt.neg.div
      (hsz.differentiableAt.hasDerivAt.pow 2) (pow_ne_zero 2 hs0) using 1
    simp only [Pi.pow_apply, Pi.neg_apply]
    push_cast
    ring
  rw [Filter.EventuallyEq.deriv_eq
      ((eventually_hasDerivAt_inv hw' hs hsw hz).mono fun x hx ↦ hx.deriv),
    hd₂.deriv, schwarzian_eq_of_sq_eq_deriv
      ((U.isOpen.eventually_mem hz).mono fun x hx ↦ ⟨hs x hx, hsw hx⟩)]
  field_simp
  ring

/-- **The quotient of `w` by a square root of `w'` solves the Schwarzian equation.** If `s` is
holomorphic on `U` with `s ^ 2 = w'` there, then `w / s` solves
`y'' + (1 / 2) * S(w) * y = 0` on `U`. -/
theorem isSolution_ofSchwarzian_div (hs : AnalyticOnNhd ℂ s U)
    (hsw : EqOn (fun z ↦ s z ^ 2) (deriv w) U) :
    (ofSchwarzian w hw hw').IsSolution fun z ↦ w z / s z := by
  rw [isSolution_ofSchwarzian_iff]
  refine ⟨fun z hz ↦ (hw z hz).div (hs z hz) (ne_zero_of_sq_eq_deriv hw' hsw hz),
    fun z hz ↦ ?_⟩
  have hs0 := ne_zero_of_sq_eq_deriv hw' hsw hz
  have hsz := hs z hz
  have hd₂ : HasDerivAt (fun x ↦ (s x ^ 3 - w x * deriv s x) / s x ^ 2)
      (((3 * s z ^ 2 * deriv s z - (deriv w z * deriv s z + w z * deriv (deriv s) z)) *
        s z ^ 2 - (s z ^ 3 - w z * deriv s z) * (2 * s z * deriv s z)) / (s z ^ 2) ^ 2) z := by
    convert ((hsz.differentiableAt.hasDerivAt.pow 3).sub
      ((hw z hz).differentiableAt.hasDerivAt.mul hsz.deriv.differentiableAt.hasDerivAt)).div
      (hsz.differentiableAt.hasDerivAt.pow 2) (pow_ne_zero 2 hs0) using 1
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
    push_cast
    ring
  rw [Filter.EventuallyEq.deriv_eq
      ((eventually_hasDerivAt_div hw hw' hs hsw hz).mono fun x hx ↦ hx.deriv),
    hd₂.deriv, schwarzian_eq_of_sq_eq_deriv
      ((U.isOpen.eventually_mem hz).mono fun x hx ↦ ⟨hs x hx, hsw hx⟩), ← hsw hz]
  field_simp
  ring

/-- **A locally univalent function is a quotient of solutions of its Schwarzian equation.**
On a simply connected domain `U`, if `w` is holomorphic with `w' ≠ 0`, then there are solutions
`v₁, v₂` of `y'' + (1 / 2) * S(w) * y = 0` on `U` with `v₂ ≠ 0`, `w = v₁ / v₂` and Wronskian
`v₁ v₂' - v₁' v₂ = -1` on `U`; namely `v₁ = w / s` and `v₂ = 1 / s` for a holomorphic square root
`s` of `w'`. In particular `v₁` and `v₂` are linearly independent solutions
(`TauCeti.LinearEquation.IsSolution.linearIndependent_of_wronskian_ne_zero`). -/
theorem exists_isSolution_ofSchwarzian (hU : IsSimplyConnected (U : Set ℂ)) :
    ∃ v₁ v₂ : ℂ → ℂ, (ofSchwarzian w hw hw').IsSolution v₁ ∧
      (ofSchwarzian w hw hw').IsSolution v₂ ∧
        ∀ z ∈ U, v₂ z ≠ 0 ∧ v₁ z / v₂ z = w z ∧ v₁ z * deriv v₂ z - deriv v₁ z * v₂ z = -1 := by
  obtain ⟨s, hsd, hsw⟩ := exists_differentiableOn_pow_eq hU U.isOpen hw.deriv.differentiableOn
    (by rintro ⟨z, hz, h⟩; exact hw' z hz h) two_ne_zero
  have hs := hsd.analyticOnNhd U.isOpen
  refine ⟨fun z ↦ w z / s z, fun z ↦ (s z)⁻¹, isSolution_ofSchwarzian_div hs hsw,
    isSolution_ofSchwarzian_inv hs hsw, fun z hz ↦ ?_⟩
  have hs0 := ne_zero_of_sq_eq_deriv hw' hsw hz
  refine ⟨inv_ne_zero hs0, by field_simp, ?_⟩
  rw [(eventually_hasDerivAt_inv hw' hs hsw hz).self_of_nhds.deriv,
    (eventually_hasDerivAt_div hw hw' hs hsw hz).self_of_nhds.deriv]
  field_simp
  ring

end Schwarzian

end LinearEquation

end TauCeti
