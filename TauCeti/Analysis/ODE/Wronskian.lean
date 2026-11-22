/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Wronskian of a scalar second-order linear equation

For two solutions `φ`, `ψ` of the equation `f'' = q f` over `ℝ` or `ℂ`, without a first-order
term, the Wronskian `ψ φ' - φ ψ'` has derivative `ψ q φ - φ q ψ = 0`, so it is constant. For the
fundamental pair with `φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1` it is identically one.

More generally, on any open preconnected subset `U` of `ℝ` or `ℂ`, if two solutions `w₁`, `w₂` of
`w'' + f w' + g w = 0` are paired with an integrating factor `E` satisfying `E' = f E` on `U`,
then `E (w₁ w₂' - w₁' w₂)` has zero derivative and is constant on `U` (Abel–Liouville identity).

## Main results

* `TauCeti.secondOrder_operator_add_const_mul`: pointwise linearity of `w'' + f w' + g w` over any
  nontrivially normed field.
* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `TauCeti.mul_wronskian_eq_of_hasDerivAt`: Abel–Liouville constancy of `E (w₁ w₂' - w₁' w₂)` on
  an open preconnected domain in `ℝ` or `ℂ`.
-/

public section

open scoped Topology

namespace TauCeti

/-- Pointwise linearity `L(ψ + c' Φ) = L(ψ) + c' L(Φ)` for the second-order linear differential
operator `L(w) = w'' + f w' + g w` under local differentiability assumptions near `z`. -/
theorem secondOrder_operator_add_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f g ψ Φ : 𝕜 → 𝕜} {c' z : 𝕜}
    (hψ₁ : ∀ᶠ w in nhds z, DifferentiableAt 𝕜 ψ w)
    (hΦ₁ : ∀ᶠ w in nhds z, DifferentiableAt 𝕜 Φ w)
    (hψ₂ : DifferentiableAt 𝕜 (deriv ψ) z)
    (hΦ₂ : DifferentiableAt 𝕜 (deriv Φ) z) :
    (deriv (deriv fun w ↦ ψ w + c' * Φ w) z + f z * deriv (fun w ↦ ψ w + c' * Φ w) z +
        g z * (ψ z + c' * Φ z)) =
      (deriv (deriv ψ) z + f z * deriv ψ z + g z * ψ z) +
        c' * (deriv (deriv Φ) z + f z * deriv Φ z + g z * Φ z) := by
  have hd1_ev :
      deriv (fun w ↦ ψ w + c' * Φ w) =ᶠ[nhds z] fun w ↦ deriv ψ w + c' * deriv Φ w := by
    filter_upwards [hψ₁, hΦ₁] with w hwψ hwΦ
    exact ((hwψ.hasDerivAt).add ((hwΦ.hasDerivAt).const_mul c')).deriv
  have hd2 : deriv (deriv fun w ↦ ψ w + c' * Φ w) z =
      deriv (deriv ψ) z + c' * deriv (deriv Φ) z :=
    (((hψ₂.hasDerivAt).add ((hΦ₂.hasDerivAt).const_mul c')).congr_of_eventuallyEq hd1_ev).deriv
  rw [hd1_ev.self_of_nhds, hd2]
  ring

/-- **Abel–Liouville Wronskian constancy** on an open preconnected domain `U` in `ℝ` or `ℂ`: if
`w₁` and `w₂` satisfy `w'' + f w' + g w = 0` on `U` and `E` is an integrating factor with
`E' = f * E` on `U`, then `E * (w₁ * w₂' - w₁' * w₂)` is constant on `U`. -/
theorem mul_wronskian_eq_of_hasDerivAt {𝕜 : Type*} [RCLike 𝕜] {U : Set 𝕜}
    (hU : IsOpen U) (hconn : IsPreconnected U) {f g E w₁ w₁' w₂ w₂' : 𝕜 → 𝕜}
    (hE : ∀ z ∈ U, HasDerivAt E (f z * E z) z)
    (hw₁ : ∀ z ∈ U, HasDerivAt w₁ (w₁' z) z)
    (hw₁' : ∀ z ∈ U, HasDerivAt w₁' (-(f z * w₁' z + g z * w₁ z)) z)
    (hw₂ : ∀ z ∈ U, HasDerivAt w₂ (w₂' z) z)
    (hw₂' : ∀ z ∈ U, HasDerivAt w₂' (-(f z * w₂' z + g z * w₂ z)) z)
    {z₁ z₂ : 𝕜} (hz₁ : z₁ ∈ U) (hz₂ : z₂ ∈ U) :
    E z₁ * (w₁ z₁ * w₂' z₁ - w₁' z₁ * w₂ z₁) =
      E z₂ * (w₁ z₂ * w₂' z₂ - w₁' z₂ * w₂ z₂) := by
  have hderiv : ∀ z ∈ U, HasDerivAt (fun w ↦ E w * (w₁ w * w₂' w - w₁' w * w₂ w)) 0 z :=
    fun z hz ↦
      ((hE z hz).mul (((hw₁ z hz).mul (hw₂' z hz)).sub ((hw₁' z hz).mul (hw₂ z hz)))).congr_deriv
        (by dsimp; ring)
  exact hU.is_const_of_deriv_eq_zero hconn
    (fun z hz ↦ (hderiv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hderiv z hz).deriv) hz₁ hz₂

variable {𝕜 : Type*} [RCLike 𝕜] {q φ φ' ψ ψ' : 𝕜 → 𝕜}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on `ℝ` or `ℂ` is constant. -/
theorem wronskian_eq_of_hasDerivAt
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t) (t a : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  have h := mul_wronskian_eq_of_hasDerivAt (U := Set.univ) isOpen_univ isPreconnected_univ
    (f := 0) (g := -q) (E := fun _ ↦ (1 : 𝕜))
    (fun z _ ↦ (hasDerivAt_const z (1 : 𝕜)).congr_deriv (by simp only [Pi.zero_apply, zero_mul]))
    (fun z _ ↦ hψ z)
    (fun z _ ↦ (hψ' z).congr_deriv (by simp only [Pi.zero_apply, Pi.neg_apply, zero_mul,
      zero_add, neg_mul, neg_neg]))
    (fun z _ ↦ hφ z)
    (fun z _ ↦ (hφ' z).congr_deriv (by simp only [Pi.zero_apply, Pi.neg_apply, zero_mul,
      zero_add, neg_mul, neg_neg]))
    (Set.mem_univ t) (Set.mem_univ a)
  simpa only [one_mul, mul_comm (φ t), mul_comm (φ a)] using h

/-- The Wronskian `ψ φ' - φ ψ'` of the fundamental pair of solutions of `f'' = q f` at `a`, with
`φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1`, is identically one. The value `ψ'(a)` is irrelevant,
since it is multiplied by `φ(a) = 0`. -/
theorem wronskian_eq_one_of_hasDerivAt {a : 𝕜}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (t : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = 1 := by
  rw [wronskian_eq_of_hasDerivAt hφ hφ' hψ hψ' t a, hφa, hφ'a, hψa]
  ring

end TauCeti
