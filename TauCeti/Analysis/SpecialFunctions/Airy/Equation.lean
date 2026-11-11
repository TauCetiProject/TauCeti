/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Airy's equation

The Airy functions `Ai` and `Bi` solve Airy's equation `w'' = z w`, their Wronskian is `1/π`, and
every entire solution of Airy's equation is a combination of them, with coefficients given by the
values of the solution and its derivative at a single point. The logarithmic derivative of a
solution satisfies the Riccati equation `W' = z − W²`.

## Main results

* `TauCeti.deriv_airyAi`, `TauCeti.deriv_airyBi`: the derivatives as regularized `₀F₁` series;
* `TauCeti.airyAi_ode`, `TauCeti.airyBi_ode`: Airy's equation (DLMF 9.2.1);
* `TauCeti.wronskian_airyAi_airyBi`: `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7);
* `TauCeti.eq_airy_combination`: every entire solution is
  `π (w(0) Bi′(0) − w′(0) Bi(0)) Ai + π (w′(0) Ai(0) − w(0) Ai′(0)) Bi`;
* `TauCeti.eq_of_airy_ode`: two entire solutions with the same value and derivative at one point
  are equal;
* `TauCeti.hasDerivAt_deriv_div_of_airy_ode`: the Riccati form (DLMF 9.2.16).

## Implementation notes

Uniqueness is proved with Wronskians: the Wronskian of two entire solutions is constant, and
`𝒲{Ai, Bi} ≠ 0`, so no general existence and uniqueness theorem for linear ODEs is needed.

## References

* NIST Digital Library of Mathematical Functions, §9.2, <https://dlmf.nist.gov/9.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Airy/Basic/Properties.lean` and `DLMF/Bessel/Basic/RegularizedSeries.lean`.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- Differentiating `₀F₁(; b; ·)` raises its parameter by one. -/
private theorem hasDerivAt_regularizedHGFun_zero_singleton (b w : ℂ) :
    HasDerivAt (regularizedHGFun 0 {b}) (regularizedHGFun 0 {b + 1} w) w := by
  have hd := (analyticAt_regularizedHGFun_zero (b := {b}) w).differentiableAt.hasDerivAt
  convert hd using 1
  refine (hasSum_regularizedHGFun (a := 0) (b := {b + 1}) (by simp) w).unique ?_
  convert hasSum_deriv_regularizedHGFun (a := 0) (b := {b}) (by simp) w using 1
  funext n
  simp only [regularizedHGFunCoeff_zero_singleton, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_succ, mul_inv_rev]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [show b + (n + 1) = b + 1 + n by ring]
  field_simp

/-- The chain rule for `z ↦ ₀F₁(; b; z³/9)`. -/
private theorem hasDerivAt_airy_hypergeometric (b z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun 0 {b} (z ^ 3 / 9))
      (z ^ 2 / 3 * regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  have h := (hasDerivAt_regularizedHGFun_zero_singleton b (z ^ 3 / 9)).comp z
    ((hasDerivAt_pow 3 z).div_const 9)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- `3 ^ (a + 1) = 3 ^ a * 3` for complex `a`. -/
private theorem three_cpow_add_one (a : ℂ) : (3 : ℂ) ^ (a + 1) = (3 : ℂ) ^ a * 3 := by
  rw [cpow_add _ _ (by norm_num), cpow_one]

/-- The derivative of `Ai` as a combination of regularized `₀F₁` series. -/
theorem hasDerivAt_airyAi (z : ℂ) :
    HasDerivAt airyAi (-(3 : ℂ) ^ (-1 / 3 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := ((hasDerivAt_airy_hypergeometric (2 / 3) z).const_mul ((3 : ℂ) ^ (-2 / 3 : ℂ))).sub
    (((hasDerivAt_id z).mul (hasDerivAt_airy_hypergeometric (4 / 3) z)).const_mul
      ((3 : ℂ) ^ (-4 / 3 : ℂ)))
  simp only [Pi.sub_def, Pi.mul_def, id] at h
  rw [funext airyAi_def]
  convert h using 1
  · ext w
    ring
  · rw [regularizedHGFun_zero_singleton_eq_mul_add_mul (1 / 3 : ℂ),
      show (-1 / 3 : ℂ) = -4 / 3 + 1 by norm_num, three_cpow_add_one]
    norm_num
    ring

/-- The derivative of `Bi` as a combination of regularized `₀F₁` series. -/
theorem hasDerivAt_airyBi (z : ℂ) :
    HasDerivAt airyBi ((3 : ℂ) ^ (1 / 6 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-1 / 6 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := ((hasDerivAt_airy_hypergeometric (2 / 3) z).const_mul ((3 : ℂ) ^ (-1 / 6 : ℂ))).add
    (((hasDerivAt_id z).mul (hasDerivAt_airy_hypergeometric (4 / 3) z)).const_mul
      ((3 : ℂ) ^ (-5 / 6 : ℂ)))
  simp only [Pi.add_def, Pi.mul_def, id] at h
  rw [funext airyBi_def]
  convert h using 1
  · ext w
    ring
  · rw [regularizedHGFun_zero_singleton_eq_mul_add_mul (1 / 3 : ℂ),
      show (1 / 6 : ℂ) = -5 / 6 + 1 by norm_num, three_cpow_add_one]
    norm_num
    ring

/-- The derivative of `Ai`: `Ai′(z) = −3^{−1/3} 𝐅(⅓, z³/9) + 3^{−2/3} (z²/3) 𝐅(5/3, z³/9)`. -/
theorem deriv_airyAi (z : ℂ) :
    deriv airyAi z = -(3 : ℂ) ^ (-1 / 3 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9) :=
  (hasDerivAt_airyAi z).deriv

/-- The derivative of `Bi`: `Bi′(z) = 3^{1/6} 𝐅(⅓, z³/9) + 3^{−1/6} (z²/3) 𝐅(5/3, z³/9)`. -/
theorem deriv_airyBi (z : ℂ) :
    deriv airyBi z = (3 : ℂ) ^ (1 / 6 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-1 / 6 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9) :=
  (hasDerivAt_airyBi z).deriv

/-- By the contiguous relation, `z ↦ (z²/3) ₀F₁(; 5/3; z³/9)` has derivative
`z ₀F₁(; 2/3; z³/9)`. -/
private theorem hasDerivAt_airy_second (z : ℂ) :
    HasDerivAt (fun z : ℂ => z ^ 2 / 3 * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9))
      (z * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := ((hasDerivAt_pow 2 z).div_const 3).mul (hasDerivAt_airy_hypergeometric (5 / 3) z)
  refine h.congr_deriv ?_
  rw [regularizedHGFun_zero_singleton_eq_mul_add_mul (2 / 3 : ℂ)]
  norm_num
  ring

/-- **Airy's equation** for `Ai` (DLMF 9.2.1). -/
theorem airyAi_ode (z : ℂ) : deriv^[2] airyAi z = z * airyAi z := by
  have h := ((hasDerivAt_airy_hypergeometric (1 / 3) z).const_mul (-(3 : ℂ) ^ (-1 / 3 : ℂ))).add
    ((hasDerivAt_airy_second z).const_mul ((3 : ℂ) ^ (-2 / 3 : ℂ)))
  have hfun : deriv airyAi = fun x =>
      -(3 : ℂ) ^ (-1 / 3 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (x ^ 3 / 9) +
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (x ^ 2 / 3 * regularizedHGFun 0 {(5 / 3 : ℂ)} (x ^ 3 / 9)) :=
    funext fun x => by rw [deriv_airyAi]; ring
  simp only [Pi.add_def] at h
  rw [Function.iterate_succ_apply', Function.iterate_one, hfun, h.deriv]
  · rw [airyAi_def, show (-1 / 3 : ℂ) = -4 / 3 + 1 by norm_num, three_cpow_add_one]
    norm_num
    ring

/-- **Airy's equation** for `Bi` (DLMF 9.2.1). -/
theorem airyBi_ode (z : ℂ) : deriv^[2] airyBi z = z * airyBi z := by
  have h := ((hasDerivAt_airy_hypergeometric (1 / 3) z).const_mul ((3 : ℂ) ^ (1 / 6 : ℂ))).add
    ((hasDerivAt_airy_second z).const_mul ((3 : ℂ) ^ (-1 / 6 : ℂ)))
  have hfun : deriv airyBi = fun x =>
      (3 : ℂ) ^ (1 / 6 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (x ^ 3 / 9) +
      (3 : ℂ) ^ (-1 / 6 : ℂ) * (x ^ 2 / 3 * regularizedHGFun 0 {(5 / 3 : ℂ)} (x ^ 3 / 9)) :=
    funext fun x => by rw [deriv_airyBi]; ring
  simp only [Pi.add_def] at h
  rw [Function.iterate_succ_apply', Function.iterate_one, hfun, h.deriv]
  · rw [airyBi_def, show (1 / 6 : ℂ) = -5 / 6 + 1 by norm_num, three_cpow_add_one]
    norm_num
    ring

/-- The Wronskian of two entire solutions of Airy's equation is constant. -/
theorem wronskian_eq_of_airy_ode {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z w : ℂ) :
    f z * deriv g z - deriv f z * g z = f w * deriv g w - deriv f w * g w := by
  have hd : ∀ u, HasDerivAt (fun u => f u * deriv g u - deriv f u * g u) 0 u := by
    intro u
    have h2f : HasDerivAt (deriv f) (u * f u) u := by
      rw [← hf' u]
      exact (hf.deriv u).hasDerivAt
    have h2g : HasDerivAt (deriv g) (u * g u) u := by
      rw [← hg' u]
      exact (hg.deriv u).hasDerivAt
    exact (((hf u).hasDerivAt.mul h2g).sub (h2f.mul (hg u).hasDerivAt)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) z w

/-- `Γ(1/3) Γ(2/3) = 2π/√3`, in the form `Γ(1/3) Γ(2/3) 3^{1/2} = 2π`. -/
private theorem Gamma_one_third_mul_Gamma_two_thirds :
    Gamma (1 / 3) * Gamma (2 / 3) * (3 : ℂ) ^ (1 / 2 : ℂ) = 2 * π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num] at h
  have hs : Complex.sin (π * (1 / 3)) = (3 : ℂ) ^ (1 / 2 : ℂ) / 2 := by
    rw [show (π : ℂ) * (1 / 3) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_pi_div_three, Real.sqrt_eq_rpow, ofReal_div,
      ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h3 : (3 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by simp
  rw [h, hs]
  field_simp

/-- **The Wronskian** `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7). -/
theorem wronskian_airyAi_airyBi (z : ℂ) :
    airyAi z * deriv airyBi z - deriv airyAi z * airyBi z = (π : ℂ)⁻¹ := by
  rw [wronskian_eq_of_airy_ode differentiable_airyAi differentiable_airyBi airyAi_ode airyBi_ode
    z 0, airyAi_zero, airyBi_zero, deriv_airyAi_zero, deriv_airyBi_zero]
  have hG := Gamma_one_third_mul_Gamma_two_thirds
  have h1 : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have h2 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e1 : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (1 / 6 : ℂ) * (3 : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num)]
    norm_num
  have e2 : (3 : ℂ) ^ (-1 / 3 : ℂ) * (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num)]
    norm_num
  have hs : (3 : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by simp
  have ha := eq_inv_of_mul_eq_one_left e1
  have hb := eq_inv_of_mul_eq_one_left e2
  calc _ = ((3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (1 / 6 : ℂ) +
        (3 : ℂ) ^ (-1 / 3 : ℂ) * (3 : ℂ) ^ (-1 / 6 : ℂ)) / (Gamma (1 / 3) * Gamma (2 / 3)) := by
        field_simp
        ring
    _ = (π : ℂ)⁻¹ := by
        rw [ha, hb]
        field_simp
        linear_combination -hG

/-- An entire solution of Airy's equation is determined by the Wronskians with `Ai` and `Bi` at
any one point `w`. -/
theorem eq_airy_combination_of_wronskian {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf' : ∀ z, deriv^[2] f z = z * f z) (w z : ℂ) :
    f z = π * (f w * deriv airyBi w - deriv f w * airyBi w) * airyAi z +
      π * (deriv f w * airyAi w - f w * deriv airyAi w) * airyBi z := by
  have hA := wronskian_eq_of_airy_ode hf differentiable_airyAi hf' airyAi_ode z w
  have hB := wronskian_eq_of_airy_ode hf differentiable_airyBi hf' airyBi_ode z w
  have hW := wronskian_airyAi_airyBi z
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hW' : π * (airyAi z * deriv airyBi z - deriv airyAi z * airyBi z) = 1 := by
    rw [hW, mul_inv_cancel₀ hπ]
  linear_combination (π * airyAi z) * hB - (π * airyBi z) * hA - f z * hW'

/-- **Uniqueness** (DLMF §9.2(i)): every entire solution of Airy's equation is
`π (w(0) Bi′(0) − w′(0) Bi(0)) Ai + π (w′(0) Ai(0) − w(0) Ai′(0)) Bi`. -/
theorem eq_airy_combination {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hode : ∀ z, deriv^[2] w z = z * w z) :
    w = fun z => π * (w 0 * deriv airyBi 0 - deriv w 0 * airyBi 0) * airyAi z +
      π * (deriv w 0 * airyAi 0 - w 0 * deriv airyAi 0) * airyBi z :=
  funext (eq_airy_combination_of_wronskian hw hode 0)

/-- Two entire solutions of Airy's equation with the same value and derivative at one point are
equal. -/
theorem eq_of_airy_ode {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hf' : ∀ z, deriv^[2] f z = z * f z) (hg' : ∀ z, deriv^[2] g z = z * g z) {w : ℂ}
    (h0 : f w = g w) (h1 : deriv f w = deriv g w) : f = g := by
  funext z
  rw [eq_airy_combination_of_wronskian hf hf' w z, eq_airy_combination_of_wronskian hg hg' w z,
    h0, h1]

/-- **The Riccati form** (DLMF 9.2.16): if `w` is an entire solution of Airy's equation and
`w(z) ≠ 0`, then `W = w′/w` has derivative `z − W(z)²` at `z`. -/
theorem hasDerivAt_deriv_div_of_airy_ode {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hode : ∀ z, deriv^[2] w z = z * w z) {z : ℂ} (hz : w z ≠ 0) :
    HasDerivAt (fun u => deriv w u / w u) (z - (deriv w z / w z) ^ 2) z := by
  have h2 : HasDerivAt (deriv w) (z * w z) z := by
    rw [← hode z]
    exact (hw.deriv z).hasDerivAt
  refine (h2.div (hw z).hasDerivAt hz).congr_deriv ?_
  field_simp

end TauCeti
