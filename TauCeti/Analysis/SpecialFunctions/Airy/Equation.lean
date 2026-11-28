/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.ODE.Wronskian
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Airy's equation

The Airy functions `Ai` and `Bi` solve Airy's equation `w'' = z w`, their Wronskian is `1/π`, and
every entire solution of Airy's equation is a combination of them, with coefficients given by the
values of the solution and its derivative at a single point. The logarithmic derivative of a
solution satisfies the Riccati equation `W' = z − W²`.

## Main results

* `TauCeti.deriv_airyAi`, `TauCeti.deriv_airyBi`: the derivatives as regularized `₀F₁` series;
* `TauCeti.airyAi_ode`, `TauCeti.airyBi_ode`: Airy's equation (DLMF 9.2.1);
* `TauCeti.hasDerivAt_deriv_of_airy_ode`: the derivative of an entire solution `w` has
  derivative `z w(z)`;
* `TauCeti.wronskian_airyAi_airyBi`: `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7);
* `TauCeti.eq_airy_combination`: every entire solution is
  `π (w(0) Bi′(0) − w′(0) Bi(0)) Ai + π (w′(0) Ai(0) − w(0) Ai′(0)) Bi`;
* `TauCeti.eq_of_airy_ode`: two entire solutions with the same value and derivative at one point
  are equal;
* `TauCeti.hasDerivAt_deriv_div_of_airy_ode_at`, `TauCeti.hasDerivAt_deriv_div_of_airy_ode`: the
  Riccati form (DLMF 9.2.16), pointwise and for entire solutions;
* `TauCeti.airy_ode_comp_mul_left`: if `w'' = z w` and `ν³ = 1`, then `z ↦ w(νz)` solves the same
  equation;
* `TauCeti.airy_inhomogeneous_ode_rotation`: for a cube root of unity `ν`, the rotation
  `f ↦ (z ↦ ν f(ν z))` preserves every equation `w'' = z w + c`.

## Implementation notes

Uniqueness is proved with Wronskians: the Wronskian of two entire solutions is constant
(`TauCeti.wronskian_eq_of_hasDerivAt`), and
`𝒲{Ai, Bi} ≠ 0`, so no general existence and uniqueness theorem for linear ODEs is needed.

## References

* NIST Digital Library of Mathematical Functions, §9.2, <https://dlmf.nist.gov/9.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Airy/Basic/Properties.lean` and `DLMF/Bessel/Basic/RegularizedSeries.lean`;
`TauCeti.airy_inhomogeneous_ode_rotation` is adapted from `IsAiryInhomSol.rotate` in
`DLMF/Airy/Scorer/Representations.lean`.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- The chain rule for `z ↦ ₀F₁(; b; z³/9)`. -/
private theorem hasDerivAt_airy_hypergeometric (b z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun 0 {b} (z ^ 3 / 9))
      (z ^ 2 / 3 * regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  have h := (hasDerivAt_regularizedHGFun_zero_singleton b (z ^ 3 / 9)).comp z
    ((hasDerivAt_pow 3 z).div_const 9)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- `3 ^ s = 3 ^ t * 3` when `s = t + 1`. This relates the constants `3^{-1/3}` and `3^{1/6}` of
`Ai′` and `Bi′` to the constants `3^{-4/3}` and `3^{-5/6}` of `Ai` and `Bi`. -/
private theorem three_cpow_of_eq_add_one {s t : ℂ} (h : s = t + 1) :
    (3 : ℂ) ^ s = 3 ^ t * 3 := by
  rw [h, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]

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
      three_cpow_of_eq_add_one (by norm_num : (-1 / 3 : ℂ) = -4 / 3 + 1)]
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
      three_cpow_of_eq_add_one (by norm_num : (1 / 6 : ℂ) = -5 / 6 + 1)]
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
  · rw [airyAi_def, three_cpow_of_eq_add_one (by norm_num : (-1 / 3 : ℂ) = -4 / 3 + 1)]
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
  · rw [airyBi_def, three_cpow_of_eq_add_one (by norm_num : (1 / 6 : ℂ) = -5 / 6 + 1)]
    norm_num
    ring

/-- For an entire solution `w` of Airy's equation, `w'` has derivative `z w(z)` at `z`. -/
theorem hasDerivAt_deriv_of_airy_ode {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hw' : ∀ z, deriv^[2] w z = z * w z) (z : ℂ) : HasDerivAt (deriv w) (z * w z) z := by
  rw [← hw' z, Function.iterate_succ_apply, Function.iterate_one]
  exact (hw.deriv z).hasDerivAt

/-- The Wronskian of two entire solutions of Airy's equation is constant. -/
theorem wronskian_eq_of_airy_ode {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z w : ℂ) :
    f z * deriv g z - deriv f z * g z = f w * deriv g w - deriv f w * g w := by
  have h := wronskian_eq_of_hasDerivAt (q := id) isOpen_univ isPreconnected_univ
    (fun t _ => (hg t).hasDerivAt) (fun t _ => hasDerivAt_deriv_of_airy_ode hg hg' t)
    (fun t _ => (hf t).hasDerivAt) (fun t _ => hasDerivAt_deriv_of_airy_ode hf hf' t)
    (Set.mem_univ z) (Set.mem_univ w)
  linear_combination h

/-- **The Wronskian** `𝒲{Ai, Bi} = 1/π` (DLMF 9.2.7). -/
theorem wronskian_airyAi_airyBi (z : ℂ) :
    airyAi z * deriv airyBi z - deriv airyAi z * airyBi z = (π : ℂ)⁻¹ := by
  rw [wronskian_eq_of_airy_ode differentiable_airyAi differentiable_airyBi airyAi_ode airyBi_ode
    z 0, airyAi_zero, airyBi_zero, deriv_airyAi_zero, deriv_airyBi_zero]
  have hG : Gamma (1 / 3) * Gamma (2 / 3) * (3 : ℂ) ^ (1 / 2 : ℂ) = 2 * π := by
    have h30 : (Real.sqrt 3 : ℂ) ≠ 0 := by simp
    rw [Complex.Gamma_one_third_mul_Gamma_two_thirds, ofNat_cpow_one_half]
    field_simp
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

/-- **The Riccati form** (DLMF 9.2.16), pointwise: if `w` and `w′` are differentiable at `z`,
`w′′(z) = z w(z)` and `w(z) ≠ 0`, then `W = w′/w` has derivative `z − W(z)²` at `z`. -/
theorem hasDerivAt_deriv_div_of_airy_ode_at {w : ℂ → ℂ} {z : ℂ} (hw : DifferentiableAt ℂ w z)
    (hw' : DifferentiableAt ℂ (deriv w) z) (hode : deriv^[2] w z = z * w z) (hz : w z ≠ 0) :
    HasDerivAt (fun u => deriv w u / w u) (z - (deriv w z / w z) ^ 2) z := by
  have h2 : HasDerivAt (deriv w) (z * w z) z := by
    rw [← hode]
    exact hw'.hasDerivAt
  refine (h2.div hw.hasDerivAt hz).congr_deriv ?_
  field_simp

/-- **The Riccati form** (DLMF 9.2.16): if `w` is an entire solution of Airy's equation and
`w(z) ≠ 0`, then `W = w′/w` has derivative `z − W(z)²` at `z`. -/
theorem hasDerivAt_deriv_div_of_airy_ode {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hode : ∀ z, deriv^[2] w z = z * w z) {z : ℂ} (hz : w z ≠ 0) :
    HasDerivAt (fun u => deriv w u / w u) (z - (deriv w z / w z) ^ 2) z :=
  hasDerivAt_deriv_div_of_airy_ode_at (hw z) (hw.deriv z) (hode z) hz

/-- **Rotation symmetry** of Airy's equation: if `w'' = z w` and `ν³ = 1`, then `z ↦ w(νz)` solves
the same equation. No differentiability of `w` is needed. -/
theorem airy_ode_comp_mul_left {w : ℂ → ℂ} {ν : ℂ} (hw : ∀ z, deriv^[2] w z = z * w z)
    (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun u => w (ν * u)) z = z * w (ν * z) := by
  simp only [← iteratedDeriv_eq_iterate, iteratedDeriv_comp_mul_left, smul_eq_mul]
  rw [iteratedDeriv_eq_iterate, hw]
  linear_combination z * w (ν * z) * hν

/-- **Rotation symmetry** of the inhomogeneous Airy equation: if `f'' = z f + c` and `ν³ = 1`,
then the rotated function `z ↦ ν f(ν z)` satisfies the same equation. No differentiability of `f`
is needed. With `c = 0`, `z ↦ ν w(ν z)` solves Airy's equation whenever `w` does. -/
theorem airy_inhomogeneous_ode_rotation {f : ℂ → ℂ} {c ν : ℂ}
    (hf : ∀ z, deriv^[2] f z = z * f z + c) (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun w => ν * f (ν * w)) z = z * (ν * f (ν * z)) + c := by
  simp only [← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_mul_left, smul_eq_mul]
  rw [iteratedDeriv_eq_iterate, hf]
  linear_combination (ν * z * f (ν * z) + c) * hν

end TauCeti
