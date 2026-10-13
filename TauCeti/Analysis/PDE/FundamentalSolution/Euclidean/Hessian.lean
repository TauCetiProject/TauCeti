/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic

/-!
# The Hessian of the Newtonian kernel

For `n ≠ 2`, the second derivatives of the Newtonian kernel `Gₙ = TauCeti.newtonianKernel n`
on `ℝⁿ` are, away from the pole,

`D²Gₙ(x)(v, w) = ωₙ⁻¹ ‖x‖⁻ⁿ⁻² ⟪x, v⟫ ⟪x, w⟫ - (n ωₙ)⁻¹ ‖x‖⁻ⁿ ⟪v, w⟫`,

where `ωₙ` is the volume of the unit ball. This file proves that formula and the two estimates
that make `K(x, y) = D²Gₙ(x - y)` a **standard Calderón–Zygmund kernel**:

* the size estimate `‖D²Gₙ(x)‖ ≤ (n + 1) (n ωₙ)⁻¹ ‖x‖⁻ⁿ`;
* the smoothness estimate `‖D²Gₙ(a) - D²Gₙ(b)‖ ≤ 2ⁿ⁺¹ (n + 5) ωₙ⁻¹ ‖a - b‖ ‖b‖⁻ⁿ⁻¹` whenever
  `2 ‖a - b‖ ≤ ‖b‖`; with `a = x - y` and `b = x - y'` it reads
  `‖K(x, y) - K(x, y')‖ ≤ C ‖y - y'‖ ‖x - y'‖⁻ⁿ⁻¹` for `2 ‖y - y'‖ ≤ ‖x - y'‖`.

For `n ≥ 3` the kernel is nonzero and homogeneous of degree `-n`, so it is not locally
integrable, and the operator `f ↦ D²(Gₙ ⋆ f)` is a singular integral. (In dimension one the
formula vanishes identically, and in dimension two the totalized kernel is zero; see
below.) The two estimates are the kernel hypotheses of the Calderón–Zygmund theory of such
operators; together with the `L²` bound of the operator, that theory gives the `Lᵖ` bound
`‖D²u‖_p ≤ C ‖Δu‖_p`, `1 < p < ∞`, behind the `W^{2,p}` estimates for the Laplacian.

In dimension two `TauCeti.newtonianKernel 2` is the zero function (its normalizing constant is
`0⁻¹ = 0`), so the formula needs `n ≠ 2`; the two estimates are stated for every `n`, and hold
trivially at `n = 2`. The logarithmic planar kernel `TauCeti.planarNewtonianKernel` is not
covered here.

Both estimates are instances of the general bounds for the Hessian of `x ↦ ‖x‖ ^ p`,
`TauCeti.norm_iteratedFDeriv_two_norm_rpow_le` and
`TauCeti.norm_iteratedFDeriv_two_norm_rpow_sub_le`, at `p = 2 - n`.

## Main declarations

* `TauCeti.iteratedFDeriv_two_newtonianKernel_apply`: the Hessian formula, and its evenness
  `TauCeti.iteratedFDeriv_two_newtonianKernel_neg`.
* `TauCeti.norm_iteratedFDeriv_two_newtonianKernel_le`: the size estimate.
* `TauCeti.norm_iteratedFDeriv_two_newtonianKernel_sub_le`: the smoothness estimate.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.4 (the derivatives of the fundamental solution) and Section 9.4.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2
  and §3.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Away from the pole, the Hessian of `Gₙ` is the Hessian of `‖x‖ ^ (2 - n)` scaled by the
normalizing constant of `Gₙ`. -/
private theorem iteratedFDeriv_two_newtonianKernel_eq_smul {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) :
    iteratedFDeriv ℝ 2 (newtonianKernel n) x = ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ))) x := by
  have hfun : newtonianKernel n = ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)) :=
    funext fun y ↦ newtonianKernel_def n y
  rw [hfun]
  exact iteratedFDeriv_const_smul_apply
    ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx))

/-- In dimension two the totalized kernel `TauCeti.newtonianKernel 2` vanishes, and so does its
Hessian. -/
private theorem iteratedFDeriv_two_newtonianKernel_two (x : EuclideanSpace ℝ (Fin 2)) :
    iteratedFDeriv ℝ 2 (newtonianKernel 2) x = 0 := by
  have h : newtonianKernel 2 = 0 := funext fun y ↦ by simp [newtonianKernel_def]
  simp [h]

/-- **The Hessian of the Newtonian kernel** away from its pole:
`D²Gₙ(x)(v, w) = ωₙ⁻¹ ‖x‖⁻ⁿ⁻² ⟪x, v⟫ ⟪x, w⟫ - (n ωₙ)⁻¹ ‖x‖⁻ⁿ ⟪v, w⟫`. -/
theorem iteratedFDeriv_two_newtonianKernel_apply (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (v w : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (newtonianKernel n) x ![v, w] =
      (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * ‖x‖ ^ (-((n : ℝ) + 2)) *
          ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ -
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
          ‖x‖ ^ (-(n : ℝ)) * ⟪v, w⟫_ℝ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hx (Subsingleton.elim _ _))
  have hn2 : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  have hvol := (volume_real_unitBall_pos n).ne'
  have he₄ : (2 : ℝ) - n - 4 = -(n + 2) := by ring
  have he₂ : (2 : ℝ) - n - 2 = -n := by ring
  rw [iteratedFDeriv_two_newtonianKernel_eq_smul hx, smul_apply,
    iteratedFDeriv_two_norm_rpow_apply _ hx, smul_eq_mul, he₄, he₂]
  field_simp
  ring

/-- The Hessian of the Newtonian kernel is even: `D²Gₙ(-x) = D²Gₙ(x)`. -/
@[simp]
theorem iteratedFDeriv_two_newtonianKernel_neg (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (newtonianKernel n) (-x) = iteratedFDeriv ℝ 2 (newtonianKernel n) x := by
  rcases eq_or_ne n 2 with rfl | hn
  · simp [iteratedFDeriv_two_newtonianKernel_two]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  ext m
  have hm : m = ![m 0, m 1] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [hm, iteratedFDeriv_two_newtonianKernel_apply hn (neg_ne_zero.mpr hx),
    iteratedFDeriv_two_newtonianKernel_apply hn hx, norm_neg, inner_neg_left, inner_neg_left]
  ring

/-- **The size estimate for the Hessian of the Newtonian kernel**: away from the pole,
`‖D²Gₙ(x)‖ ≤ (n + 1) (n ωₙ)⁻¹ ‖x‖⁻ⁿ`. -/
theorem norm_iteratedFDeriv_two_newtonianKernel_le {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 2 (newtonianKernel n) x‖ ≤
      ((n : ℝ) + 1) * ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (-(n : ℝ)) := by
  rcases eq_or_ne n 2 with rfl | hn
  · rw [iteratedFDeriv_two_newtonianKernel_two, norm_zero]
    positivity
  have hn0 : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by rintro rfl; exact hx (Subsingleton.elim _ _)))
  have hn2 : 0 < |2 - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hn.symm))
  have hvol := volume_real_unitBall_pos n
  have he₂ : (2 : ℝ) - n - 2 = -n := by ring
  rw [iteratedFDeriv_two_newtonianKernel_eq_smul hx, norm_smul]
  refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_two_norm_rpow_le _ hx)
    (norm_nonneg _)).trans_eq ?_
  rw [Real.norm_eq_abs, abs_inv, abs_mul, abs_mul, abs_of_pos hn0, abs_of_pos hvol,
    abs_sub_comm (n : ℝ), he₂, abs_neg, abs_of_pos hn0]
  field_simp

/-- **The smoothness estimate for the Hessian of the Newtonian kernel.** If
`2 ‖a - b‖ ≤ ‖b‖`, then

`‖D²Gₙ(a) - D²Gₙ(b)‖ ≤ 2ⁿ⁺¹ (n + 5) ωₙ⁻¹ ‖a - b‖ ‖b‖⁻ⁿ⁻¹`.

With `a = x - y` and `b = x - y'`, this is the smoothness estimate
`‖K(x, y) - K(x, y')‖ ≤ C ‖y - y'‖ ‖x - y'‖⁻ⁿ⁻¹` for `2 ‖y - y'‖ ≤ ‖x - y'‖` of the
Calderón–Zygmund kernel `K(x, y) = D²Gₙ(x - y)`. -/
theorem norm_iteratedFDeriv_two_newtonianKernel_sub_le {a b : EuclideanSpace ℝ (Fin n)}
    (hab : 2 * ‖a - b‖ ≤ ‖b‖) :
    ‖iteratedFDeriv ℝ 2 (newtonianKernel n) a - iteratedFDeriv ℝ 2 (newtonianKernel n) b‖ ≤
      2 ^ (n + 1) * ((n : ℝ) + 5) * (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖a - b‖ * ‖b‖ ^ (-((n : ℝ) + 1)) := by
  rcases eq_or_ne b 0 with rfl | hb
  · obtain rfl : a = 0 := by
      rw [sub_zero, norm_zero] at hab
      exact norm_eq_zero.mp (by linarith [norm_nonneg a])
    simp
  rcases eq_or_ne n 2 with rfl | hn
  · rw [iteratedFDeriv_two_newtonianKernel_two, iteratedFDeriv_two_newtonianKernel_two, sub_zero,
      norm_zero]
    positivity
  have ha : a ≠ 0 := by
    have := norm_sub_norm_le b (b - a)
    rw [sub_sub_cancel, norm_sub_rev] at this
    exact norm_pos_iff.mp (by linarith [norm_pos_iff.mpr hb])
  have hn0 : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by rintro rfl; exact hb (Subsingleton.elim _ _)))
  have hn2 : 0 < |2 - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hn.symm))
  have hvol := volume_real_unitBall_pos n
  have he₂ : (2 : ℝ) - n - 2 = -n := by ring
  have he₃ : (3 : ℝ) - (2 - n) = n + 1 := by ring
  have he₃' : (2 : ℝ) - n - 3 = -(n + 1) := by ring
  rw [iteratedFDeriv_two_newtonianKernel_eq_smul ha,
    iteratedFDeriv_two_newtonianKernel_eq_smul hb, ← smul_sub, norm_smul]
  refine (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_two_norm_rpow_sub_le (by linarith) hab) (norm_nonneg _)).trans_eq ?_
  rw [Real.norm_eq_abs, abs_inv, abs_mul, abs_mul, abs_mul, abs_of_pos hn0, abs_of_pos hvol,
    abs_sub_comm (n : ℝ), he₂, abs_neg, abs_of_pos hn0, he₃, he₃',
    Real.rpow_add two_pos, Real.rpow_natCast, Real.rpow_one, pow_succ]
  field_simp
  ring

end TauCeti
