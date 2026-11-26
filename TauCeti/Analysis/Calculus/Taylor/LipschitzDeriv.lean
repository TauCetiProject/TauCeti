/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Taylor and quadrature residuals of curves with a Lipschitz derivative

Let `w : ℝ → E` be a curve in a real normed space with derivative `w' r` within `[a, b]` at every
`r ∈ [a, b]`. This file bounds, with sharp constants, the residuals of the elementary Taylor
expansions and quadrature rules when the last derivative involved is Lipschitz on `[a, b]`. The
space `E` need not be complete, and the derivatives are taken within `[a, b]`, so they are
one-sided at the endpoints.

* First order, `w'` `M`-Lipschitz: `‖w u - w s - (u - s) • w' s‖ ≤ M (u - s)² / 2` for `s`, `u`
  in `[a, b]` in either order (`TauCeti.norm_sub_sub_smul_le_of_lipschitzOnWith`). With `u > s`
  this is the forward Taylor residual, with `u < s` the backward one.
* Second order, `w'` with derivative `w''` and `w''` `M`-Lipschitz:
  `‖w u - w s - (u - s) • w' s - ((u - s)² / 2) • w'' s‖ ≤ M |u - s|³ / 6`
  (`TauCeti.norm_sub_sub_smul_sub_smul_le_of_lipschitzOnWith`).
* Midpoint interpolation: `‖w (t + h/2) - (1/2) • (w t + w (t + h))‖ ≤ M h² / 8` for
  `w'` `M`-Lipschitz (`TauCeti.norm_sub_half_smul_add_le_of_lipschitzOnWith`).
* The trapezoidal rule: `‖w (t + h) - w t - (h/2) • (w' t + w' (t + h))‖ ≤ M h³ / 12` for `w''`
  `M`-Lipschitz (`TauCeti.norm_sub_sub_smul_add_le_of_lipschitzOnWith`).
* The midpoint rule: `‖w (t + h) - w t - h • w' (t + h/2)‖ ≤ M h³ / 24` for `w''` `M`-Lipschitz
  (`TauCeti.norm_sub_sub_smul_apply_add_half_le_of_lipschitzOnWith`).

The constants are attained by `w r = r²` (first order and midpoint interpolation) and `w r = r³`
(the second order and the two quadrature rules), and a Lipschitz bound `M` on a derivative holds
whenever the next derivative has norm at most `M`. For a solution `y` of `y' = f(t, y)`, with
`w = y` and `w' r = f r (y r)`, these residuals are the parts of the local errors of the Euler,
trapezoidal and midpoint one-step methods that do not involve the Lipschitz constant of `f`.

All bounds come from the mean value inequality with a polynomial majorant in
`TauCeti.Analysis.Calculus.MeanValue`, chiefly its two-sided form
`TauCeti.norm_image_sub_le_of_norm_deriv_le_mul_abs_sub_pow`.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford (2022), (19) and Section 2.4, for the truncation errors of the Euler, trapezoidal and
  midpoint methods.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Taylor residuals -/

variable {w w' w'' : ℝ → E} {a b : ℝ} {M : ℝ≥0}

/-- The derivative of `r ↦ w r - (r - s) • v`, the first-order Taylor residual of `w` at `s`
with the slope `v`. -/
private lemma hasDerivWithinAt_sub_sub_smul {S : Set ℝ} {r s : ℝ} {v : E}
    (hw : HasDerivWithinAt w (w' r) S r) :
    HasDerivWithinAt (fun ρ ↦ w ρ - (ρ - s) • v) (w' r - v) S r := by
  simpa using hw.fun_sub (((hasDerivAt_id' r).sub_const s).smul_const v).hasDerivWithinAt

/-- **The first-order Taylor residual.** If `w` has derivative `w' r` within `[a, b]` at every
`r ∈ [a, b]` and `w'` is `M`-Lipschitz on `[a, b]`, then for `s`, `u` in `[a, b]`, in either
order, `‖w u - w s - (u - s) • w' s‖ ≤ M (u - s) ^ 2 / 2`. -/
theorem norm_sub_sub_smul_le_of_lipschitzOnWith
    (hw : ∀ r ∈ Icc a b, HasDerivWithinAt w (w' r) (Icc a b) r)
    (hM : LipschitzOnWith M w' (Icc a b)) {s u : ℝ} (hs : s ∈ Icc a b) (hu : u ∈ Icc a b) :
    ‖w u - w s - (u - s) • w' s‖ ≤ M * (u - s) ^ 2 / 2 := by
  have key := norm_image_sub_le_of_norm_deriv_le_mul_abs_sub_pow (n := 1) (C := M)
    (fun r hr ↦ hasDerivWithinAt_sub_sub_smul (s := s) (v := w' s) (hw r hr))
    (fun r hr ↦ by simpa [← dist_eq_norm, Real.dist_eq] using hM.dist_le_mul r hr s hs) hs hu
  convert key using 1
  · rw [sub_self, zero_smul, sub_zero, sub_right_comm]
  · norm_num [sq_abs]

/-- **The second-order Taylor residual.** If `w` has derivative `w' r` and `w'` has derivative
`w'' r` within `[a, b]` at every `r ∈ [a, b]`, and `w''` is `M`-Lipschitz on `[a, b]`, then for `s`,
`u` in `[a, b]`, in either order,
`‖w u - w s - (u - s) • w' s - ((u - s) ^ 2 / 2) • w'' s‖ ≤ M |u - s| ^ 3 / 6`. -/
theorem norm_sub_sub_smul_sub_smul_le_of_lipschitzOnWith
    (hw : ∀ r ∈ Icc a b, HasDerivWithinAt w (w' r) (Icc a b) r)
    (hw' : ∀ r ∈ Icc a b, HasDerivWithinAt w' (w'' r) (Icc a b) r)
    (hM : LipschitzOnWith M w'' (Icc a b)) {s u : ℝ} (hs : s ∈ Icc a b) (hu : u ∈ Icc a b) :
    ‖w u - w s - (u - s) • w' s - ((u - s) ^ 2 / 2) • w'' s‖ ≤ M * |u - s| ^ 3 / 6 := by
  have hd (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun ρ ↦ w ρ - (ρ - s) • w' s - ((ρ - s) ^ 2 / 2) • w'' s)
        (w' r - w' s - (r - s) • w'' s) (Icc a b) r := by
    convert (hasDerivWithinAt_sub_sub_smul (s := s) (v := w' s) (hw r hr)).fun_sub
      ((((hasDerivAt_id' r).sub_const s).fun_pow 2).div_const 2 |>.smul_const
        (w'' s)).hasDerivWithinAt using 1
    simp
  have key := norm_image_sub_le_of_norm_deriv_le_mul_abs_sub_pow (n := 2) (C := M / 2) hd
    (fun r hr ↦ by
      simpa [sq_abs, mul_div_right_comm] using
        norm_sub_sub_smul_le_of_lipschitzOnWith hw' hM hs hr) hs hu
  convert key using 1
  · congr 1
    simp only [sub_self, zero_smul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div]
    abel
  · ring

/-! ### Quadrature residuals -/

variable {t h : ℝ}

/-- **The midpoint interpolation residual.** If `w` has derivative `w' r` within `[a, b]` at every
`r ∈ [a, b]` and `w'` is `M`-Lipschitz on `[a, b]`, then for `a ≤ t`, `0 ≤ h` and `t + h ≤ b`,
`‖w (t + h / 2) - (1 / 2) • (w t + w (t + h))‖ ≤ M h ^ 2 / 8`. -/
theorem norm_sub_half_smul_add_le_of_lipschitzOnWith
    (hw : ∀ r ∈ Icc a b, HasDerivWithinAt w (w' r) (Icc a b) r)
    (hM : LipschitzOnWith M w' (Icc a b)) (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖w (t + h / 2) - (1 / 2 : ℝ) • (w t + w (t + h))‖ ≤ M * h ^ 2 / 8 := by
  have hc : t + h / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have h₁ := norm_sub_sub_smul_le_of_lipschitzOnWith hw hM hc (u := t + h) ⟨by linarith, hth⟩
  have h₂ := norm_sub_sub_smul_le_of_lipschitzOnWith hw hM hc (u := t) ⟨ht, by linarith⟩
  -- The two first-order residuals at the midpoint, towards `t + h` and towards `t`, have the
  -- slopes `± h / 2`, which cancel in their sum.
  have heq : w (t + h / 2) - (1 / 2 : ℝ) • (w t + w (t + h)) =
      -(1 / 2 : ℝ) • ((w (t + h) - w (t + h / 2) - (t + h - (t + h / 2)) • w' (t + h / 2)) +
        (w t - w (t + h / 2) - (t - (t + h / 2)) • w' (t + h / 2))) := by
    module
  rw [heq, norm_smul]
  calc ‖-(1 / 2 : ℝ)‖ * ‖_ + _‖ ≤ 1 / 2 * (M * (t + h - (t + h / 2)) ^ 2 / 2 +
        M * (t - (t + h / 2)) ^ 2 / 2) := by
        rw [norm_neg, Real.norm_of_nonneg (by norm_num)]
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ = M * h ^ 2 / 8 := by ring

/-- **The trapezoidal rule residual.** If `w` has derivative `w' r` and `w'` has derivative
`w'' r` within `[a, b]` at every `r ∈ [a, b]`, and `w''` is `M`-Lipschitz on `[a, b]`, then for
`a ≤ t`, `0 ≤ h` and `t + h ≤ b`,
`‖w (t + h) - w t - (h / 2) • (w' t + w' (t + h))‖ ≤ M h ^ 3 / 12`. -/
theorem norm_sub_sub_smul_add_le_of_lipschitzOnWith
    (hw : ∀ r ∈ Icc a b, HasDerivWithinAt w (w' r) (Icc a b) r)
    (hw' : ∀ r ∈ Icc a b, HasDerivWithinAt w' (w'' r) (Icc a b) r)
    (hM : LipschitzOnWith M w'' (Icc a b)) (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖w (t + h) - w t - (h / 2) • (w' t + w' (t + h))‖ ≤ M * h ^ 3 / 12 := by
  have hsub : Icc t (t + h) ⊆ Icc a b := Icc_subset_Icc ht hth
  -- The residual `R r = w r - w t - ((r - t) / 2) • (w' t + w' r)` has derivative
  -- `(1 / 2) • (w' r - w' t - (r - t) • w'' r)`, half a backward Taylor residual of `w'`.
  have hd (r : ℝ) (hr : r ∈ Icc t (t + h)) :
      HasDerivWithinAt (fun ρ ↦ w ρ - w t - ((ρ - t) / 2) • (w' t + w' ρ))
        ((1 / 2 : ℝ) • (w' r - w' t - (r - t) • w'' r)) (Icc t (t + h)) r := by
    convert (((hw r (hsub hr)).mono hsub).sub_const (w t)).fun_sub
      ((((hasDerivAt_id' r).sub_const t).div_const 2).hasDerivWithinAt.fun_smul
        (((hw' r (hsub hr)).mono hsub).const_add (w' t))) using 1
    module
  have key := norm_image_sub_le_of_norm_deriv_le_mul_pow_sub_left (n := 2) (C := M / 4)
    (by linarith) hd fun r hr ↦ by
      have hr' := hsub (Ico_subset_Icc_self hr)
      rw [norm_smul, ← norm_neg (w' r - _ - _), show -(w' r - w' t - (r - t) • w'' r) =
        w' t - w' r - (t - r) • w'' r by module]
      calc ‖(1 / 2 : ℝ)‖ * ‖w' t - w' r - (t - r) • w'' r‖ ≤
            1 / 2 * (M * (t - r) ^ 2 / 2) := by
            rw [Real.norm_of_nonneg (by norm_num)]
            gcongr
            exact norm_sub_sub_smul_le_of_lipschitzOnWith hw' hM hr' ⟨ht, by linarith⟩
        _ = M / 4 * (r - t) ^ 2 := by ring
  convert key using 1
  · simp
  · ring

/-- **The midpoint rule residual.** If `w` has derivative `w' r` and `w'` has derivative `w'' r`
within `[a, b]` at every `r ∈ [a, b]`, and `w''` is `M`-Lipschitz on `[a, b]`, then for `a ≤ t`,
`0 ≤ h` and `t + h ≤ b`, `‖w (t + h) - w t - h • w' (t + h / 2)‖ ≤ M h ^ 3 / 24`. -/
theorem norm_sub_sub_smul_apply_add_half_le_of_lipschitzOnWith
    (hw : ∀ r ∈ Icc a b, HasDerivWithinAt w (w' r) (Icc a b) r)
    (hw' : ∀ r ∈ Icc a b, HasDerivWithinAt w' (w'' r) (Icc a b) r)
    (hM : LipschitzOnWith M w'' (Icc a b)) (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖w (t + h) - w t - h • w' (t + h / 2)‖ ≤ M * h ^ 3 / 24 := by
  have hc : t + h / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have h₁ := norm_sub_sub_smul_sub_smul_le_of_lipschitzOnWith hw hw' hM hc (u := t + h)
    ⟨by linarith, hth⟩
  have h₂ := norm_sub_sub_smul_sub_smul_le_of_lipschitzOnWith hw hw' hM hc (u := t)
    ⟨ht, by linarith⟩
  -- The second-order residuals at the midpoint, towards `t + h` and towards `t`, have the same
  -- quadratic term, which cancels in their difference.
  have heq : w (t + h) - w t - h • w' (t + h / 2) =
      (w (t + h) - w (t + h / 2) - (t + h - (t + h / 2)) • w' (t + h / 2) -
          ((t + h - (t + h / 2)) ^ 2 / 2) • w'' (t + h / 2)) -
        (w t - w (t + h / 2) - (t - (t + h / 2)) • w' (t + h / 2) -
          ((t - (t + h / 2)) ^ 2 / 2) • w'' (t + h / 2)) := by
    module
  rw [heq]
  refine (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  rw [show t + h - (t + h / 2) = h / 2 by ring, show t - (t + h / 2) = -(h / 2) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  ring

end TauCeti
