/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# The exponential potential dominates the modular `√(1 + t²) - 1`

The convex potential `exp (2t) - 1 - 2t` is nonnegative and vanishes to second order at `0`, like
the modular `√(1 + t²) - 1`. For positive `t` it grows exponentially, but for negative `t` only
linearly, as does the modular. This file records the comparison

`√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`

(`Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`), which turns a bound on the
potential into a bound on a quantity comparable to `min (t², |t|)`. It is the pointwise input to
coercivity estimates for functionals with this potential, such as Taubes's functional for planar
vortices.

Below a fixed level `M ≥ 0` the potential is locally Lipschitz with a linear constant:
`|Φ(a) - Φ(b)| ≤ 4 exp (2M) (|a| + |b|) |a - b|` for `a, b ≤ M`, where `Φ(t) = exp (2t) - 1 - 2t`
(`Real.abs_exp_two_mul_sub_one_sub_two_mul_sub_le`). This makes the potential integral continuous
in `L²` on functions bounded above.

## Main results

* `Real.exp_two_mul_sub_one_sub_two_mul_nonneg`: for every real `t`, `0 ≤ exp (2t) - 1 - 2t`.
* `Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`: for every real `t`,
  `√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`.
* `Real.abs_exp_two_mul_sub_one_le`: for `s ≤ M` with `0 ≤ M`, `|exp (2s) - 1| ≤ 2 |s| exp (2M)`.
* `Real.abs_exp_two_mul_sub_one_sub_two_mul_sub_le`: the local Lipschitz bound on the potential
  below the level `M`.
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` is nonnegative. -/
theorem exp_two_mul_sub_one_sub_two_mul_nonneg (t : ℝ) : 0 ≤ exp (2 * t) - 1 - 2 * t := by
  linarith [add_one_le_exp (2 * t)]

/-- The potential `exp (2t) - 1 - 2t` dominates the modular `√(1 + t²) - 1`. -/
theorem sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (t : ℝ) :
    √(1 + t ^ 2) - 1 ≤ exp (2 * t) - 1 - 2 * t := by
  have hsq : √(1 + t ^ 2) ≤ 1 + t ^ 2 / 2 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (t ^ 2)]⟩
  rcases le_total 0 t with ht | ht
  · have := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * t)
    nlinarith
  rcases le_total (-1) t with ht1 | ht1
  · -- For `-1 ≤ t ≤ 0`, `(1 + 2t/3)³ ≤ exp (2t)`.
    have h := one_sub_div_pow_le_exp_neg (n := 3) (t := -(2 * t)) (by push_cast; linarith)
    rw [neg_neg] at h
    have ht3 : 0 ≤ t ^ 2 * (t + 1) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  · -- For `t ≤ -1`, `exp (2t) - 1 - 2t ≥ -t - (1 + t) ≥ |t| ≥ √(1 + t²) - 1`.
    have habs := sqrt_one_add_sq_sub_one_le_abs t
    rw [abs_of_nonpos ht] at habs
    nlinarith [exp_pos (2 * t)]

/-- `|exp (2s) - 1| ≤ 2 |s| exp (2M)` for `s ≤ M` with `0 ≤ M`. -/
theorem abs_exp_two_mul_sub_one_le {M s : ℝ} (hM : 0 ≤ M) (hs : s ≤ M) :
    |exp (2 * s) - 1| ≤ 2 * |s| * exp (2 * M) := by
  have hexpM : 1 ≤ exp (2 * M) := one_le_exp (by linarith)
  rcases le_total 0 s with h | h
  · have h1 := add_one_le_exp (-(2 * s))
    have h2 : exp (2 * s) * exp (-(2 * s)) = 1 := by rw [← exp_add]; simp
    have h3 : exp (2 * s) ≤ exp (2 * M) := exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith [one_le_exp (by linarith : 0 ≤ 2 * s)]), abs_of_nonneg h]
    nlinarith [exp_pos (2 * s)]
  · have h1 := add_one_le_exp (2 * s)
    rw [abs_of_nonpos (by linarith [exp_le_one_iff.2 (by linarith : 2 * s ≤ 0)]),
      abs_of_nonpos h]
    nlinarith

/-- The potential `Φ(t) = exp (2t) - 1 - 2t` is locally Lipschitz with linear constant below a
fixed level: `|Φ(a) - Φ(b)| ≤ 4 exp (2M) (|a| + |b|) |a - b|` for `a, b ≤ M`. -/
theorem abs_exp_two_mul_sub_one_sub_two_mul_sub_le {M a b : ℝ} (hM : 0 ≤ M) (ha : a ≤ M)
    (hb : b ≤ M) :
    |(exp (2 * a) - 1 - 2 * a) - (exp (2 * b) - 1 - 2 * b)| ≤
      4 * exp (2 * M) * (|a| + |b|) * |a - b| := by
  have hderiv (x : ℝ) : HasDerivWithinAt (fun s ↦ exp (2 * s) - 1 - 2 * s)
      (2 * (exp (2 * x) - 1)) (Set.uIcc b a) x := by
    have h1 : HasDerivAt (fun s ↦ exp (2 * s)) (exp (2 * x) * 2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).exp
    have h2 : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    refine (((h1.sub_const 1).sub h2).congr_deriv ?_).hasDerivWithinAt
    ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.uIcc b a)
    (x := b) (y := a) (C := 4 * exp (2 * M) * (|a| + |b|)) (fun x _ ↦ hderiv x)
    (fun x hx ↦ ?_) (convex_uIcc b a) Set.left_mem_uIcc Set.right_mem_uIcc
  · simpa only [norm_eq_abs] using h
  · rw [norm_eq_abs, abs_mul, abs_two]
    have ha' := neg_abs_le a
    have hb' := neg_abs_le b
    have ha'' := le_abs_self a
    have hb'' := le_abs_self b
    have hxM : x ≤ M ∧ |x| ≤ |a| + |b| := by
      rcases Set.mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩
    have h := abs_exp_two_mul_sub_one_le hM hxM.1
    have h' := mul_le_mul_of_nonneg_right hxM.2 (exp_pos (2 * M)).le
    nlinarith

end Real

end
