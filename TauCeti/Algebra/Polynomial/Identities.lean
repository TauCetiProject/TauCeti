/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities

/-!
# Taylor's estimate for the linearisation of a polynomial

By the binomial expansion `f(x + h) = f(x) + f'(x) h + c h ^ 2`, the derivative `f'(t)` at a point
`t` linearises `f` near `t` up to an error controlled by divisibility: if `d ∣ x - t`, `d ∣ e` and
`e ∣ x' - x`, then `f(x') - f(x) - f'(t) (x' - x)` is divisible by `d * e`. With `d = π ^ (k + 1)`
and `e = π ^ n`, `n ≥ k + 1`, this is the estimate behind Hensel's lemma with a derivative dividing
`π ^ k`.

## Main results

* `Polynomial.mul_dvd_eval_sub_eval_sub_mul`: Taylor's estimate
  `d * e ∣ f(x') - f(x) - f'(t) (x' - x)`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **Taylor's estimate.** If `d ∣ x - t`, `d ∣ e` and `e ∣ x' - x`, then the derivative at `t`
linearises the polynomial `f` from `x` to `x'` up to an error divisible by `d * e`. -/
theorem mul_dvd_eval_sub_eval_sub_mul (f : R[X]) {d e t x x' : R} (hx : d ∣ x - t) (hde : d ∣ e)
    (hxx' : e ∣ x' - x) :
    d * e ∣ f.eval x' - f.eval x - f.derivative.eval t * (x' - x) := by
  obtain ⟨c, hc⟩ := f.binomExpansion x (x' - x)
  rw [add_sub_cancel] at hc
  have h : f.eval x' - f.eval x - f.derivative.eval t * (x' - x) =
      (f.derivative.eval x - f.derivative.eval t) * (x' - x) + c * ((x' - x) * (x' - x)) := by
    rw [hc]
    ring
  rw [h]
  exact dvd_add (mul_dvd_mul (hx.trans (sub_dvd_eval_sub _ _ _)) hxx')
    (dvd_mul_of_dvd_right (mul_dvd_mul (hde.trans hxx') hxx') c)

end Polynomial
