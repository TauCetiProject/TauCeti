/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Ring

/-!
# Taylor coefficients at a root, and the second-highest Taylor coefficient

The Taylor expansion `taylor r p = p(X + r)` of a polynomial `p` at `r` starts in degree
`p.rootMultiplicity r`, and its trailing coefficient is the value at `r` of `p` divided by the
largest power of `X - r` dividing it. This is the coefficient that survives when `X - r` is
divided out of `p` as often as possible before evaluating at `r`; for `p ≠ 0` it is nonzero
(`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`), so it is the lowest nonzero
coefficient of the Taylor expansion.

Since the Taylor coefficients of `p` at `r` are the values at `r` of the Hasse derivatives of `p`,
divisibility of `p` by `(X - r) ^ n` is the vanishing of its Hasse derivatives of order less than
`n` at `r`. A Hasse derivative of order `k` therefore lowers such a divisibility by at most `k`.

At the other end of the expansion, translating the variable of a polynomial of degree `n` by `r`
adds `n * r` times the leading coefficient to the coefficient of `X ^ (n - 1)`. When `n` is
invertible, translating a monic polynomial by minus `1 / n` times that coefficient therefore
removes its term of degree `n - 1`.

## Main results

* `Polynomial.natTrailingDegree_taylor`: the Taylor expansion at `r` starts in degree
  `p.rootMultiplicity r`.
* `Polynomial.coeff_taylor_rootMultiplicity`, `Polynomial.trailingCoeff_taylor`: its trailing
  coefficient is `(p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r`.
* `Polynomial.eval_hasseDeriv_rootMultiplicity_ne_zero`: for `p ≠ 0`, the Hasse derivative of
  order `p.rootMultiplicity r` does not vanish at `r`.
* `Polynomial.pow_sub_dvd_hasseDeriv_of_pow_dvd`: if `(X - r) ^ n` divides `p`, then
  `(X - r) ^ (n - k)` divides the Hasse derivative of `p` of order `k`.
* `Polynomial.eval_hasseDeriv_X_sub_C_pow`: the Hasse derivatives of `(X - r) ^ m` at `r`.
* `Polynomial.nextCoeff_taylor`: the second-highest coefficient of `p(X + r)`.
-/

public section

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- The Taylor expansion of `p` at `r` starts in degree `p.rootMultiplicity r`. -/
theorem natTrailingDegree_taylor (p : R[X]) (r : R) :
    (taylor r p).natTrailingDegree = p.rootMultiplicity r := by
  rw [rootMultiplicity_eq_natTrailingDegree, taylor_apply]

/-- The coefficient of `X ^ p.rootMultiplicity r` in the Taylor expansion of `p` at `r` is the
value at `r` of `p` divided by the largest power of `X - r` dividing it. -/
theorem coeff_taylor_rootMultiplicity (p : R[X]) (r : R) :
    (taylor r p).coeff (p.rootMultiplicity r) =
      (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  set m := p.rootMultiplicity r
  conv_lhs => rw [← pow_mul_divByMonic_rootMultiplicity_eq p r]
  simpa [taylor_mul, taylor_pow, taylor_coeff_zero] using
    coeff_X_pow_mul (taylor r (p /ₘ (X - C r) ^ m)) m 0

/-- The trailing coefficient of the Taylor expansion of `p` at `r` is the value at `r` of `p`
divided by the largest power of `X - r` dividing it. For `p ≠ 0` this is the lowest nonzero
coefficient. -/
theorem trailingCoeff_taylor (p : R[X]) (r : R) :
    (taylor r p).trailingCoeff = (p /ₘ (X - C r) ^ p.rootMultiplicity r).eval r := by
  rw [trailingCoeff, natTrailingDegree_taylor, coeff_taylor_rootMultiplicity]

/-- For `p ≠ 0`, the Hasse derivative of `p` of order `p.rootMultiplicity r` does not vanish
at `r`. -/
theorem eval_hasseDeriv_rootMultiplicity_ne_zero {p : R[X]} (hp : p ≠ 0) (r : R) :
    (hasseDeriv (p.rootMultiplicity r) p).eval r ≠ 0 := by
  rw [← taylor_coeff, ← natTrailingDegree_taylor]
  exact coeff_natTrailingDegree_ne_zero.2 ((taylor_eq_zero _ _).not.2 hp)

/-- If `(X - r) ^ n` divides `p`, then `(X - r) ^ (n - k)` divides the Hasse derivative of `p` of
order `k`. This is the analogue of `Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd` for
Hasse derivatives; it does not follow from it when `k !` is not invertible in `R`. -/
theorem pow_sub_dvd_hasseDeriv_of_pow_dvd {p : R[X]} {r : R} {n : ℕ} (k : ℕ)
    (h : (X - C r) ^ n ∣ p) : (X - C r) ^ (n - k) ∣ hasseDeriv k p := by
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff] at h ⊢
  intro j hj
  have := h (j + k) (by omega)
  rw [taylor_coeff] at this ⊢
  rw [← LinearMap.comp_apply, hasseDeriv_comp, LinearMap.smul_apply, nsmul_eq_mul, eval_mul, this,
    mul_zero]

/-- The Hasse derivative of order `i` of `(X - r) ^ m` is `1` at `r` if `i = m`, and `0`
otherwise: the Taylor expansion of `(X - r) ^ m` at `r` is `X ^ m`. -/
@[simp]
theorem eval_hasseDeriv_X_sub_C_pow (r : R) (i m : ℕ) :
    (hasseDeriv i ((X - C r) ^ m)).eval r = if i = m then 1 else 0 := by
  rw [← taylor_coeff]
  simp [taylor_pow, coeff_X_pow]

end CommRing

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Translating the variable by `r` adds `n * r` times the leading coefficient to the coefficient
of `X ^ (n - 1)`, where `n` is the degree. -/
@[simp]
theorem nextCoeff_taylor (p : R[X]) (r : R) :
    (taylor r p).nextCoeff = p.nextCoeff + p.natDegree * r * p.leadingCoeff := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · simp [nextCoeff, natDegree_taylor, h]
  -- The relevant Taylor coefficient is the value at `r` of a Hasse derivative of degree `≤ 1`.
  have h2 : (hasseDeriv (p.natDegree - 1) p).natDegree < 2 :=
    (natDegree_hasseDeriv_le p _).trans_lt (by omega)
  rw [nextCoeff_of_natDegree_pos (by rwa [natDegree_taylor]), nextCoeff_of_natDegree_pos h,
    natDegree_taylor, taylor_coeff, eval_eq_sum_range' h2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hasseDeriv_coeff, zero_add, pow_zero,
    pow_one, Nat.choose_self, Nat.cast_one, one_mul, mul_one, leadingCoeff]
  rw [Nat.add_sub_of_le h, Nat.choose_symm_of_eq_add (Nat.sub_add_cancel h).symm,
    Nat.choose_one_right]
  ring

end CommSemiring

end Polynomial
