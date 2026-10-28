/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor coefficients at a root and in subleading degree

The Taylor expansion `taylor r p = p(X + r)` of a polynomial `p` at `r` starts in degree
`p.rootMultiplicity r`, and its trailing coefficient is the value at `r` of `p` divided by the
largest power of `X - r` dividing it. This is the coefficient that survives when `X - r` is
divided out of `p` as often as possible before evaluating at `r`; for `p ≠ 0` it is nonzero
(`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`), so it is the lowest nonzero
coefficient of the Taylor expansion.

Since the Taylor coefficients of `p` at `r` are the values at `r` of the Hasse derivatives of `p`,
divisibility of `p` by `(X - r) ^ n` is the vanishing of its Hasse derivatives of order less than
`n` at `r`. A Hasse derivative of order `k` therefore lowers such a divisibility by at most `k`.

At the other end of the expansion, the leading coefficient is unchanged and the subleading
coefficient moves by `p.natDegree * r * p.leadingCoeff`. This is the input for the Tschirnhaus
shift, which removes the subleading coefficient whenever `p.natDegree` is invertible.

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
* `Polynomial.nextCoeff_taylor`: the subleading coefficient of the Taylor expansion of `p` at `r`
  is `p.nextCoeff + p.natDegree * r * p.leadingCoeff`.
-/

public section

namespace Polynomial

/-- The subleading coefficient of the Taylor expansion `p(X + r)` is that of `p` plus
`p.natDegree * r * p.leadingCoeff`. -/
theorem nextCoeff_taylor {R : Type*} [CommSemiring R] (p : R[X]) (r : R) :
    (taylor r p).nextCoeff = p.nextCoeff + p.natDegree * r * p.leadingCoeff := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · simp [nextCoeff, natDegree_taylor, h]
  -- The Hasse derivative of order `p.natDegree - 1` is linear; evaluate it at `r`.
  rw [nextCoeff_of_natDegree_pos (by rwa [natDegree_taylor]), nextCoeff_of_natDegree_pos h,
    natDegree_taylor, taylor_coeff,
    eq_X_add_C_of_natDegree_le_one ((natDegree_hasseDeriv_le _ _).trans (by omega))]
  obtain ⟨d, hd⟩ : ∃ d, p.natDegree = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  simp [hasseDeriv_coeff, leadingCoeff, hd, add_comm 1 d]
  ring

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

end Polynomial
