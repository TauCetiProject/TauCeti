/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal logarithms of power series

For a power series `f` with constant coefficient one, Mathlib's `PowerSeries.logOf f` is the
formal expansion of `log f`. This file defines its formal derivative and records the
characteristic identity

`logDeriv f * f = derivative f`.

Thus over a field it is the usual quotient `f' / f`. The multiplicative identity is more general:
it needs only a commutative ring over the rationals, because the constant coefficient one makes
`f - 1` a valid substitution into the logarithm series.

The file also truncates Mathlib's formal identity `(log A).subst (exp A - 1) = X` to polynomials:
composing the truncations of the two series gives `X` below both truncation degrees. Evaluating
these polynomial identities is how the identity `log (exp x) = x` is proved at points where the
two series converge, for instance on the deep ideals of a `p`-adic field.

## Main definitions

* `PowerSeries.logDeriv`: the formal derivative of `PowerSeries.logOf`.
* `PowerSeries.coeff_logDeriv`: the coefficient formula for the formal logarithmic derivative.
* `PowerSeries.logDeriv_mul`: the product identity characterizing the logarithmic derivative.
* `PowerSeries.logDeriv_eq_derivative_mul_inv`: the quotient form over a field.
* `PowerSeries.coeff_trunc_log_comp_trunc_exp_sub_one`: the identity `log (exp X) = X`, truncated
  to polynomials: the composite of the truncations of the two series agrees with `X` below both
  truncation degrees.
-/

public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The **formal logarithmic derivative** of a power series: the derivative of
`PowerSeries.logOf f`. When `f` has constant coefficient one, this is characterized by
`PowerSeries.logDeriv_mul`. -/
noncomputable def logDeriv (f : A⟦X⟧) : A⟦X⟧ :=
  d⁄dX (logOf f)

/-- The formal logarithmic derivative is the derivative of the formal logarithm. -/
theorem logDeriv_def (f : A⟦X⟧) :
    logDeriv f = d⁄dX (logOf f) := by
  rw [logDeriv]

/-- Coefficients of the formal logarithmic derivative are the shifted coefficients of the formal
logarithm, multiplied by their positive degree. -/
theorem coeff_logDeriv (f : A⟦X⟧) (n : ℕ) :
    coeff n (logDeriv f) = coeff (n + 1) (logOf f) * (n + 1) := by
  rw [logDeriv, coeff_derivative]

/-- The formal logarithmic derivative of a power series with constant coefficient one satisfies
`(log f)' * f = f'`. -/
theorem logDeriv_mul (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    logDeriv f * f = d⁄dX f := by
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [logDeriv, logOf_eq, derivative_subst hsub]
  have hlog := congrArg (substAlgHom hsub)
    (derivative_log_mul_one_add_X (A := A))
  simp only [map_mul, map_one, coe_substAlgHom] at hlog
  have hone : (1 : A⟦X⟧).subst (f - 1) = 1 := by
    rw [← coe_substAlgHom hsub, map_one]
  have hadd : (1 + X : A⟦X⟧).subst (f - 1) = f := by
    rw [subst_add hsub, subst_X hsub]
    rw [hone]
    ring
  rw [hadd] at hlog
  have hderiv : d⁄dX (f - 1) = d⁄dX f := by
    rw [map_sub, derivative_one, sub_zero]
  rw [hderiv]
  calc
    subst (f - 1) (d⁄dX (log A)) * d⁄dX f * f =
        (subst (f - 1) (d⁄dX (log A)) * f) * d⁄dX f := by ring
    _ = d⁄dX f := by rw [hlog, one_mul]

/-- Over a field, the formal logarithmic derivative of a power series with constant coefficient
one is the quotient `f' / f`. -/
theorem logDeriv_eq_derivative_mul_inv {k : Type*} [Field k] [Algebra ℚ k]
    (f : k⟦X⟧) (hf : constantCoeff f = 1) :
    logDeriv f = d⁄dX f * f⁻¹ := by
  have hunit : IsUnit f := isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)
  apply hunit.mul_right_cancel
  rw [logDeriv_mul f hf, mul_assoc, f.inv_mul_cancel (by simp [hf]), mul_one]

/-- Below degrees `M` and `N`, composing the truncation of the logarithm series below degree `M`
after the truncation of `exp - 1` below degree `N` gives `X`: this is the truncated form of
`PowerSeries.subst_log_exp_sub_one`. It is what evaluates the identity `log (exp x) = x` at a
point where the two series converge. -/
theorem coeff_trunc_log_comp_trunc_exp_sub_one {M N k : ℕ} (hM : k < M) (hN : k < N) :
    ((trunc M (log A)).comp (trunc N (exp A - 1))).coeff k =
      (Polynomial.X : Polynomial A).coeff k := by
  set E : A⟦X⟧ := exp A - 1
  -- The coefficient of `X ^ k` in `E ^ n` vanishes for `n > k`, as `X` divides `E`.
  have hvan : ∀ n, k < n → coeff k (E ^ n) = 0 := fun n hn =>
    X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr (by simp [E])) n) k hn
  -- Below degree `N`, powers of the truncation of `E` agree with powers of `E`.
  have hpow : ∀ n, ((trunc N E) ^ n).coeff k = coeff k (E ^ n) := by
    intro n
    calc ((trunc N E) ^ n).coeff k = coeff k ((trunc N E : A⟦X⟧) ^ n) := by
          rw [← Polynomial.coe_pow, Polynomial.coeff_coe]
      _ = (trunc N ((trunc N E : A⟦X⟧) ^ n)).coeff k := by
          simp only [coeff_trunc, hN, ite_true]
      _ = coeff k (E ^ n) := by
          simp only [trunc_trunc_pow, coeff_trunc, hN, ite_true]
  have hlhs : ((trunc M (log A)).comp (trunc N E)).coeff k =
      ∑ n ∈ Finset.range M, coeff n (log A) * coeff k (E ^ n) := by
    rw [Polynomial.comp, eval₂_trunc_eq_sum_range, Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_C_mul, hpow]
  rw [hlhs]
  have hX : (Polynomial.X : Polynomial A).coeff k = coeff k (X : A⟦X⟧) := by
    rw [Polynomial.coeff_X, coeff_X]
    grind
  rw [hX, ← subst_log_exp_sub_one, coeff_subst' HasSubst.exp_sub_one,
    finsum_eq_sum_of_support_subset (s := Finset.range M)]
  · rfl
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    have h0 := hvan n (by omega)
    simp only [E] at h0
    exact hn (by rw [h0, smul_zero])

end PowerSeries
