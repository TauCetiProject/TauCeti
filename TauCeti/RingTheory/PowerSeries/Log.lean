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

Finally, the file shows that `logOf` and substitution into `exp` are inverse bijections between
power series with constant coefficient one and power series without constant term, and that
`logOf` turns products into sums. A logarithm of the form `∑ sₙ Xⁿ / n` is recognized from the
logarithmic derivative `∑ sₙ₊₁ Xⁿ`. This computes the logarithms of `1 - c X` and of
`1 - a X + q X²`, the latter through the sequence `t` with `t₀ = 2`, `t₁ = a` and
`tₙ₊₂ = a tₙ₊₁ - q tₙ`, without factoring the quadratic. Exponentiating gives rationality of
`exp (∑ (1 + qⁿ - tₙ) Xⁿ / n)`: this is the shape of the zeta function of an elliptic curve over a
finite field with `q` elements whose point counts are `1 + qⁿ - tₙ`.

## Main definitions

* `PowerSeries.logDeriv`: the formal derivative of `PowerSeries.logOf`.
* `PowerSeries.coeff_logDeriv`: the coefficient formula for the formal logarithmic derivative.
* `PowerSeries.logDeriv_mul`: the product identity characterizing the logarithmic derivative.
* `PowerSeries.logDeriv_eq_derivative_mul_inv`: the quotient form over a field.
* `PowerSeries.coeff_trunc_log_comp_trunc_exp_sub_one`: the identity `log (exp X) = X`, truncated
  to polynomials: the composite of the truncations of the two series agrees with `X` below both
  truncation degrees.

## Main results

* `PowerSeries.subst_exp_logOf` and `PowerSeries.logOf_subst_exp`: `exp (log f) = f` and
  `log (exp g) = g`.
* `PowerSeries.logOf_mul`: `log (f g) = log f + log g`.
* `PowerSeries.logOf_eq_mk_iff`: `log f = ∑ sₙ Xⁿ / n` exactly when `(∑ sₙ₊₁ Xⁿ) f = f'`.
* `PowerSeries.logOf_one_sub_C_mul_X` and `PowerSeries.logOf_one_sub_C_mul_X_add_C_mul_X_sq`: the
  logarithms of `1 - c X` and of `1 - a X + q X²`.
* `PowerSeries.subst_exp_mul_one_sub_C_mul_X`: `exp (∑ cⁿ Xⁿ / n) (1 - c X) = 1`.
* `PowerSeries.subst_exp_mul_one_sub_X_mul_one_sub_C_mul_X`:
  `exp (∑ (1 + qⁿ - tₙ) Xⁿ / n) (1 - X) (1 - q X) = 1 - a X + q X²`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.
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


/-! ## Logarithm and exponential as inverse operations -/

/-- The derivative of `∑ sₙ Xⁿ / n` is `∑ sₙ₊₁ Xⁿ`. The constant term `s₀` plays no role. -/
theorem derivative_mk_inv_smul (s : ℕ → A) :
    d⁄dX (mk fun n ↦ (n : ℚ)⁻¹ • s n) = mk fun n ↦ s (n + 1) := by
  ext n
  simp only [coeff_derivative, coeff_mk]
  -- Move the factor `n + 1` into the rational scalar, where it cancels against `(n + 1)⁻¹`.
  rw [mul_comm, ← Nat.cast_succ, ← map_natCast (algebraMap ℚ A), ← Algebra.smul_def, smul_smul]
  simp [Nat.cast_add_one_ne_zero]

/-- A power series with constant coefficient one has logarithm `∑ sₙ Xⁿ / n` exactly when
`∑ sₙ₊₁ Xⁿ` is its logarithmic derivative, that is, when `(∑ sₙ₊₁ Xⁿ) * f = f'`. -/
theorem logOf_eq_mk_iff {f : A⟦X⟧} (hf : constantCoeff f = 1) (s : ℕ → A) :
    logOf f = (mk fun n ↦ (n : ℚ)⁻¹ • s n) ↔ (mk fun n ↦ s (n + 1)) * f = d⁄dX f := by
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hunit : IsUnit f := isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)
  rw [← logDeriv_mul f hf]
  refine ⟨fun h ↦ by rw [logDeriv, h, derivative_mk_inv_smul], fun h ↦ ?_⟩
  refine derivative.ext ?_ ?_
  · rw [derivative_mk_inv_smul, ← logDeriv_def]
    exact (hunit.mul_right_cancel h).symm
  · simp [constantCoeff_logOf hf]

/-- The exponential of a power series without constant term has constant coefficient one. -/
@[simp]
theorem constantCoeff_subst_exp {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    constantCoeff ((exp A).subst g) = 1 := by
  rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hg, constantCoeff_exp, map_one]

/-- The formal exponential undoes the formal logarithm: `exp (log f) = f` when `f` has constant
coefficient one. -/
@[simp]
theorem subst_exp_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    (exp A).subst (logOf f) = f := by
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [logOf_eq, ← subst_comp_subst_apply HasSubst.log hsub, subst_exp_log, subst_add hsub,
    subst_X hsub, ← coe_substAlgHom hsub, map_one]
  ring

/-- The formal logarithm undoes the formal exponential: `log (exp g) = g` when `g` has no constant
term. -/
@[simp]
theorem logOf_subst_exp {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    logOf ((exp A).subst g) = g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hsub_one : (exp A).subst g - 1 = (exp A - 1).subst g := by
    rw [subst_sub hsub, ← coe_substAlgHom hsub, map_one]
  rw [logOf_eq, hsub_one, ← subst_comp_subst_apply HasSubst.exp_sub_one hsub,
    subst_log_exp_sub_one, subst_X hsub]

/-- The formal logarithm is injective on power series with constant coefficient one. -/
theorem logOf_inj {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf f = logOf g ↔ f = g :=
  ⟨fun h ↦ by rw [← subst_exp_logOf hf, h, subst_exp_logOf hg], congrArg logOf⟩

/-- The formal logarithm turns products into sums: `log (f g) = log f + log g` when `f` and `g`
have constant coefficient one. -/
theorem logOf_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  have hunit : IsUnit (f * g) := isUnit_iff_constantCoeff.mpr (hfg ▸ isUnit_one)
  refine derivative.ext ?_ ?_
  · simp only [map_add, ← logDeriv_def]
    refine hunit.mul_right_cancel ?_
    rw [logDeriv_mul _ hfg, Derivation.leibniz, ← logDeriv_mul f hf, ← logDeriv_mul g hg,
      smul_eq_mul, smul_eq_mul]
    ring
  · rw [map_add, constantCoeff_logOf hf, constantCoeff_logOf hg, constantCoeff_logOf hfg,
      add_zero]

/-- The formal logarithm of `1` is `0`. -/
@[simp]
theorem logOf_one : logOf (1 : A⟦X⟧) = 0 := by
  have h := logOf_mul (A := A) (f := 1) (g := 1) (by simp) (by simp)
  rwa [mul_one, left_eq_add] at h

/-! ## Logarithms of linear and quadratic polynomials -/

/-- The logarithm of `1 - c X` is `-∑ cⁿ Xⁿ / n`. -/
theorem logOf_one_sub_C_mul_X (c : A) :
    logOf (1 - C c * X) = mk fun n ↦ (n : ℚ)⁻¹ • -c ^ n := by
  rw [logOf_eq_mk_iff (by simp), mul_sub, mul_one, mul_comm _ (C c * X), mul_assoc]
  ext (_ | n) <;> simp [coeff_succ_X_mul, pow_succ, mul_comm]

/-- The logarithm of `1 - a X + q X²` is `-∑ tₙ Xⁿ / n`, where `t` is the sequence with `t₀ = 2`,
`t₁ = a` and `tₙ₊₂ = a tₙ₊₁ - q tₙ`. If `1 - a X + q X²` factors as `(1 - α X)(1 - β X)`, then
`tₙ = αⁿ + βⁿ`; the recurrence describes the same sequence without such a factorization. -/
theorem logOf_one_sub_C_mul_X_add_C_mul_X_sq (a q : A) {t : ℕ → A} (h₀ : t 0 = 2) (h₁ : t 1 = a)
    (h : ∀ n, t (n + 2) = a * t (n + 1) - q * t n) :
    logOf (1 - C a * X + C q * X ^ 2) = mk fun n ↦ (n : ℚ)⁻¹ • -t n := by
  rw [logOf_eq_mk_iff (by simp), mul_add, mul_sub, mul_one, mul_comm _ (C a * X),
    mul_comm _ (C q * X ^ 2), mul_assoc, mul_assoc]
  ext (_ | _ | n)
  · simp [h₁]
  · simp [coeff_succ_X_mul, coeff_X_pow_mul', coeff_X, h, h₀, h₁]
  · simp [coeff_succ_X_mul, coeff_X_pow_mul', coeff_X, h (n + 1)]

/-! ## Exponentials of power sums -/

/-- The formal identity `exp (∑ cⁿ Xⁿ / n) = (1 - c X)⁻¹`, stated without inverses. -/
theorem subst_exp_mul_one_sub_C_mul_X (c : A) :
    (exp A).subst (mk fun n ↦ (n : ℚ)⁻¹ • c ^ n) * (1 - C c * X) = 1 := by
  have hL : constantCoeff (mk fun n ↦ (n : ℚ)⁻¹ • c ^ n : A⟦X⟧) = 0 := by simp
  rw [← logOf_inj (by simp [hL]) constantCoeff_one, logOf_mul (constantCoeff_subst_exp hL)
    (by simp), logOf_subst_exp hL, logOf_one_sub_C_mul_X, logOf_one]
  ext n
  simp

/-- **Rationality of an exponential of power sums.** Let `t` satisfy `t₀ = 2`, `t₁ = a` and
`tₙ₊₂ = a tₙ₊₁ - q tₙ`. Then
`exp (∑ (1 + qⁿ - tₙ) Xⁿ / n) = (1 - a X + q X²) / ((1 - X) (1 - q X))`, stated without inverses.

Over a finite field with `q` elements, the zeta function of an elliptic curve with Frobenius
trace `a` has this shape, so this is its rationality once the point counts are expressed through
the trace recurrence. -/
theorem subst_exp_mul_one_sub_X_mul_one_sub_C_mul_X (a q : A) {t : ℕ → A} (h₀ : t 0 = 2)
    (h₁ : t 1 = a) (h : ∀ n, t (n + 2) = a * t (n + 1) - q * t n) :
    (exp A).subst (mk fun n ↦ (n : ℚ)⁻¹ • (1 + q ^ n - t n)) * ((1 - X) * (1 - C q * X)) =
      1 - C a * X + C q * X ^ 2 := by
  have hL : constantCoeff (mk fun n ↦ (n : ℚ)⁻¹ • (1 + q ^ n - t n) : A⟦X⟧) = 0 := by simp
  have hX : (1 - X : A⟦X⟧) = 1 - C 1 * X := by rw [map_one, one_mul]
  rw [← logOf_inj (by simp [hL]) (by simp), logOf_mul (constantCoeff_subst_exp hL) (by simp),
    logOf_mul (by simp) (by simp), logOf_subst_exp hL, hX, logOf_one_sub_C_mul_X,
    logOf_one_sub_C_mul_X, logOf_one_sub_C_mul_X_add_C_mul_X_sq a q h₀ h₁ h]
  ext n
  simp only [map_add, coeff_mk, one_pow, ← smul_add]
  congr 1
  ring

end PowerSeries
