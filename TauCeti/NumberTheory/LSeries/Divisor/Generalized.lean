/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import TauCeti.NumberTheory.ArithmeticFunction.GeneralizedDivisor
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.SumPrimeReciprocals
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct
import TauCeti.NumberTheory.LSeries.Zeta.Pow

/-!
# The Dirichlet series of the generalized divisor function `d_z`

For complex `z`, the Dirichlet series of the generalized divisor function
`d_z = TauCeti.ArithmeticFunction.generalizedDivisor z` converges absolutely on `Re s > 1`, where
it is the Euler-product power of the Riemann zeta function:

`∑ d_z(n) n ^ (-s) = exp (z · L(Λ / log, s))`.

Here `L(Λ / log, s) = ∑ Λ(n) / log n · n ^ (-s)` is the logarithm of `ζ(s)` given by its Euler
product, `exp (L(Λ / log, s)) = ζ(s)` (`riemannZeta_eq_exp_LSeries`). It is not in general the
principal logarithm of the value `ζ(s)`, so the right side is not the principal power
`ζ(s) ^ z`: for `z = 1/2` the two square roots of `ζ(s)` can differ by a sign. At `z = k : ℕ` the
right side is `ζ(s) ^ k`, the series of `d_k = ζ ^ k`. For `z ≠ 0` the abscissa of absolute
convergence is exactly `1`; for `z = 0` the series is the constant `1` and the abscissa is `⊥`.

Absolute convergence comes from the majorant `‖d_z(n)‖ ≤ (ζ ^ k)(n)` for `‖z‖ ≤ k`, whose series
converges absolutely on `Re s > 1`. The series of the multiplicative `d_z` is then the Euler
product of its local factors `∑_a Ring.multichoose z a p ^ (-a s)`. The binomial series
evaluates each as `(1 - p ^ (-s)) ^ (-z) = exp (-z log (1 - p ^ (-s)))`, and the product of these
exponentials is the exponential of `z ∑_p -log (1 - p ^ (-s)) = z L(Λ / log, s)`
(`DirichletCharacter.eulerProduct_log_eq_LSeries` at the trivial character). At `s = 1` the
terms at the primes have modulus `‖z‖ / p`, so the series diverges absolutely there when
`z ≠ 0`.

## Main results

* `TauCeti.LSeries.LSeriesSummable_generalizedDivisor_iff` and
  `TauCeti.LSeries.abscissaOfAbsConv_generalizedDivisor`: for `z ≠ 0` the series of `d_z`
  converges absolutely exactly on `Re s > 1`;
  `TauCeti.LSeries.abscissaOfAbsConv_generalizedDivisor_zero` is the case `z = 0`.
* `TauCeti.LSeries.tsum_term_prime_pow_generalizedDivisor`: the local factor
  `(1 - p ^ (-s)) ^ (-z)`, written as `exp (z · -log (1 - p ^ (-s)))`.
* `TauCeti.LSeries.LSeriesHasSum_generalizedDivisor` and
  `TauCeti.LSeries.LSeries_generalizedDivisor`: `L(d_z, s) = exp (z · L(Λ / log, s))` on
  `Re s > 1`.
* `TauCeti.LSeries.LSeries_generalizedDivisor_add`: `L(d_{z + w}, s) = L(d_z, s) L(d_w, s)`.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter II.5.
* Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*, blueprint,
  Theorems 9.1.11–9.1.12, for `z ∈ ℕ`.
-/

public section

open Complex LSeries ArithmeticFunction TauCeti.ArithmeticFunction
open scoped LSeries.notation

namespace TauCeti.LSeries

/-- For `Re s > 1`, the Dirichlet series of `d_z` converges absolutely. -/
theorem LSeriesSummable_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(generalizedDivisor z) s :=
  .of_norm_bounded (summable_norm_term_zeta_pow ⌈‖z‖⌉₊ hs) fun _ ↦ norm_term_le s <| by
    simpa using norm_generalizedDivisor_le_zeta_pow (Nat.le_ceil ‖z‖) _

/-- For `z ≠ 0`, the Dirichlet series of `d_z` converges absolutely exactly on `Re s > 1`. -/
theorem LSeriesSummable_generalizedDivisor_iff {z : ℂ} (hz : z ≠ 0) {s : ℂ} :
    LSeriesSummable ↗(generalizedDivisor z) s ↔ 1 < s.re := by
  refine ⟨fun hf ↦ ?_, LSeriesSummable_generalizedDivisor z⟩
  by_contra! hs
  -- At `s = 1` the terms at the primes are `z / p`, and `∑_p 1 / p` diverges.
  have hf1 : LSeriesSummable ↗(generalizedDivisor z) 1 := hf.of_re_le_re (by simpa using hs)
  refine Nat.Primes.not_summable_one_div
    (((hf1.comp_injective Subtype.val_injective).norm.mul_left ‖z‖⁻¹).congr fun p ↦ ?_)
  simp [p.prop.ne_zero, generalizedDivisor_apply_prime z p.prop, div_eq_mul_inv,
    inv_mul_cancel_left₀ (norm_ne_zero_iff.2 hz)]

/-- For `z ≠ 0`, the abscissa of absolute convergence of the Dirichlet series of `d_z` is `1`. -/
theorem abscissaOfAbsConv_generalizedDivisor {z : ℂ} (hz : z ≠ 0) :
    abscissaOfAbsConv ↗(generalizedDivisor z) = 1 :=
  (abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_generalizedDivisor_iff hz).trans EReal.coe_one

/-- At `z = 0` the series of `d_0 = 1` is the constant `1`, so its abscissa of absolute
convergence is `⊥`. -/
theorem abscissaOfAbsConv_generalizedDivisor_zero :
    abscissaOfAbsConv ↗(generalizedDivisor (0 : ℂ)) = ⊥ := by
  refine le_bot_iff.1 <| abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y _ ↦ ?_
  refine summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_
  simp [term, one_apply_ne (Finset.notMem_singleton.1 hn)]

/-- The local factor at `p` of the series of `d_z` is `(1 - p ^ (-s)) ^ (-z)`, written through
the principal logarithm of `1 - p ^ (-s)`, which lies in the right half-plane. -/
theorem tsum_term_prime_pow_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    ∑' e : ℕ, term ↗(generalizedDivisor z) s (p ^ e) =
      exp (z * -log (1 - (p : ℂ) ^ (-s))) := by
  have hq : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (neg_neg_of_pos hs)
  have hq0 : 1 - (p : ℂ) ^ (-s) ≠ 0 := fun h ↦ by
    simp [← sub_eq_zero.mp h] at hq
  have h := hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := z) hq
  simp only [← generalizedDivisor_apply_prime_pow z p.prop, ← term_pow p p.prop.ne_zero] at h
  rw [h.tsum_eq, cpow_def_of_ne_zero hq0, one_div, ← exp_neg, mul_neg, mul_comm]

/-- **The Dirichlet series of `d_z`.** For `Re s > 1`, the series `∑ d_z(n) n ^ (-s)` converges
absolutely to `exp (z · L(Λ / log, s))`, the power `ζ(s) ^ z` defined through the Euler-product
logarithm `L(Λ / log, s)` of `ζ(s)`. -/
theorem LSeriesHasSum_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum ↗(generalizedDivisor z) s
      (exp (z * LSeries (fun n ↦ Λ n / Real.log n) s)) := by
  have hsum := LSeriesSummable_generalizedDivisor z hs
  -- The Euler product of the multiplicative `d_z`, with the local factors evaluated.
  have hprod := EulerProduct.eulerProduct_hasProd (by simp)
    (term_mul_of_coprime fun _ _ hmn ↦ (isMultiplicative_generalizedDivisor z).map_mul_of_coprime
      hmn) hsum.norm (term_zero _ s)
  simp only [tsum_term_prime_pow_generalizedDivisor z (zero_lt_one.trans hs)] at hprod
  -- The product of the exponentials is the exponential of the summed logarithms.
  have hlog : Summable fun p : Nat.Primes ↦ z * -log (1 - (p : ℂ) ^ (-s)) := by
    refine ((Summable.clog_one_sub (f := fun n : ℕ ↦ (n : ℂ) ^ (-s)) ?_).neg.mul_left
      z).comp_injective Subtype.val_injective
    simpa [cpow_neg] using summable_one_div_nat_cpow.mpr hs
  -- `∑_p -log (1 - p ^ (-s))` is the Euler-product logarithm `L(Λ / log, s)`.
  have hL := DirichletCharacter.eulerProduct_log_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
  simp only [MulChar.one_apply (isUnit_of_subsingleton _), one_mul] at hL
  have hexp := hlog.hasSum.cexp
  rw [tsum_mul_left, hL] at hexp
  rw [← hprod.unique hexp]
  exact hsum.LSeriesHasSum

/-- For `Re s > 1`, `L(d_z, s) = exp (z · L(Λ / log, s))`. -/
theorem LSeries_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor z) s = exp (z * LSeries (fun n ↦ Λ n / Real.log n) s) :=
  (LSeriesHasSum_generalizedDivisor z hs).LSeries_eq

/-- On `Re s > 1` the series of the family `d_z` multiply as the exponents add:
`L(d_{z + w}, s) = L(d_z, s) L(d_w, s)`. -/
theorem LSeries_generalizedDivisor_add (z w : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor (z + w)) s =
      LSeries ↗(generalizedDivisor z) s * LSeries ↗(generalizedDivisor w) s := by
  simp only [LSeries_generalizedDivisor _ hs, add_mul, exp_add]

/-! ### Examples -/

/-- At `z = k : ℕ` the Euler-product power is the ordinary power: `L(d_k, s) = ζ(s) ^ k`. -/
example (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor (k : ℂ)) s = riemannZeta s ^ k := by
  rw [LSeries_generalizedDivisor _ hs, exp_natCast_mul, riemannZeta_eq_exp_LSeries hs]

/-- `L(d_{1/2}, s)` is a square root of `ζ(s)` on `Re s > 1`. -/
example {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor (1 / 2 : ℂ)) s ^ 2 = riemannZeta s := by
  rw [sq, ← LSeries_generalizedDivisor_add _ _ hs, add_halves, LSeries_generalizedDivisor _ hs,
    one_mul, riemannZeta_eq_exp_LSeries hs]

end TauCeti.LSeries
