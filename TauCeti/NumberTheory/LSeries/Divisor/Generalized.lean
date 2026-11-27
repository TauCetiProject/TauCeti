/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import TauCeti.NumberTheory.ArithmeticFunction.GeneralizedDivisor
import Mathlib.NumberTheory.SumPrimeReciprocals
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct
import TauCeti.NumberTheory.LSeries.Zeta.Pow

/-!
# The Dirichlet series of the generalized divisor function `d_z`

For complex `z`, the Dirichlet series of the generalized divisor function
`d_z = TauCeti.ArithmeticFunction.generalizedDivisor z` converges absolutely on `Re s > 1` and
equals the Euler-product power of the Riemann zeta function,

`∑ d_z(n) n ^ (-s) = exp(z · ∑ Λ(n) / log n · n ^ (-s))`.

The series in the exponent is the logarithm of `ζ(s)` given by its Euler product, whose
exponential is `ζ(s)` (`riemannZeta_eq_exp_LSeries`); it is not the principal logarithm of the
value `ζ(s)`. Where the two logarithms differ by `2πik`, the principal power `ζ(s) ^ z` differs
from the series by the factor `exp(2πikz)`, which is not `1` unless `kz` is an integer. For
`z ≠ 0` the abscissa of absolute convergence is exactly `1`.

Absolute convergence comes from the domination of `d_z` by the divisor function `ζ ^ ⌈‖z‖⌉₊`,
whose series is `ζ(s) ^ ⌈‖z‖⌉₊`. The series is then the product over the primes of its local
factors `∑_k Ring.multichoose z k p ^ (-ks)`, which the binomial series sums to
`(1 - p ^ (-s)) ^ (-z) = exp(-z log(1 - p ^ (-s)))`; the sum over the primes of
`-log(1 - p ^ (-s))` is the series of `Λ(n) / log n`. Conversely, `d_z(p) = z`, so at real
`s ≤ 1` the terms at the primes alone, of size `‖z‖ / p ^ s`, already diverge.

## Main results

* `TauCeti.LSeries.LSeriesSummable_generalizedDivisor_iff`: for `z ≠ 0` the series of `d_z`
  converges absolutely exactly on `Re s > 1`.
* `TauCeti.LSeries.LSeries_generalizedDivisor_eulerProduct_hasProd`: the Euler product
  `∏_p (1 - p ^ (-s)) ^ (-z)`.
* `TauCeti.LSeries.LSeries_generalizedDivisor`: the series is `exp(z · L(Λ / log, s))`.
* `TauCeti.LSeries.abscissaOfAbsConv_generalizedDivisor`: for `z ≠ 0` the abscissa of absolute
  convergence is `1`; at `z = 0` it is `⊥`
  (`TauCeti.LSeries.abscissaOfAbsConv_generalizedDivisor_zero`).

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter II.5.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, (1.25).
-/

public section

open ArithmeticFunction TauCeti.ArithmeticFunction Complex
open scoped LSeries.notation ArithmeticFunction.zeta

namespace TauCeti.LSeries

/-- The series of `d_z` converges absolutely on `Re s > 1`: it is dominated by the series of the
divisor function `ζ ^ ⌈‖z‖⌉₊`. -/
theorem LSeriesSummable_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(generalizedDivisor z) s :=
  Summable.of_norm_bounded (summable_norm_term_zeta_pow ⌈‖z‖⌉₊ hs) fun n ↦
    _root_.LSeries.norm_term_le s (by
      simpa only [Complex.norm_natCast] using norm_generalizedDivisor_le_zeta_pow z n)

/-- For `z ≠ 0` the series of `d_z` converges absolutely exactly on `Re s > 1`. -/
theorem LSeriesSummable_generalizedDivisor_iff {z : ℂ} (hz : z ≠ 0) {s : ℂ} :
    LSeriesSummable ↗(generalizedDivisor z) s ↔ 1 < s.re := by
  refine ⟨fun h ↦ ?_, LSeriesSummable_generalizedDivisor z⟩
  -- Restricted to the primes, the terms have norm `‖z‖ p ^ (-Re s)`.
  have hp : Summable fun p : Nat.Primes ↦ ‖z‖⁻¹ * ‖_root_.LSeries.term
      ↗(generalizedDivisor z) s p‖ :=
    (h.norm.comp_injective Subtype.val_injective).mul_left _
  have hprimes : Summable fun p : Nat.Primes ↦ (p : ℝ) ^ (-s.re) := by
    refine hp.congr fun p ↦ ?_
    rw [_root_.LSeries.term_of_ne_zero p.prop.ne_zero, generalizedDivisor_apply_prime z p.prop,
      norm_div, norm_natCast_cpow_of_pos p.prop.pos, Real.rpow_neg (Nat.cast_nonneg _)]
    field_simp
  have := Nat.Primes.summable_rpow.mp hprimes
  linarith

/-- The local factor of the series of `d_z` at a prime `p` is `(1 - p ^ (-s)) ^ (-z)`, the
binomial series in `p ^ (-s)`. -/
private theorem tsum_term_generalizedDivisor_prime_pow (z : ℂ) {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    ∑' k : ℕ, _root_.LSeries.term ↗(generalizedDivisor z) s (p.val ^ k) =
      exp (z * -log (1 - (p : ℂ) ^ (-s))) := by
  have hq : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hs)
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hq
    exact lt_irrefl 1 hq
  have h := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := z) hq
  rw [cpow_def_of_ne_zero hne, one_div, ← exp_neg, ← neg_mul, mul_comm] at h
  refine Eq.trans (tsum_congr fun k ↦ ?_) h.tsum_eq
  rw [term_pow _ p.prop.ne_zero, generalizedDivisor_apply_prime_pow z p.prop]

/-- **The Euler product of `d_z`.** For `Re s > 1`, the series of `d_z` is the product over the
primes of `(1 - p ^ (-s)) ^ (-z) = exp(-z log(1 - p ^ (-s)))`. -/
theorem LSeries_generalizedDivisor_eulerProduct_hasProd (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ exp (z * -log (1 - (p : ℂ) ^ (-s))))
      (LSeries ↗(generalizedDivisor z) s) := by
  have H := EulerProduct.eulerProduct_hasProd (by simp)
    (term_mul_of_coprime fun _ _ hmn ↦
      (isMultiplicative_generalizedDivisor z).map_mul_of_coprime hmn)
    (LSeriesSummable_generalizedDivisor z hs).norm (_root_.LSeries.term_zero _ s)
  simpa only [_root_.LSeries,
    tsum_term_generalizedDivisor_prime_pow z (zero_lt_one.trans hs)] using H

/-- **The Dirichlet series of `d_z`.** For `Re s > 1`,
`∑ d_z(n) n ^ (-s) = exp(z · ∑ Λ(n) / log n · n ^ (-s))`, the power `ζ(s) ^ z` defined through
the Euler-product logarithm of `ζ(s)`. -/
theorem LSeries_generalizedDivisor (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor z) s = exp (z * LSeries (fun n ↦ Λ n / Real.log n) s) := by
  have hsum : Summable fun p : Nat.Primes ↦ (p : ℂ) ^ (-s) := by
    refine Summable.of_norm ((Nat.Primes.summable_rpow.mpr (by linarith : -s.re < -1)).congr
      fun p ↦ ?_)
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]
  -- The logarithm of the Euler product of `ζ` is the series of `Λ / log`.
  have hlog : ∑' p : Nat.Primes, -log (1 - (p : ℂ) ^ (-s)) =
      LSeries (fun n ↦ Λ n / Real.log n) s := by
    convert DirichletCharacter.eulerProduct_log_eq_LSeries (1 : DirichletCharacter ℂ 1) hs
      using 4 <;> simp [MulChar.one_apply (isUnit_of_subsingleton _)]
  have hexp := (hsum.clog_one_sub.neg.hasSum.mul_left z).cexp
  rw [hlog] at hexp
  exact (LSeries_generalizedDivisor_eulerProduct_hasProd z hs).unique hexp

/-- For `z ≠ 0` the abscissa of absolute convergence of the series of `d_z` is `1`. -/
theorem abscissaOfAbsConv_generalizedDivisor {z : ℂ} (hz : z ≠ 0) :
    _root_.LSeries.abscissaOfAbsConv ↗(generalizedDivisor z) = 1 :=
  (abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_generalizedDivisor_iff hz).trans EReal.coe_one

/-- At `z = 0` the series of `d_0 = 1` has the single term `1`, so it converges absolutely
everywhere and its abscissa of absolute convergence is `⊥`. -/
theorem abscissaOfAbsConv_generalizedDivisor_zero :
    _root_.LSeries.abscissaOfAbsConv ↗(generalizedDivisor (0 : ℂ)) = ⊥ := by
  rw [generalizedDivisor_zero, one_eq_delta]
  refine le_bot_iff.mp
    (_root_.LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun y _ ↦ ?_)
  rw [LSeriesSummable, funext (_root_.LSeries.term_delta _)]
  exact (hasSum_ite_eq 1 1).summable

/-! ### Examples -/

/-- The series of `d_{1/2}` is a square root of `ζ(s)` on `Re s > 1`. -/
example {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(generalizedDivisor (2⁻¹ : ℂ)) s ^ 2 = riemannZeta s := by
  rw [LSeries_generalizedDivisor _ hs, ← exp_natCast_mul, ← mul_assoc, Nat.cast_ofNat,
    mul_inv_cancel₀ two_ne_zero, one_mul, riemannZeta_eq_exp_LSeries hs]

end TauCeti.LSeries
