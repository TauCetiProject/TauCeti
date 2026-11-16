/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Dirichlet series of the square of the Möbius function

On `Re s > 1`, the squarefree-indicator series is absolutely convergent and satisfies
`ζ(s) = ζ(2s) L(μ²,s)`. Its local factor at a prime is `1 + p^(-s)`.
At index zero the coefficient and the Dirichlet-series term are both zero.

The argument is adapted from `zeta_alt` and its Möbius-square Euler-product stages in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT].
Specializing to real `σ > 1`
gives the real identity `∑ |μ(n)| n^(-σ) = ζ(σ)/ζ(2σ)`.

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/05076dfe4e396e6dbdea50fde395a5154341f59e/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1530-L1696
-/

public section

open Nat Complex
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The square of the Möbius function has an absolutely convergent Dirichlet series
on `Re s > 1`. -/
theorem LSeriesSummable_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s := by
  have hnorm :
      (fun n ↦ ‖_root_.LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s n‖) =
      (fun n ↦ ‖_root_.LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) s n‖) := by
    funext n
    simp only [_root_.LSeries.norm_term_eq]
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
  rw [LSeriesSummable]
  rw [← summable_norm_iff, hnorm]
  exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm


private theorem moebius_sq_prime_pow_sum {s : ℂ} {p : Nat.Primes} :
    (∑' e : ℕ, _root_.LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2)
      s (p.val ^ e)) = 1 + (p : ℂ) ^ (-s) := by
  rw [tsum_eq_sum (s := {0, 1})]
  · have hμ := ArithmeticFunction.moebius_apply_prime p.prop
    simp [TauCeti.LSeries.term_pow p p.prop.ne_zero, hμ]
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [TauCeti.LSeries.term_pow p p.prop.ne_zero e]
    simp [ArithmeticFunction.moebius_apply_prime_pow p.prop he.1, he.2]

/-- The Möbius-square Dirichlet series has the squarefree Euler product on `Re s > 1`. -/
theorem LSeries_moebius_sq_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ 1 + (p : ℂ) ^ (-s))
      (_root_.LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s) := by
  have hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      (ArithmeticFunction.moebius (m * n) : ℂ) ^ 2 =
        (ArithmeticFunction.moebius m : ℂ) ^ 2 *
          (ArithmeticFunction.moebius n : ℂ) ^ 2 := by
    intro m n _ _ hmn
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast
    ring
  have hp : HasProd (fun p : Nat.Primes ↦ ∑' e : ℕ,
      _root_.LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s (p.val ^ e))
      (_root_.LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s) :=
    EulerProduct.eulerProduct_hasProd (by simp)
    (TauCeti.LSeries.term_mul_of_coprime hmul)
      (TauCeti.LSeriesSummable_moebius_sq hs).norm
    (_root_.LSeries.term_zero (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s)
  simpa only [moebius_sq_prime_pow_sum] using hp

/-- The Möbius-square series gives the Euler correction `ζ(s) = ζ(2s) L(μ²,s)`
throughout the full complex half-plane `Re s > 1`. -/
theorem riemannZeta_eq_mul_LSeries_moebius_sq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = riemannZeta (2 * s) *
      _root_.LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s := by
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hfactor (p : Nat.Primes) :
      (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * (1 + (p : ℂ) ^ (-s)) =
        (1 - (p : ℂ) ^ (-s))⁻¹ := by
    have hexp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
      have hneg : -(2 * s) = -s + -s := by ring
      rw [hneg, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), pow_two]
    have h1 := Complex.one_sub_prime_cpow_ne_zero p.prop hs
    have h2 := Complex.one_sub_prime_cpow_ne_zero p.prop hs2
    rw [hexp] at h2 ⊢
    field_simp
    ring
  have hprod := (riemannZeta_eulerProduct_hasProd hs2).mul
    (LSeries_moebius_sq_eulerProduct_hasProd hs)
  have H : HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹)
      (riemannZeta (2 * s) *
        _root_.LSeries (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s) := by
    simpa only [hfactor] using hprod
  exact (riemannZeta_eulerProduct_hasProd hs).unique H

end TauCeti
