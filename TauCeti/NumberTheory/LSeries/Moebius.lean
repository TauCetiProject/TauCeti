/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# The Dirichlet series of the square of the Möbius function

The squarefree-indicator series converges absolutely exactly on `Re s > 1`, so its abscissa of
absolute convergence is `1`: at `s = 1` its terms at the primes are the divergent `1/p`. On
`Re s > 1` it satisfies `ζ(s) = ζ(2s) L(μ²,s)`. Its local factor at a prime is `1 + p^(-s)`.
At index zero the coefficient and the Dirichlet-series term are both zero.

The argument is adapted from `zeta_alt` and its Möbius-square Euler-product stages in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT].
Specializing to real `σ > 1`
gives the real identity `∑ |μ(n)| n^(-σ) = ζ(σ)/ζ(2σ)`.

Comparing it termwise with `1/L(χ,s) = ∑ χ(n) μ(n) n^(-s)` gives, for every Dirichlet character
`χ`, the lower bound `ζ(2σ)/ζ(σ) ≤ |L(χ,s)|` for `σ = Re s > 1`. For `ζ` itself this is
`1/|ζ(s)| ≤ ζ(σ)/ζ(2σ)`. The bound for `ζ` is
`norm_riemannZeta_ratio_le_on_verticalLine` in
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaConvexity.lean` of [PNTConvexity],
which proves it through the Euler product.

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/05076dfe4e396e6dbdea50fde395a5154341f59e/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1530-L1696
[PNTConvexity]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/f761e9afa785412f0df0a0de48ef807996a9456f/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaConvexity.lean#L35-L54
-/

public section

open Nat Complex
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace TauCeti

/-- The Möbius-square and Möbius Dirichlet-series terms have the same norm. -/
private theorem norm_term_moebius_sq (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n ↦ (μ n : ℂ) ^ 2) s n‖ = ‖LSeries.term ↗μ s n‖ := by
  simp only [LSeries.norm_term_eq]
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- At a real point the Möbius-square Dirichlet-series terms are nonnegative reals. -/
private theorem re_term_moebius_sq (x : ℝ) (n : ℕ) :
    (LSeries.term (fun n ↦ (μ n : ℂ) ^ 2) x n).re =
      ‖LSeries.term (fun n ↦ (μ n : ℂ) ^ 2) x n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpos : 0 ≤ (n : ℝ) ^ x := Real.rpow_nonneg n.cast_nonneg x
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [h, LSeries.term_of_ne_zero hn, ← ofReal_natCast, ← ofReal_cpow n.cast_nonneg,
      abs_of_nonneg hpos]

/-- The Dirichlet series of the square of the Möbius function converges absolutely exactly on
`Re s > 1`. -/
theorem LSeriesSummable_moebius_sq_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) s ↔ 1 < s.re := by
  constructor
  · intro hf
    by_contra! hs
    have hf1 : LSeriesSummable (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) 1 :=
      hf.of_re_le_re (by simpa using hs)
    refine Nat.Primes.not_summable_one_div ((hf1.comp_injective Subtype.val_injective).norm.congr
      fun p ↦ ?_)
    simp [p.prop.ne_zero, ArithmeticFunction.moebius_apply_prime p.prop]
  · intro hs
    rw [LSeriesSummable, ← summable_norm_iff, funext (norm_term_moebius_sq s)]
    exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm

/-- The abscissa of absolute convergence of the Dirichlet series of the square of the Möbius
function is one. -/
theorem abscissaOfAbsConv_moebius_sq :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (ArithmeticFunction.moebius n : ℂ) ^ 2) = 1 :=
  (LSeries.abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_moebius_sq_iff).trans EReal.coe_one

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
      (LSeriesSummable_moebius_sq_iff.mpr hs).norm
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

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- For `1 < re s`, `‖L(χ, s)‖` is bounded below by `ζ(2 re s)/ζ(re s)`, uniformly in the positive
level `N` and the character `χ`. -/
theorem norm_riemannZeta_two_mul_re_div_le_norm_LFunction [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta (2 * s.re) / riemannZeta s.re‖ ≤ ‖LFunction χ s‖ := by
  have hσ : 1 < (s.re : ℂ).re := by simpa using hs
  have hσ2 : 1 < (2 * (s.re : ℂ)).re := by simpa using (by linarith : (1 : ℝ) < 2 * s.re)
  have hμ2 := TauCeti.LSeriesSummable_moebius_sq_iff.mpr hσ
  have hinv := LSeries.mul_mu_eq_one χ hs
  have hζ2 : riemannZeta (2 * s.re) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hσ2
  have hχμ : L (↗χ * ↗μ) s ≠ 0 := right_ne_zero_of_mul_eq_one hinv
  have hbound : ‖L (↗χ * ↗μ) s‖ ≤ ‖L (fun n ↦ (μ n : ℂ) ^ 2) s.re‖ := by
    calc _ ≤ ∑' n, ‖LSeries.term (fun n ↦ (μ n : ℂ) ^ 2) s.re n‖ := by
          refine tsum_of_norm_bounded hμ2.norm.hasSum fun n ↦ ?_
          calc ‖LSeries.term (↗χ * ↗μ) s n‖ ≤ ‖LSeries.term ↗μ s n‖ :=
                LSeries.norm_term_le s
                  (by simpa using mul_le_of_le_one_left (norm_nonneg (μ n : ℂ)) (χ.norm_le_one n))
            _ = _ := by
                rw [← TauCeti.norm_term_moebius_sq, LSeries.norm_term_eq, LSeries.norm_term_eq,
                  ofReal_re]
      _ = (L (fun n ↦ (μ n : ℂ) ^ 2) s.re).re := by
          simp only [LSeries, re_tsum hμ2, TauCeti.re_term_moebius_sq]
      _ ≤ _ := re_le_norm _
  rw [TauCeti.riemannZeta_eq_mul_LSeries_moebius_sq hσ, div_mul_cancel_left₀ hζ2, norm_inv,
    LFunction_eq_LSeries χ hs, eq_inv_of_mul_eq_one_left hinv, norm_inv]
  exact inv_anti₀ (norm_pos_iff.2 hχμ) hbound

end DirichletCharacter

namespace TauCeti

/-- For `1 < re s`, `1/‖ζ(s)‖` is at most `ζ(re s)/ζ(2 re s)`. -/
theorem inv_norm_riemannZeta_le_norm_riemannZeta_re_div {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖⁻¹ ≤ ‖riemannZeta s.re / riemannZeta (2 * s.re)‖ := by
  have hζ : riemannZeta s.re ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  have hζ2 : riemannZeta (2 * s.re) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using (by linarith : (1 : ℝ) < 2 * s.re))
  have h := (1 : DirichletCharacter ℂ 1).norm_riemannZeta_two_mul_re_div_le_norm_LFunction hs
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  rw [← inv_div, norm_inv]
  exact inv_anti₀ (norm_pos_iff.2 (div_ne_zero hζ2 hζ)) h

end TauCeti
