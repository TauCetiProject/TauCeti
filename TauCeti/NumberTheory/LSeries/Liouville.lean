/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import TauCeti.NumberTheory.LSeries.Convergence

/-!
# The Dirichlet series of the Liouville function

The canonical Liouville coefficients have absolute value one at every positive index. Their
Dirichlet series therefore converges absolutely exactly on `Re s > 1`, and there it has sum
`ζ(2s) / ζ(s)`.

The quotient identity follows the Euler-product argument in
[Arend Mellendijk and the PNT+ contributors, Prime Number Theorem and More][PNT],
`LSeries_liouville_eq`, using Mathlib's canonical Liouville function and completely
multiplicative Euler product.

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/f2692ef9a88ca93932d61265c73dd3491fbc08d8/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L1860-L1897
-/

public section

open Nat Complex ArithmeticFunction

namespace TauCeti

/-- The Liouville Dirichlet series converges absolutely exactly on `Re s > 1`. -/
theorem LSeriesSummable_liouville_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (liouville n : ℂ)) s ↔ 1 < s.re := by
  have hnorm : (fun n ↦ ‖_root_.LSeries.term (fun n ↦ (liouville n : ℂ)) s n‖) =
      (fun n ↦ ‖_root_.LSeries.term 1 s n‖) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [liouville_apply hn, hn]
  calc
    LSeriesSummable (fun n ↦ (liouville n : ℂ)) s ↔
        Summable (fun n ↦ ‖_root_.LSeries.term (fun n ↦ (liouville n : ℂ)) s n‖) :=
      by rw [LSeriesSummable]; exact summable_norm_iff.symm
    _ ↔ Summable (fun n ↦ ‖_root_.LSeries.term 1 s n‖) := by rw [hnorm]
    _ ↔ LSeriesSummable 1 s := by rw [LSeriesSummable]; exact summable_norm_iff
    _ ↔ 1 < s.re := LSeriesSummable_one_iff

/-- The abscissa of absolute convergence of the Liouville Dirichlet series is one. -/
theorem abscissaOfAbsConv_liouville :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (liouville n : ℂ)) = 1 :=
  (LSeries.abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦
    LSeriesSummable_liouville_iff).trans EReal.coe_one


/-- The Liouville Dirichlet series has sum `ζ(2s) / ζ(s)` on `Re s > 1`. -/
theorem LSeriesHasSum_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (ArithmeticFunction.liouville n : ℂ)) s
      (riemannZeta (2 * s) / riemannZeta s) := by
  let a : ℕ →*₀ ℂ :=
    { toFun := fun n ↦ (ArithmeticFunction.liouville n : ℂ)
      map_zero' := by simp
      map_one' := by simp [ArithmeticFunction.liouville_apply_one]
      map_mul' := fun m n ↦ by simp [ArithmeticFunction.liouville_apply_mul] }
  let f : ℕ →*₀ ℂ := a * riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  have hf (n : ℕ) : f n = (ArithmeticFunction.liouville n : ℂ) * (n : ℂ) ^ (-s) := rfl
  have hterm (n : ℕ) :
      f n = _root_.LSeries.term (fun n ↦ (ArithmeticFunction.liouville n : ℂ)) s n := by
    rw [hf, _root_.LSeries.term_def₀ (by simp)]
  have hprime (p : Primes) : f p = -(p : ℂ) ^ (-s) := by
    rw [hf]
    simp [ArithmeticFunction.liouville_apply p.prop.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime p.prop]
  have hsum := LSeriesSummable_liouville_iff.mpr hs
  have hp : HasProd (fun p : Primes ↦ (1 + (p : ℂ) ^ (-s))⁻¹)
      (_root_.LSeries (fun n ↦ (ArithmeticFunction.liouville n : ℂ)) s) := by
    have H := EulerProduct.eulerProduct_completely_multiplicative_hasProd
      (f := f) (by simpa only [hterm] using hsum.norm)
    simpa only [hprime, sub_neg_eq_add, hterm, _root_.LSeries] using H
  have hs2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hp2 : HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-(2 * s)))⁻¹)
      (_root_.LSeries (fun n ↦ (ArithmeticFunction.liouville n : ℂ)) s *
        riemannZeta s) := by
    convert hp.mul (riemannZeta_eulerProduct_hasProd hs) using 1
    funext p
    have hexponent : -(2 * s) = -s + -s := by ring
    rw [hexponent, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr p.prop.ne_zero), ← mul_inv]
    congr 1
    ring
  refine LSeriesHasSum_iff.mpr ⟨hsum, ?_⟩
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr
    (hp2.unique (riemannZeta_eulerProduct_hasProd hs2))

end TauCeti
