/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Root averaging of integral polynomials

For an integral polynomial `P` and a primitive `p`-th root of unity `ζ`, the sum of the
translated polynomials `P(ζⁱ(1 + X) - 1)` is `p` times Frobenius after the bounded psi
operator applied to `P`. The identity holds after any coefficient homomorphism from `ℤ_p`
to a domain containing `ζ`; no topology on the receiving ring is required.

This is the polynomial form of root averaging for bounded measures. The factor `p` is kept
on the integral side, so the identity does not require division by `p`. Translation is
polynomial evaluation, including the constant term `ζⁱ - 1`, rather than formal substitution
of an infinite series at a series with nonzero constant coefficient.

## Main results

* `IsPrimitiveRoot.sum_eval₂_mul_one_add_X_sub_one`: the polynomial root-average identity.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  Sections 3.5.3–3.5.5, equations (3-5), (3-6), and (3-9).
-/

public noncomputable section

open PowerSeries TauCeti

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [IsDomain R]

/-- Summing the root translates of an integral polynomial gives `p` times its
Frobenius-after-psi projection, after extending coefficients to any domain containing a
primitive `p`-th root of unity. -/
theorem sum_eval₂_mul_one_add_X_sub_one {ζ : R} (hζ : IsPrimitiveRoot ζ p)
    (j : ℤ_[p] →+* R) (P : Polynomial ℤ_[p]) :
    ∑ i : Fin p, P.eval₂ (C.comp j) (C (ζ ^ (i : ℕ)) * (1 + X) - 1) =
      (p : R⟦X⟧) * map j ((psiSeries p (P : ℤ_[p]⟦X⟧)).subst
        ((1 + X) ^ p - 1)) := by
  have hb : HasSubst ((1 + X : ℤ_[p]⟦X⟧) ^ p - 1) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  simp only [← coe_substAlgHom hb]
  -- Taylor translation reduces the identity to the known psi formula on `(1 + X)^n`.
  obtain ⟨Q, hP⟩ : ∃ Q, Polynomial.taylor 1 Q = P :=
    ⟨Polynomial.taylor (-1) P, by
      simp only [Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]⟩
  rw [← hP]
  clear hP P
  induction Q using Polynomial.induction_on' with
  | add Q S hQ hS =>
      simpa only [map_add, Polynomial.coe_add, Polynomial.eval₂_add, Finset.sum_add_distrib,
        mul_add] using congrArg₂ (· + ·) hQ hS
  | monomial n a =>
      rw [Polynomial.taylor_monomial]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.comp_apply,
        Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one,
        map_one, sub_add_cancel, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one]
      have hsmul : C a * (X + 1 : ℤ_[p]⟦X⟧) ^ n = a • (1 + X) ^ n := by
        simp [Algebra.smul_def, add_comm]
      rw [hsmul, map_smul, psiSeries_one_add_X_pow]
      simp only [mul_pow, ← map_pow, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
      have hsum : ∑ i : Fin p, (ζ ^ (i : ℕ)) ^ n = if p ∣ n then (p : R) else 0 := by
        simpa only [← pow_mul, Nat.mul_comm] using hζ.sum_pow_pow_eq n
      rw [hsum]
      split_ifs with hn
      · simp only [map_smul, map_pow, map_add, map_one, substAlgHom_X hb,
          ← add_sub_assoc, add_sub_cancel_left]
        rw [← pow_mul, Nat.mul_div_cancel' hn]
        simp [Algebra.smul_def, mul_comm, mul_assoc]
      · simp

end IsPrimitiveRoot

namespace TauCeti

-- The dyadic formula keeps both the translated constant term and the factor two.
example (P : Polynomial ℤ_[2]) :
    P.eval₂ C (X : ℤ_[2]⟦X⟧) + P.eval₂ C (-2 - X) =
      2 * (psiSeries 2 (P : ℤ_[2]⟦X⟧)).subst ((1 + X) ^ 2 - 1) := by
  have hζ : IsPrimitiveRoot (-1 : ℤ_[2]) 2 :=
    IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num)
  have h := hζ.sum_eval₂_mul_one_add_X_sub_one (RingHom.id ℤ_[2]) P
  have ht : C (-1 : ℤ_[2]) * (1 + X) - 1 = (-2 - X : ℤ_[2]⟦X⟧) := by
    simp only [map_neg, map_one]
    ring
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [ht] at h
  simpa using h

example :
    (Polynomial.X : Polynomial ℤ_[2]).eval₂ C (X : ℤ_[2]⟦X⟧) +
      (Polynomial.X : Polynomial ℤ_[2]).eval₂ C (-2 - X) = -2 := by
  simp

end TauCeti
