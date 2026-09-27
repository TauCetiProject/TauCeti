/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# Euler products of full Hecke eigenforms

The Fourier coefficients of a normalized full Hecke eigenform are multiplicative at coprime
indices and obey the quadratic Hecke recurrence at every prime. These are precisely the
hypotheses of `TauCeti.LSeries.LSeries_eulerProduct_tprod_of_recurrence`. The character is
extended by zero at primes dividing the level, so the quadratic Euler factor becomes linear
there.

This gives the Euler product for the coefficient L-series. The newform version follows once
the bad-prime eigenrelations upgrade a newform to a full eigenform.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Proposition 5.8.5 and §5.9.
-/

public section

noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GL2
open scoped MatrixGroups

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

private lemma coeff_summable (f : Eigenform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
  LSeriesSummable_of_isBigO_rpow hs (by
    simpa [strictWidthInfty_Gamma1] using
      CuspFormClass.qExpansion_isBigO f.toCuspForm)

/-- The local prime-power series of a normalized full Hecke eigenform is the inverse of its
quadratic Hecke factor. At a prime dividing the level the character term is zero. -/
theorem primePowerSeries_eq_inv (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' r : ℕ,
      LSeries.term (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s (p ^ r)) =
      (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
          (p : ℂ) ^ (-2 * s))⁻¹ := by
  exact TauCeti.LSeries.tsum_term_prime_pow_eq_inv_of_recurrence
    (c := fun q ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) q * (q : ℂ) ^ (k - 1))
    h₁ ⟨p, hp⟩
    (fun r ↦ by simpa only [← mul_assoc] using f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    ((f.coeff_summable hs).comp_injective (Nat.pow_right_injective hp.two_le))

/-- **Euler product of a normalized full Hecke eigenform.** On `Re s > k/2 + 1`, its
coefficient L-series is the product of the quadratic Hecke factors. The zero-extended
Dirichlet character makes the factors linear at bad primes. -/
theorem eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹ := by
  symm
  exact TauCeti.LSeries.LSeries_eulerProduct_tprod_of_recurrence
    (c := fun q ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) q * (q : ℂ) ^ (k - 1)) h₁
    (fun hm hn hmn ↦ f.qExpansion_coeff_mul h₁ hmn)
    (fun p hp r ↦ by
      simpa only [← mul_assoc] using f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    (f.coeff_summable hs)

/-- The Euler product in Mathlib's `ModularForm.L` normalization. At level `Γ₁(N)` the
width at infinity is one, so its Dirichlet series is the coefficient L-series above. -/
theorem L_eq_eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForm.L hk f.toCuspForm s =
      ∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹ := by
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rw [← hL]
  exact f.eulerProduct h₁ hs

end HeckeRing.GL2.Eigenform
