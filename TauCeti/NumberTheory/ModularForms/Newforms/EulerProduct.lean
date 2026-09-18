/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.ModularForms.LFunction
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# The Euler product of a normalised Hecke eigenform

Let `f ∈ S_k(N, χ)` be a normalised full Hecke eigenform (`a₁(f) = 1`). Its L-series
`L(s, f) = ∑ₙ aₙ(f) n^{-s}` converges absolutely for `Re s > k/2 + 1`, and there

`L(s, f) = ∏ₚ (1 - a_p(f) p^{-s} + χ(p) p^{k-1-2s})⁻¹`,

with the nebentypus zero-extended to the primes dividing the level through Mathlib's
`MulChar.ofUnitHom`, so that the bad factors are `(1 - a_p(f) p^{-s})⁻¹`.

The proof feeds the coefficient identities of `Newforms/Eigenform.lean` (multiplicativity at
coprime indices and the prime-power recurrence, at good and bad primes alike) into the general
degree-two Euler product `TauCeti.LSeries.eulerProduct_hasProd_of_prime_pow_recurrence`, on the
half-plane of absolute convergence supplied by Hecke's bound
`CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`.

The hypothesis is a *full* eigenform, eigen for `T_n` at every `n` including the `U_p` with
`p ∣ N`, as in Diamond–Shurman's Theorem 5.9.2: the bad Euler factors depend on the
`U_p`-eigenvalues. A newform is such a form by the Atkin–Lehner–Li theorem.

## Main results

* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`,
  `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_tprod`: the Euler product.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.9.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.16.
-/

public section

open Complex LSeries UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The Euler product of a normalised full Hecke eigenform**, as a `HasProd`: for
`Re s > k/2 + 1`,
`L(s, f) = ∏ₚ (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹`, with `χ(p) = 0` for `p ∣ N`
(Diamond–Shurman Theorem 5.9.2). -/
theorem LSeries_eulerProduct_hasProd (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  have hsum : LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s := by
    have hab := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le
      (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) f.toCuspForm
    rw [strictWidthInfty_Gamma1] at hab
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re (hab.trans_lt ?_)
    exact_mod_cast hs
  have h := TauCeti.LSeries.eulerProduct_hasProd_of_prime_pow_recurrence
    (d := fun p ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) h₁
    (f.qExpansion_coeff_mul h₁) (fun p hp r ↦ f.qExpansion_coeff_prime_pow_add_two h₁ hp r) hsum
  convert h using 4 with p
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  rw [mul_assoc, ← cpow_intCast, ← cpow_add _ _ hp0]
  push_cast
  ring_nf

/-- **The Euler product of a normalised full Hecke eigenform**, as a `tprod`: see
`HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`. -/
theorem LSeries_eulerProduct_tprod (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ =
      LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
  (f.LSeries_eulerProduct_hasProd h₁ hs).tprod_eq

end HeckeRing.GL2.Eigenform
