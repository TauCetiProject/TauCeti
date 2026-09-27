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

This gives the Euler product for the coefficient L-series and, through the width-one
normalization, for Mathlib's `ModularForm.L`. It applies to newforms equipped with a full
eigenform structure from their bad-prime eigenrelations.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Proposition 5.8.5 and §5.9.
-/

public section

noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GL2 Filter Topology
open scoped MatrixGroups

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The quadratic Euler factors of a normalized full Hecke eigenform have product equal to
its coefficient L-series on `Re s > k/2 + 1`. The zero-extended character makes the factors
linear at bad primes. -/
theorem LSeries_eulerProduct_hasProd (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  have habs := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f.toCuspForm
  rw [strictWidthInfty_Gamma1] at habs
  have hsum : LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (habs.trans_lt (by exact_mod_cast hs))
  exact TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence
    (a := fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) (s := s)
    (c := fun q ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) q * (q : ℂ) ^ (k - 1)) h₁
    (fun hm hn hmn ↦ f.qExpansion_coeff_mul h₁ hmn)
    (fun p hp r ↦ by
      simpa only [← mul_assoc] using f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    hsum

/-- **Euler product of a normalized full Hecke eigenform**, as a `tprod` equality on
`Re s > k/2 + 1`. -/
theorem LSeries_eulerProduct_tprod (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹) =
      LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
  (f.LSeries_eulerProduct_hasProd h₁ hs).tprod_eq

/-- Finite products of the quadratic Euler factors converge to the coefficient L-series. -/
theorem LSeries_eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦
        ∏ p ∈ Nat.primesBelow n,
          (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
              (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹)
      atTop (𝓝 (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s)) := by
  let F : ℕ → ℂ := fun p ↦
    (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
      (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
        (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹
  have hprod : HasProd (fun p : Nat.Primes ↦ F p)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) :=
    f.LSeries_eulerProduct_hasProd h₁ hs
  have h := ((hasProd_subtype_iff_mulIndicator (f := F)
    (s := {p : ℕ | Nat.Prime p})).mp hprod).tendsto_prod_nat
  have H (n : ℕ) : ∏ i ∈ Finset.range n, Set.mulIndicator {p | Nat.Prime p} F i =
      ∏ p ∈ Nat.primesBelow n, F p :=
    Finset.prod_mulIndicator_eq_prod_filter (Finset.range n) (fun _ ↦ F)
      (fun _ ↦ {p | Nat.Prime p}) id
  simpa only [F, H] using h

/-- The Euler product in Mathlib's `ModularForm.L` normalization. At level `Γ₁(N)` the
width at infinity is one, so its Dirichlet series is the coefficient L-series above. -/
theorem L_eulerProduct_tprod (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹) =
      ModularForm.L hk f.toCuspForm s := by
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rw [← hL]
  exact f.LSeries_eulerProduct_tprod h₁ hs

/-- The quadratic Euler factors have product equal to Mathlib's `ModularForm.L` for a
normalized full Hecke eigenform. -/
theorem L_eulerProduct_hasProd (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹)
      (ModularForm.L hk f.toCuspForm s) := by
  have h := f.LSeries_eulerProduct_hasProd h₁ hs
  rw [← f.LSeries_eulerProduct_tprod h₁ hs, f.L_eulerProduct_tprod h₁ hk hs] at h
  exact h

/-- Finite products of the quadratic Euler factors converge to Mathlib's `ModularForm.L`. -/
theorem L_eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦
        ∏ p ∈ Nat.primesBelow n,
          (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
              (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹)
      atTop (𝓝 (ModularForm.L hk f.toCuspForm s)) := by
  have h := f.LSeries_eulerProduct h₁ hs
  rw [← f.LSeries_eulerProduct_tprod h₁ hs, f.L_eulerProduct_tprod h₁ hk hs] at h
  exact h

end HeckeRing.GL2.Eigenform
