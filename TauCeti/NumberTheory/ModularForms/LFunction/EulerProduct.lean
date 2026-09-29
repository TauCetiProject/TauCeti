/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# Euler products of full Hecke eigenforms and newforms

The Fourier coefficients of a normalized full Hecke eigenform are multiplicative at coprime
indices and obey the quadratic Hecke recurrence at every prime. These are precisely the
hypotheses of `TauCeti.LSeries.LSeries_eulerProduct_tprod_of_recurrence`. The character is
extended by zero at primes dividing the level, so the quadratic Euler factor becomes linear
there.

This gives the Euler product for the coefficient L-series and, through the width-one
normalization, for Mathlib's `ModularForm.L`. The full eigenform structure of a newform,
including its bad-prime eigenrelations, gives the newform Euler product.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Proposition 5.8.5 and §5.9.
* C. Birkbeck and the LeanModularForms contributors, AINTLIB,
  `projects/LeanModularForms/LeanModularForms/Modularforms/LFunctionEuler.lean`,
  [revision `112d12d95`](https://github.com/CBirkbeck/AINTLIB/blob/112d12d95e9c19f0d477b7a687bd49563ab8d07d/projects/LeanModularForms/LeanModularForms/Modularforms/LFunctionEuler.lean)
  (Apache 2.0 license).
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
  have habs := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f.toCuspForm
  rw [strictWidthInfty_Gamma1] at habs
  have hsum : LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (habs.trans_lt (by exact_mod_cast hs))
  exact TauCeti.LSeries.LSeries_eulerProduct_of_recurrence
    (a := fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) (s := s)
    (c := fun q ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) q * (q : ℂ) ^ (k - 1)) h₁
    (fun hm hn hmn ↦ f.qExpansion_coeff_mul h₁ hmn)
    (fun p hp r ↦ by
      simpa only [← mul_assoc] using f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    hsum

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
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rw [← hL]
  exact f.LSeries_eulerProduct_hasProd h₁ hs

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
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa using CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rw [← hL]
  exact f.LSeries_eulerProduct h₁ hs

end HeckeRing.GL2.Eigenform

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The Euler factors of a newform have product equal to its coefficient L-series on
`Re s > k/2 + 1`. The character is zero-extended at primes dividing the level. -/
theorem LSeries_eulerProduct_hasProd (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          f.dirichletLift p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  simpa only [dirichletLift_eq_ofUnitHom, toEigenform_toCuspForm, toEigenform_χ] using
    (f.toEigenform.LSeries_eulerProduct_hasProd
      (by simpa only [toEigenform_toCuspForm] using f.isNorm) hs)

/-- The coefficient L-series of a newform equals its Euler product on `Re s > k/2 + 1`. -/
theorem LSeries_eulerProduct_tprod (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          f.dirichletLift p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹) =
      LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
  (f.LSeries_eulerProduct_hasProd hs).tprod_eq

/-- Finite Euler products converge to the coefficient L-series of a newform. -/
theorem LSeries_eulerProduct (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦
        ∏ p ∈ Nat.primesBelow n,
          (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            f.dirichletLift p *
              (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹)
      atTop (𝓝 (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s)) := by
  simpa only [dirichletLift_eq_ofUnitHom, toEigenform_toCuspForm, toEigenform_χ] using
    (f.toEigenform.LSeries_eulerProduct
      (by simpa only [toEigenform_toCuspForm] using f.isNorm) hs)

/-- The Euler factors of a newform have product equal to Mathlib's `ModularForm.L`. -/
theorem L_eulerProduct_hasProd (f : Newform N k) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          f.dirichletLift p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹)
      (ModularForm.L hk f.toCuspForm s) := by
  simpa only [dirichletLift_eq_ofUnitHom, toEigenform_toCuspForm, toEigenform_χ] using
    (f.toEigenform.L_eulerProduct_hasProd
      (by simpa only [toEigenform_toCuspForm] using f.isNorm) hk hs)

/-- The L-function of a newform equals its Euler product on `Re s > k/2 + 1`. -/
theorem L_eulerProduct_tprod (f : Newform N k) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p.val * (p.val : ℂ) ^ (-s) +
          f.dirichletLift p.val *
            (p.val : ℂ) ^ (k - 1) * (p.val : ℂ) ^ (-2 * s))⁻¹) =
      ModularForm.L hk f.toCuspForm s :=
  (f.L_eulerProduct_hasProd hk hs).tprod_eq

/-- Finite Euler products converge to Mathlib's `ModularForm.L` for a newform. -/
theorem L_eulerProduct (f : Newform N k) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦
        ∏ p ∈ Nat.primesBelow n,
          (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
            f.dirichletLift p *
              (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s))⁻¹)
      atTop (𝓝 (ModularForm.L hk f.toCuspForm s)) := by
  simpa only [dirichletLift_eq_ofUnitHom, toEigenform_toCuspForm, toEigenform_χ] using
    (f.toEigenform.L_eulerProduct
      (by simpa only [toEigenform_toCuspForm] using f.isNorm) hk hs)

end HeckeRing.GL2.Newform
