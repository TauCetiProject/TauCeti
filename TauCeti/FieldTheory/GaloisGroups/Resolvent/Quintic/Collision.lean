/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A collision in the quintic resolvent

The quintic `X⁵ - X` is separable, but Dummit's sextic resolvent has a repeated rational root.
Its exact factorization exhibits the collision that requires separation evidence when using a
resolvent root to infer a Galois subgroup bound.
-/

public section

open Polynomial

namespace TauCeti

private def collisionRoots : Fin 5 → ℂ := ![0, 1, -1, Complex.I, -Complex.I]

private theorem collisionPolynomial_map :
    (X ^ 5 - X : ℤ[X]).map (Int.castRingHom ℂ) =
      ∏ i : Fin 5, (X - C (collisionRoots i)) := by
  rw [Fin.prod_univ_five]
  simp [collisionRoots]
  ring_nf
  have hI : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [← map_pow]
    norm_num [Complex.I_mul_I]
  rw [hI]
  ring

/-- The discriminant of `X⁵ - X` is `-256`. Its nonzero value proves separability over `ℚ`. -/
theorem discr_X_pow_five_sub_X : (X ^ 5 - X : ℤ[X]).discr = -256 := by
  have hf : (X ^ 5 - X : ℤ[X]).Monic := by monicity!
  have h := hf.discr_map (Int.castRingHom ℂ)
  rw [collisionPolynomial_map, discr_prod_X_sub_C] at h
  have hcalc : (∏ i : Fin 5, ∏ j ∈ Finset.Ioi i,
      (collisionRoots i - collisionRoots j) ^ 2) = (-256 : ℂ) := by
    have h0 : Finset.Ioi (0 : Fin 5) = {1, 2, 3, 4} := by decide
    have h1 : Finset.Ioi (1 : Fin 5) = {2, 3, 4} := by decide
    have h2 : Finset.Ioi (2 : Fin 5) = {3, 4} := by decide
    have h3 : Finset.Ioi (3 : Fin 5) = {4} := by decide
    have h4 : Finset.Ioi (4 : Fin 5) = ∅ := by decide
    norm_num [Fin.prod_univ_five, h0, h1, h2, h3, h4, collisionRoots,
      Complex.I_mul_I]
    ring_nf
    norm_num [Complex.I_sq, ← pow_mul]
  rw [hcalc] at h
  apply Int.cast_injective (α := ℂ)
  simpa using h.symm

/-- The quintic `X⁵ - X` is separable over `ℚ`. -/
theorem separable_X_pow_five_sub_X : (X ^ 5 - X : ℚ[X]).Separable := by
  have hf : (X ^ 5 - X : ℤ[X]).Monic := by monicity!
  have hsep := (hf.discr_ne_zero_iff_separable_map ℚ).mp (by
    rw [discr_X_pow_five_sub_X]
    norm_num)
  simpa using hsep

/-- Dummit's sextic of `X⁵ - X` has a quadruple root at `2` and two nonreal roots. -/
theorem resolventSextic_X_pow_five_sub_X :
    resolventSextic (X ^ 5 - X : ℤ[X]) = (X - 2) ^ 4 * (X ^ 2 + 16) := by
  have hf : (X ^ 5 - X : ℤ[X]) = X ^ 5 + C (-1) * X + C 0 := by simp [sub_eq_add_neg]
  rw [hf, resolventSextic_X_pow_five_add_C_mul_X_add_C]
  norm_num
  ring

/-- The quintic `X⁵ - X` has `2` as an integral root of its sextic resolvent. -/
theorem isRoot_resolventSextic_X_pow_five_sub_X :
    (resolventSextic (X ^ 5 - X : ℤ[X])).IsRoot 2 := by
  rw [resolventSextic_X_pow_five_sub_X]
  simp

/-- The specialized sextic of `X⁵ - X` over `ℚ` is inseparable, despite the quintic having
distinct roots. -/
theorem not_separable_resolventSextic_X_pow_five_sub_X :
    ¬ (Polynomial.Separable
      ((resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ))) := by
  intro hsep
  have hformula : (resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ) =
      (X - 2) ^ 4 * (X ^ 2 + 16 : ℚ[X]) := by
    rw [resolventSextic_X_pow_five_sub_X]
    simp
  have hdiv : (X - 2 : ℚ[X]) * (X - 2) ∣
      (resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ) := by
    rw [hformula]
    refine ⟨(X - 2) ^ 2 * (X ^ 2 + 16), ?_⟩
    ring
  exact not_isUnit_X_sub_C (2 : ℚ) (isUnit_of_self_mul_dvd_separable hsep hdiv)

end TauCeti
