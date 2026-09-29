/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit
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

private theorem collisionRoots_eval_invariant :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots quinticF20Invariant = 2 := by
  rw [quinticF20Invariant_def]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Complex.I_mul_I]

private theorem collisionOrbitValue_one :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename (⇑(1 : Equiv.Perm (Fin 5))) quinticF20Invariant) = 2 := by
  simpa using collisionRoots_eval_invariant

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

private theorem collisionPolynomial_roots :
    ((X ^ 5 - X : ℤ[X]).map (Int.castRingHom ℂ)).roots =
      Finset.univ.val.map collisionRoots := by
  rw [collisionPolynomial_map]
  simpa only [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
    using (roots_multiset_prod_X_sub_C (Finset.univ.val.map collisionRoots))

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

private theorem collisionOrbitValue_swap23 :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename (⇑(Equiv.swap (2 : Fin 5) 3)) quinticF20Invariant) = 2 := by
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Equiv.swap_apply_def,
    Fin.reduceEq, Fin.reduceAdd, Fin.reduceSub, Complex.I_mul_I]
  ring

private theorem collisionOrbitValue_swap34 :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename (⇑(Equiv.swap (3 : Fin 5) 4)) quinticF20Invariant) = 2 := by
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Equiv.swap_apply_def,
    Fin.reduceEq, Fin.reduceAdd, Fin.reduceSub, Complex.I_mul_I]

private theorem collisionOrbitValue_swap24 :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename (⇑(Equiv.swap (2 : Fin 5) 4)) quinticF20Invariant) =
        -4 * Complex.I := by
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Equiv.swap_apply_def,
    Fin.reduceEq, Fin.reduceAdd, Fin.reduceSub, Complex.I_mul_I]
  ring

private theorem collisionOrbitValue_swap23_mul_swap34 :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename
        (⇑(Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5)))
        quinticF20Invariant) =
        4 * Complex.I := by
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceAdd, Fin.reduceSub, Complex.I_mul_I]
  ring

private theorem collisionOrbitValue_swap34_mul_swap23 :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) collisionRoots
      (MvPolynomial.rename
        (⇑(Equiv.swap (3 : Fin 5) 4) ∘ ⇑(Equiv.swap 2 3))
        quinticF20Invariant) = 2 := by
  rw [← Equiv.Perm.coe_mul, rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  norm_num [Fin.sum_univ_succ, collisionRoots, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceAdd, Fin.reduceSub, Complex.I_mul_I]
  ring

private theorem collision_resolvent_complex :
    ((resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℂ)) =
      (X - 2) ^ 4 * (X ^ 2 + 16 : ℂ[X]) := by
  have hf : (X ^ 5 - X : ℤ[X]).Monic := by monicity!
  have hdeg : (X ^ 5 - X : ℤ[X]).natDegree = 5 := by compute_degree!
  rw [resolventSextic_def,
    quinticF20Spec.map_specialize_eq_galResolvent (Int.castRingHom ℂ) hf hdeg
      collisionPolynomial_roots, quinticF20Spec_Φ,
    ← MvPolynomial.map_universalResolvent_eq_galResolvent,
    universalResolvent_quinticF20Invariant, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    MvPolynomial.coe_eval₂Hom]
  rw [quinticF20OrbitRepresentatives_def]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton, collisionOrbitValue_swap23_mul_swap34,
    Equiv.Perm.coe_mul, collisionOrbitValue_swap34_mul_swap23]
  simp only [collisionOrbitValue_one, collisionOrbitValue_swap23,
    collisionOrbitValue_swap34, collisionOrbitValue_swap24]
  simp only [map_ofNat]
  have hI : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [← map_pow]
    norm_num [Complex.I_mul_I]
  have hquad : (X - C (-(Complex.I * 4))) * (X - C (Complex.I * 4)) =
      (X ^ 2 + 16 : ℂ[X]) := by
    simp only [map_neg, map_mul, map_ofNat]
    calc
      _ = X ^ 2 - 16 * (C Complex.I) ^ 2 := by ring
      _ = X ^ 2 + 16 := by rw [hI]; ring
  calc
    _ = (X - 2) ^ 4 * ((X - C (-(Complex.I * 4))) * (X - C (Complex.I * 4))) := by ring_nf
    _ = (X - 2) ^ 4 * (X ^ 2 + 16) := by rw [hquad]

/-- Dummit's sextic of `X⁵ - X` has a quadruple root at `2` and two nonreal roots. -/
theorem resolventSextic_X_pow_five_sub_X :
    resolventSextic (X ^ 5 - X : ℤ[X]) = (X - 2) ^ 4 * (X ^ 2 + 16) := by
  apply (Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)
  simpa using collision_resolvent_complex

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
