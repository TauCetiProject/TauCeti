/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.FormDiscriminant
public import TauCeti.RingTheory.MvPolynomial.StronglyDvd
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.LinearAlgebra.Matrix.LeibnizPart
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic
import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Stickelberger's congruence for binary forms

The universal discriminant of a binary form is a square modulo four. Consequently the
discriminant of every integral binary form is zero or one modulo four, and its value modulo
four depends only on the coefficients modulo two. This includes forms with roots at infinity.

For a monic polynomial, use the even and odd parts of the Vandermonde determinant, as in
Stickelberger's argument for number-field discriminants formalized in
`TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger`. The permanent and the product
of the two parts are symmetric in the roots, so they descend to the coefficients. For the
universal binary form, integral normalization multiplies the discriminant by an even power of
the leading variable. Reduction modulo two first gives the corresponding factor of the
square root, so the even power can be cancelled modulo four before specializing.
-/

public section

open Finset MvPolynomial
open UniqueFactorizationMonoid

namespace Polynomial

private theorem exists_discr_freeMonic_eq_sq_sub_four_mul (R : Type*) [CommRing R] (n : ℕ) :
    ∃ s t : MvPolynomial (Fin n) R, (freeMonic R n).discr = s ^ 2 - 4 * t := by
  let A := MvPolynomial (Fin n) R
  let M : Matrix (Fin n) (Fin n) A := Matrix.vandermonde (MvPolynomial.X (R := R))
  let e : A ≃ₐ[R] symmetricSubalgebra (Fin n) R :=
    (renameEquiv R Fin.revPerm).trans (esymmAlgEquiv (Fin n) R (Fintype.card_fin n))
  let φ : A →ₐ[R] A := (symmetricSubalgebra (Fin n) R).val.comp e.toAlgHom
  have hφ : φ = MvPolynomial.aeval fun i : Fin n ↦ esymm (Fin n) R (n - i) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp only [φ, e, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply,
      renameEquiv_apply, rename_X, Fin.revPerm_apply, esymmAlgEquiv_apply, Subalgebra.coe_val,
      esymmAlgHom_apply, MvPolynomial.aeval_X, Fin.val_rev]
    congr 1
    have := i.isLt
    omega
  have hM (σ : Equiv.Perm (Fin n)) : M.map (rename σ) = M.submatrix σ id := by
    ext i j
    simp [M, Matrix.vandermonde_apply]
  have hS : M.permanent.IsSymmetric := fun σ ↦ by
    have hperm : (rename σ) M.permanent = (M.map (rename σ)).permanent := by
      simp [Matrix.permanent, map_sum, map_prod]
    rw [hperm, hM, Matrix.permanent_permute_cols]
  have hT : (M.leibnizPart 1 * M.leibnizPart (-1)).IsSymmetric := fun σ ↦ by
    rw [map_mul, ← Matrix.leibnizPart_map, ← Matrix.leibnizPart_map, hM,
      Matrix.leibnizPart_one_mul_leibnizPart_neg_one_submatrix_left]
  obtain ⟨s, hs⟩ := e.surjective ⟨_, hS⟩
  obtain ⟨t, ht⟩ := e.surjective ⟨_, hT⟩
  have hD : φ (freeMonic R n).discr = M.det ^ 2 := by
    have hprod : (freeMonic R n).map φ.toRingHom =
        ∏ j : Fin n, (X - C (-(MvPolynomial.X j : A))) := by
      rw [hφ, map_aeval_esymm_freeMonic]
      simp
    calc
      φ (freeMonic R n).discr = ((freeMonic R n).map φ.toRingHom).discr :=
        ((monic_freeMonic R n).discr_map φ.toRingHom).symm
      _ = M.det ^ 2 := by
        rw [hprod, discr_prod_X_sub_C_eq_sq, Matrix.det_vandermonde]
        simp only [neg_sub_neg]
  have hs' : φ s = M.permanent := congrArg Subtype.val hs
  have ht' : φ t = M.leibnizPart 1 * M.leibnizPart (-1) := congrArg Subtype.val ht
  have hinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  refine ⟨s, t, hinj ?_⟩
  rw [hD, map_sub, map_mul, map_pow, map_ofNat, hs', ht']
  exact M.det_sq_eq_permanent_sq_sub_four_mul

/-- The discriminant of a monic polynomial is a square minus four times an element of its
coefficient ring. -/
theorem Monic.exists_discr_eq_sq_sub_four_mul {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) :
    ∃ s t : R, f.discr = s ^ 2 - 4 * t := by
  let φ := MvPolynomial.aeval (R := R) fun i : Fin f.natDegree ↦ f.coeff i
  obtain ⟨s, t, h⟩ := exists_discr_freeMonic_eq_sq_sub_four_mul R f.natDegree
  refine ⟨φ s, φ t, ?_⟩
  have hmap : (freeMonic R f.natDegree).map φ.toRingHom = f :=
    map_aeval_coeff_freeMonic hf rfl
  calc
    f.discr = ((freeMonic R f.natDegree).map φ.toRingHom).discr := congrArg discr hmap.symm
    _ = φ s ^ 2 - 4 * φ t := by
      rw [(monic_freeMonic R _).discr_map, h, map_sub, map_pow, map_mul, map_ofNat,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

end Polynomial

namespace TauCeti

open Polynomial

private theorem exists_eq_sq_sub_four_mul_of_X_pow_mul {σ : Type*} (i : σ) (k : ℕ)
    {d s t : MvPolynomial σ ℤ} (h : (MvPolynomial.X i ^ k) ^ 2 * d = s ^ 2 - 4 * t) :
    ∃ u v : MvPolynomial σ ℤ, d = u ^ 2 - 4 * v := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ₂ := MvPolynomial.map (Int.castRingHom (ZMod 2)) (σ := σ)
  let ρ₄ := MvPolynomial.map (Int.castRingHom (ZMod 4)) (σ := σ)
  have h4₂ : (4 : MvPolynomial σ (ZMod 2)) = 0 := by
    rw [← map_ofNat MvPolynomial.C, show (4 : ZMod 2) = 0 by decide, map_zero]
  have h4₄ : (4 : MvPolynomial σ (ZMod 4)) = 0 := by
    rw [← map_ofNat MvPolynomial.C, show (4 : ZMod 4) = 0 by decide, map_zero]
  have h₂ : ((MvPolynomial.X i : MvPolynomial σ (ZMod 2)) ^ k) ^ 2 * ρ₂ d = (ρ₂ s) ^ 2 := by
    simpa [ρ₂, h4₂] using congrArg ρ₂ h
  have hdiv : (MvPolynomial.X i : MvPolynomial σ (ZMod 2)) ^ k ∣ ρ₂ s :=
    (pow_dvd_pow_iff_dvd two_ne_zero).mp ⟨ρ₂ d, h₂.symm⟩
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨u, hu⟩ := MvPolynomial.map_surjective (σ := σ)
    (f := Int.castRingHom (ZMod 2)) ZMod.intCast_surjective q
  have heven : MvPolynomial.C (2 : ℤ) ∣ s - MvPolynomial.X i ^ k * u := by
    rw [C_dvd_iff_map_hom_eq_zero (Int.castRingHom (ZMod 2)) 2
      (fun x ↦ ZMod.intCast_zmod_eq_zero_iff_dvd x 2)]
    simpa [ρ₂, hu] using sub_eq_zero.mpr hq
  obtain ⟨b, hb⟩ := heven
  have hb' : s = MvPolynomial.X i ^ k * u + 2 * b := by
    rw [sub_eq_iff_eq_add] at hb
    simpa [add_comm] using hb
  have h₄ : ((MvPolynomial.X i : MvPolynomial σ (ZMod 4)) ^ k) ^ 2 * ρ₄ d =
      (ρ₄ s) ^ 2 := by
    simpa [ρ₄, h4₄] using congrArg ρ₄ h
  have hsq : (ρ₄ s) ^ 2 =
      ((MvPolynomial.X i : MvPolynomial σ (ZMod 4)) ^ k) ^ 2 * (ρ₄ u) ^ 2 := by
    have hs : ρ₄ s = MvPolynomial.X i ^ k * ρ₄ u + 2 * ρ₄ b := by
      simp only [hb', map_add, map_mul, map_pow, map_ofNat, ρ₄, MvPolynomial.map_X]
    rw [hs, ← mul_pow]
    linear_combination (MvPolynomial.X i ^ k * ρ₄ u * ρ₄ b + (ρ₄ b) ^ 2) * h4₄
  have hd : ρ₄ d = (ρ₄ u) ^ 2 :=
    ((MvPolynomial.isRegular_X_pow (R := ZMod 4) (n := i) k).pow 2).left (h₄.trans hsq)
  have hfour : MvPolynomial.C (4 : ℤ) ∣ u ^ 2 - d := by
    rw [C_dvd_iff_map_hom_eq_zero (Int.castRingHom (ZMod 4)) 4
      (fun x ↦ ZMod.intCast_zmod_eq_zero_iff_dvd x 4)]
    simp [← hd, ρ₄]
  obtain ⟨v, hv⟩ := hfour
  rw [map_ofNat] at hv
  exact ⟨u, v, by linear_combination -hv⟩

/-- The universal binary-form discriminant is a square modulo four in the coefficient ring. -/
theorem exists_universalDiscr_eq_sq_sub_four_mul (n : ℕ) :
    ∃ s t : MvPolynomial (Fin (n + 1)) ℤ, universalDiscr n = s ^ 2 - 4 * t := by
  have hnz : universalPoly n ≠ 0 := leadingCoeff_ne_zero.mp <| by simp
  obtain ⟨s, t, h⟩ := (monic_integralNormalization hnz).exists_discr_eq_sq_sub_four_mul
  obtain ⟨k, hk⟩ : Even ((n - 1) * (n - 2)) := by
    simpa only [Nat.sub_sub, one_add_one_eq_two] using Nat.even_mul_pred_self (n - 1)
  rw [discr_integralNormalization, natDegree_universalPoly, leadingCoeff_universalPoly,
    ← universalDiscr_def, hk, pow_add, ← pow_two] at h
  exact exists_eq_sq_sub_four_mul_of_X_pow_mul (Fin.last n) k h

end TauCeti

namespace Polynomial

/-- Stickelberger's congruence for an integral binary form, including a form with zero leading
coefficient at the specified degree. -/
theorem formDiscr_emod_four_eq_zero_or_one (f : ℤ[X]) (n : ℕ) :
    f.formDiscr n % 4 = 0 ∨ f.formDiscr n % 4 = 1 := by
  obtain ⟨s, t, h⟩ := TauCeti.exists_universalDiscr_eq_sq_sub_four_mul n
  rw [formDiscr_def, h, map_sub, map_pow, map_mul, map_ofNat, Int.sub_mul_emod_self_left]
  generalize MvPolynomial.aeval (fun i : Fin (n + 1) ↦ f.coeff i) s = z
  have hz := Int.sq_emod_four z
  omega

end Polynomial

namespace TauCeti

/-- At the prime two the binary-form discriminant has no weak square divisibility. -/
@[simp]
theorem not_weaklyDvdAt_universalDiscr_two (n : ℕ) (a : Fin (n + 1) → ℤ) :
    ¬ (universalDiscr n).WeaklyDvdAt 2 4 a := by
  obtain ⟨s, t, h⟩ := exists_universalDiscr_eq_sq_sub_four_mul n
  have hdvd (b : Fin (n + 1) → ℤ) : 4 ∣ eval b (universalDiscr n) ↔ 2 ∣ eval b s := by
    rw [h, map_sub, map_pow, map_mul, map_ofNat, dvd_sub_left (dvd_mul_right 4 (eval b t))]
    simpa using (pow_dvd_pow_iff_dvd (a := (2 : ℤ)) (b := eval b s) two_ne_zero)
  rw [weaklyDvdAt_iff, stronglyDvdAt_iff]
  rintro ⟨ha, hnot⟩
  exact hnot fun b hb ↦ (hdvd b).2 <|
    (dvd_iff_dvd_of_dvd_sub (dvd_eval_sub_eval s hb)).2 ((hdvd a).1 ha)

end TauCeti
