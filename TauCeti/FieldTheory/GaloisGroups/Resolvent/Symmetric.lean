/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.Subring

/-!
# Symmetric descent for the universal resolvent

Given an integral multivariable polynomial `Φ` in `n` formal roots, its universal resolvent is
the product of `X - Ψ` over the orbit of `Φ` under permutations of the variables. Permuting the
formal roots permutes these factors, so every coefficient of the product is symmetric.

The fundamental theorem of symmetric polynomials then gives a unique polynomial whose
coefficients specialize to the universal resolvent after sending the variables to the elementary
symmetric polynomials. This is the integral orbit product used by a resolvent specification.

## Main definitions

* `MvPolynomial.universalResolvent`: the product over the rename-orbit of an invariant.
* `TauCeti.esymmSubst`: substitution of the elementary symmetric polynomials for the variables.

## Main results

* `MvPolynomial.universalResolvent_def`: the universal resolvent is the product of the linear
  factors attached to the orbit.
* `MvPolynomial.universalResolvent_map_rename`: the universal resolvent is invariant under
  renaming.
* `MvPolynomial.isSymmetric_universalResolvent_coeff`: all of its coefficients are
  symmetric.
* `TauCeti.esymmSubst_injective`: elementary-symmetric substitution is injective.
* `MvPolynomial.existsUnique_orbitProduct`: the universal resolvent descends uniquely
  through elementary-symmetric substitution.
* `MvPolynomial.monic_universalResolvent` and `MvPolynomial.natDegree_universalResolvent`: the
  universal resolvent is monic of degree the size of the orbit, and
  `MvPolynomial.monic_of_map_esymmSubst_eq`, `MvPolynomial.natDegree_of_map_esymmSubst_eq`
  transfer this to its integral expression.
-/

public section

open Polynomial

namespace MvPolynomial

open Classical in
/-- The finite set of distinct polynomials obtained by permuting the variables of `Φ`. -/
noncomputable def renameOrbit {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    Finset (MvPolynomial (Fin n) ℤ) := by
  let _ := Fintype.ofFinite (Equiv.Perm (Fin n))
  exact Finset.univ.image fun σ : Equiv.Perm (Fin n) => MvPolynomial.rename (⇑σ) Φ

/-- Membership in the rename-orbit is witnessed by a permutation of the variables. -/
@[simp]
theorem mem_renameOrbit {n : ℕ} (Φ Ψ : MvPolynomial (Fin n) ℤ) :
    Ψ ∈ renameOrbit Φ ↔ ∃ σ : Equiv.Perm (Fin n), MvPolynomial.rename (⇑σ) Φ = Ψ := by
  classical
  let _ := Fintype.ofFinite (Equiv.Perm (Fin n))
  simp [renameOrbit]

/-- The universal resolvent of `Φ`, formed over the orbit obtained by permuting its variables. -/
noncomputable def universalResolvent {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial (Fin n) ℤ)[X] :=
  ∏ Ψ ∈ renameOrbit Φ, (Polynomial.X - Polynomial.C Ψ)

/-- The universal resolvent is the product of the monic linear factors `X - Ψ` attached to the
elements of the rename-orbit. -/
theorem universalResolvent_def {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    universalResolvent Φ = ∏ Ψ ∈ renameOrbit Φ, (Polynomial.X - Polynomial.C Ψ) := (rfl)

/-- The universal resolvent is monic, being a product of monic linear factors. -/
theorem monic_universalResolvent {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    (universalResolvent Φ).Monic := by
  rw [universalResolvent_def]
  exact Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

/-- The universal resolvent has degree the number of elements of the rename-orbit. -/
@[simp]
theorem natDegree_universalResolvent {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    (universalResolvent Φ).natDegree = (renameOrbit Φ).card := by
  rw [universalResolvent_def,
    Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
  simp

end MvPolynomial

namespace TauCeti

/-- The substitution sending variable `i` to the elementary symmetric polynomial `e_(i+1)`. -/
noncomputable def esymmSubst (n : ℕ) :
    MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ :=
  (MvPolynomial.aeval fun i : Fin n =>
    MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1)).toRingHom

/-- Elementary-symmetric substitution sends `X i` to `e_(i+1)`. -/
@[simp]
theorem esymmSubst_X (n : ℕ) (i : Fin n) :
    esymmSubst n (MvPolynomial.X i) = MvPolynomial.esymm (Fin n) ℤ ((i : ℕ) + 1) := by
  simp [esymmSubst]

/-- Elementary-symmetric substitution agrees with Mathlib's fundamental-theorem map. -/
theorem esymmSubst_apply (n : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    esymmSubst n p = (MvPolynomial.esymmAlgHom (Fin n) ℤ n p).1 := by
  rw [esymmSubst, AlgHom.toRingHom_eq_coe]
  exact (MvPolynomial.esymmAlgHom_apply p).symm

end TauCeti

namespace MvPolynomial

private lemma renameOrbit_image (n : ℕ) (Φ : MvPolynomial (Fin n) ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (renameOrbit Φ).image (MvPolynomial.rename (⇑σ)) = renameOrbit Φ := by
  classical
  let _ := Fintype.ofFinite (Equiv.Perm (Fin n))
  ext Ψ
  simp only [renameOrbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Φ', ⟨τ, rfl⟩, rfl⟩
    exact ⟨σ * τ, by simp [MvPolynomial.rename_rename, Function.comp_def]⟩
  · rintro ⟨τ, rfl⟩
    refine ⟨MvPolynomial.rename (⇑σ⁻¹) (MvPolynomial.rename (⇑τ) Φ), ?_, ?_⟩
    · exact ⟨σ⁻¹ * τ, by simp [MvPolynomial.rename_rename, Function.comp_def]⟩
    · simp [MvPolynomial.rename_rename, Function.comp_def]

/-- Permuting the formal roots leaves the universal resolvent unchanged. -/
@[simp]
theorem universalResolvent_map_rename {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ)
    (σ : Equiv.Perm (Fin n)) :
    (universalResolvent Φ).map
        (↑(MvPolynomial.rename (R := ℤ) (⇑σ)) :
          MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ) =
      universalResolvent Φ := by
  classical
  rw [universalResolvent, Polynomial.map_prod]
  refine Finset.prod_bij (fun Ψ _ => MvPolynomial.rename (⇑σ) Ψ) ?_ ?_ ?_ ?_
  · intro Ψ hΨ
    rw [← renameOrbit_image n Φ σ]
    exact Finset.mem_image.mpr ⟨Ψ, hΨ, rfl⟩
  · intro Ψ₁ h₁ Ψ₂ h₂ h
    exact MvPolynomial.rename_injective (⇑σ) σ.injective h
  · intro Ψ hΨ
    have hΨ' : Ψ ∈ (renameOrbit Φ).image (MvPolynomial.rename (⇑σ)) := by
      rw [renameOrbit_image n Φ σ]
      exact hΨ
    obtain ⟨Φ', hΦ', hΦΨ⟩ := Finset.mem_image.mp hΨ'
    exact ⟨Φ', hΦ', hΦΨ⟩
  · simp

/-- Every coefficient of the universal resolvent is symmetric in the formal roots. -/
theorem isSymmetric_universalResolvent_coeff {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ)
    (k : ℕ) : ((universalResolvent Φ).coeff k).IsSymmetric := by
  intro σ
  have h := congrArg (fun p : (MvPolynomial (Fin n) ℤ)[X] => p.coeff k)
    (universalResolvent_map_rename Φ σ)
  rw [Polynomial.coeff_map] at h
  exact (congrFun (AlgHom.coe_toRingHom (MvPolynomial.rename (⇑σ)))
    ((universalResolvent Φ).coeff k)).symm.trans h

end MvPolynomial

namespace TauCeti

/-- Substitution by the elementary symmetric polynomials is injective. -/
lemma esymmSubst_injective (n : ℕ) : Function.Injective (esymmSubst n) := by
  intro p q hpq
  apply (MvPolynomial.esymmAlgHom_fin_bijective ℤ n).1
  apply Subtype.ext
  simpa only [← esymmSubst_apply] using hpq

end TauCeti

namespace MvPolynomial

/-- The universal resolvent has a unique expression in the elementary symmetric polynomials. -/
theorem existsUnique_orbitProduct {n : ℕ} (Φ : MvPolynomial (Fin n) ℤ) :
    ∃! D : (MvPolynomial (Fin n) ℤ)[X],
      D.map (TauCeti.esymmSubst n) = universalResolvent Φ := by
  classical
  let S := MvPolynomial.symmetricSubalgebra (Fin n) ℤ
  have hcoeffs : (↑(universalResolvent Φ).coeffs : Set (MvPolynomial (Fin n) ℤ)) ⊆ S := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    exact (MvPolynomial.mem_symmetricSubalgebra _).2
      (isSymmetric_universalResolvent_coeff Φ k)
  let P : S.toSubring[X] := (universalResolvent Φ).toSubring S.toSubring hcoeffs
  obtain ⟨D, hD⟩ := Polynomial.map_surjective
    (MvPolynomial.esymmAlgHom (Fin n) ℤ n).toRingHom
    (MvPolynomial.esymmAlgHom_fin_bijective ℤ n).2 P
  have hD' : D.map (TauCeti.esymmSubst n) = universalResolvent Φ := by
    apply Polynomial.ext
    intro k
    have hk := congrArg (fun p : S.toSubring[X] => p.coeff k) hD
    rw [Polynomial.coeff_map] at hk
    rw [Polynomial.coeff_map, TauCeti.esymmSubst_apply]
    have hk' :
        ((MvPolynomial.esymmAlgHom (Fin n) ℤ n).toRingHom (D.coeff k)).1 =
          (universalResolvent Φ).coeff k := by
      simpa only [P, Polynomial.coeff_toSubring] using congrArg Subtype.val hk
    exact (congrArg Subtype.val (congrFun
      (AlgHom.coe_toRingHom (MvPolynomial.esymmAlgHom (Fin n) ℤ n)) (D.coeff k))).symm.trans hk'
  refine ⟨D, hD', ?_⟩
  intro E hE
  apply Polynomial.map_injective (TauCeti.esymmSubst n) (TauCeti.esymmSubst_injective n)
  exact hE.trans hD'.symm

/-- An integral expression for the universal resolvent in the elementary symmetric polynomials is
itself monic, since elementary-symmetric substitution is injective. -/
theorem monic_of_map_esymmSubst_eq {n : ℕ} {Φ : MvPolynomial (Fin n) ℤ}
    {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (TauCeti.esymmSubst n) = universalResolvent Φ) : D.Monic :=
  Polynomial.monic_of_injective (TauCeti.esymmSubst_injective n)
    (hD ▸ monic_universalResolvent Φ)

/-- An integral expression for the universal resolvent has the degree of the universal resolvent,
the number of elements of the rename-orbit. -/
theorem natDegree_of_map_esymmSubst_eq {n : ℕ} {Φ : MvPolynomial (Fin n) ℤ}
    {D : (MvPolynomial (Fin n) ℤ)[X]}
    (hD : D.map (TauCeti.esymmSubst n) = universalResolvent Φ) :
    D.natDegree = (renameOrbit Φ).card := by
  rw [← Polynomial.natDegree_map_eq_of_injective (TauCeti.esymmSubst_injective n) D, hD,
    natDegree_universalResolvent]

end MvPolynomial
