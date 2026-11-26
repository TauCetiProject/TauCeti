/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.RingTheory.ClassGroup.RelNorm
import TauCeti.NumberTheory.ClassGroup.Equiv
import TauCeti.RingTheory.Ideal.Norm.Galois
import TauCeti.RingTheory.Ideal.Norm.RelNorm

/-!
# Galois equivariance and orbit products on class groups

For a finite extension `S / R` of Dedekind domains, the relative norm `ClassGroup.relNorm R` and
extension homomorphism `ClassGroup.extendedHom R S` interact with ring equivalences and Galois
automorphisms in two complementary ways:

1. **Equivariance under commuting ring equivalences.** Any commuting square of ring equivalences
   `f : R ≃+* R'` and `g : S ≃+* S'` commutes with `ClassGroup.relNorm` and
   `ClassGroup.extendedHom` (`ClassGroup.relNorm_mulEquiv`, `ClassGroup.extendedHom_mulEquiv`).
2. **Galois orbit product.** When `S` is the integral closure of `R` in a finite Galois extension
   `L / K` of fraction fields, norming an ideal class down from `S` to `R` and extending it back to
   `S` multiplies all Galois conjugates of the class:
   `extendedHom R S (relNorm R c) = ∏ σ : L ≃ₐ[K] L, mulEquiv (galRestrict σ) c`
   (`ClassGroup.extendedHom_relNorm`, the companion to `ClassGroup.relNorm_extendedHom`, which
   evaluates the opposite composite as `c ^ [L : K]`).

Base-changing along a ring `R` turns `ClassGroup.mulEquiv` into an `R`-linear equivalence
`ClassGroup.mulEquivBaseChange` and `ClassGroup.relNorm` and `ClassGroup.extendedHom` into
`R`-linear maps on `R ⊗[ℤ] Additive (ClassGroup _)`, where the two norm-extension composites become
`finrank • id` and the Galois orbit sum `∑ σ, σ`.

Number-field specializations for rings of integers live in
`TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv`.

## Main results

* `ClassGroup.relNorm_mulEquiv` and `ClassGroup.extendedHom_mulEquiv`: equivariance of
  `ClassGroup.relNorm` and `ClassGroup.extendedHom` under commuting ring equivalences.
* `ClassGroup.extendedHom_relNorm`: the Galois orbit-product identity
  `extendedHom R S (relNorm R c) = ∏ σ : L ≃ₐ[K] L, mulEquiv (galRestrict σ) c`.
* `ClassGroup.mulEquivBaseChange`, `ClassGroup.relNormBaseChange`, and
  `ClassGroup.extendedBaseChange`: base-changed `R`-linear equivalence and maps on
  `R ⊗[ℤ] Additive (ClassGroup _)` together with their functoriality, norm-extension composites,
  and transitivity (`ClassGroup.relNormBaseChange_comp_relNormBaseChange`).
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

section Equivariance

/-- **Equivariance of `ClassGroup.relNorm` under commuting ring equivalences.** -/
theorem relNorm_mulEquiv {R S R' S' : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDedekindDomain R'] [CommRing S'] [IsDedekindDomain S']
    [Algebra R' S'] [Module.Finite R' S'] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) (c : ClassGroup S) :
    ClassGroup.mulEquiv f (ClassGroup.relNorm R c) =
      ClassGroup.relNorm R' (ClassGroup.mulEquiv g c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [relNorm_mk0, mulEquiv_mk0, mulEquiv_mk0, relNorm_mk0]
  congr 1
  apply Subtype.ext
  simpa only [Ideal.coe_relNorm0, Ideal.map_coe] using
    Ideal.map_relNorm_of_ringEquiv f g hfg I.val

/-- **Equivariance of `ClassGroup.extendedHom` under commuting ring equivalences.** -/
theorem extendedHom_mulEquiv {R S R' S' : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDedekindDomain R'] [CommRing S'] [IsDedekindDomain S']
    [Algebra R' S'] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) (c : ClassGroup R) :
    ClassGroup.mulEquiv g (ClassGroup.extendedHom R S c) =
      ClassGroup.extendedHom R' S' (ClassGroup.mulEquiv f c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [extendedHom_mk0, mulEquiv_mk0, mulEquiv_mk0, extendedHom_mk0]
  congr 1
  apply Subtype.ext
  dsimp only [extendedIdeal]
  rw [← Ideal.map_coe g, ← Ideal.map_coe f, Ideal.map_map, Ideal.map_map]
  exact congrArg (Ideal.map · I.val) (RingHom.ext hfg)

end Equivariance

section GaloisOrbitProduct

/-- **Class-group Galois orbit product**: norming a class down from `S` to `R` and extending it
back to `S` multiplies all Galois conjugates of the class. This is the companion to
`ClassGroup.relNorm_extendedHom`. -/
theorem extendedHom_relNorm (R K L S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [Algebra R S] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K] [IsFractionRing S L]
    [IsIntegralClosure S R L] [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite R S] [Module.IsTorsionFree R S] (c : ClassGroup S) :
    ClassGroup.extendedHom R S (ClassGroup.relNorm R c) =
      ∏ σ : L ≃ₐ[K] L, ClassGroup.mulEquiv (galRestrict R K L S σ).toRingEquiv c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [relNorm_mk0, extendedHom_mk0]
  simp_rw [mulEquiv_mk0]
  rw [← map_prod]
  congr 1
  apply Subtype.ext
  have hmap (σ : L ≃ₐ[K] L) :
      Ideal.map (galRestrict R K L S σ).toRingEquiv I.val =
        Ideal.map (galRestrict R K L S σ : S →+* S) I.val :=
    (Ideal.map_coe (galRestrict R K L S σ).toRingEquiv I.val).symm
  simp only [Ideal.coe_relNorm0, SubmonoidClass.coe_finsetProd, hmap]
  exact Ideal.map_algebraMap_relNorm_eq_prod_galRestrict R K L S I.val

end GaloisOrbitProduct

section BaseChange

open scoped TensorProduct

/-- The `R`-linear equivalence on `R ⊗[ℤ] Additive (ClassGroup _)` obtained by base-changing
`ClassGroup.mulEquiv f`. -/
noncomputable def mulEquivBaseChange (R : Type*) [Ring R] {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDomain B] (f : A ≃+* B) :
    (R ⊗[ℤ] Additive (ClassGroup A)) ≃ₗ[R] (R ⊗[ℤ] Additive (ClassGroup B)) :=
  (ClassGroup.mulEquiv f).toAdditive.toIntLinearEquiv.baseChange ℤ R _ _

@[simp]
theorem mulEquivBaseChange_tmul (R : Type*) [Ring R] {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (f : A ≃+* B) (r : R) (c : ClassGroup A) :
    mulEquivBaseChange R f (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mulEquiv f c) :=
  (rfl)

theorem mulEquivBaseChange_symm_tmul (R : Type*) [Ring R] {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (f : A ≃+* B) (r : R) (c : ClassGroup B) :
    (mulEquivBaseChange R f).symm (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul ((ClassGroup.mulEquiv f).symm c) :=
  (rfl)

@[simp]
theorem mulEquivBaseChange_refl (R : Type*) [Ring R] (A : Type*) [CommRing A] [IsDomain A] :
    mulEquivBaseChange R (RingEquiv.refl A) =
      LinearEquiv.refl R (R ⊗[ℤ] Additive (ClassGroup A)) := by
  apply LinearEquiv.toLinearMap_injective
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [ClassGroup.mulEquiv_refl]

@[simp]
theorem mulEquivBaseChange_symm (R : Type*) [Ring R] {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (f : A ≃+* B) :
    (mulEquivBaseChange R f).symm = mulEquivBaseChange R f.symm := by
  apply LinearEquiv.toLinearMap_injective
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [mulEquivBaseChange_symm_tmul, ← ClassGroup.mulEquiv_symm]

@[simp]
theorem mulEquivBaseChange_trans (R : Type*) [Ring R] {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain A] [IsDomain B] [IsDomain C] (f : A ≃+* B) (g : B ≃+* C) :
    mulEquivBaseChange R (f.trans g) =
      (mulEquivBaseChange R f).trans (mulEquivBaseChange R g) := by
  apply LinearEquiv.toLinearMap_injective
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [ClassGroup.mulEquiv_trans]

/-- The `R`-linear base change of `ClassGroup.relNorm A` to `R ⊗[ℤ] Additive (ClassGroup _)`. -/
noncomputable def relNormBaseChange (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] :
    (R ⊗[ℤ] Additive (ClassGroup B)) →ₗ[R] (R ⊗[ℤ] Additive (ClassGroup A)) :=
  (MonoidHom.toAdditive (ClassGroup.relNorm A (S := B))).toIntLinearMap.baseChange R

@[simp]
theorem relNormBaseChange_tmul (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] (r : R) (c : ClassGroup B) :
    relNormBaseChange R A B (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.relNorm A c) :=
  LinearMap.baseChange_tmul _ r (Additive.ofMul c)

/-- The `R`-linear base change of `ClassGroup.extendedHom A B` to
`R ⊗[ℤ] Additive (ClassGroup _)`. -/
noncomputable def extendedBaseChange (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] :
    (R ⊗[ℤ] Additive (ClassGroup A)) →ₗ[R] (R ⊗[ℤ] Additive (ClassGroup B)) :=
  (MonoidHom.toAdditive (ClassGroup.extendedHom A B)).toIntLinearMap.baseChange R

@[simp]
theorem extendedBaseChange_tmul (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] (r : R) (c : ClassGroup A) :
    extendedBaseChange R A B (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.extendedHom A B c) :=
  LinearMap.baseChange_tmul _ r (Additive.ofMul c)

/-- **Extend then norm on `R ⊗[ℤ] Additive (ClassGroup A)` is scalar multiplication by
`Module.finrank A B`.** -/
theorem relNormBaseChange_comp_extendedBaseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] :
    (relNormBaseChange R A B).comp (extendedBaseChange R A B) =
      (Module.finrank A B : R) • LinearMap.id := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [relNorm_extendedHom, TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul R]

/-- **Norm then extend on `R ⊗[ℤ] Additive (ClassGroup B)` is the Galois orbit sum.** -/
theorem extendedBaseChange_comp_relNormBaseChange (R A K L B : Type*) [CommRing R] [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Field K] [Field L] [Algebra A K]
    [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L] [IsIntegralClosure B A L]
    [FiniteDimensional K L] [IsGalois K L] [Module.Finite A B] [Module.IsTorsionFree A B] :
    (extendedBaseChange R A B).comp (relNormBaseChange R A B) =
      ∑ σ : L ≃ₐ[K] L, (mulEquivBaseChange R (galRestrict A K L B σ).toRingEquiv).toLinearMap := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [extendedHom_relNorm A K L B, TensorProduct.tmul_sum]

/-- **Equivariance of `ClassGroup.relNormBaseChange` under commuting ring equivalences.** -/
theorem mulEquivBaseChange_comp_relNormBaseChange (R : Type*) [CommRing R] {A B A' B' : Type*}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [CommRing A'] [IsDedekindDomain A'] [CommRing B'] [IsDedekindDomain B']
    [Algebra A' B'] [Module.Finite A' B'] [Module.IsTorsionFree A' B']
    (f : A ≃+* A') (g : B ≃+* B')
    (hfg : ∀ r : A, g (algebraMap A B r) = algebraMap A' B' (f r)) :
    (mulEquivBaseChange R f).toLinearMap.comp (relNormBaseChange R A B) =
      (relNormBaseChange R A' B').comp (mulEquivBaseChange R g).toLinearMap := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [relNorm_mulEquiv f g hfg]

/-- **Equivariance of `ClassGroup.extendedBaseChange` under commuting ring equivalences.** -/
theorem mulEquivBaseChange_comp_extendedBaseChange (R : Type*) [CommRing R] {A B A' B' : Type*}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [CommRing A'] [IsDedekindDomain A'] [CommRing B'] [IsDedekindDomain B']
    [Algebra A' B'] [Module.IsTorsionFree A' B']
    (f : A ≃+* A') (g : B ≃+* B')
    (hfg : ∀ r : A, g (algebraMap A B r) = algebraMap A' B' (f r)) :
    (mulEquivBaseChange R g).toLinearMap.comp (extendedBaseChange R A B) =
      (extendedBaseChange R A' B').comp (mulEquivBaseChange R f).toLinearMap := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [extendedHom_mulEquiv f g hfg]

/-- **Transitivity of `ClassGroup.relNormBaseChange`** in a tower `A ⊆ B ⊆ C` of Dedekind
domains. -/
theorem relNormBaseChange_comp_relNormBaseChange (R A B C : Type*) [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C] :
    (relNormBaseChange R A B).comp (relNormBaseChange R B C) = relNormBaseChange R A C := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [relNorm_relNorm A B]

end BaseChange

end ClassGroup
