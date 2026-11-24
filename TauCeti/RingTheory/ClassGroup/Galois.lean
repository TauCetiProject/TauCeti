/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import TauCeti.RingTheory.ClassGroup.RelNorm
import Mathlib.FieldTheory.Normal.Basic
import TauCeti.NumberTheory.DedekindDomain.RelNorm
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# Galois equivariance and orbit products on class groups

For a finite extension `S / R` of Dedekind domains, the relative norm `ClassGroup.relNorm R` and
extension homomorphism `ClassGroup.extendedHom R S` interact with ring equivalences and Galois
automorphisms in two complementary ways:

1. **Equivariance under commuting ring equivalences.** Any commuting square of ring equivalences
   `f : R ≃+* R'` and `g : S ≃+* S'` commutes with `Algebra.intNorm`, `Ideal.relNorm`,
   `ClassGroup.relNorm`, and `ClassGroup.extendedHom`. In particular, for a tower of number fields
   `K / F` normal inside `L / F`, every automorphism `τ : L ≃ₐ[F] L` intertwines
   `ClassGroup.relNorm (𝓞 K)` and `ClassGroup.extendedHom (𝓞 K) (𝓞 L)` with its restriction
   `τ.restrictNormal K`.
2. **Galois orbit product.** When `S` is the integral closure of `R` in a finite Galois extension
   `L / K` of fraction fields, extending the relative norm of an ideal `I` of `S` recovers the
   product of its Galois conjugates:
   `Ideal.map (algebraMap R S) (Ideal.relNorm R I) = ∏ σ : Gal(L/K), Ideal.map (galRestrict σ) I`.
   Passing to ideal classes yields the class-group norm-extension identity
   `extendedHom R S (relNorm R c) = ∏ σ, mulEquiv (galRestrict σ) c`
   (the companion to `ClassGroup.relNorm_extendedHom`, which evaluates the opposite composite as
   `c ^ [L : K]`).

Base-changing along any commutative ring `R` turns `ClassGroup.relNorm`, `ClassGroup.extendedHom`,
and `ClassGroup.mulEquiv` into `R`-linear maps on `R ⊗[ℤ] Additive (ClassGroup _)`, where the two
norm-extension composites become `finrank • id` and the Galois orbit sum `∑ σ, σ`.

## Main results

* `Algebra.map_intNorm_of_ringEquiv`: equivariance of `Algebra.intNorm` under commuting ring
  equivalences.
* `Ideal.map_relNorm_of_ringEquiv`: equivariance of `Ideal.relNorm` under commuting ring
  equivalences.
* `ClassGroup.relNorm_mulEquiv` and `ClassGroup.extendedHom_mulEquiv`: equivariance of
  `ClassGroup.relNorm` and `ClassGroup.extendedHom` under commuting ring equivalences.
* `Ideal.map_algebraMap_relNorm_eq_prod_galRestrict`: for a Galois extension of fraction fields,
  `Ideal.map (algebraMap R S) (Ideal.relNorm R I) = ∏ σ : L ≃ₐ[K] L, Ideal.map (galRestrict σ) I`.
* `ClassGroup.extendedHom_relNorm`: the Galois orbit-product identity
  `extendedHom R S (relNorm R c) = ∏ σ : L ≃ₐ[K] L, mulEquiv (galRestrict σ) c`.
* `ClassGroup.extendedHom_relNorm_ringOfIntegers`, `ClassGroup.relNorm_mulEquiv_ringOfIntegers`,
  and `ClassGroup.extendedHom_mulEquiv_ringOfIntegers`: specializations to rings of integers of
  number fields, formulated with `NumberField.RingOfIntegers.mapRingEquiv`.
* `ClassGroup.relNormBaseChange`, `ClassGroup.extendedBaseChange`, and
  `ClassGroup.mulEquivBaseChange`: base-changed `R`-linear maps on `R ⊗[ℤ] Additive (ClassGroup _)`
  together with their norm-extension composites and transitivity
  (`ClassGroup.relNormBaseChange_comp_relNormBaseChange`).
-/

public section

open scoped nonZeroDivisors

section Equivariance

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Equivariance of `Algebra.intNorm` under commuting ring equivalences.** If `f : R ≃+* R'` and
`g : S ≃+* S'` commute with `algebraMap`, then `f (intNorm R S x) = intNorm R' S' (g x)`. -/
theorem Algebra.map_intNorm_of_ringEquiv {R S R' S' : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [Algebra R S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [CommRing S'] [IsDomain S'] [IsIntegrallyClosed S']
    [Algebra R' S'] [Algebra.IsIntegral R' S'] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) (x : S) :
    f (Algebra.intNorm R S x) = Algebra.intNorm R' S' (g x) := by
  let ef : FractionRing R ≃+* FractionRing R' := IsFractionRing.ringEquivOfRingEquiv f
  let eg : FractionRing S ≃+* FractionRing S' := IsFractionRing.ringEquivOfRingEquiv g
  have hcomm : (algebraMap (FractionRing R') (FractionRing S')).comp ef.toRingHom =
      eg.toRingHom.comp (algebraMap (FractionRing R) (FractionRing S)) := by
    refine IsLocalization.ringHom_ext R⁰ (RingHom.ext fun r ↦ ?_)
    have h1 : algebraMap (FractionRing R) (FractionRing S) (algebraMap R (FractionRing R) r) =
        algebraMap S (FractionRing S) (algebraMap R S r) := by
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
        IsScalarTower.algebraMap_apply R S (FractionRing S)]
    have h2 : algebraMap (FractionRing R') (FractionRing S')
        (algebraMap R' (FractionRing R') (f r)) =
        algebraMap S' (FractionRing S') (algebraMap R' S' (f r)) := by
      rw [← IsScalarTower.algebraMap_apply R' (FractionRing R') (FractionRing S'),
        IsScalarTower.algebraMap_apply R' S' (FractionRing S')]
    have hef : ef (algebraMap R (FractionRing R) r) = algebraMap R' (FractionRing R') (f r) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap f r
    have heg : eg (algebraMap S (FractionRing S) (algebraMap R S r)) =
        algebraMap S' (FractionRing S') (g (algebraMap R S r)) :=
      IsFractionRing.ringEquivOfRingEquiv_algebraMap g (algebraMap R S r)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hef, h1, h2, heg, hfg]
  apply IsFractionRing.injective R' (FractionRing R')
  have hnorm := Algebra.norm_eq_of_equiv_equiv ef eg hcomm (algebraMap S (FractionRing S) x)
  have hnorm' : ef (Algebra.norm (FractionRing R) (algebraMap S (FractionRing S) x)) =
      Algebra.norm (FractionRing R') (eg (algebraMap S (FractionRing S) x)) := by
    simpa using congrArg ef hnorm
  have heg_x : eg (algebraMap S (FractionRing S) x) = algebraMap S' (FractionRing S') (g x) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap g x
  calc algebraMap R' (FractionRing R') (f (Algebra.intNorm R S x))
      = ef (algebraMap R (FractionRing R) (Algebra.intNorm R S x)) :=
        (IsFractionRing.ringEquivOfRingEquiv_algebraMap f _).symm
    _ = ef (Algebra.norm (FractionRing R) (algebraMap S (FractionRing S) x)) := by
        rw [Algebra.algebraMap_intNorm_fractionRing]
    _ = Algebra.norm (FractionRing R') (eg (algebraMap S (FractionRing S) x)) := hnorm'
    _ = Algebra.norm (FractionRing R') (algebraMap S' (FractionRing S') (g x)) := by
        rw [heg_x]
    _ = algebraMap R' (FractionRing R') (Algebra.intNorm R' S' (g x)) := by
        rw [Algebra.algebraMap_intNorm_fractionRing]

/-- **Equivariance of `Ideal.relNorm` under commuting ring equivalences.** -/
theorem Ideal.map_relNorm_of_ringEquiv {R S R' S' : Type*}
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [CommRing R'] [IsDedekindDomain R'] [CommRing S'] [IsDedekindDomain S']
    [Algebra R' S'] [Module.Finite R' S'] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hfg : ∀ r : R, g (algebraMap R S r) = algebraMap R' S' (f r)) (I : Ideal S) :
    Ideal.map (f : R →+* R') (Ideal.relNorm R I) =
      Ideal.relNorm R' (Ideal.map (g : S →+* S') I) := by
  rw [Ideal.map_relNorm, Ideal.relNorm_apply]
  congr 1
  ext y
  simp only [Set.mem_image, Function.comp_apply, SetLike.mem_coe, RingEquiv.coe_toRingHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g x, Ideal.mem_map_of_mem _ hx,
      (Algebra.map_intNorm_of_ringEquiv f g hfg x).symm⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : g.symm z ∈ I := by
      rwa [Ideal.symm_apply_mem_of_equiv_iff]
    refine ⟨g.symm z, hz', ?_⟩
    simpa using Algebra.map_intNorm_of_ringEquiv f g hfg (g.symm z)

namespace ClassGroup

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

end ClassGroup

end Equivariance

section GaloisOrbitProduct

/-- **Extending the relative ideal norm yields the Galois orbit product.** For a finite Galois
extension `L / K` of fraction fields of Dedekind domains `S / R` with `S` the integral closure of
`R` in `L`, extending `Ideal.relNorm R I` back to `S` equals the product of all Galois conjugates
of `I`. -/
theorem Ideal.map_algebraMap_relNorm_eq_prod_galRestrict (R K L S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [Algebra R S] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K] [IsFractionRing S L]
    [IsIntegralClosure S R L] [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite R S] [Module.IsTorsionFree R S] (I : Ideal S) :
    Ideal.map (algebraMap R S) (Ideal.relNorm R I) =
      ∏ σ : L ≃ₐ[K] L, Ideal.map (galRestrict R K L S σ : S →+* S) I := by
  refine Ideal.eq_of_le_of_relNorm_eq (A := R) ?_ ?_
  · rw [Ideal.map_relNorm, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hprod : (∏ σ : L ≃ₐ[K] L, galRestrict R K L S σ x) =
        algebraMap R S (Algebra.intNorm R S x) := by
      apply IsFractionRing.injective S L
      rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L,
        Algebra.algebraMap_intNorm (L := L), map_prod]
      simp only [algebraMap_galRestrict_apply]
      exact (Algebra.norm_eq_prod_automorphisms K (algebraMap S L x)).symm
    rw [Function.comp_apply, SetLike.mem_coe, ← hprod]
    exact Ideal.prod_mem_prod fun σ _ ↦ Ideal.mem_map_of_mem _ hx
  · rw [Ideal.relNorm_algebraMap, map_prod]
    have hterm (σ : L ≃ₐ[K] L) :
        Ideal.relNorm R (Ideal.map (galRestrict R K L S σ : S →+* S) I) = Ideal.relNorm R I :=
      Ideal.relNorm_map_algEquiv (galRestrict R K L S σ) I
    simp only [hterm, Finset.prod_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L,
      IsFractionRing.finrank_eq R K S L]

/-- **Class-group Galois orbit product**: norming a class down from `S` to `R` and extending it
back to `S` multiplies all Galois conjugates of the class. This is the companion to
`ClassGroup.relNorm_extendedHom`. -/
theorem ClassGroup.extendedHom_relNorm (R K L S : Type*)
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

section NumberField

open NumberField
open scoped NumberField

namespace ClassGroup

/-- **Class-group Galois orbit product for number fields**, expressed in terms of
`NumberField.RingOfIntegers.mapRingEquiv`. -/
theorem extendedHom_relNorm_ringOfIntegers (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L] (c : ClassGroup (𝓞 L)) :
    ClassGroup.extendedHom (𝓞 K) (𝓞 L) (ClassGroup.relNorm (𝓞 K) c) =
      ∏ σ : L ≃ₐ[K] L,
        ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) c := by
  rw [extendedHom_relNorm (𝓞 K) K L (𝓞 L) c]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  have hEq : (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv =
      RingOfIntegers.mapRingEquiv σ.toRingEquiv :=
    RingEquiv.ext fun z ↦ RingOfIntegers.ext (algebraMap_galRestrict_apply (𝓞 K) σ z)
  rw [hEq]

/-- **Galois equivariance of `ClassGroup.relNorm` on rings of integers** for a normal subextension
`K / F` inside `L / F`. -/
theorem relNorm_mulEquiv_ringOfIntegers {F K L : Type*} [Field F] [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F K] (τ : L ≃ₐ[F] L) (c : ClassGroup (𝓞 L)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv)
        (ClassGroup.relNorm (𝓞 K) c) =
      ClassGroup.relNorm (𝓞 K)
        (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv τ.toRingEquiv) c) :=
  relNorm_mulEquiv _ _ (fun x ↦ RingOfIntegers.ext <| by
    simp only [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
      RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (τ.restrictNormal_commutes K _).symm) c

/-- **Galois equivariance of `ClassGroup.extendedHom` on rings of integers** for a normal
subextension `K / F` inside `L / F`. -/
theorem extendedHom_mulEquiv_ringOfIntegers {F K L : Type*} [Field F] [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra F K] [Algebra F L] [Algebra K L]
    [IsScalarTower F K L] [Normal F K] (τ : L ≃ₐ[F] L) (c : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv τ.toRingEquiv)
        (ClassGroup.extendedHom (𝓞 K) (𝓞 L) c) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv) c) :=
  extendedHom_mulEquiv _ _ (fun x ↦ RingOfIntegers.ext <| by
    simp only [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv,
      RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L]
    exact (τ.restrictNormal_commutes K _).symm) c

end ClassGroup

end NumberField

section BaseChange

open scoped TensorProduct

namespace ClassGroup

/-- The `R`-linear base change of `ClassGroup.mulEquiv f` to `R ⊗[ℤ] Additive (ClassGroup _)`. -/
noncomputable def mulEquivBaseChange (R : Type*) [CommRing R] {A B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsDomain B] (f : A ≃+* B) :
    (R ⊗[ℤ] Additive (ClassGroup A)) →ₗ[R] (R ⊗[ℤ] Additive (ClassGroup B)) :=
  (MonoidHom.toAdditive (ClassGroup.mulEquiv f).toMonoidHom).toIntLinearMap.baseChange R

@[simp]
theorem mulEquivBaseChange_tmul (R : Type*) [CommRing R] {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (f : A ≃+* B) (r : R) (c : ClassGroup A) :
    mulEquivBaseChange R f (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mulEquiv f c) :=
  LinearMap.baseChange_tmul _ r (Additive.ofMul c)

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
      ∑ σ : L ≃ₐ[K] L, mulEquivBaseChange R (galRestrict A K L B σ).toRingEquiv := by
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
    (mulEquivBaseChange R f).comp (relNormBaseChange R A B) =
      (relNormBaseChange R A' B').comp (mulEquivBaseChange R g) := by
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
    (mulEquivBaseChange R g).comp (extendedBaseChange R A B) =
      (extendedBaseChange R A' B').comp (mulEquivBaseChange R f) := by
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

end ClassGroup

end BaseChange
