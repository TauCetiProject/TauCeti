/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Prod

/-!
# Relative projective `K₀` of a nonunital algebra

Let `A` be a possibly nonunital algebra over a commutative ring `R`, and `A⁺ = Unitization R A`
its forced unitization, used even when `A` already has a unit. The augmentation
`ε : A⁺ → R`, `(r, a) ↦ r`, induces a homomorphism `K₀(A⁺) → K₀(R)` of projective `K₀`-groups
(`TauCeti.KZero.map`), and the **relative `K₀`** of `A` is its kernel. For `R = ℤ` this is the
reduced `K₀` of the nonunital ring `A`, computed on its Dorroh unitization.

The scalar inclusion `s : R → A⁺` is a ring homomorphism with `ε ∘ s = id`, so `K₀(s)` splits
`K₀(ε)`: every class of `A⁺` is the sum of its relative part and the class `K₀(s ∘ ε)(x)` coming
from the scalars, and `K₀(A⁺)` is the product of relative `K₀` and `K₀(R)`. A homomorphism of
nonunital algebras induces a homomorphism of relative `K₀` through the induced map of forced
unitizations, which preserves the augmentation, and so does a change of the scalar ring
`R → S`. The zero algebra has trivial relative `K₀`, since its unitization is `R` itself.

On the idempotent model of `K₀` (`TauCeti.IdempotentMonoid.kZeroEquiv`), the relative classes
are exactly the differences `[e] - [s(ε(e))]`, where `e` is an idempotent matrix over `A⁺` and
`s(ε(e))` is its scalar part, an idempotent matrix over `R`, included into `A⁺`.

For a unital algebra `B` the forced unitization is the product ring `B × R`
(`Unitization.prodAlgEquiv`), with the augmentation as second projection. Since `K₀` turns
finite products of rings into products of groups (`TauCeti.KZero.prodEquiv`), the map induced by
`Unitization R B → B`, `(r, b) ↦ r • 1 + b`, identifies the relative `K₀` of `B` with `K₀(B)`.

This is the `K₀` counterpart of the relative `K₁` and `K₂` of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.RelativeK1` and
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.RelativeK2`. The scalar ring and the
algebra share one universe, as the maps of `TauCeti.KZero` require.

## Main definitions

* `TauCeti.relativeKZero`: the kernel of `K₀(A⁺) → K₀(R)`.
* `TauCeti.relativeKZero.projection`: the projection of `K₀(A⁺)` onto relative `K₀` along the
  classes coming from the scalars.
* `TauCeti.relativeKZero.unitizationEquiv`: the splitting
  `K₀(A⁺) ≃+ relativeKZero R A × K₀(R)`.
* `TauCeti.relativeKZero.map`: the homomorphism induced by a homomorphism of nonunital algebras.
* `TauCeti.relativeKZero.mapScalars`: change of the scalar ring along an algebra `R → S`.
* `TauCeti.relativeKZero.equivKZero`: for a unital algebra `B`, the isomorphism of its relative
  `K₀` with `K₀(B)`.

## Main results

* `TauCeti.relativeKZero_eq_bot`: the zero algebra has trivial relative `K₀`.
* `TauCeti.kZeroEquiv_sub_kZeroEquiv_mem_relativeKZero`,
  `TauCeti.relativeKZero.exists_kZeroEquiv_sub_kZeroEquiv_eq`: the relative classes are exactly
  the differences `[e] - [s(ε(e))]` of an idempotent matrix `e` over `A⁺` and its scalar part.
* `TauCeti.relativeKZero.coe_projection_add_map_algebraMap`: every class of `A⁺` is its relative
  part plus the class coming from the scalars.
* `TauCeti.relativeKZero.map_projection`, `TauCeti.relativeKZero.map_id`,
  `TauCeti.relativeKZero.map_comp`: naturality of the projection and functoriality.
* `TauCeti.relativeKZero.mapScalars_map`: change of scalars is natural.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter II, Exercises 2.3 and 2.4, for `K₀` of a nonunital ring as the
  kernel of `K₀(I⁺) → K₀(ℤ)` on its unitization, and the comparison with `K₀` of a unital ring.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), Chapter 1, for `K₀`
  of nonunital rings through their unitization.
-/

public section

noncomputable section

namespace TauCeti

open Unitization _root_.Algebra

universe u

variable (R A : Type u) [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

/-- The **relative projective `K₀`** of a possibly nonunital algebra `A`: the kernel of the
homomorphism `K₀(A⁺) → K₀(R)` induced by the augmentation of the forced unitization
`A⁺ = Unitization R A`. For `R = ℤ` it is the reduced `K₀` of the nonunital ring `A`. -/
def relativeKZero : AddSubgroup (KZero (Unitization R A)) :=
  (KZero.map (fstHom R A : Unitization R A →+* R)).ker

variable {R A}

/-- A class of `A⁺` is relative exactly when the augmentation sends it to zero. -/
@[simp]
theorem mem_relativeKZero_iff {x : KZero (Unitization R A)} :
    x ∈ relativeKZero R A ↔ KZero.map (fstHom R A : Unitization R A →+* R) x = 0 :=
  AddMonoidHom.mem_ker

/-- The augmentation is a left inverse of the scalar inclusion on projective `K₀`. -/
theorem KZero.map_fstHom_map_algebraMap (x : KZero R) :
    KZero.map (fstHom R A : Unitization R A →+* R)
      (KZero.map (algebraMap R (Unitization R A)) x) = x := by
  simp

/-- The zero algebra has trivial relative `K₀`: its forced unitization is `R`, through the
augmentation. -/
theorem relativeKZero_eq_bot [Subsingleton A] : relativeKZero R A = ⊥ := by
  refine (AddMonoidHom.ker_eq_bot_iff _).2 (Function.LeftInverse.injective
    (g := KZero.map (algebraMap R (Unitization R A))) fun x ↦ ?_)
  have h : (algebraMap R (Unitization R A)).comp (fstHom R A : Unitization R A →+* R) =
      RingHom.id _ :=
    RingHom.ext fun u ↦ Unitization.ext (by simp) (Subsingleton.elim _ _)
  rw [KZero.map_map, h, KZero.map_id, AddMonoidHom.id_apply]

/-- For an idempotent matrix `e` over `A⁺`, the class `[e] - [s(ε(e))]` is relative, where
`s(ε(e))` is the scalar part of `e`, an idempotent matrix over `R`, included into `A⁺`. -/
theorem kZeroEquiv_sub_kZeroEquiv_mem_relativeKZero {n : ℕ}
    {e : Matrix (Fin n) (Fin n) (Unitization R A)} (he : IsIdempotentElem e) :
    IdempotentMonoid.kZeroEquiv _ (GrothendieckAddGroup.of (IdempotentMonoid.mk e he)) -
        IdempotentMonoid.kZeroEquiv _ (GrothendieckAddGroup.of (IdempotentMonoid.mk
          (e.map ((algebraMap R (Unitization R A)).comp (fstHom R A : Unitization R A →+* R)))
          (he.matrix_map _))) ∈ relativeKZero R A := by
  rw [← KZero.map_kZeroEquiv_of_mk _ he, ← KZero.map_map, mem_relativeKZero_iff, map_sub,
    KZero.map_fstHom_map_algebraMap, sub_self]

namespace relativeKZero

variable (R A) in
/-- The projection of `K₀(A⁺)` onto relative `K₀` along the classes coming from the scalars,
`x ↦ x - s(ε(x))`, where `ε` is induced by the augmentation and `s` by the scalar inclusion. -/
def projection : KZero (Unitization R A) →+ relativeKZero R A :=
  (AddMonoidHom.id _ - (KZero.map (algebraMap R (Unitization R A))).comp
    (KZero.map (fstHom R A : Unitization R A →+* R))).codRestrict _
    fun x ↦ by
      rw [mem_relativeKZero_iff, AddMonoidHom.sub_apply, map_sub, AddMonoidHom.comp_apply,
        KZero.map_fstHom_map_algebraMap, AddMonoidHom.id_apply, sub_self]

/-- The relative part of a class `x` of `A⁺` is `x - s(ε(x))`. -/
theorem coe_projection_apply (x : KZero (Unitization R A)) :
    (projection R A x : KZero (Unitization R A)) =
      x - KZero.map (algebraMap R (Unitization R A))
        (KZero.map (fstHom R A : Unitization R A →+* R) x) := by
  simp [projection]

/-- The projection is the identity on relative classes. -/
@[simp]
theorem projection_coe (x : relativeKZero R A) : projection R A x = x := by
  ext
  simp [coe_projection_apply, mem_relativeKZero_iff.1 x.property]

/-- The projection kills the classes coming from the scalars. -/
@[simp]
theorem projection_map_algebraMap (y : KZero R) :
    projection R A (KZero.map (algebraMap R (Unitization R A)) y) = 0 := by
  ext
  simp [coe_projection_apply]

/-- Every class of `A⁺` is the sum of its relative part and the class coming from the scalars,
the image of `x` under the map induced by `s ∘ ε`. -/
@[simp]
theorem coe_projection_add_map_algebraMap (x : KZero (Unitization R A)) :
    (projection R A x : KZero (Unitization R A)) +
        KZero.map ((algebraMap R (Unitization R A)).comp
          (fstHom R A : Unitization R A →+* R)) x = x := by
  rw [← KZero.map_map, coe_projection_apply, sub_add_cancel]

/-- **Idempotent representatives of relative `K₀`.** Every relative class is `[e] - [s(ε(e))]`
for an idempotent matrix `e` over `A⁺`, where `s(ε(e))` is the scalar part of `e`, an idempotent
matrix over `R`, included into `A⁺`. -/
theorem exists_kZeroEquiv_sub_kZeroEquiv_eq {x : KZero (Unitization R A)}
    (hx : x ∈ relativeKZero R A) :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) (Unitization R A)) (he : IsIdempotentElem e),
      IdempotentMonoid.kZeroEquiv _ (GrothendieckAddGroup.of (IdempotentMonoid.mk e he)) -
        IdempotentMonoid.kZeroEquiv _ (GrothendieckAddGroup.of (IdempotentMonoid.mk
          (e.map ((algebraMap R (Unitization R A)).comp (fstHom R A : Unitization R A →+* R)))
          (he.matrix_map _))) = x := by
  obtain ⟨n, e, he, m, rfl⟩ := IdempotentMonoid.exists_kZeroEquiv_sub_nsmul_eq x
  refine ⟨n, e, he, ?_⟩
  -- The scalar part of `x = [e] - m [A⁺]` vanishes, so `[s(ε(e))] = m [A⁺]`.
  have h : KZero.map ((algebraMap R (Unitization R A)).comp
      (fstHom R A : Unitization R A →+* R)) (IdempotentMonoid.kZeroEquiv _
        (GrothendieckAddGroup.of (IdempotentMonoid.mk e he)) -
          m • SplitK0.of.{u} (finiteProjectiveModulesRegular (Unitization R A)ᵐᵒᵖ)) = 0 := by
    rw [← KZero.map_map, mem_relativeKZero_iff.1 hx, map_zero]
  rw [map_sub, map_nsmul, KZero.map_kZeroEquiv_of_mk, KZero.map_of_finiteProjectiveModulesRegular,
    sub_eq_zero] at h
  rw [h]

variable (R A) in
/-- The augmentation splitting of projective `K₀` of a forced unitization: `K₀(A⁺)` is the
product of the relative `K₀` of `A` and `K₀(R)`, through the projection and the augmentation, with
inverse `(y, z) ↦ y + s(z)`. -/
def unitizationEquiv : KZero (Unitization R A) ≃+ relativeKZero R A × KZero R :=
  AddMonoidHom.toAddEquiv
    ((projection R A).prod (KZero.map (fstHom R A : Unitization R A →+* R)))
    ((relativeKZero R A).subtype.coprod (KZero.map (algebraMap R (Unitization R A))))
    (AddMonoidHom.ext fun x ↦ by simp [coe_projection_apply])
    (by ext ⟨y, z⟩ <;> simp [mem_relativeKZero_iff.1 y.property])

/-- The splitting sends a class to its relative part and its augmentation. -/
@[simp]
theorem unitizationEquiv_apply (x : KZero (Unitization R A)) :
    unitizationEquiv R A x =
      (projection R A x, KZero.map (fstHom R A : Unitization R A →+* R) x) :=
  (rfl)

/-- The inverse of the splitting adds to a relative class the image of a class of `R` under the
scalar inclusion. -/
@[simp]
theorem unitizationEquiv_symm_apply (y : relativeKZero R A) (z : KZero R) :
    (unitizationEquiv R A).symm (y, z) =
      (y : KZero (Unitization R A)) + KZero.map (algebraMap R (Unitization R A)) z :=
  (rfl)

section Map

variable {B C : Type u} [NonUnitalRing B] [Module R B] [IsScalarTower R B B]
  [SMulCommClass R B B] [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The homomorphism of relative `K₀` induced by a homomorphism of nonunital algebras, through the
induced map of forced unitizations. -/
def map (f : A →ₙₐ[R] B) : relativeKZero R A →+ relativeKZero R B :=
  ((KZero.map (Unitization.map f : Unitization R A →+* Unitization R B)).comp
    (relativeKZero R A).subtype).codRestrict _ fun x ↦ by
      rw [mem_relativeKZero_iff, AddMonoidHom.comp_apply, KZero.map_map,
        ← AlgHom.comp_toRingHom, fstHom_comp_map]
      exact mem_relativeKZero_iff.1 x.property

/-- The induced homomorphism of relative `K₀` is the induced homomorphism of `K₀(A⁺)`. -/
@[simp]
theorem coe_map_apply (f : A →ₙₐ[R] B) (x : relativeKZero R A) :
    (map f x : KZero (Unitization R B)) =
      KZero.map (Unitization.map f : Unitization R A →+* Unitization R B) x :=
  (rfl)

/-- The projection onto relative `K₀` is natural for homomorphisms of nonunital algebras. -/
theorem map_projection (f : A →ₙₐ[R] B) (x : KZero (Unitization R A)) :
    map f (projection R A x) =
      projection R B (KZero.map (Unitization.map f : Unitization R A →+* Unitization R B) x) := by
  ext
  simp only [coe_map_apply, coe_projection_apply, map_sub]
  congr 1
  simp only [KZero.map_map, ← AlgHom.comp_toRingHom, fstHom_comp_map]
  rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]

/-- The identity homomorphism induces the identity of relative `K₀`. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = AddMonoidHom.id (relativeKZero R A) := by
  ext x
  simp [Unitization.map_id]

/-- Relative `K₀` is functorial. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp only [coe_map_apply, AddMonoidHom.comp_apply, Unitization.map_comp, AlgHom.comp_toRingHom,
    KZero.map_comp]

end Map

section ChangeOfScalars

variable {S : Type u} [CommRing S] [Algebra R S] [Module S A] [IsScalarTower S A A]
  [SMulCommClass S A A] [IsScalarTower R S A]

variable (S) in
/-- Change of the scalar ring of relative `K₀`: for an algebra `R → S` and an `S`-algebra `A`,
the homomorphism `K₀(A⁺_R) → K₀(A⁺_S)` induced by the change of scalars of forced unitizations
`Unitization.mapScalars`, `(r, a) ↦ (algebraMap R S r, a)`, restricted to relative classes. -/
def mapScalars : relativeKZero R A →+ relativeKZero S A :=
  ((KZero.map (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A)).comp
      (relativeKZero R A).subtype).codRestrict _
    fun x ↦ by
      simp [← KZero.map_map _ (algebraMap R S), mem_relativeKZero_iff.1 x.property]

/-- The change of scalars of relative `K₀` is the homomorphism of `K₀` induced by the map of
forced unitizations. -/
@[simp]
theorem coe_mapScalars_apply (x : relativeKZero R A) :
    (mapScalars S x : KZero (Unitization S A)) =
      KZero.map (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A) x :=
  (rfl)

/-- The change of scalars of relative `K₀` is natural for homomorphisms of nonunital
`S`-algebras. -/
theorem mapScalars_map {B : Type u} [NonUnitalRing B] [Module S B] [IsScalarTower S B B]
    [SMulCommClass S B B] [Module R B] [IsScalarTower R S B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : A →ₙₐ[S] B) (x : relativeKZero R A) :
    mapScalars S (map (f.restrictScalars R) x) = map f (mapScalars S x) := by
  have h : (Unitization.mapScalars R S B : Unitization R B →+* Unitization S B).comp
        (Unitization.map (f.restrictScalars R) : Unitization R A →+* Unitization R B) =
      (Unitization.map f : Unitization S A →+* Unitization S B).comp
        (Unitization.mapScalars R S A : Unitization R A →+* Unitization S A) :=
    RingHom.ext (Unitization.mapScalars_map f)
  apply Subtype.ext
  simp only [coe_mapScalars_apply, coe_map_apply, KZero.map_map, h]

end ChangeOfScalars

section Unital

variable {B : Type u} [Ring B] [Algebra R B]

variable (R B) in
/-- The inverse of `relativeKZero.equivKZero`: a class `z` of `B` goes to the class over
`Unitization R B ≃ B × R` with components `z` and `0`. -/
private def ofKZero : KZero B →+ relativeKZero R B :=
  ((KZero.map ((prodAlgEquiv R B).symm : B × R →+* Unitization R B)).comp
      ((KZero.prodEquiv B R).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _))).codRestrict _
    fun z ↦ by
      rw [mem_relativeKZero_iff, AddMonoidHom.comp_apply, KZero.map_map,
        fstHom_comp_prodAlgEquiv_symm, ← KZero.prodEquiv_apply_snd]
      simp

private theorem coe_ofKZero_apply (z : KZero B) :
    (ofKZero R B z : KZero (Unitization R B)) =
      KZero.map ((prodAlgEquiv R B).symm : B × R →+* Unitization R B)
        ((KZero.prodEquiv B R).symm (z, 0)) :=
  (rfl)

variable (R B) in
/-- **Relative `K₀` of a unital algebra is its `K₀`.** For a unital `R`-algebra `B`, the
homomorphism induced by `Unitization R B → B`, `(r, b) ↦ r • 1 + b`, restricts to an
isomorphism from the relative `K₀` of `B`, computed on its forced unitization, onto `K₀(B)`. The
inverse sends a class `z` to the class over `Unitization R B ≃ B × R` with components `z` and
`0`. -/
def equivKZero : relativeKZero R B ≃+ KZero B :=
  AddMonoidHom.toAddEquiv
    ((KZero.map (lift (NonUnitalAlgHom.id R B) : Unitization R B →+* B)).comp
      (relativeKZero R B).subtype)
    (ofKZero R B)
    (by
      ext ⟨x, hx⟩
      -- Through `Unitization R B ≃ B × R`, the components of `x` are its image in `K₀(B)` and
      -- its augmentation, which vanishes.
      have h : (KZero.map (lift (NonUnitalAlgHom.id R B) : Unitization R B →+* B) x,
          (0 : KZero R)) =
          KZero.prodEquiv B R (KZero.map (prodAlgEquiv R B : Unitization R B →+* B × R) x) := by
        refine Prod.ext ?_ ?_
        · rw [KZero.prodEquiv_apply_fst, KZero.map_map, fst_comp_prodAlgEquiv]
        · rw [KZero.prodEquiv_apply_snd, KZero.map_map, snd_comp_prodAlgEquiv,
            mem_relativeKZero_iff.1 hx]
      simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, AddMonoidHom.id_apply,
        coe_ofKZero_apply, h, AddEquiv.symm_apply_apply]
      have hψφ : ((prodAlgEquiv R B).symm : B × R →+* Unitization R B).comp
          (prodAlgEquiv R B : Unitization R B →+* B × R) = RingHom.id _ :=
        RingHom.ext (prodAlgEquiv R B).symm_apply_apply
      rw [KZero.map_map, hψφ, KZero.map_id, AddMonoidHom.id_apply])
    (by
      ext z
      simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, coe_ofKZero_apply,
        KZero.map_map, lift_comp_prodAlgEquiv_symm, ← KZero.prodEquiv_apply_fst,
        AddEquiv.apply_symm_apply, AddMonoidHom.id_apply])

/-- `relativeKZero.equivKZero` is induced by `Unitization R B → B`, `(r, b) ↦ r • 1 + b`. -/
@[simp]
theorem equivKZero_apply (x : relativeKZero R B) :
    equivKZero R B x =
      KZero.map (lift (NonUnitalAlgHom.id R B) : Unitization R B →+* B) x :=
  (rfl)

/-- The inverse of `relativeKZero.equivKZero` sends a class `z` of `B` to the class over
`Unitization R B ≃ B × R` with components `z` and `0`. -/
@[simp]
theorem coe_equivKZero_symm_apply (z : KZero B) :
    ((equivKZero R B).symm z : KZero (Unitization R B)) =
      KZero.map ((prodAlgEquiv R B).symm : B × R →+* Unitization R B)
        ((KZero.prodEquiv B R).symm (z, 0)) :=
  (rfl)

end Unital

end relativeKZero

end TauCeti
