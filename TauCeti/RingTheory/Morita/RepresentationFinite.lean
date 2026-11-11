/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
-- Non-public: the transport lemmas below are used only inside proofs.
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.ModuleCat.Equivalence
import TauCeti.Algebra.Category.ModuleCat.Indecomposable
import TauCeti.CategoryTheory.ObjectProperty

/-!
# Morita invariance of the indecomposable modules

A ring `A` is representation-finite (`TauCeti.IsRepresentationFinite`) when it has finitely many
isomorphism classes of finitely generated indecomposable modules, that is, when the skeleton of the
full subcategory of `ModuleCat A` spanned by these modules is finite. This file shows that this
skeleton, and with it its cardinality and representation-finiteness, is an invariant of the module
category:

* it does not depend on the universe of the modules, as long as `A` is small in it: every finitely
  generated module is small, so `ModuleCat.uliftFunctor` identifies the finitely generated
  indecomposable modules in two universes;
* an equivalence of module categories `ModuleCat A ≌ ModuleCat B` preserves and reflects finite
  generation and indecomposability, so it identifies the two skeletons;
* hence **Morita equivalent algebras** (`IsMoritaEquivalent R A B`) have the same number of
  isomorphism classes of finitely generated indecomposable modules, and one is
  representation-finite exactly when the other is.

To tell Morita classes apart with this invariant one has to compute it. Over a commutative
semisimple ring `R`, a finite product of fields, the finitely generated indecomposable modules are
the simple modules `R ⧸ m`, one for each maximal ideal `m`, and they are pairwise non-isomorphic
because `m` is the annihilator of `R ⧸ m`. So their number is the number of maximal ideals. For a
field `k` this gives one class and for `k × k` two, so `k` and `k × k` are not Morita equivalent.

## Main results

* `TauCeti.isRepresentationFinite_iff_isRepresentationFinite` and
  `TauCeti.card_skeleton_indecomposable_eq_card_skeleton_indecomposable`: representation-finiteness
  and the number of finitely generated indecomposable modules do not depend on the universe of the
  modules.
* `CategoryTheory.Equivalence.indecomposable_functor_obj_iff`: an equivalence of module categories
  preserves and reflects indecomposability.
* `CategoryTheory.Equivalence.isRepresentationFinite_iff` and
  `CategoryTheory.Equivalence.card_skeleton_indecomposable_eq`: rings with equivalent module
  categories are representation-finite together and have equally many finitely generated
  indecomposable modules.
* `IsMoritaEquivalent.isRepresentationFinite_iff` and
  `IsMoritaEquivalent.card_skeleton_indecomposable_eq`: the same for Morita equivalent algebras.
* `TauCeti.card_skeleton_indecomposable_eq_card_maximalSpectrum`: over a commutative semisimple
  ring the finitely generated indecomposable modules are counted by the maximal ideals.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*, Cambridge
  Studies in Advanced Mathematics 36 (1995), Section II.2.
-/

public section

universe u u' v v' u₁ u₂

open CategoryTheory

namespace TauCeti

section Universe

variable {A : Type u} [Ring A]

/-- Finite generation and indecomposability transfer along a linear equivalence, also between
modules in different universes. -/
private theorem finite_and_indecomposable_of_linearEquiv {M : ModuleCat.{v} A}
    {N : ModuleCat.{v'} A} (e : M ≃ₗ[A] N) (h : Module.Finite A M ∧ Indecomposable M) :
    Module.Finite A N ∧ Indecomposable N :=
  have := h.1
  ⟨Module.Finite.equiv e, (indecomposable_iff_isIndecomposableModule N).mpr
    (((indecomposable_iff_isIndecomposableModule M).mp h.2).of_linearEquiv e)⟩

variable (A) in
/-- `ModuleCat.uliftFunctor` induces a bijection from the isomorphism classes of finitely generated
indecomposable modules in the universe `v` to those in the universe `max v v'`, when `A` is small
in `v`. -/
private theorem bijective_uliftFunctor_mapSkeleton [Small.{v} A] :
    Function.Bijective (ObjectProperty.lift
      (fun N : ModuleCat.{max v v'} A ↦ Module.Finite A N ∧ Indecomposable N)
      ((ObjectProperty.ι fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ⋙
        ModuleCat.uliftFunctor.{v'} A)
      fun M ↦ finite_and_indecomposable_of_linearEquiv ULift.moduleEquiv.symm
        M.property).mapSkeleton.obj := by
  refine ⟨Functor.mapSkeleton_injective _, @Functor.mapSkeleton_surjective _ _ _ _ _ ?_⟩
  rw [ObjectProperty.essSurj_lift_iff]
  intro N hN
  have := hN.1
  have : Small.{v} N := Module.Finite.small A N
  -- A finitely generated module is small, so it is the lift of a module in the universe `v`.
  let e : N ≃ₗ[A] Shrink.{v} N := (Shrink.linearEquiv A N).symm
  exact ⟨⟨ModuleCat.of A (Shrink.{v} N), finite_and_indecomposable_of_linearEquiv e hN⟩,
    ⟨(ULift.moduleEquiv.trans e.symm).toModuleIso⟩⟩

variable (A) in
/-- The isomorphism classes of finitely generated indecomposable modules in the universe `v`
correspond to those in the universe `max v v'`. -/
private noncomputable def skeletonIndecomposableEquivMax [Small.{v} A] :
    Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ≃
      Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{max v v'} A ↦ Module.Finite A N ∧ Indecomposable N) :=
  Equiv.ofBijective _ (bijective_uliftFunctor_mapSkeleton.{u, v, v'} A)

variable (A) in
/-- **The number of finitely generated indecomposable modules does not depend on the universe** of
the modules, among the universes in which the ring is small. -/
theorem card_skeleton_indecomposable_eq_card_skeleton_indecomposable [Small.{v} A]
    [Small.{v'} A] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} A ↦ Module.Finite A N ∧ Indecomposable N)) :=
  (Nat.card_congr (skeletonIndecomposableEquivMax.{u, v, v'} A)).trans
    (Nat.card_congr (skeletonIndecomposableEquivMax.{u, v', v} A)).symm

variable (A) in
/-- **Representation-finiteness does not depend on the universe** of the modules, among the
universes in which the ring is small. -/
theorem isRepresentationFinite_iff_isRepresentationFinite [Small.{v} A] [Small.{v'} A] :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v'} A := by
  rw [isRepresentationFinite_iff, isRepresentationFinite_iff,
    (skeletonIndecomposableEquivMax.{u, v, v'} A).finite_iff,
    (skeletonIndecomposableEquivMax.{u, v', v} A).finite_iff]

end Universe

section Equivalence

variable {A : Type u} [Ring A] {B : Type u'} [Ring B]

/-- **An equivalence of module categories preserves and reflects indecomposability.** -/
@[simp]
theorem _root_.CategoryTheory.Equivalence.indecomposable_functor_obj_iff
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) (M : ModuleCat.{v} A) :
    Indecomposable (e.functor.obj M) ↔ Indecomposable M :=
  ⟨fun h ↦ (e.inverse.indecomposable_obj_of_map_bijective h
      (e.fullyFaithfulInverse.map_bijective _ _)).of_iso (e.unitIso.app M).symm,
    fun h ↦ e.functor.indecomposable_obj_of_map_bijective h
      (e.fullyFaithfulFunctor.map_bijective _ _)⟩

/-- An equivalence of module categories identifies the isomorphism classes of finitely generated
indecomposable modules over the two rings. -/
private noncomputable def skeletonIndecomposableEquiv (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ≃
      Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N) :=
  let Q : ObjectProperty (ModuleCat.{v'} B) := fun N ↦ Module.Finite B N ∧ Indecomposable N
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun f h ↦ have := h.1; ⟨Module.Finite.equiv f.toLinearEquiv, h.2.of_iso f⟩⟩
  (e.congrFullSubcategory (Q := Q) (funext fun M ↦ propext (and_congr
    (e.finite_functor_obj_iff M) (e.indecomposable_functor_obj_iff M)))).skeletonIsoCat.objEquiv

/-- **Rings with equivalent module categories have equally many finitely generated indecomposable
modules** up to isomorphism. No linearity of the equivalence is needed, and the two module
categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.card_skeleton_indecomposable_eq
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N)) :=
  Nat.card_congr (skeletonIndecomposableEquiv e)

/-- **Rings with equivalent module categories are representation-finite together.** No linearity
of the equivalence is needed, and the two module categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.isRepresentationFinite_iff
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v'} B := by
  rw [TauCeti.isRepresentationFinite_iff, TauCeti.isRepresentationFinite_iff,
    (skeletonIndecomposableEquiv e).finite_iff]

end Equivalence

section Morita

variable {R : Type*} [CommSemiring R] {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B]
  [Algebra R B] [Small.{v} A] [Small.{v} B]

/-- **Morita equivalent algebras have equally many finitely generated indecomposable modules** up
to isomorphism, counted with modules in any universe in which both algebras are small. -/
theorem _root_.IsMoritaEquivalent.card_skeleton_indecomposable_eq (h : IsMoritaEquivalent R A B) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v} B ↦ Module.Finite B N ∧ Indecomposable N)) := by
  obtain ⟨e⟩ := h.cond
  rw [card_skeleton_indecomposable_eq_card_skeleton_indecomposable.{u₁, v, max u₁ u₂} A,
    card_skeleton_indecomposable_eq_card_skeleton_indecomposable.{u₂, v, max u₁ u₂} B]
  exact e.eqv.card_skeleton_indecomposable_eq

/-- **Representation-finiteness is a Morita invariant**, with modules in any universe in which both
algebras are small. -/
theorem _root_.IsMoritaEquivalent.isRepresentationFinite_iff (h : IsMoritaEquivalent R A B) :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v} B := by
  obtain ⟨e⟩ := h.cond
  rw [isRepresentationFinite_iff_isRepresentationFinite.{u₁, v, max u₁ u₂} A,
    isRepresentationFinite_iff_isRepresentationFinite.{u₂, v, max u₁ u₂} B]
  exact e.eqv.isRepresentationFinite_iff

end Morita

section CommSemisimple

variable (R : Type u) [CommRing R]

/-- The quotient `R ⧸ m` by a maximal ideal, as a finitely generated indecomposable module. -/
private def quotientMaximal (m : MaximalSpectrum R) :
    ObjectProperty.FullSubcategory
      fun M : ModuleCat.{u} R ↦ Module.Finite R M ∧ Indecomposable M :=
  have : IsSimpleModule R (R ⧸ m.asIdeal) := isSimpleModule_iff_isCoatom.mpr m.isMaximal.out
  ⟨ModuleCat.of R (R ⧸ m.asIdeal), inferInstance,
    (indecomposable_iff_isIndecomposableModule _).mpr IsSimpleModule.isIndecomposableModule⟩

/-- Over a commutative semisimple ring, the quotients by the maximal ideals represent each
isomorphism class of finitely generated indecomposable modules exactly once. -/
private theorem bijective_toSkeleton_quotientMaximal [IsSemisimpleRing R] :
    Function.Bijective fun m : MaximalSpectrum R ↦ toSkeleton (quotientMaximal R m) := by
  refine ⟨fun m m' h ↦ ?_, fun x ↦ ?_⟩
  · -- Isomorphic quotients have the same annihilator, which is the maximal ideal.
    obtain ⟨f⟩ := toSkeleton_eq_toSkeleton_iff.mp h
    -- The objects of `quotientMaximal` are the quotient modules, by definition.
    let g : (R ⧸ m.asIdeal) ≃ₗ[R] R ⧸ m'.asIdeal := ((ObjectProperty.ι _).mapIso f).toLinearEquiv
    have := g.annihilator_eq
    rw [Ideal.annihilator_quotient, Ideal.annihilator_quotient] at this
    exact MaximalSpectrum.ext this
  · -- An indecomposable module over a semisimple ring is simple, hence a quotient by a maximal
    -- ideal.
    let N := (fromSkeleton _).obj x
    have hN : IsSimpleModule R N.obj :=
      ((indecomposable_iff_isIndecomposableModule _).mp N.property.2).isSimpleModule
    obtain ⟨I, hI, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.mp hN
    refine ⟨⟨I, hI⟩, ?_⟩
    rw [← toSkeleton_fromSkeleton_obj x]
    exact toSkeleton_eq_toSkeleton_iff.mpr ⟨ObjectProperty.isoMk _ f.symm.toModuleIso⟩

/-- **Over a commutative semisimple ring the finitely generated indecomposable modules are counted
by the maximal ideals**: they are the simple modules `R ⧸ m`, pairwise non-isomorphic. The modules
may be taken in any universe in which the ring is small. -/
theorem card_skeleton_indecomposable_eq_card_maximalSpectrum [IsSemisimpleRing R] [Small.{v} R] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} R ↦ Module.Finite R M ∧ Indecomposable M)) =
      Nat.card (MaximalSpectrum R) := by
  rw [card_skeleton_indecomposable_eq_card_skeleton_indecomposable.{u, v, u} R]
  exact (Nat.card_congr (Equiv.ofBijective _ (bijective_toSkeleton_quotientMaximal R))).symm

end CommSemisimple

end TauCeti
