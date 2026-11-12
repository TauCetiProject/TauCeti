/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
-- Non-public: the transport lemmas below are used only inside proofs.
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.ModuleCat.Equivalence
import TauCeti.Algebra.Category.ModuleCat.Indecomposable
import TauCeti.CategoryTheory.ObjectProperty

/-!
# Representation-finite rings

A ring `A` is **representation-finite** (`TauCeti.IsRepresentationFinite`) if it has only finitely
many isomorphism classes of finitely generated indecomposable modules. As for quivers
(`TauCeti.IsFiniteRepType`), this is stated as the finiteness of the skeleton of the full
subcategory these modules span, so that "isomorphism class" is Mathlib's. The modules are taken in
a universe `w`, which is a parameter of the predicate.

The predicate is used for the module category of a finite-dimensional algebra, where it says that
the quiver of irreducible morphisms has finitely many vertices
(`TauCeti.IrreducibleMorphismQuiver.finite_iff_isRepresentationFinite`), and for path algebras,
where it agrees with finite representation type of the quiver
(`TauCeti.isFiniteRepType_iff_isRepresentationFinite_pathAlgebra`).

The skeleton, and with it its cardinality and representation-finiteness, is an invariant of the
module category:

* it does not depend on the universe of the modules, as long as `A` is small in it: every finitely
  generated module is small, so `ModuleCat.uliftFunctor` identifies the finitely generated
  indecomposable modules in two universes;
* an equivalence of module categories `ModuleCat A ≌ ModuleCat B` preserves and reflects finite
  generation and indecomposability (`CategoryTheory.Equivalence.indecomposable_functor_obj_iff`),
  so it identifies the two skeletons.

To tell module categories apart with this invariant one has to compute it. Over a commutative
semisimple ring `R`, a finite product of fields, the finitely generated indecomposable modules are
the simple modules `R ⧸ m`, one for each maximal ideal `m`, and they are pairwise non-isomorphic
because `m` is the annihilator of `R ⧸ m`. So their number is the number of maximal ideals.

## Main results

* `TauCeti.skeletonIndecomposableEquivSkeletonIndecomposable`,
  `TauCeti.isRepresentationFinite_iff_isRepresentationFinite` and
  `TauCeti.card_skeleton_indecomposable_eq_card_skeleton_indecomposable`: the isomorphism classes of
  finitely generated indecomposable modules, and so representation-finiteness and their number, do
  not depend on the universe of the modules.
* `CategoryTheory.Equivalence.skeletonIndecomposableEquiv`,
  `CategoryTheory.Equivalence.isRepresentationFinite_iff` and
  `CategoryTheory.Equivalence.card_skeleton_indecomposable_eq`: an equivalence of module categories
  identifies these isomorphism classes, so the two rings are representation-finite together and
  have equally many finitely generated indecomposable modules.
* `TauCeti.maximalSpectrumEquivSkeletonIndecomposable`,
  `TauCeti.card_skeleton_indecomposable_eq_card_maximalSpectrum` and
  `TauCeti.isRepresentationFinite_iff_finite_maximalSpectrum`: over a commutative semisimple ring
  the finitely generated indecomposable modules correspond to the maximal ideals.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006).
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory

section Definition

universe w v

variable (A : Type v) [Ring A]

/-- **Representation-finite rings**: `A` has only finitely many isomorphism classes of finitely
generated indecomposable modules (in the universe `w`). It is stated as the finiteness of the
skeleton of the full subcategory they span. -/
def IsRepresentationFinite : Prop :=
  Finite (Skeleton (ObjectProperty.FullSubcategory
    fun M : ModuleCat.{w} A ↦ Module.Finite A M ∧ Indecomposable M))

/-- Unfolding `TauCeti.IsRepresentationFinite` in modules where its body is not exposed. -/
@[simp]
theorem isRepresentationFinite_iff :
    IsRepresentationFinite.{w} A ↔ Finite (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{w} A ↦ Module.Finite A M ∧ Indecomposable M)) :=
  Iff.rfl

variable {A} in
/-- A ring is representation-finite as soon as every finitely generated indecomposable module is
isomorphic to a member of a fixed finite set of modules. -/
theorem isRepresentationFinite_of_forall_exists_iso {S : Set (ModuleCat.{w} A)} (hS : S.Finite)
    (h : ∀ M : ModuleCat.{w} A, Module.Finite A M → Indecomposable M →
      ∃ Q ∈ S, Nonempty (M ≅ Q)) :
    IsRepresentationFinite.{w} A := by
  rw [isRepresentationFinite_iff]
  let P : ObjectProperty (ModuleCat.{w} A) := fun M ↦ Module.Finite A M ∧ Indecomposable M
  have := hS.to_subtype
  have hrep (x : Skeleton P.FullSubcategory) :=
    h ((fromSkeleton P.FullSubcategory).obj x).obj ((fromSkeleton _).obj x).property.1
      ((fromSkeleton _).obj x).property.2
  choose q hq he using hrep
  refine Finite.of_injective (fun x ↦ (⟨q x, hq x⟩ : S)) fun x y hxy ↦ ?_
  have hxy' : q x = q y := congrArg Subtype.val hxy
  obtain ⟨ex⟩ := he x
  obtain ⟨ey⟩ := he y
  let e : ((fromSkeleton P.FullSubcategory).obj x).obj ≅ ((fromSkeleton _).obj y).obj :=
    ex ≪≫ eqToIso hxy' ≪≫ ey.symm
  exact skeleton_skeletal _ ⟨(fromSkeleton _).preimageIso (P.fullyFaithfulι.preimageIso e)⟩

end Definition

universe v v' u u'

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
  Equiv.ofBijective _ (bijective_uliftFunctor_mapSkeleton.{v, v', u} A)

/-- The class of `M` is sent to the class of its lift `ULift M`. -/
private theorem skeletonIndecomposableEquivMax_toSkeleton [Small.{v} A]
    (M : ObjectProperty.FullSubcategory
      fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) :
    skeletonIndecomposableEquivMax.{v, v', u} A (toSkeleton M) =
      toSkeleton ⟨ModuleCat.of A (ULift.{v'} M.obj),
        finite_and_indecomposable_of_linearEquiv ULift.moduleEquiv.symm M.property⟩ :=
  Functor.mapSkeleton_obj_toSkeleton _ M

variable (A) in
/-- The isomorphism classes of finitely generated indecomposable modules in two universes in which
`A` is small correspond to each other, a class corresponding to the class of the linearly
equivalent modules
(`TauCeti.skeletonIndecomposableEquivSkeletonIndecomposable_toSkeleton_eq_toSkeleton_iff`). -/
noncomputable def skeletonIndecomposableEquivSkeletonIndecomposable [Small.{v} A]
    [Small.{v'} A] :
    Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ≃
      Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} A ↦ Module.Finite A N ∧ Indecomposable N) :=
  (skeletonIndecomposableEquivMax.{v, v', u} A).trans
    (skeletonIndecomposableEquivMax.{v', v, u} A).symm

/-- The universe-change correspondence sends the class of `M` to the class of `N` exactly when `M`
and `N` are linearly equivalent. -/
@[simp]
theorem skeletonIndecomposableEquivSkeletonIndecomposable_toSkeleton_eq_toSkeleton_iff
    [Small.{v} A] [Small.{v'} A]
    {M : ObjectProperty.FullSubcategory
      fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M}
    {N : ObjectProperty.FullSubcategory
      fun N : ModuleCat.{v'} A ↦ Module.Finite A N ∧ Indecomposable N} :
    skeletonIndecomposableEquivSkeletonIndecomposable.{v, v', u} A (toSkeleton M) = toSkeleton N ↔
      Nonempty (M.obj ≃ₗ[A] N.obj) := by
  rw [skeletonIndecomposableEquivSkeletonIndecomposable, Equiv.trans_apply, Equiv.symm_apply_eq,
    skeletonIndecomposableEquivMax_toSkeleton, skeletonIndecomposableEquivMax_toSkeleton,
    toSkeleton_eq_toSkeleton_iff]
  refine ⟨fun ⟨f⟩ ↦ ⟨ULift.moduleEquiv.{u, v, v'}.symm.trans
      (((ObjectProperty.ι _).mapIso f).toLinearEquiv.trans ULift.moduleEquiv.{u, v', v})⟩,
    fun ⟨f⟩ ↦ ⟨ObjectProperty.isoMk _ (ULift.moduleEquiv.{u, v, v'}.trans
      (f.trans ULift.moduleEquiv.{u, v', v}.symm)).toModuleIso⟩⟩

variable (A) in
/-- **The number of finitely generated indecomposable modules does not depend on the universe** of
the modules, among the universes in which the ring is small. -/
theorem card_skeleton_indecomposable_eq_card_skeleton_indecomposable [Small.{v} A]
    [Small.{v'} A] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} A ↦ Module.Finite A N ∧ Indecomposable N)) :=
  Nat.card_congr (skeletonIndecomposableEquivSkeletonIndecomposable.{v, v', u} A)

variable (A) in
/-- **Representation-finiteness does not depend on the universe** of the modules, among the
universes in which the ring is small. -/
theorem isRepresentationFinite_iff_isRepresentationFinite [Small.{v} A] [Small.{v'} A] :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v'} A := by
  rw [isRepresentationFinite_iff, isRepresentationFinite_iff,
    (skeletonIndecomposableEquivSkeletonIndecomposable.{v, v'} A).finite_iff]

end Universe

section Equivalence

variable {A : Type u} [Ring A] {B : Type u'} [Ring B]

/-- An equivalence of module categories identifies the isomorphism classes of finitely generated
indecomposable modules over the two rings, the class of `M` going to the class of `e.functor.obj M`
(`CategoryTheory.Equivalence.skeletonIndecomposableEquiv_toSkeleton_eq_toSkeleton_iff`). No
linearity of the equivalence is needed, and the two module categories may live in different
universes. -/
noncomputable def _root_.CategoryTheory.Equivalence.skeletonIndecomposableEquiv
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ≃
      Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N) :=
  let Q : ObjectProperty (ModuleCat.{v'} B) := fun N ↦ Module.Finite B N ∧ Indecomposable N
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun f h ↦ have := h.1; ⟨Module.Finite.equiv f.toLinearEquiv, h.2.of_iso f⟩⟩
  (e.congrFullSubcategory (Q := Q) (funext fun M ↦ propext (and_congr
    (e.finite_functor_obj_iff M) (e.indecomposable_functor_obj_iff M)))).skeletonIsoCat.objEquiv

/-- The correspondence induced by an equivalence of module categories sends the class of `M` to the
class of `N` exactly when `e.functor.obj M` is isomorphic to `N`. -/
@[simp]
theorem _root_.CategoryTheory.Equivalence.skeletonIndecomposableEquiv_toSkeleton_eq_toSkeleton_iff
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B)
    {M : ObjectProperty.FullSubcategory
      fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M}
    {N : ObjectProperty.FullSubcategory
      fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N} :
    e.skeletonIndecomposableEquiv (toSkeleton M) = toSkeleton N ↔
      Nonempty (e.functor.obj M.obj ≅ N.obj) := by
  rw [Equivalence.skeletonIndecomposableEquiv]
  refine (congrArg (· = toSkeleton N) (Functor.mapSkeleton_obj_toSkeleton _ M)).to_iff.trans
    (toSkeleton_eq_toSkeleton_iff.trans
      ⟨fun ⟨f⟩ ↦ ⟨(ObjectProperty.ι _).mapIso f⟩, fun ⟨f⟩ ↦ ⟨ObjectProperty.isoMk _ f⟩⟩)

/-- **Rings with equivalent module categories have equally many finitely generated indecomposable
modules** up to isomorphism. No linearity of the equivalence is needed, and the two module
categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.card_skeleton_indecomposable_eq
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N)) :=
  Nat.card_congr e.skeletonIndecomposableEquiv

/-- **Rings with equivalent module categories are representation-finite together.** No linearity
of the equivalence is needed, and the two module categories may live in different universes. -/
theorem _root_.CategoryTheory.Equivalence.isRepresentationFinite_iff
    (e : ModuleCat.{v} A ≌ ModuleCat.{v'} B) :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v'} B := by
  rw [TauCeti.isRepresentationFinite_iff, TauCeti.isRepresentationFinite_iff,
    e.skeletonIndecomposableEquiv.finite_iff]

end Equivalence

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

/-- Over a commutative semisimple ring the maximal ideals correspond to the isomorphism classes of
finitely generated indecomposable modules, in any universe in which the ring is small: `m` goes to
the class of the simple module `R ⧸ m`
(`TauCeti.maximalSpectrumEquivSkeletonIndecomposable_apply_eq_toSkeleton_iff`). -/
noncomputable def maximalSpectrumEquivSkeletonIndecomposable [IsSemisimpleRing R] [Small.{v} R] :
    MaximalSpectrum R ≃ Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{v} R ↦ Module.Finite R M ∧ Indecomposable M) :=
  (Equiv.ofBijective _ (bijective_toSkeleton_quotientMaximal R)).trans
    (skeletonIndecomposableEquivSkeletonIndecomposable.{u, v, u} R)

variable {R} in
/-- The maximal ideal `m` corresponds to the class of `N` exactly when `N` is linearly equivalent
to `R ⧸ m`. -/
@[simp]
theorem maximalSpectrumEquivSkeletonIndecomposable_apply_eq_toSkeleton_iff [IsSemisimpleRing R]
    [Small.{v} R] {m : MaximalSpectrum R}
    {N : ObjectProperty.FullSubcategory
      fun N : ModuleCat.{v} R ↦ Module.Finite R N ∧ Indecomposable N} :
    maximalSpectrumEquivSkeletonIndecomposable.{v, u} R m = toSkeleton N ↔
      Nonempty ((R ⧸ m.asIdeal) ≃ₗ[R] N.obj) :=
  skeletonIndecomposableEquivSkeletonIndecomposable_toSkeleton_eq_toSkeleton_iff.{u, v, u}

/-- **Over a commutative semisimple ring the finitely generated indecomposable modules are counted
by the maximal ideals**: they are the simple modules `R ⧸ m`, pairwise non-isomorphic. The modules
may be taken in any universe in which the ring is small. -/
theorem card_skeleton_indecomposable_eq_card_maximalSpectrum [IsSemisimpleRing R] [Small.{v} R] :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} R ↦ Module.Finite R M ∧ Indecomposable M)) =
      Nat.card (MaximalSpectrum R) :=
  (Nat.card_congr (maximalSpectrumEquivSkeletonIndecomposable R)).symm

/-- **A commutative semisimple ring is representation-finite exactly when it has finitely many
maximal ideals.** The modules may be taken in any universe in which the ring is small. -/
theorem isRepresentationFinite_iff_finite_maximalSpectrum [IsSemisimpleRing R] [Small.{v} R] :
    IsRepresentationFinite.{v} R ↔ Finite (MaximalSpectrum R) := by
  rw [isRepresentationFinite_iff, (maximalSpectrumEquivSkeletonIndecomposable.{v, u} R).finite_iff]

end CommSemisimple

end TauCeti
