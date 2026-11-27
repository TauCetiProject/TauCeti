/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.AuslanderReitenDuality
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import TauCeti.CategoryTheory.Functor.LocalEnd
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Quotient
import TauCeti.RingTheory.LocalRing.Basic

/-!
# The Auslander–Reiten translate on isomorphism classes

An equivalence `τ : E/𝒫 ≌ E/ℐ` between the quotients by projectively and injectively trivial
morphisms gives a bijection between the isomorphism classes of indecomposable nonprojectives and
indecomposable noninjectives in a Krull–Schmidt exact category. For the equivalence of an
Auslander–Reiten duality, this bijection sends the class of the right end of an almost-split
conflation to the class of its left end.

See Iyama, Nakaoka and Palu, *Auslander–Reiten theory in extriangulated categories*,
arXiv:1805.03776v3, Remark 3.5 for the stable translate over a field and Proposition 3.15(1)
for the description of the bijection by almost-split extensions.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasFiniteBiproducts C] [IsKrullSchmidt C] (E : ExactStructure C)

private noncomputable def projectivelyTrivialSkeletonEquiv :=
  E.projectivelyTrivialIdeal.quotientFunctor.skeletonEquivOfIsLocalRingEnd E.isProjective
    (fun Z ↦ (E.projectivelyTrivialIdeal.isZero_quotientFunctor_obj_iff Z).trans
      (E.id_mem_projectivelyTrivialIdeal_iff Z))

private noncomputable def injectivelyTrivialSkeletonEquiv :=
  E.injectivelyTrivialIdeal.quotientFunctor.skeletonEquivOfIsLocalRingEnd E.isInjective
    (fun X ↦ (E.injectivelyTrivialIdeal.isZero_quotientFunctor_obj_iff X).trans
      (E.id_mem_injectivelyTrivialIdeal_iff X))

variable (τ : E.projectivelyTrivialIdeal.Quotient ≌ E.injectivelyTrivialIdeal.Quotient)

private def stableTranslateLocalEndEquivalence :
    (ObjectProperty.FullSubcategory fun Z : E.projectivelyTrivialIdeal.Quotient ↦
      IsLocalRing (End Z)) ≌
    (ObjectProperty.FullSubcategory fun X : E.injectivelyTrivialIdeal.Quotient ↦
      IsLocalRing (End X)) := by
  let Q : ObjectProperty E.injectivelyTrivialIdeal.Quotient := fun X ↦ IsLocalRing (End X)
  haveI : Q.IsClosedUnderIsomorphisms :=
    ⟨fun {X _} e h ↦ by
      let : IsLocalRing (End X) := h
      exact e.endRingEquiv.isLocalRing⟩
  haveI : τ.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact τ.congrFullSubcategory (Q := Q) (funext fun Z ↦
    propext (τ.functor.isLocalRing_end_obj_iff Z))

/-- The stable translate induces a bijection between the isomorphism classes of indecomposable
nonprojectives and indecomposable noninjectives of the exact category. -/
noncomputable def auslanderReitenTranslateEquiv :
    Skeleton (ObjectProperty.FullSubcategory fun Z ↦ Indecomposable Z ∧ ¬ E.isProjective Z) ≃
      Skeleton (ObjectProperty.FullSubcategory fun X ↦ Indecomposable X ∧ ¬ E.isInjective X) :=
  E.projectivelyTrivialSkeletonEquiv.trans
    ((E.stableTranslateLocalEndEquivalence τ).skeletonIsoCat.objEquiv.trans
      E.injectivelyTrivialSkeletonEquiv.symm)

/-- The image of the class of `Z` under the Auslander–Reiten translate is the class of `X` exactly
when the stable translate of `Z` is isomorphic to the image of `X` modulo injectively trivial
morphisms. -/
theorem auslanderReitenTranslateEquiv_apply_eq_iff {Z X : C}
    (hZ : Indecomposable Z) (hZp : ¬ E.isProjective Z)
    (hX : Indecomposable X) (hXi : ¬ E.isInjective X) :
    E.auslanderReitenTranslateEquiv τ (toSkeleton ⟨Z, hZ, hZp⟩) = toSkeleton ⟨X, hX, hXi⟩ ↔
      Nonempty (τ.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ≅
        E.injectivelyTrivialIdeal.quotientFunctor.obj X) := by
  let q := E.projectivelyTrivialIdeal.quotientFunctor
  have hq (Z : C) : IsZero (q.obj Z) ↔ E.isProjective Z :=
    (E.projectivelyTrivialIdeal.isZero_quotientFunctor_obj_iff Z).trans
      (E.id_mem_projectivelyTrivialIdeal_iff Z)
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  let Z' : ObjectProperty.FullSubcategory (fun W ↦ IsLocalRing (End W)) :=
    ⟨q.obj Z, q.isLocalRing_end_obj ((hq Z).not.mpr hZp)⟩
  have hsource : E.projectivelyTrivialSkeletonEquiv (toSkeleton ⟨Z, hZ, hZp⟩) = toSkeleton Z' :=
    (q.skeletonEquivOfIsLocalRingEnd_apply_eq_iff E.isProjective hq hZ hZp Z'.property).mpr
      ⟨Iso.refl _⟩
  have htranslate :
      (E.stableTranslateLocalEndEquivalence τ).skeletonIsoCat.objEquiv (toSkeleton Z') =
      toSkeleton ((E.stableTranslateLocalEndEquivalence τ).functor.obj Z') :=
    Functor.mapSkeleton_obj_toSkeleton _ _
  unfold auslanderReitenTranslateEquiv
  simp only [Equiv.trans_apply, Equiv.symm_apply_eq, hsource, htranslate]
  rw [eq_comm]
  unfold injectivelyTrivialSkeletonEquiv
  exact (Functor.skeletonEquivOfIsLocalRingEnd_apply_eq_iff
    E.injectivelyTrivialIdeal.quotientFunctor E.isInjective _ hX hXi
    ((E.stableTranslateLocalEndEquivalence τ).functor.obj Z').property).trans
    (Iso.nonempty_iso_symm _ _)

namespace AuslanderReitenDuality

universe w

variable {E} {R : Type*} [CommRing R] [Linear R C] {Q : Type w}
  [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Small.{w} R]
  (A : E.AuslanderReitenDuality R Q)
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)

include hQ in
/-- For an Auslander–Reiten duality, the translate sends the class of `Z` to the class of `X`
exactly when there is an almost-split conflation with left end `X` and right end `Z`. -/
theorem translateEquiv_apply_eq_iff_exists_isAlmostSplit {Z X : C}
    (hZ : Indecomposable Z) (hZp : ¬ E.isProjective Z) (hX : Indecomposable X)
    (hXi : ¬ E.isInjective X) (hfin : ∀ Y, IsFiniteLength R (E.Ext1 Z Y)) :
    E.auslanderReitenTranslateEquiv A.functor.asEquivalence (toSkeleton ⟨Z, hZ, hZp⟩) =
      toSkeleton ⟨X, hX, hXi⟩ ↔
      ∃ e : E.Extension Z X, e.shortComplex.IsAlmostSplit := by
  rw [E.auslanderReitenTranslateEquiv_apply_eq_iff _ hZ hZp hX hXi]
  refine ⟨?_, fun ⟨e, he⟩ ↦ ⟨(A.isoTranslateOfIsAlmostSplit hQ hfin e he).symm⟩⟩
  rintro ⟨i⟩
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).mp hX
  obtain ⟨b, hb⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective
    (X := X) (Y := A.translateObj Z) i.inv
  have hb' : IsIso (E.injectivelyTrivialIdeal.quotientFunctor.map b) := hb ▸ inferInstance
  exact exists_isAlmostSplit_of_bijective_costablePairing hQ hXi (hfin X) fun Y ↦
    bijective_costablePairing_comp_pushout (A.bijective_costablePairing_form hQ (hfin Y)) hb'

end AuslanderReitenDuality

end TauCeti.ExactStructure
