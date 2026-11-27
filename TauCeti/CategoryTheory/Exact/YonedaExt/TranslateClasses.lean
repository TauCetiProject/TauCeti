/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.AuslanderReitenDuality
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import Mathlib.CategoryTheory.Skeletal
import TauCeti.CategoryTheory.Functor.LocalEnd
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Quotient

/-!
# The Auslander–Reiten translate on isomorphism classes

An equivalence `τ : E/𝒫 ≌ E/ℐ` between the quotients by projectively and injectively trivial
morphisms gives a bijection between the isomorphism classes of indecomposable nonprojectives and
indecomposable noninjectives in a Krull–Schmidt exact category. For an Auslander–Reiten duality
whose dualizing module `Q` gives a dual of length one for each simple `R`-module, suppose
`Ext¹_E(Z, Y)` has finite length for every `Y`. Then the bijection sends the class of `Z` to the
class of `X` exactly when there is an almost-split conflation with left end `X` and right end `Z`.

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
    E.isZero_projectivelyTrivialIdeal_quotientFunctor_obj_iff

private noncomputable def injectivelyTrivialSkeletonEquiv :=
  E.injectivelyTrivialIdeal.quotientFunctor.skeletonEquivOfIsLocalRingEnd E.isInjective
    E.isZero_injectivelyTrivialIdeal_quotientFunctor_obj_iff

variable (τ : E.projectivelyTrivialIdeal.Quotient ≌ E.injectivelyTrivialIdeal.Quotient)

/-- An equivalence `τ` between the quotients by projectively and injectively trivial morphisms
induces a bijection between the isomorphism classes of indecomposable nonprojectives and
indecomposable noninjectives. When `τ` comes from an Auslander–Reiten duality, this bijection is
the Auslander–Reiten translate on classes. -/
noncomputable def skeletonEquivOfQuotientEquiv :
    Skeleton (ObjectProperty.FullSubcategory fun Z ↦ Indecomposable Z ∧ ¬ E.isProjective Z) ≃
      Skeleton (ObjectProperty.FullSubcategory fun X ↦ Indecomposable X ∧ ¬ E.isInjective X) :=
  haveI : τ.functor.Additive := Functor.additive_of_preserves_binary_products _
  E.projectivelyTrivialSkeletonEquiv.trans
    (τ.congrLocalEndFullSubcategory.skeletonIsoCat.objEquiv.trans
      E.injectivelyTrivialSkeletonEquiv.symm)

/-- The bijection induced by `τ` sends the class of `Z` to the class of `X` exactly when `τ`
sends the projectively trivial quotient image of `Z` to an object isomorphic to the
injectively trivial quotient image of `X`. -/
theorem skeletonEquivOfQuotientEquiv_apply_eq_iff {Z X : C}
    (hZ : Indecomposable Z) (hZp : ¬ E.isProjective Z)
    (hX : Indecomposable X) (hXi : ¬ E.isInjective X) :
    E.skeletonEquivOfQuotientEquiv τ (toSkeleton ⟨Z, hZ, hZp⟩) = toSkeleton ⟨X, hX, hXi⟩ ↔
      Nonempty (τ.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) ≅
        E.injectivelyTrivialIdeal.quotientFunctor.obj X) := by
  let q := E.projectivelyTrivialIdeal.quotientFunctor
  have : τ.functor.Additive := Functor.additive_of_preserves_binary_products _
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  let Z' : ObjectProperty.FullSubcategory (fun W ↦ IsLocalRing (End W)) :=
    ⟨q.obj Z, q.isLocalRing_end_obj
      ((E.isZero_projectivelyTrivialIdeal_quotientFunctor_obj_iff Z).not.mpr hZp)⟩
  have hsource : E.projectivelyTrivialSkeletonEquiv (toSkeleton ⟨Z, hZ, hZp⟩) = toSkeleton Z' :=
    (q.skeletonEquivOfIsLocalRingEnd_apply_eq_iff E.isProjective
      E.isZero_projectivelyTrivialIdeal_quotientFunctor_obj_iff hZ hZp Z'.property).mpr ⟨Iso.refl _⟩
  have htranslate : τ.congrLocalEndFullSubcategory.skeletonIsoCat.objEquiv (toSkeleton Z') =
      toSkeleton (τ.congrLocalEndFullSubcategory.functor.obj Z') :=
    Functor.mapSkeleton_obj_toSkeleton _ _
  unfold skeletonEquivOfQuotientEquiv
  simp only [Equiv.trans_apply, Equiv.symm_apply_eq, hsource, htranslate]
  have himage : (τ.congrLocalEndFullSubcategory.functor.obj Z').obj = τ.functor.obj (q.obj Z) :=
    τ.congrLocalEndFullSubcategory_functor_obj_obj Z'
  rw [eq_comm, ← himage]
  exact (E.injectivelyTrivialIdeal.quotientFunctor.skeletonEquivOfIsLocalRingEnd_apply_eq_iff
    E.isInjective E.isZero_injectivelyTrivialIdeal_quotientFunctor_obj_iff hX hXi
    (τ.congrLocalEndFullSubcategory.functor.obj Z').property).trans (Iso.nonempty_iso_symm _ _)

namespace AuslanderReitenDuality

universe w

variable {E} {R : Type*} [CommRing R] [Linear R C] {Q : Type w}
  [AddCommGroup Q] [Module R Q] [Module.Injective R Q] [Small.{w} R]
  (A : E.AuslanderReitenDuality R Q)
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)

/-- The Auslander–Reiten translate on isomorphism classes of indecomposable nonprojectives,
with values in the isomorphism classes of indecomposable noninjectives. -/
noncomputable def translateEquiv :
    Skeleton (ObjectProperty.FullSubcategory fun Z ↦ Indecomposable Z ∧ ¬ E.isProjective Z) ≃
      Skeleton (ObjectProperty.FullSubcategory fun X ↦ Indecomposable X ∧ ¬ E.isInjective X) :=
  E.skeletonEquivOfQuotientEquiv A.functor.asEquivalence

include hQ in
/-- For an Auslander–Reiten duality whose module `Q` gives a dual of length one for each simple
`R`-module (`hQ`), assume `Ext¹_E(Z, Y)` has finite length for every `Y`. The translate sends
the class of `Z` to the class of `X` exactly when there is an almost-split conflation with left
end `X` and right end `Z`. -/
theorem translateEquiv_apply_eq_iff_exists_isAlmostSplit {Z X : C}
    (hZ : Indecomposable Z) (hZp : ¬ E.isProjective Z) (hX : Indecomposable X)
    (hXi : ¬ E.isInjective X) (hfin : ∀ Y, IsFiniteLength R (E.Ext1 Z Y)) :
    A.translateEquiv (toSkeleton ⟨Z, hZ, hZp⟩) =
      toSkeleton ⟨X, hX, hXi⟩ ↔
      ∃ e : E.Extension Z X, e.shortComplex.IsAlmostSplit := by
  rw [translateEquiv, E.skeletonEquivOfQuotientEquiv_apply_eq_iff _ hZ hZp hX hXi]
  refine ⟨?_, fun ⟨e, he⟩ ↦ ⟨(A.isoTranslateOfIsAlmostSplit hQ hfin e he).symm⟩⟩
  rintro ⟨i⟩
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).mp hX
  exact A.exists_isAlmostSplit_of_iso_translateObj hQ hXi hfin i

end AuslanderReitenDuality

end TauCeti.ExactStructure
