/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# Finite representation type

A quiver has **finite representation type** when it has only finitely many isomorphism classes of
finite-dimensional indecomposable representations. This file defines `TauCeti.IsFiniteRepType`, the
finiteness of the skeleton of the full subcategory of finite-dimensional indecomposables, whose
objects are the representations that are pointwise finite-dimensional
(`TauCeti.IsFinDim`, from `TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional`)
and indecomposable; and it proves the criterion by which the property is refuted: an infinite
family of pairwise non-isomorphic finite-dimensional indecomposables.

Both directions of that criterion are proved, because both are used. The refuting direction is what
exhibits a quiver of infinite representation type; the affirming direction is what a quiver of
finite representation type is *for*, namely that any family of pairwise non-isomorphic
finite-dimensional indecomposables is finite, so that "the indecomposables" may be counted.

## Main definitions

* `TauCeti.IsFiniteRepType`: the quiver has finitely many finite-dimensional indecomposables up to
  isomorphism.

## Main results

* `TauCeti.not_isFiniteRepType_of_infinite`: an infinite family of pairwise non-isomorphic
  finite-dimensional indecomposables refutes finite representation type.
* `TauCeti.IsFiniteRepType.finite_of_pairwise_nonisomorphic`: conversely, under finite
  representation type every such family is indexed by a finite type.
* `TauCeti.isFiniteRepType_of_map`: finite representation type transfers along a map of
  indecomposables reflecting isomorphisms outside one exceptional isomorphism class.
* `TauCeti.IsFiniteRepType.of_ulift`: finite representation type for vertex spaces in a universe
  implies it for vertex spaces in any smaller one.

## Implementation notes

The definition does not carry `[Finite Q]`. The roadmap pins `IsFiniteRepType` with that instance
binder, to record the intended setting, but nothing in the statement consumes it and an unused
instance argument is a linter error here; a consumer that needs a finite vertex set -- Gabriel's
dichotomy does -- states it where it is used. Dropping it costs nothing: the definition reads the
same, and it stays meaningful over an infinite quiver.

The skeleton is Mathlib's `CategoryTheory.Skeleton`, so `IsFiniteRepType` is a finiteness statement
about an honest type of isomorphism classes rather than about a hand-rolled quotient. The bridge in
both proofs below is `CategoryTheory.ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso`,
that two objects of a full subcategory have the same class in its skeleton exactly when they are
isomorphic in the ambient category.

The two results are stated for a family `M : α → QuiverRep k Q` rather than for a set of
representations: a family is what the worked examples produce -- the loop quiver's family is
indexed by the base field -- and injectivity up to isomorphism is expressed directly on the index
type.

## References

This implements the "finite representation type" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, on which its Gabriel
dichotomy and the loop-quiver and Kronecker worked examples are stated.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w t v' w' t'

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

variable (k Q) in
/-- **Finite representation type**: the quiver `Q` has only finitely many isomorphism classes of
finite-dimensional indecomposable representations over `k`. It is stated as the finiteness of the
skeleton of the full subcategory they span, so that "isomorphism class" is Mathlib's. -/
def IsFiniteRepType : Prop :=
  Finite (Skeleton (ObjectProperty.FullSubcategory
    (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)))

/-- **The elimination and introduction rule for `TauCeti.IsFiniteRepType`**: it is the finiteness
of the skeleton of the full subcategory of finite-dimensional indecomposable representations. -/
@[simp]
theorem isFiniteRepType_iff :
    IsFiniteRepType.{u, v, w, t} k Q ↔ Finite (Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M))) :=
  Iff.rfl

section Criterion

variable {α : Type*} {M : α → QuiverRep.{u, v, w, t} k Q}

/-- The class in the skeleton of a finite-dimensional indecomposable representation. -/
private def toIndecSkeleton {N : QuiverRep.{u, v, w, t} k Q} (hN : IsFinDim k Q N)
    (hN' : Indecomposable N) :
    Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)) :=
  toSkeleton ⟨N, hN, hN'⟩

/-- Non-isomorphic representations have distinct classes in the skeleton: the inclusion of the full
subcategory of finite-dimensional indecomposables is full and faithful, so an isomorphism there is
an isomorphism of representations. -/
private theorem toIndecSkeleton_injective (hfin : ∀ a, IsFinDim k Q (M a))
    (hind : ∀ a, Indecomposable (M a))
    (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) :
    Function.Injective fun a ↦ toIndecSkeleton (hfin a) (hind a) := by
  intro a b hab
  by_contra hne'
  exact hne a b hne'
    ((ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _).mp hab)

/-- **An infinite family of pairwise non-isomorphic finite-dimensional indecomposables refutes
finite representation type.** This is how a quiver is shown to have infinite representation type:
exhibit such a family. -/
theorem not_isFiniteRepType_of_infinite [Infinite α] (hfin : ∀ a, IsFinDim k Q (M a))
    (hind : ∀ a, Indecomposable (M a)) (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) :
    ¬ IsFiniteRepType.{u, v, w, t} k Q :=
  fun h ↦ (@Finite.of_injective _ _ h _ (toIndecSkeleton_injective hfin hind hne)).false

/-- **Under finite representation type a family of pairwise non-isomorphic finite-dimensional
indecomposables is finite.** This is the counting form of the property: only finitely many
indecomposables are available to be listed. -/
theorem IsFiniteRepType.finite_of_pairwise_nonisomorphic (h : IsFiniteRepType.{u, v, w, t} k Q)
    (hfin : ∀ a, IsFinDim k Q (M a)) (hind : ∀ a, Indecomposable (M a))
    (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) : Finite α :=
  @Finite.of_injective _ _ h _ (toIndecSkeleton_injective hfin hind hne)

end Criterion

/-- **Finite representation type descends along a map of indecomposables reflecting isomorphisms
away from one isomorphism class.** If a map `F` carries the finite-dimensional indecomposable
representations of `Q` outside an exceptional family `E` to finite-dimensional indecomposables of
`Q'`, reflects isomorphisms among them, and the members of `E` are mutually isomorphic, then finite
representation type of `Q'` implies that of `Q`. -/
theorem isFiniteRepType_of_map {Q' : Type v'} [Quiver.{w'} Q']
    (E : QuiverRep.{u, v, w, t} k Q → Prop)
    (F : QuiverRep.{u, v, w, t} k Q → QuiverRep.{u, v', w', t'} k Q')
    (hF : ∀ M, IsFinDim k Q M → Indecomposable M → ¬ E M →
      IsFinDim k Q' (F M) ∧ Indecomposable (F M))
    (hFiso : ∀ M N, Indecomposable M → Indecomposable N → ¬ E M → ¬ E N →
      Nonempty (F M ≅ F N) → Nonempty (M ≅ N))
    (hE : ∀ M N, Indecomposable M → Indecomposable N → E M → E N → Nonempty (M ≅ N))
    (h : IsFiniteRepType.{u, v', w', t'} k Q') : IsFiniteRepType.{u, v, w, t} k Q := by
  classical
  let P : ObjectProperty (QuiverRep.{u, v, w, t} k Q) :=
    fun M ↦ IsFinDim k Q M ∧ Indecomposable M
  let M : Skeleton P.FullSubcategory → QuiverRep.{u, v, w, t} k Q :=
    fun a ↦ ((fromSkeleton _).obj a).obj
  have hM (a : Skeleton P.FullSubcategory) : P (M a) := ((fromSkeleton _).obj a).property
  have heq (a b : Skeleton P.FullSubcategory) (hab : Nonempty (M a ≅ M b)) : a = b := by
    rw [← toSkeleton_fromSkeleton_obj a, ← toSkeleton_fromSkeleton_obj b]
    exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso P (hM a) (hM b)).mpr hab
  -- the classes outside `E` embed in the classes of `Q'`
  have hreg : Finite {a // ¬ E (M a)} := h.finite_of_pairwise_nonisomorphic
    (M := fun a ↦ F (M a.1)) (fun a ↦ (hF _ (hM a).1 (hM a).2 a.2).1)
    (fun a ↦ (hF _ (hM a).1 (hM a).2 a.2).2) fun a b hab hiso ↦
      hab (Subtype.ext (heq _ _ (hFiso _ _ (hM a).2 (hM b).2 a.2 b.2 hiso)))
  -- the classes in `E` are a single one
  have hexc : Subsingleton {a // E (M a)} :=
    ⟨fun a b ↦ Subtype.ext (heq _ _ (hE _ _ (hM a).2 (hM b).2 a.2 b.2))⟩
  exact isFiniteRepType_iff.mpr (Finite.of_equiv _ (Equiv.sumCompl fun a ↦ E (M a)))

/-- **Finite representation type descends to a smaller universe of vertex spaces.** Lifting the
vertex spaces of a representation to a larger universe, through `ModuleCat.uliftFunctor`, is fully
faithful, so it carries the finite-dimensional indecomposables to finite-dimensional indecomposables
and non-isomorphic ones to non-isomorphic ones. -/
theorem IsFiniteRepType.of_ulift (h : IsFiniteRepType.{u, v, w, max t t'} k Q) :
    IsFiniteRepType.{u, v, w, t} k Q := by
  let L := (Functor.whiskeringRight (Paths Q) _ _).obj (ModuleCat.uliftFunctor.{t', t} k)
  have hL : L.FullyFaithful := (ModuleCat.fullyFaithfulUliftFunctor k).whiskeringRight (Paths Q)
  refine isFiniteRepType_of_map (fun _ ↦ False) L.obj (fun M hM hM' _ ↦ ⟨?_,
    L.indecomposable_obj_of_map_bijective hM' (hL.map_bijective _ _)⟩)
    (fun _ _ _ _ _ _ ⟨e⟩ ↦ ⟨hL.preimageIso e⟩) (fun _ _ _ _ h ↦ h.elim) h
  refine isFinDim_iff.mpr fun x ↦ ?_
  have := isFinDim_iff.mp hM x
  rw [Functor.whiskeringRight_obj_obj, Functor.comp_obj, ModuleCat.uliftFunctor_obj]
  exact ULift.moduleEquiv.symm.finiteDimensional

end TauCeti
