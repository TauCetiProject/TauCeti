/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.ExtendByZero

/-!
# Finite representation type passes to subquivers

If a quiver `Q'` embeds in a quiver `Q` (`TauCeti.QuiverEmbedding`) and `Q` has finite
representation type, then so does `Q'` (`TauCeti.IsFiniteRepType.of_quiverEmbedding`): extension
by zero along the embedding carries the finite-dimensional indecomposable representations of `Q'`
to finite-dimensional indecomposable representations of `Q`, and it reflects isomorphism, so it
embeds the isomorphism classes of the one into those of the other.

Read contrapositively, a quiver containing a subquiver of infinite representation type has
infinite representation type itself. This is the reduction by which the non-Dynkin half of
Gabriel's theorem is proved: a finite connected quiver whose underlying graph is not a Dynkin
diagram contains a subquiver whose graph is an extended Dynkin diagram, and each has infinitely
many indecomposables. Applications to loops and parallel arrows are in
`TauCeti.RepresentationTheory.Quiver.FiniteRepType.Obstructions`.

## Main results

* `TauCeti.IsFiniteRepType.of_quiverEmbedding`: finite representation type passes to subquivers.
* `TauCeti.isFiniteRepType_iff_of_homEquiv`: finite representation type is invariant under
  isomorphism of quivers.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w v' w' t

variable {k : Type u} [Field k] {Q' : Type v'} [Quiver.{w'} Q'] {Q : Type v} [Quiver.{w} Q]

/-- **Finite representation type passes to subquivers.** If `Q'` embeds in a quiver `Q` of finite
representation type then `Q'` has finite representation type: extension by zero carries the
finite-dimensional indecomposables of `Q'` to finite-dimensional indecomposables of `Q`, and
non-isomorphic ones to non-isomorphic ones.

The representations of `Q` are taken with vertex spaces in the universe `max v' t`, where those
of `Q'` live in `t` and the vertices of `Q'` in `v'`; the extension by zero lands there. -/
theorem IsFiniteRepType.of_quiverEmbedding (h : IsFiniteRepType.{u, v, w, max v' t} k Q)
    (φ : QuiverEmbedding Q' Q) : IsFiniteRepType.{u, v', w', t} k Q' := by
  let P : ObjectProperty (QuiverRep.{u, v', w', t} k Q') :=
    fun M ↦ IsFinDim k Q' M ∧ Indecomposable M
  let M : Skeleton P.FullSubcategory → QuiverRep.{u, v', w', t} k Q' :=
    fun a ↦ ((fromSkeleton _).obj a).obj
  have hM (a : Skeleton P.FullSubcategory) : P (M a) := ((fromSkeleton _).obj a).property
  refine isFiniteRepType_iff.mpr (h.finite_of_pairwise_nonisomorphic
    (M := fun a ↦ φ.extendByZeroRep (M a)) (fun a ↦ φ.isFinDim_extendByZeroRep (hM a).1)
    (fun a ↦ φ.indecomposable_extendByZeroRep (hM a).2) fun a b hab hiso ↦ hab ?_)
  rw [← toSkeleton_fromSkeleton_obj a, ← toSkeleton_fromSkeleton_obj b]
  exact (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso P (hM a) (hM b)).mpr
    ((φ.nonempty_extendByZeroRep_iso_iff _ _).mp hiso)

/-- The quiver embedding which is the identity on vertices, given a correspondence between the
arrows of two quiver structures on the same vertices. -/
private def quiverEmbeddingOfHomEquiv {V : Type v} {q q' : Quiver.{w} V}
    (e : ∀ a b : V, @Quiver.Hom V q a b ≃ @Quiver.Hom V q' a b) :
    @QuiverEmbedding V q V q' :=
  @QuiverEmbedding.mk V q V q' (@Prefunctor.mk V q V q' id fun {a b} ↦ e a b)
    Function.injective_id fun {a b} ↦ (e a b).injective

/-- **Finite representation type is invariant under isomorphism of quivers.** Two quiver
structures on the same vertices whose arrows between any two vertices correspond have finite
representation type together. -/
theorem isFiniteRepType_iff_of_homEquiv {V : Type v} {q q' : Quiver.{w} V}
    (e : ∀ a b : V, @Quiver.Hom V q a b ≃ @Quiver.Hom V q' a b) :
    @IsFiniteRepType.{u, v, w, max v t} k V _ q ↔ @IsFiniteRepType.{u, v, w, max v t} k V _ q' :=
  ⟨fun h ↦ @IsFiniteRepType.of_quiverEmbedding _ _ _ q' _ q h
      (quiverEmbeddingOfHomEquiv fun a b ↦ (e a b).symm),
    fun h ↦ @IsFiniteRepType.of_quiverEmbedding _ _ _ q _ q' h (quiverEmbeddingOfHomEquiv e)⟩

end TauCeti
