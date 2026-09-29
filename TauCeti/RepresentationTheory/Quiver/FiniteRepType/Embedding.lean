/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType
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
Gabriel's theorem is proved: a connected quiver whose underlying graph is not a Dynkin diagram
contains a subquiver whose graph is an extended Dynkin diagram, and each of those has infinitely
many indecomposables. The two smallest extended Dynkin diagrams are the loop `Ã₀` and the double
edge `Ã₁`, and for them the infinite families are already known: the nilpotent Jordan blocks of the
loop quiver (`TauCeti.not_isFiniteRepType_oneLoop`) and of the Kronecker quiver `• ⇉ •`
(`TauCeti.not_isFiniteRepType_kronecker`). Transported along the reduction, they say that a quiver
of finite representation type has no loops (`TauCeti.IsFiniteRepType.isEmpty_hom_self`) and at
most one arrow from any vertex to any other (`TauCeti.IsFiniteRepType.subsingleton_hom`).

## Main results

* `TauCeti.IsFiniteRepType.of_quiverEmbedding`: finite representation type passes to subquivers.
* `TauCeti.IsFiniteRepType.isEmpty_hom_self`: a quiver of finite representation type has no loops.
* `TauCeti.IsFiniteRepType.subsingleton_hom`: a quiver of finite representation type has no two
  parallel arrows.

## Implementation notes

The consequences are stated for representations with vertex spaces in the universe of the base
field, the universe in which the loop-quiver and Kronecker families are built.

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

/-- The embedding of the loop quiver onto a loop `α` of `Q`. -/
private def oneLoopEmbedding {i : Q} (α : i ⟶ i) : QuiverEmbedding Quiver.OneLoop Q where
  obj _ := i
  map _ := α
  obj_injective a b _ := Subsingleton.elim a b
  map_injective _ := Subsingleton.elim _ _

/-- The embedding of the Kronecker quiver `• ⇉ •` onto two distinct parallel arrows `α`, `β` of `Q`
between distinct vertices. -/
private def kroneckerEmbedding {i j : Q} (hij : i ≠ j) {α β : i ⟶ j} (hαβ : α ≠ β) :
    QuiverEmbedding (Quiver.Kronecker Bool) Q where
  obj
    | .src => i
    | .tgt => j
  map {a b} e := match a, b, e with
    | .src, .tgt, e => bif e then α else β
    | .src, .src, e => isEmptyElim e
    | .tgt, .src, e => isEmptyElim e
    | .tgt, .tgt, e => isEmptyElim e
  obj_injective a b hab := by
    cases a <;> cases b
    · rfl
    · exact absurd hab hij
    · exact absurd hab.symm hij
    · rfl
  map_injective {a b} e₁ e₂ he := by
    match a, b, e₁, e₂ with
    | .src, .tgt, e₁, e₂ =>
      cases e₁ <;> cases e₂ <;> first | rfl | exact absurd he hαβ | exact absurd he.symm hαβ
    | .src, .src, e₁, _ => exact isEmptyElim e₁
    | .tgt, .src, e₁, _ => exact isEmptyElim e₁
    | .tgt, .tgt, e₁, _ => exact isEmptyElim e₁

/-- **A quiver of finite representation type has no loops**: a loop embeds the loop quiver, whose
nilpotent Jordan blocks are infinitely many pairwise non-isomorphic indecomposables. -/
theorem IsFiniteRepType.isEmpty_hom_self (h : IsFiniteRepType.{u, v, w, u} k Q) (i : Q) :
    IsEmpty (i ⟶ i) :=
  ⟨fun α ↦ not_isFiniteRepType_oneLoop k (h.of_quiverEmbedding (oneLoopEmbedding.{v, w, 0} α))⟩

/-- **A quiver of finite representation type has at most one arrow from any vertex to any other**:
two parallel arrows between distinct vertices embed the Kronecker quiver `• ⇉ •`, and two loops
at one vertex are excluded already by `TauCeti.IsFiniteRepType.isEmpty_hom_self`. -/
theorem IsFiniteRepType.subsingleton_hom (h : IsFiniteRepType.{u, v, w, u} k Q) (i j : Q) :
    Subsingleton (i ⟶ j) := by
  refine ⟨fun α β ↦ by_contra fun hαβ ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    exact (h.isEmpty_hom_self i).false α
  · exact not_isFiniteRepType_kronecker k Bool (h.of_quiverEmbedding (kroneckerEmbedding hij hαβ))

end TauCeti
