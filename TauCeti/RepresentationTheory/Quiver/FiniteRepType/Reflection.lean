/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.Admissible
public import TauCeti.RepresentationTheory.Quiver.Reflection.FullyFaithful
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.FullyFaithful
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Indecomposable

/-!
# Finite representation type does not depend on reflecting at a sink or a source

Reflecting a quiver at a sink or at a source reverses the arrows meeting that vertex, and the
Bernstein-Gelfand-Ponomarev reflection functors carry its representations along. This file proves
that the change of orientation does not affect finite representation type: for a sink `i` of a
finite quiver `Q`, the reflected quiver `TauCeti.Quiver.Reflect Q i` has finite representation type
exactly when `Q` does (`TauCeti.isFiniteRepType_reflect_iff_of_isSink`), and likewise for a source
(`TauCeti.isFiniteRepType_reflect_iff_of_isSource`). Iterating, the same holds along every
sink-admissible list of vertices (`TauCeti.isFiniteRepType_reflectList_iff`).

The argument is the same at a sink and at a source. A finite-dimensional indecomposable
representation `M` of `Q` either vanishes away from `i`, or the reflection functor at `i` is
injective on its morphisms in the appropriate sense, so that it carries `M` to a finite-dimensional
indecomposable representation of the reflected quiver and reflects isomorphisms among such
representations. The representations of the first kind form a single isomorphism class, by
`TauCeti.nonempty_iso_of_forall_subsingleton`: that of the vertex simple at `i`. So the isomorphism
classes of finite-dimensional indecomposables of `Q` are, up to that one class, embedded in those of
the reflected quiver; and reflecting the reflected quiver at `i` once more returns `Q`
(`TauCeti.Quiver.reflectAt_reflectAt`), which gives the converse.

This is how Gabriel's dichotomy is freed from the choice of orientation: whether a quiver has
finite representation type depends only on its underlying graph as soon as any two orientations
are related by reflections at sinks, which is the case for a tree.

## Main results

* `TauCeti.IsFiniteRepType.of_reflect_of_isSink` and
  `TauCeti.IsFiniteRepType.of_reflect_of_isSource`: if the quiver reflected at a sink,
  respectively a source, has finite representation type, then so does the original one.
* `TauCeti.isFiniteRepType_reflect_iff_of_isSink` and
  `TauCeti.isFiniteRepType_reflect_iff_of_isSource`: **finite representation type is invariant under
  reflection at a sink or at a source.**
* `TauCeti.isFiniteRepType_reflectList_iff`: it is invariant under reflection along every
  sink-admissible list of vertices.

## Implementation notes

The representations of `Q` are taken with vertex spaces in `max v w x`, the universe in which the
reflection functors produce them, and those of the reflected quiver in the same universe. The
iterated statement carries the quiver structure explicitly, as `TauCeti.Quiver.reflectList` does,
because it is the structure that the recursion along the list changes.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x v' w' t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **Finite representation type descends along a map of indecomposables reflecting isomorphisms
away from one isomorphism class.** If a map `F` carries the finite-dimensional indecomposable
representations of `Q` outside an exceptional family `E` to finite-dimensional indecomposables of
`Q'`, reflects isomorphisms among them, and the members of `E` are mutually isomorphic, then finite
representation type of `Q'` implies that of `Q`. -/
private theorem isFiniteRepType_of_map {Q' : Type v'} [Quiver.{w'} Q']
    (E : QuiverRep.{u, v, w, max v w x} k Q → Prop)
    (F : QuiverRep.{u, v, w, max v w x} k Q → QuiverRep.{u, v', w', t} k Q')
    (hF : ∀ M, IsFinDim k Q M → Indecomposable M → ¬ E M →
      IsFinDim k Q' (F M) ∧ Indecomposable (F M))
    (hFiso : ∀ M N, Indecomposable M → Indecomposable N → ¬ E M → ¬ E N →
      Nonempty (F M ≅ F N) → Nonempty (M ≅ N))
    (hE : ∀ M N, Indecomposable M → Indecomposable N → E M → E N → Nonempty (M ≅ N))
    (h : IsFiniteRepType.{u, v', w', t} k Q') : IsFiniteRepType.{u, v, w, max v w x} k Q := by
  classical
  let P : ObjectProperty (QuiverRep.{u, v, w, max v w x} k Q) :=
    fun M ↦ IsFinDim k Q M ∧ Indecomposable M
  let M : Skeleton P.FullSubcategory → QuiverRep.{u, v, w, max v w x} k Q :=
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

variable {i : Q}

/-- **Finite representation type ascends along the reflection at a source.** If `i` is a source of
`Q` and the quiver obtained by reflecting `Q` at `i` has finite representation type, then so does
`Q`: a finite-dimensional indecomposable representation of `Q` is either the vertex simple at `i`,
or its source reflection is a finite-dimensional indecomposable representation of the reflected
quiver, from which it is recovered up to isomorphism. -/
theorem IsFiniteRepType.of_reflect_of_isSource [Finite (Σ b : Q, (i ⟶ b))] (hi : IsSource i)
    (h : IsFiniteRepType.{u, v, w, max v w x} k (Reflect Q i)) :
    IsFiniteRepType.{u, v, w, max v w x} k Q :=
  isFiniteRepType_of_map (fun M ↦ ∀ a : Q, a ≠ i → Subsingleton (M.obj a))
    (fun M ↦ sourceReflectRep M hi)
    (fun M hfin hM hE ↦ ⟨isFinDim_iff.mpr
        (finiteDimensional_sourceReflectRep_obj M hi (isFinDim_iff.mp hfin)),
      indecomposable_sourceReflectRep hi hM
        ((outgoingMap_injective_or_forall_subsingleton hi hM).resolve_right hE)⟩)
    (fun _ _ hM hN hEM hEN ↦ nonempty_iso_of_nonempty_iso_sourceReflectRep hi
      ((outgoingMap_injective_or_forall_subsingleton hi hM).resolve_right hEM)
      ((outgoingMap_injective_or_forall_subsingleton hi hN).resolve_right hEN))
    (fun _ _ hM hN hEM hEN ↦ nonempty_iso_of_forall_subsingleton hi.path_self_eq_nil hM hN hEM hEN)
    h

variable [Finite Q] [∀ a b : Q, Finite (a ⟶ b)]

/-- **Finite representation type ascends along the reflection at a sink.** If `i` is a sink of
`Q` and the quiver obtained by reflecting `Q` at `i` has finite representation type, then so does
`Q`: a finite-dimensional indecomposable representation of `Q` is either the vertex simple at `i`,
or its reflection is a finite-dimensional indecomposable representation of the reflected quiver,
from which it is recovered up to isomorphism. -/
theorem IsFiniteRepType.of_reflect_of_isSink (hi : IsSink i)
    (h : IsFiniteRepType.{u, v, w, max v w x} k (Reflect Q i)) :
    IsFiniteRepType.{u, v, w, max v w x} k Q := by
  have := Fintype.ofFinite Q
  have := fun a b : Q ↦ Fintype.ofFinite (a ⟶ b)
  exact isFiniteRepType_of_map (fun M ↦ ∀ a : Q, a ≠ i → Subsingleton (M.obj a))
    (fun M ↦ reflectRep M hi)
    (fun M hfin hM hE ↦ ⟨isFinDim_iff.mpr
        (finiteDimensional_reflectRep_obj M hi (isFinDim_iff.mp hfin)),
      indecomposable_reflectRep hi hM
        ((incomingSum_surjective_or_forall_subsingleton hi hM).resolve_right hE)⟩)
    (fun _ _ hM hN hEM hEN ↦ nonempty_iso_of_nonempty_iso_reflectRep hi
      ((incomingSum_surjective_or_forall_subsingleton hi hM).resolve_right hEM)
      ((incomingSum_surjective_or_forall_subsingleton hi hN).resolve_right hEN))
    (fun _ _ hM hN hEM hEN ↦ nonempty_iso_of_forall_subsingleton hi.path_self_eq_nil hM hN hEM hEN)
    h

omit [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] in
variable (i) in
/-- Finite representation type passes to the quiver reflected twice at the same vertex, which is
the original quiver. -/
private theorem IsFiniteRepType.reflect_reflect (h : IsFiniteRepType.{u, v, w, max v w x} k Q) :
    @IsFiniteRepType.{u, v, w, max v w x} k (Reflect (Reflect Q i) i) _
      (reflectQuiver (V := Reflect Q i) i) := by
  have h' : @IsFiniteRepType.{u, v, w, max v w x} k Q _
      (reflectAt (reflectAt inferInstance i) i) := by
    rwa [reflectAt_reflectAt]
  -- `Reflect (Reflect Q i) i` is `Q` carrying `reflectAt (reflectAt _ i) i`, by unfolding the type
  -- synonym `Reflect` and its quiver instance `reflectQuiver`
  exact h'

/-- **Finite representation type is invariant under reflection at a sink.** The quiver obtained by
reversing the arrows into a sink `i` of a finite quiver `Q` has finite representation type exactly
when `Q` does. -/
theorem isFiniteRepType_reflect_iff_of_isSink (hi : IsSink i) :
    IsFiniteRepType.{u, v, w, max v w x} k (Reflect Q i) ↔
      IsFiniteRepType.{u, v, w, max v w x} k Q := by
  have := Fintype.ofFinite Q
  have := fun a b : Q ↦ Fintype.ofFinite (a ⟶ b)
  -- the arrows of the reflected quiver are finite by `TauCeti.Quiver.instFintypeHomReflect`, which
  -- instance search does not find through the quiver instance of the type synonym `Reflect Q i`
  have : Finite (Σ b : Reflect Q i, @Quiver.Hom (Reflect Q i) _ i b) := @Finite.of_fintype _
    (@Sigma.instFintype _ _ (fun b ↦ instFintypeHomReflect i i b) inferInstance)
  exact ⟨IsFiniteRepType.of_reflect_of_isSink hi, fun h ↦
    IsFiniteRepType.of_reflect_of_isSource hi.isSource_reflect (h.reflect_reflect i)⟩

/-- **Finite representation type is invariant under reflection at a source.** The quiver obtained
by reversing the arrows out of a source `i` of a finite quiver `Q` has finite representation type
exactly when `Q` does. -/
theorem isFiniteRepType_reflect_iff_of_isSource (hi : IsSource i) :
    IsFiniteRepType.{u, v, w, max v w x} k (Reflect Q i) ↔
      IsFiniteRepType.{u, v, w, max v w x} k Q := by
  have := Fintype.ofFinite Q
  have := fun a b : Q ↦ Fintype.ofFinite (a ⟶ b)
  -- as in `TauCeti.isFiniteRepType_reflect_iff_of_isSink`, the finiteness of the reflected quiver
  -- is supplied by hand
  have : Finite (Reflect Q i) := inferInstanceAs (Finite Q)
  have : ∀ a b : Reflect Q i, Finite (a ⟶ b) := fun a b ↦
    @Finite.of_fintype _ (instFintypeHomReflect i a b)
  have : Finite (Σ b : Q, (i ⟶ b)) := inferInstance
  exact ⟨IsFiniteRepType.of_reflect_of_isSource hi, fun h ↦
    IsFiniteRepType.of_reflect_of_isSink hi.isSink_reflect (h.reflect_reflect i)⟩

/-- **Finite representation type is invariant under reflection along a sink-admissible list.**
Reflecting a finite quiver successively at the entries of a list, each a sink of the quiver its
predecessors produce, does not change whether it has finite representation type. -/
theorem isFiniteRepType_reflectList_iff {V : Type v} [Finite V] :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (_hq : ∀ a b : V, Finite (@_root_.Quiver.Hom V q a b)),
      Quiver.IsSinkAdmissible q l →
      (@IsFiniteRepType.{u, v, w, max v w x} k V _ (Quiver.reflectList q l) ↔
        @IsFiniteRepType.{u, v, w, max v w x} k V _ q)
  | [], _, _, _ => Iff.rfl
  | i :: l, q, hq, hl => by
      let := q
      let := hq
      have := Fintype.ofFinite V
      have := fun a b : V ↦ Fintype.ofFinite (a ⟶ b)
      -- `reflectList q (i :: l)` is `reflectList (reflectAt q i) l`, and `reflectAt q i` is the
      -- quiver of `Reflect V i`, both by definition
      exact (isFiniteRepType_reflectList_iff l (reflectAt q i)
        (fun a b ↦ @Finite.of_fintype _ (instFintypeReflectHom i a b))
        (Quiver.isSinkAdmissible_cons.mp hl).2).trans
          (isFiniteRepType_reflect_iff_of_isSink (Quiver.isSinkAdmissible_cons.mp hl).1)

end TauCeti
