/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.IrreducibleMorphism
public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential

/-!
# The quiver of irreducible morphisms

The vertices of `irreducibleMorphismQuiver k Q` are isomorphism classes of indecomposable
representations of `Q` that are pointwise finite-dimensional. For each pair of vertices, choose
representatives and a basis of their space `rad / rad²` of irreducible morphisms. The arrows index
that basis. Their number is independent of the representatives, and every basis vector is
represented by an irreducible morphism. An arrow exists precisely when an irreducible morphism
exists.

For a quiver with finitely many vertices, these spaces are finite-dimensional even if the quiver
has infinitely many arrows or oriented cycles. Finite representation type is exactly finiteness
of the new vertex type, and then the total arrow type is finite too.

Over an algebraically closed field this is the underlying Auslander–Reiten quiver. Over other
fields the construction still indexes a basis over the ground field; it does not encode the
valuations over residue division rings. This file constructs the underlying quiver only, without
its partial translation. The choices of representatives and bases are noncomputable.

The equivalence `irreducibleMorphismQuiver.equivSkeleton` identifies the vertices with Mathlib's
`CategoryTheory.Skeleton`, and the arrows use its
`Module.Free.chooseBasis` on `TauCeti.irreducibleMorphismSpace`. The Hom differential identifies
representation morphisms with a subspace of the finite product of vertex-map spaces.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

/-- Isomorphism classes of pointwise finite-dimensional indecomposable representations. The
quiver structure uses a chosen basis of `rad / rad²` between representatives. -/
def irreducibleMorphismQuiver : Type (max u v w (t + 1)) :=
  Skeleton (ObjectProperty.FullSubcategory
    (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M))

namespace irreducibleMorphismQuiver

variable {k Q}

/-- The vertex type as Mathlib's skeleton of finite-dimensional indecomposables.

This equivalence transports classifications of indecomposables to the vertex type. In files using
`module` with a regular `public import`, the body of `irreducibleMorphismQuiver` is not exposed,
so this identification is available through the equivalence and its lemmas. -/
def equivSkeleton : irreducibleMorphismQuiver.{u, v, w, t} k Q ≃
    Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)) :=
  Equiv.refl _

/-- The vertex represented by a finite-dimensional indecomposable representation. -/
def of {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M) (hI : Indecomposable M) :
    irreducibleMorphismQuiver.{u, v, w, t} k Q :=
  toSkeleton ⟨M, hM, hI⟩

/-- A representation's vertex corresponds to its skeleton class, without unfolding `of`
in importing modules. -/
@[simp]
theorem equivSkeleton_of {M : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M) :
    equivSkeleton (of hM hI) =
      toSkeleton (⟨M, hM, hI⟩ : ObjectProperty.FullSubcategory
        (fun N : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q N ∧ Indecomposable N)) :=
  (rfl)

/-- A skeleton class becomes the vertex of the same representation, without unfolding `of`
in importing modules. -/
@[simp]
theorem equivSkeleton_symm_toSkeleton
    (M : ObjectProperty.FullSubcategory
      (fun N : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q N ∧ Indecomposable N)) :
    equivSkeleton.symm (toSkeleton M) = of M.property.1 M.property.2 :=
  (rfl)

/-- Two representations determine the same vertex exactly when they are isomorphic. -/
@[simp]
theorem of_eq_of_iff {M N : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M)
    (hN : IsFinDim k Q N) (hJ : Indecomposable N) :
    of hM hI = of hN hJ ↔ Nonempty (M ≅ N) :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _

/-- A chosen representation in the isomorphism class of a vertex. -/
noncomputable def representative (a : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    QuiverRep.{u, v, w, t} k Q :=
  ((fromSkeleton _).obj a).obj

/-- A representative is pointwise finite-dimensional and indecomposable. -/
theorem representative_property (a : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    IsFinDim k Q a.representative ∧ Indecomposable a.representative :=
  ((fromSkeleton _).obj a).property

/-- The chosen representative of a representation's vertex is isomorphic to that representation. -/
noncomputable def representativeIso {M : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M) : (of hM hI).representative ≅ M := by
  let P : ObjectProperty (QuiverRep.{u, v, w, t} k Q) :=
    fun N ↦ IsFinDim k Q N ∧ Indecomposable N
  exact P.ι.mapIso (fromSkeletonToSkeletonIso (⟨M, hM, hI⟩ : P.FullSubcategory))

/-- Taking the class of a chosen representative recovers the vertex. -/
@[simp]
theorem of_representative (a : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    of a.representative_property.1 a.representative_property.2 = a :=
  toSkeleton_fromSkeleton_obj a

/-- Arrows index a ground-field basis of the irreducible morphism space between representatives. -/
noncomputable instance : Quiver (irreducibleMorphismQuiver.{u, v, w, t} k Q) where
  Hom a b := Module.Free.ChooseBasisIndex k
    (irreducibleMorphismSpace k a.representative b.representative)

/-- The basis of `rad / rad²` indexed by the arrows of the quiver. -/
noncomputable def arrowBasis (a b : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    Module.Basis (a ⟶ b) k
      (irreducibleMorphismSpace k a.representative b.representative) :=
  Module.Free.chooseBasis k _

variable [Finite Q]

instance (a b : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    FiniteDimensional k (a.representative ⟶ b.representative) :=
  QuiverRep.finiteDimensional_hom a.representative_property.1 b.representative_property.1

instance (a b : irreducibleMorphismQuiver.{u, v, w, t} k Q) : Finite (a ⟶ b) := by
  dsimp only [Quiver.Hom, instQuiver]
  infer_instance

/-- The arrow count is the dimension of the irreducible morphism space. -/
@[simp]
theorem card_arrows (a b : irreducibleMorphismQuiver.{u, v, w, t} k Q) :
    Nat.card (a ⟶ b) = Module.finrank k
      (irreducibleMorphismSpace k a.representative b.representative) := by
  dsimp only [Quiver.Hom, instQuiver]
  rw [Nat.card_eq_fintype_card, ← Module.finrank_eq_card_chooseBasisIndex]

/-- The arrow count can be computed on any representatives of the two classes. -/
theorem card_arrows_of {M N : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M)
    (hN : IsFinDim k Q N) (hJ : Indecomposable N) :
    Nat.card (of hM hI ⟶ of hN hJ) =
      Module.finrank k (irreducibleMorphismSpace k M N) := by
  rw [card_arrows]
  exact (irreducibleMorphismSpaceCongr k (representativeIso hM hI)
    (representativeIso hN hJ)).finrank_eq

/-- Every arrow's basis vector is represented by an irreducible morphism. -/
theorem exists_irreducibleMorphism_arrowBasis
    (a b : irreducibleMorphismQuiver.{u, v, w, t} k Q) (i : a ⟶ b) :
    ∃ f : jacobsonRadicalSubmodule k a.representative b.representative,
      IsIrreducibleMorphism (f : a.representative ⟶ b.representative) ∧
        irreducibleMorphismMk k _ _ f = arrowBasis a b i := by
  have : IsLocalRing (End a.representative) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end a.representative_property.1).mp
      a.representative_property.2
  have : IsLocalRing (End b.representative) :=
    (QuiverRep.indecomposable_iff_isLocalRing_end b.representative_property.1).mp
      b.representative_property.2
  exact exists_isIrreducibleMorphism_irreducibleMorphismMk_eq ((arrowBasis a b).ne_zero i)

/-- There is an arrow between two classes exactly when their representatives admit an
irreducible morphism. -/
theorem nonempty_arrows_of_iff {M N : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hI : Indecomposable M)
    (hN : IsFinDim k Q N) (hJ : Indecomposable N) :
    Nonempty (of hM hI ⟶ of hN hJ) ↔ ∃ f : M ⟶ N, IsIrreducibleMorphism f := by
  have : FiniteDimensional k (M ⟶ N) := QuiverRep.finiteDimensional_hom hM hN
  have hcard : Nonempty (of hM hI ⟶ of hN hJ) ↔
      0 < Nat.card (of hM hI ⟶ of hN hJ) := by
    simp only [Nat.card_pos_iff, and_iff_left (inferInstance : Finite _)]
  rw [hcard, card_arrows_of, Module.finrank_pos_iff_of_free]
  exact QuiverRep.nontrivial_irreducibleMorphismSpace_iff hM hN hI hJ

end irreducibleMorphismQuiver

/-- Finite representation type is precisely finiteness of the vertices of the irreducible
morphism quiver. -/
@[simp]
theorem finite_irreducibleMorphismQuiver_iff :
    Finite (irreducibleMorphismQuiver.{u, v, w, t} k Q) ↔ IsFiniteRepType.{u, v, w, t} k Q :=
  (isFiniteRepType_iff (k := k) (Q := Q)).symm

/-- In finite representation type, the irreducible morphism quiver has finitely many arrows
in total. -/
theorem IsFiniteRepType.finite_irreducibleMorphismQuiver_arrows [Finite Q]
    (h : IsFiniteRepType.{u, v, w, t} k Q) :
    Finite (Σ a b : irreducibleMorphismQuiver.{u, v, w, t} k Q, a ⟶ b) := by
  have : Finite (irreducibleMorphismQuiver.{u, v, w, t} k Q) :=
    (finite_irreducibleMorphismQuiver_iff k Q).mpr h
  infer_instance

end TauCeti
