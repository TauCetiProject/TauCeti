/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Quotient
public import TauCeti.CategoryTheory.Skeletal
public import Mathlib.LinearAlgebra.FreeModule.Basic
-- Non-public: the dimension–cardinality comparison is used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The quiver of irreducible morphisms of a linear category

Let `C` be a `k`-linear category over a division ring `k`, and let `P` be a property of objects
of `C`, such as finite generation or pointwise finite dimensionality. The vertices of
`TauCeti.IrreducibleMorphismQuiver k P` are the isomorphism classes of indecomposable objects
satisfying `P`. For each pair of vertices, choose representatives and a `k`-basis of their space
`rad / rad²` of irreducible morphisms, `TauCeti.irreducibleMorphismSpace`; the arrows index that
basis.

The number of arrows is independent of the representatives (`card_arrows_of`). Between objects
with local endomorphism rings, in a category with binary biproducts, every basis vector is
represented by an irreducible morphism
(`exists_isIrreducibleMorphism_irreducibleMorphismMk_eq_arrowBasis`), and an arrow exists exactly
when an irreducible morphism exists (`nonempty_arrows_of_iff`). No finiteness of
the morphism spaces is needed for these statements; it is needed only for finiteness of the arrow
sets.

When every indecomposable has endomorphism ring with residue division ring `k`, as over an
algebraically closed field for finite-dimensional objects, this is the underlying quiver of the
Auslander–Reiten quiver. Over other fields the arrows index a basis over the ground field, not
over the residue division rings, so the valuations of the Auslander–Reiten quiver are not
recorded.

The vertex type is a structure wrapping Mathlib's `CategoryTheory.Skeleton` of the full
subcategory, identified with it by `IrreducibleMorphismQuiver.equivSkeleton`, so that the ground
ring `k` determining the arrows is part of the type. The choices of representatives and bases
are noncomputable.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.1.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), VII.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasBinaryBiproducts C]

/-- The isomorphism classes of indecomposable objects satisfying `P`. Its quiver structure, over
a division ring `k` acting linearly on `C`, has as arrows a chosen `k`-basis of `rad / rad²`
between representatives. -/
@[ext]
structure IrreducibleMorphismQuiver (k : Type w) (P : ObjectProperty C) where
  /-- The isomorphism class, as an element of Mathlib's skeleton of the full subcategory. -/
  isoClass : Skeleton (ObjectProperty.FullSubcategory fun X : C ↦ P X ∧ Indecomposable X)

namespace IrreducibleMorphismQuiver

variable {k : Type w} {P : ObjectProperty C}

/-- The vertices are the skeleton of the indecomposable objects satisfying `P`. -/
def equivSkeleton : IrreducibleMorphismQuiver k P ≃
    Skeleton (ObjectProperty.FullSubcategory fun X : C ↦ P X ∧ Indecomposable X) where
  toFun a := a.isoClass
  invFun a := ⟨a⟩

/-- `equivSkeleton` reads off the skeleton class. -/
@[simp]
theorem equivSkeleton_apply (a : IrreducibleMorphismQuiver k P) :
    equivSkeleton a = a.isoClass :=
  (rfl)

/-- The inverse of `equivSkeleton` wraps a skeleton class. -/
@[simp]
theorem isoClass_equivSkeleton_symm
    (a : Skeleton (ObjectProperty.FullSubcategory fun X : C ↦ P X ∧ Indecomposable X)) :
    (equivSkeleton.symm a : IrreducibleMorphismQuiver k P).isoClass = a :=
  (rfl)

/-- The vertex represented by an indecomposable object satisfying `P`. -/
def of (k : Type w) {M : C} (hM : P M) (hI : Indecomposable M) : IrreducibleMorphismQuiver k P :=
  ⟨toSkeleton ⟨M, hM, hI⟩⟩

/-- The vertex of an object corresponds to its skeleton class. -/
@[simp]
theorem isoClass_of {M : C} (hM : P M) (hI : Indecomposable M) :
    (of k hM hI).isoClass =
      toSkeleton (⟨M, hM, hI⟩ : ObjectProperty.FullSubcategory
        fun X : C ↦ P X ∧ Indecomposable X) :=
  (rfl)

/-- A skeleton class becomes the vertex of the same object. -/
@[simp]
theorem equivSkeleton_symm_toSkeleton
    (M : ObjectProperty.FullSubcategory fun X : C ↦ P X ∧ Indecomposable X) :
    equivSkeleton.symm (toSkeleton M) = of k M.property.1 M.property.2 :=
  (rfl)

/-- Two objects determine the same vertex exactly when they are isomorphic. -/
@[simp]
theorem of_eq_of_iff {M N : C} (hM : P M) (hI : Indecomposable M)
    (hN : P N) (hJ : Indecomposable N) :
    of k hM hI = of k hN hJ ↔ Nonempty (M ≅ N) := by
  rw [IrreducibleMorphismQuiver.ext_iff, isoClass_of, isoClass_of]
  exact ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _

/-- A chosen object in the isomorphism class of a vertex. -/
noncomputable def representative (a : IrreducibleMorphismQuiver k P) : C :=
  ((fromSkeleton _).obj a.isoClass).obj

/-- A representative satisfies `P` and is indecomposable. -/
theorem representative_property (a : IrreducibleMorphismQuiver k P) :
    P a.representative ∧ Indecomposable a.representative :=
  ((fromSkeleton _).obj a.isoClass).property

/-- The chosen representative of an object's vertex is isomorphic to that object. -/
noncomputable def representativeIso (k : Type w) {M : C} (hM : P M) (hI : Indecomposable M) :
    (of k hM hI).representative ≅ M :=
  ObjectProperty.ι _ |>.mapIso (fromSkeletonToSkeletonIso
    (⟨M, hM, hI⟩ : ObjectProperty.FullSubcategory fun X : C ↦ P X ∧ Indecomposable X))

/-- Taking the class of a chosen representative recovers the vertex. -/
@[simp]
theorem of_representative (a : IrreducibleMorphismQuiver k P) :
    of k a.representative_property.1 a.representative_property.2 = a :=
  IrreducibleMorphismQuiver.ext (toSkeleton_fromSkeleton_obj a.isoClass)

variable [DivisionRing k] [Linear k C]

/-- Arrows index a ground-ring basis of the irreducible morphism space between
representatives. -/
noncomputable instance : Quiver (IrreducibleMorphismQuiver k P) where
  Hom a b := Module.Free.ChooseBasisIndex k
    (irreducibleMorphismSpace k a.representative b.representative)

/-- The basis of `rad / rad²` indexed by the arrows of the quiver. -/
noncomputable def arrowBasis (a b : IrreducibleMorphismQuiver k P) :
    Module.Basis (a ⟶ b) k (irreducibleMorphismSpace k a.representative b.representative) :=
  Module.Free.chooseBasis k _

instance (a b : IrreducibleMorphismQuiver k P)
    [FiniteDimensional k (irreducibleMorphismSpace k a.representative b.representative)] :
    Finite (a ⟶ b) :=
  Module.Finite.finite_basis (arrowBasis a b)

/-- The arrow count is the dimension of the irreducible morphism space. Both sides are `0` when
that space is infinite-dimensional. -/
theorem card_arrows (a b : IrreducibleMorphismQuiver k P) :
    Nat.card (a ⟶ b) =
      Module.finrank k (irreducibleMorphismSpace k a.representative b.representative) :=
  (Module.finrank_eq_nat_card_basis (arrowBasis a b)).symm

/-- The arrow count can be computed on any representatives of the two classes. -/
theorem card_arrows_of {M N : C} (hM : P M) (hI : Indecomposable M)
    (hN : P N) (hJ : Indecomposable N) :
    Nat.card (of k hM hI ⟶ of k hN hJ) =
      Module.finrank k (irreducibleMorphismSpace k M N) := by
  rw [card_arrows]
  exact (irreducibleMorphismSpaceCongr k (representativeIso k hM hI)
    (representativeIso k hN hJ)).finrank_eq

/-- There is an arrow between two vertices exactly when the irreducible morphism space between
their representatives is nonzero. -/
theorem nonempty_arrows_iff (a b : IrreducibleMorphismQuiver k P) :
    Nonempty (a ⟶ b) ↔
      Nontrivial (irreducibleMorphismSpace k a.representative b.representative) := by
  refine ⟨fun ⟨i⟩ ↦ nontrivial_of_ne _ 0 ((arrowBasis a b).ne_zero i), fun _ ↦ ?_⟩
  exact (arrowBasis a b).index_nonempty

/-- Every arrow's basis vector is represented by an irreducible morphism, when the two
representatives have local endomorphism rings. -/
theorem exists_isIrreducibleMorphism_irreducibleMorphismMk_eq_arrowBasis
    (a b : IrreducibleMorphismQuiver k P)
    [IsLocalRing (End a.representative)] [IsLocalRing (End b.representative)] (i : a ⟶ b) :
    ∃ f : jacobsonRadicalSubmodule k a.representative b.representative,
      IsIrreducibleMorphism (f : a.representative ⟶ b.representative) ∧
        irreducibleMorphismMk k _ _ f = arrowBasis a b i :=
  exists_isIrreducibleMorphism_irreducibleMorphismMk_eq ((arrowBasis a b).ne_zero i)

/-- Between objects with local endomorphism rings, there is an arrow between their classes
exactly when they admit an irreducible morphism. -/
theorem nonempty_arrows_of_iff {M N : C} (hM : P M) (hI : Indecomposable M)
    (hN : P N) (hJ : Indecomposable N) [IsLocalRing (End M)] [IsLocalRing (End N)] :
    Nonempty (of k hM hI ⟶ of k hN hJ) ↔ ∃ f : M ⟶ N, IsIrreducibleMorphism f := by
  rw [nonempty_arrows_iff, ← nontrivial_irreducibleMorphismSpace_iff (k := k)]
  exact (irreducibleMorphismSpaceCongr k (representativeIso k hM hI)
    (representativeIso k hN hJ)).nontrivial_congr

end IrreducibleMorphismQuiver

end TauCeti
