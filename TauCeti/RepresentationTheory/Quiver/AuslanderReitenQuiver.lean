/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.CategoryTheory.Preadditive.Radical.Quotient
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
-- Non-public: the arrow count uses the basis-cardinality formula only inside proofs, the
-- statements mentioning `Module.finrank` alone.
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The Auslander--Reiten quiver of a quiver

The **Auslander--Reiten quiver** of a quiver `Q` over a field `k` has as vertices the isomorphism
classes of finite-dimensional indecomposable representations of `Q`, with the arrows `[M] → [N]`
recording the irreducible morphisms `M ⟶ N`, that is the space `rad(M, N) / rad²(M, N)`. This file
builds it with the arrows indexed by a `k`-basis of that space: the convention in which the arrow
count is `dim_k rad(M, N) / rad²(M, N)`, which is the classical arrow multiplicity exactly when the
residue division rings of the two endomorphism algebras are `k` -- as over an algebraically closed
`k` with finite-dimensional endomorphism algebras -- and exceeds it in general. Over a general field
no statement below claims a multiplicity in that finer sense; see the implementation notes.

Both halves of the construction are supplied by existing files and are assembled here. The vertex
type is Mathlib's `CategoryTheory.Skeleton` of the full subcategory of finite-dimensional
indecomposables -- the very type whose finiteness is `TauCeti.IsFiniteRepType`, so that a quiver
has finite representation type exactly when its Auslander--Reiten quiver has finitely many
vertices (`TauCeti.isFiniteRepType_iff_finite_arQuiver`). The arrow type is the index set of
`Module.Basis.ofVectorSpace` on `TauCeti.irreducibleMorphismSpace k M N`, the quotient
`rad(M, N) / rad²(M, N)` of `TauCeti/CategoryTheory/Preadditive/Radical/Quotient.lean`. That
quotient transports along isomorphisms of either argument
(`TauCeti.irreducibleMorphismSpaceCongr`), which is what makes an arrow set attached to
*isomorphism classes* well defined: the arrows are read off at the chosen representative
`TauCeti.arRep`, and `TauCeti.arArrowBasisOfIso` transports the answer to any other
representative.

Three facts make the quiver mean what its name says. **Detection**: there is an arrow `[M] → [N]`
exactly when there is an irreducible morphism `M ⟶ N`, and each individual arrow is the class of
such a morphism. **Local finiteness**: over a finite quiver the arrow set between two vertices is
finite, with cardinality `dim_k rad(M, N) / rad²(M, N)`, bounded by `dim_k (M ⟶ N)`. And the
**vertex count**: finiteness of the vertex set is exactly finite representation type.

## Main definitions

* `TauCeti.arQuiver`: the vertex type, the isomorphism classes of finite-dimensional
  indecomposable representations, with its `Quiver` instance.
* `TauCeti.arRep`: the representation representing a vertex, with `TauCeti.isFinDim_arRep` and
  `TauCeti.indecomposable_arRep`.
* `TauCeti.arVertex`: the vertex of a finite-dimensional indecomposable representation, with
  `TauCeti.arRepIso` identifying the representative of that vertex with the representation itself.
* `TauCeti.arArrowBasis` and `TauCeti.arArrowBasisOfIso`: **the arrows `X → Y` index a basis** of
  the space of irreducible morphisms, read at the chosen representatives and at arbitrary ones.

## Main statements

* `TauCeti.arVertex_eq_arVertex_iff`: two representations give the same vertex exactly when they
  are isomorphic, so the vertices are the isomorphism classes.
* `TauCeti.nonempty_hom_arQuiver_iff` and `TauCeti.nonempty_hom_arVertex_iff`: **there is an arrow
  exactly when there is an irreducible morphism**, stated at the chosen representatives and at a
  given pair of representations.
* `TauCeti.exists_isIrreducibleMorphism_arArrowBasis`: **every arrow is the class of an irreducible
  morphism**.
* `TauCeti.finite_hom_arQuiver`, `TauCeti.natCard_hom_arQuiver`, `TauCeti.natCard_hom_arVertex` and
  `TauCeti.natCard_hom_arQuiver_le`: **local finiteness** over a finite quiver, the arrow count
  `dim_k rad / rad²`, and its bound by the dimension of the ambient morphism space.
* `TauCeti.isFiniteRepType_iff_finite_arQuiver`: finite representation type is finiteness of the
  vertex set.

## Implementation notes

The detection statements carry `[IsLocalRing (End M)]` for the two representations involved, as
`TauCeti.nontrivial_irreducibleMorphismSpace_iff` does and as
`TauCeti/CategoryTheory/AlmostSplit/Uniqueness.lean` already does for almost-split sequences: it is
the hypothesis under which the nonzero classes in `rad / rad²` are exactly the irreducible
morphisms. For a finite-dimensional indecomposable over a finite quiver with finitely many paths
it is Fitting's lemma, but that implication is a statement about the path algebra and is not proved
here; the quiver itself, its local finiteness and its arrow count need none of it.

What is counted here is the `k`-dimension of `rad(M, N) / rad²(M, N)`. As
`TauCeti/CategoryTheory/Preadditive/Radical/Quotient.lean` records, the classical arrow
multiplicity is the dimension over the residue division rings `End M / rad(End M)` and
`End N / rad(End N)`, so over a field for which those are larger than `k` the `k`-dimension is a
multiple of it; the two counts agree when both residue division rings are `k` -- as they are over an
algebraically closed `k` with finite-dimensional endomorphism algebras -- and, vacuously, whenever
`rad(M, N) / rad²(M, N)` vanishes. No statement below claims the multiplicity in that finer sense,
and no hypothesis here could make the `Quiver` instance compute it: the instance is uniform in the
two vertices, while the agreement of the two counts is a condition on the endomorphism algebras of
the representatives, which even over an algebraically closed `k` needs them to be
finite-dimensional. The valued Auslander--Reiten quiver, whose arrows carry those two
multiplicities, would need the bimodule structure of `rad / rad²` over the residue division rings,
which `Radical/Quotient.lean` does not build.

The Auslander--Reiten translate `τ = D Tr`, which makes this quiver a translation quiver, is built
in `TauCeti/Algebra/Module/AuslanderReiten/Translate.lean`; attaching it to the vertices here is a
separate step and is not done in this file.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), VII.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.4 and VII.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

/-! ### The vertices -/

/-- **The vertex type of the Auslander--Reiten quiver**: the isomorphism classes of
finite-dimensional indecomposable representations of `Q` over `k`, as the skeleton of the full
subcategory they span.

This is the type whose finiteness is `TauCeti.IsFiniteRepType`; see
`TauCeti.isFiniteRepType_iff_finite_arQuiver`. -/
def arQuiver : Type _ :=
  Skeleton (ObjectProperty.FullSubcategory
    (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M))

variable {k Q}

/-- The representation representing a vertex of the Auslander--Reiten quiver. It is a genuine
choice -- `CategoryTheory.fromSkeleton` picks a representative of the isomorphism class -- and
`TauCeti.arRepIso` says that the representative chosen at the vertex of a given representation is
isomorphic to that representation. -/
noncomputable def arRep (X : arQuiver.{u, v, w, t} k Q) : QuiverRep.{u, v, w, t} k Q :=
  ((fromSkeleton _).obj X).obj

/-- The representative of a vertex is pointwise finite-dimensional. -/
theorem isFinDim_arRep (X : arQuiver.{u, v, w, t} k Q) : IsFinDim k Q (arRep X) :=
  ((fromSkeleton _).obj X).property.1

/-- The representative of a vertex is indecomposable. -/
theorem indecomposable_arRep (X : arQuiver.{u, v, w, t} k Q) : Indecomposable (arRep X) :=
  ((fromSkeleton _).obj X).property.2

/-- **The vertex of a finite-dimensional indecomposable representation**: its isomorphism class. -/
def arVertex {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M) (hM' : Indecomposable M) :
    arQuiver.{u, v, w, t} k Q :=
  toSkeleton ⟨M, hM, hM'⟩

/-- **Two representations give the same vertex exactly when they are isomorphic**: the vertices of
the Auslander--Reiten quiver are the isomorphism classes. -/
theorem arVertex_eq_arVertex_iff {M N : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (hM' : Indecomposable M) (hN : IsFinDim k Q N) (hN' : Indecomposable N) :
    arVertex hM hM' = arVertex hN hN' ↔ Nonempty (M ≅ N) :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _

/-- Every vertex is the vertex of its own representative. -/
theorem arVertex_arRep (X : arQuiver.{u, v, w, t} k Q) :
    arVertex (isFinDim_arRep X) (indecomposable_arRep X) = X :=
  toSkeleton_fromSkeleton_obj X

/-- **The representative of the vertex of a representation is isomorphic to that
representation.** This is what lets a statement about the arrows at a vertex be read at any
representative of it. -/
noncomputable def arRepIso {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (hM' : Indecomposable M) : arRep (arVertex hM hM') ≅ M :=
  (ObjectProperty.ι _).mapIso (fromSkeletonToSkeletonIso (⟨M, hM, hM'⟩ :
    ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)))

/-! ### The arrows -/

variable (k) in
/-- **The Auslander--Reiten quiver**, with its arrows `X → Y` the index set of a `k`-basis of the
space `rad(M, N) / rad²(M, N)` of irreducible morphisms between the representatives `M` and `N` of
the two vertices, so that -- between objects with local endomorphism rings -- there is an arrow
exactly when there is an irreducible morphism (`TauCeti.nonempty_hom_arQuiver_iff`), and the arrows
are counted by `dim_k rad / rad²` (`TauCeti.natCard_hom_arQuiver`). That count is the classical
arrow multiplicity when both residue division rings are `k` and exceeds it in general; the module
docstring records the boundary. -/
noncomputable instance : Quiver (arQuiver.{u, v, w, t} k Q) where
  Hom X Y := Module.Basis.ofVectorSpaceIndex k (irreducibleMorphismSpace k (arRep X) (arRep Y))

variable (k) in
/-- **The arrows `X → Y` index a basis of the space of irreducible morphisms** between the
representatives of `X` and `Y`. This is the sense in which the arrows of the Auslander--Reiten
quiver *are* `rad / rad²`, and it is how the arrow type is defined. -/
noncomputable def arArrowBasis (X Y : arQuiver.{u, v, w, t} k Q) :
    Module.Basis (X ⟶ Y) k (irreducibleMorphismSpace k (arRep X) (arRep Y)) :=
  Module.Basis.ofVectorSpace k _

section Representatives

variable {X Y : arQuiver.{u, v, w, t} k Q} {M N : QuiverRep.{u, v, w, t} k Q}

/-- **The arrows `X → Y` index a basis of the space of irreducible morphisms between any
representatives** of the two vertices, not only the chosen ones: the space transports along
isomorphisms of either argument. -/
noncomputable def arArrowBasisOfIso (e : arRep X ≅ M) (e' : arRep Y ≅ N) :
    Module.Basis (X ⟶ Y) k (irreducibleMorphismSpace k M N) :=
  (arArrowBasis k X Y).map (irreducibleMorphismSpaceCongr k e e')

/-- There is an arrow `X → Y` exactly when the space of irreducible morphisms between
representatives is nontrivial. This is the bare linear algebra behind the detection statements
below; it needs no hypothesis on the endomorphism rings. -/
theorem nonempty_hom_arQuiver_iff_nontrivial (e : arRep X ≅ M) (e' : arRep Y ≅ N) :
    Nonempty (X ⟶ Y) ↔ Nontrivial (irreducibleMorphismSpace k M N) :=
  ⟨fun ⟨a⟩ ↦ nontrivial_of_ne _ _ ((arArrowBasisOfIso e e').ne_zero a),
    fun _ ↦ (arArrowBasisOfIso e e').index_nonempty⟩

/-- **The arrows between two vertices are counted by `dim_k rad / rad²`** at any representatives of
them. -/
theorem natCard_hom_arVertex (hM : IsFinDim k Q M) (hM' : Indecomposable M)
    (hN : IsFinDim k Q N) (hN' : Indecomposable N) :
    Nat.card (arVertex hM hM' ⟶ arVertex hN hN') =
      Module.finrank k (irreducibleMorphismSpace k M N) :=
  (Module.finrank_eq_nat_card_basis
    (arArrowBasisOfIso (arRepIso hM hM') (arRepIso hN hN'))).symm

variable [IsLocalRing (End M)] [IsLocalRing (End N)]

/-- **There is an arrow exactly when there is an irreducible morphism**, read at arbitrary
representatives `M` of `X` and `N` of `Y`. The two specializations
`TauCeti.nonempty_hom_arQuiver_iff` and `TauCeti.nonempty_hom_arVertex_iff` are the cases of a
vertex read at its own representative and of the vertex of a given representation. -/
theorem nonempty_hom_arQuiver_iff_of_iso (e : arRep X ≅ M) (e' : arRep Y ≅ N) :
    Nonempty (X ⟶ Y) ↔ ∃ f : M ⟶ N, IsIrreducibleMorphism f :=
  (nonempty_hom_arQuiver_iff_nontrivial e e').trans nontrivial_irreducibleMorphismSpace_iff

/-- **There is an arrow between the vertices of two finite-dimensional indecomposables exactly when
there is an irreducible morphism between them.** This is the form in which the arrows of the
Auslander--Reiten quiver are computed: no representative has to be named. -/
theorem nonempty_hom_arVertex_iff (hM : IsFinDim k Q M) (hM' : Indecomposable M)
    (hN : IsFinDim k Q N) (hN' : Indecomposable N) :
    Nonempty (arVertex hM hM' ⟶ arVertex hN hN') ↔ ∃ f : M ⟶ N, IsIrreducibleMorphism f :=
  nonempty_hom_arQuiver_iff_of_iso (arRepIso hM hM') (arRepIso hN hN')

end Representatives

section Detection

variable {X Y : arQuiver.{u, v, w, t} k Q}
variable [IsLocalRing (End (arRep X))] [IsLocalRing (End (arRep Y))]

/-- **There is an arrow `X → Y` exactly when there is an irreducible morphism between the
representatives.** -/
theorem nonempty_hom_arQuiver_iff :
    Nonempty (X ⟶ Y) ↔ ∃ f : arRep X ⟶ arRep Y, IsIrreducibleMorphism f :=
  nonempty_hom_arQuiver_iff_of_iso (Iso.refl _) (Iso.refl _)

/-- **Every arrow of the Auslander--Reiten quiver is the class of an irreducible morphism.** The
arrow is a basis vector of `rad / rad²`, hence nonzero, and the nonzero classes are exactly the
irreducible morphisms. -/
theorem exists_isIrreducibleMorphism_arArrowBasis (a : X ⟶ Y) :
    ∃ f : jacobsonRadicalSubmodule k (arRep X) (arRep Y),
      IsIrreducibleMorphism (f : arRep X ⟶ arRep Y) ∧
        irreducibleMorphismMk k (arRep X) (arRep Y) f = arArrowBasis k X Y a :=
  exists_isIrreducibleMorphism_irreducibleMorphismMk_eq ((arArrowBasis k X Y).ne_zero a)

end Detection

/-! ### Local finiteness and the arrow count -/

section Finiteness

variable {X Y : arQuiver.{u, v, w, t} k Q}

/-- **The arrows between two vertices are counted by `dim_k rad / rad²`.** -/
theorem natCard_hom_arQuiver :
    Nat.card (X ⟶ Y) = Module.finrank k (irreducibleMorphismSpace k (arRep X) (arRep Y)) :=
  (Module.finrank_eq_nat_card_basis (arArrowBasis k X Y)).symm

variable [Finite Q]

/-- **The Auslander--Reiten quiver of a finite quiver is locally finite.** The arrows `X → Y` are a
basis of a subquotient of `arRep X ⟶ arRep Y`, which is finite-dimensional because both
representatives are pointwise finite-dimensional. -/
instance finite_hom_arQuiver (X Y : arQuiver.{u, v, w, t} k Q) : Finite (X ⟶ Y) :=
  have := (isFinDim_arRep X).finiteDimensional_hom (isFinDim_arRep Y)
  Module.Finite.finite_basis (arArrowBasis k X Y)

/-- **The number of arrows between two vertices is bounded by the dimension of the morphism space
between their representatives.** -/
theorem natCard_hom_arQuiver_le :
    Nat.card (X ⟶ Y) ≤ Module.finrank k (arRep X ⟶ arRep Y) :=
  have := (isFinDim_arRep X).finiteDimensional_hom (isFinDim_arRep Y)
  natCard_hom_arQuiver.trans_le (finrank_irreducibleMorphismSpace_le k (arRep X) (arRep Y))

end Finiteness

variable (k Q) in
/-- **Finite representation type is the finiteness of the Auslander--Reiten quiver.** Both sides
are the finiteness of the same type of isomorphism classes; the content of the statement is that
`TauCeti.IsFiniteRepType` is exactly the condition under which the Auslander--Reiten quiver
displays all the indecomposables in a finite picture. -/
theorem isFiniteRepType_iff_finite_arQuiver :
    IsFiniteRepType.{u, v, w, t} k Q ↔ Finite (arQuiver.{u, v, w, t} k Q) :=
  isFiniteRepType_iff

end TauCeti
