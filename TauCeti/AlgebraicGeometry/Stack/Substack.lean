/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Stack.StackInGroupoids
public import TauCeti.CategoryTheory.Sites.Descent.ObjectProperty
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Strictly full substacks

A substack of a stack in groupoids on schemes is specified by an isomorphism-invariant
property of its objects, preserved by pullback and local for the fppf topology. Its fibres
are full subgroupoids, and effective descent follows from locality of membership. Equality
of substacks means equality of their object properties inside the given ambient stack;
equivalence of their underlying stacks alone does not identify substacks.

This file bundles these properties, constructs the underlying stack and its inclusion,
and defines inverse images along morphisms of stacks. It imposes no algebraicity or
representability condition on the inclusion. These can be imposed separately when defining
open and closed substacks, as in the Stacks Project, Definition 100.9.9.

The underlying full sub-pseudofunctor and inclusion are Mathlib's
`Pseudofunctor.ObjectProperty.fullsubcategory` and `Pseudofunctor.ObjectProperty.ι`.

## References

* [Stacks Project, Definition 100.9.9](https://stacks.math.columbia.edu/tag/04YM)
-/

public section

open CategoryTheory Bicategory Opposite

namespace TauCeti.AlgebraicGeometry.StackInGroupoids

open _root_.AlgebraicGeometry

universe u

/-- A strictly full fppf substack, described by a pullback-stable, isomorphism-invariant,
fppf-local property of objects. It is not required to be algebraic. -/
structure Substack (X : StackInGroupoids.{u}) extends X.toSchPseudofunctor.ObjectProperty where
  /-- Membership is local for the fppf topology, invariant under isomorphism, and preserved
  by pullback. -/
  isLocal : toObjectProperty.IsLocal Scheme.fppfTopology

attribute [instance] Substack.isLocal

namespace Substack

variable {X Y Z : StackInGroupoids.{u}}

/-- Substacks are equal if they contain the same objects over every scheme. -/
@[ext]
theorem ext {P Q : Substack X}
    (h : ∀ (T : Scheme.{u}) (M : X.toSchPseudofunctor.obj (.mk (op T))),
      P.prop (.mk (op T)) M ↔ Q.prop (.mk (op T)) M) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      congr 1
      cases p with
      | mk p =>
        cases q with
        | mk q =>
          congr 1
          funext T M
          exact propext (h T.as.unop M)

/-- The stack in groupoids underlying a substack. Its stack condition follows from the
locality of the object property. -/
-- Expose the carrier so that the domains of the inclusion functors compute as full subcategories.
@[expose]
def toStackInGroupoids (P : Substack X) : StackInGroupoids.{u} where
  toSchPseudofunctor := P.toObjectProperty.fullsubcategory
  isGroupoid T := inferInstanceAs (IsGroupoid (P.prop (.mk (op T))).FullSubcategory)
  isStack := inferInstance

@[simp]
lemma toStackInGroupoids_toSchPseudofunctor (P : Substack X) :
    P.toStackInGroupoids.toSchPseudofunctor = P.toObjectProperty.fullsubcategory :=
  (rfl)

/-- The inclusion of a substack in its ambient stack. Its components are Mathlib's fully
faithful full-subcategory inclusions. -/
def ι (P : Substack X) : Hom P.toStackInGroupoids X :=
  P.toObjectProperty.ι

/-- The inclusion sends a substack object to its underlying ambient object. -/
@[simp]
lemma ι_app_obj (P : Substack X) (T : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (M : P.toStackInGroupoids.toSchPseudofunctor.obj T) :
    (P.ι.app T).toFunctor.obj M = M.obj :=
  (rfl)

/-- The inclusion sends a morphism to its underlying ambient morphism. Heterogeneous equality
allows the endpoints to be identified by `ι_app_obj` without exposing the inclusion. -/
@[simp]
lemma ι_app_map (P : Substack X) (T : LocallyDiscrete Scheme.{u}ᵒᵖ)
    {M N : P.toStackInGroupoids.toSchPseudofunctor.obj T} (f : M ⟶ N) :
    HEq ((P.ι.app T).toFunctor.map f) f.hom :=
  (HEq.rfl)

/-- A substack inclusion is full on every fibre category. -/
instance full_ι_app (P : Substack X) (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (P.ι.app T).toFunctor.Full := by
  dsimp [ι]
  exact (P.prop T).fullyFaithfulι.full

/-- A substack inclusion is faithful on every fibre category. -/
instance faithful_ι_app (P : Substack X) (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (P.ι.app T).toFunctor.Faithful := by
  dsimp [ι]
  exact (P.prop T).fullyFaithfulι.faithful

/-- The inverse image of a substack along a morphism of stacks, computed on objects. -/
def comap (P : Substack Y) (f : Hom X Y) : Substack X where
  toObjectProperty := P.toObjectProperty.inverseImage f
  isLocal := inferInstance

@[simp]
lemma comap_prop (P : Substack Y) (f : Hom X Y) (T : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (M : X.toSchPseudofunctor.obj T) :
    (P.comap f).prop T M ↔ P.prop T ((f.app T).toFunctor.obj M) :=
  Pseudofunctor.ObjectProperty.inverseImage_prop P.toObjectProperty f T M

@[simp]
lemma comap_id (P : Substack X) : P.comap (Pseudofunctor.StrongTrans.id _) = P := by
  ext T M
  simp only [comap_prop]
  exact Iff.rfl

@[simp]
lemma comap_comp (P : Substack Z) (f : Hom X Y) (g : Hom Y Z) :
    P.comap (Pseudofunctor.StrongTrans.vcomp f g) = (P.comap g).comap f := by
  ext T M
  simp only [comap_prop]
  exact Iff.rfl

end Substack

end TauCeti.AlgebraicGeometry.StackInGroupoids
