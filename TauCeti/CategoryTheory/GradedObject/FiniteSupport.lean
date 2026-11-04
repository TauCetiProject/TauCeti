/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import TauCeti.CategoryTheory.Limits.Shapes.Products

/-!
# Finitely supported graded objects

The support of a graded object consists of its nonzero components, where zero means
`Limits.IsZero`, so that support is invariant under isomorphism. Finite support is preserved
by reindexing via coproducts and by convolution tensor products. In a category with finite
coproducts, these coproducts exist for finitely supported objects even when the grading type
and the fibres of its addition map are infinite.

These results allow convolution of finitely supported graded finite-dimensional vector spaces
without requiring infinite coproducts in the category of finite-dimensional vector spaces.
They depend only on the tensor product, not on the choice of associator, and thus also apply
when the associator is twisted by a cocycle.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

variable {I J C : Type*} [Category* C]

/-- The degrees in which a graded object is not a zero object. -/
def support (X : GradedObject I C) : Set I := {i | ¬ IsZero (X i)}

@[simp]
lemma mem_support (X : GradedObject I C) (i : I) :
    i ∈ X.support ↔ ¬ IsZero (X i) := Iff.rfl

/-- Isomorphic graded objects have the same support. -/
lemma support_eq_of_iso {X Y : GradedObject I C} (e : X ≅ Y) : X.support = Y.support := by
  ext i
  exact not_congr ((eval i).mapIso e).isZero_iff

/-- A graded object is finitely supported if only finitely many components are nonzero. -/
def HasFiniteSupport (X : GradedObject I C) : Prop := X.support.Finite

/-- Finite support is equivalent to being zero outside a finite set of degrees. -/
lemma hasFiniteSupport_iff (X : GradedObject I C) :
    X.HasFiniteSupport ↔ ∃ s : Finset I, ∀ i ∉ s, IsZero (X i) := by
  classical
  constructor
  · intro h
    exact ⟨h.toFinset, fun i hi => not_not.mp (mt h.mem_toFinset.mpr hi)⟩
  · rintro ⟨s, hs⟩
    exact s.finite_toSet.subset fun i hi => by
      by_contra hn
      exact hi (hs i hn)

/-- Finite support is invariant under isomorphism. -/
lemma hasFiniteSupport_iff_of_iso {X Y : GradedObject I C} (e : X ≅ Y) :
    X.HasFiniteSupport ↔ Y.HasFiniteSupport := by
  unfold HasFiniteSupport
  rw [support_eq_of_iso e]

/-- An object concentrated in one degree is finitely supported. -/
lemma hasFiniteSupport_single [DecidableEq I] [HasInitial C] [HasZeroMorphisms C]
    (i : I) (A : C) :
    ((single i).obj A).HasFiniteSupport := by
  refine (Set.finite_singleton i).subset fun j hj => ?_
  by_contra h
  exact hj ((isInitialSingleObjApply i A j h).isZero)

section Reindex

variable [HasZeroMorphisms C] (X : GradedObject I C) (p : I → J) [X.HasMap p]

/-- Reindexing by coproducts cannot introduce a nonzero component outside the image of the
original support. Equality need not hold in a general category. -/
lemma support_mapObj_subset : (X.mapObj p).support ⊆ p '' X.support := by
  intro j hj
  by_contra h
  apply hj
  rw [IsZero.iff_id_eq_zero]
  refine mapObj_ext _ _ _ _ fun i hi => ?_
  have hXi : IsZero (X i) := by
    by_contra hXi
    exact h ⟨i, hXi, hi⟩
  exact hXi.eq_of_src _ _

/-- Reindexing a finitely supported graded object by coproducts preserves finite support. -/
lemma HasFiniteSupport.mapObj {X : GradedObject I C} (hX : X.HasFiniteSupport)
    (p : I → J) [X.HasMap p] : (X.mapObj p).HasFiniteSupport :=
  (hX.image p).subset (X.support_mapObj_subset p)

end Reindex

/-- Finite coproducts suffice to reindex a finitely supported graded object along any map,
even when its fibres are infinite. -/
lemma HasFiniteSupport.hasMap [HasFiniteCoproducts C] {X : GradedObject I C}
    (hX : X.HasFiniteSupport) (p : I → J) : X.HasMap p := by
  intro j
  apply TauCeti.hasCoproduct_of_finite_setOf_not_isZero
  exact Set.Finite.preimage (fun _ _ _ _ h => Subtype.ext h) hX

section Tensor

variable [MonoidalCategory C] [HasZeroMorphisms C]
  [∀ A : C, (tensorLeft A).PreservesZeroMorphisms]
  [∀ A : C, (tensorRight A).PreservesZeroMorphisms]

/-- The support of the external tensor product is contained in the product of the supports.
No nonvanishing assertion for tensor products is assumed. -/
lemma support_mapBifunctor_tensor_subset (X : GradedObject I C) (Y : GradedObject J C) :
    (((mapBifunctor (curriedTensor C) I J).obj X).obj Y).support ⊆
      X.support ×ˢ Y.support := by
  rintro ⟨i, j⟩ h
  constructor
  · exact fun hi => h ((tensorRight (Y j)).map_isZero hi)
  · exact fun hj => h ((tensorLeft (X i)).map_isZero hj)

/-- The external tensor product of two finitely supported objects is finitely supported. -/
lemma HasFiniteSupport.mapBifunctor_tensor {X : GradedObject I C} {Y : GradedObject J C}
    (hX : X.HasFiniteSupport) (hY : Y.HasFiniteSupport) :
    (((mapBifunctor (curriedTensor C) I J).obj X).obj Y).HasFiniteSupport :=
  (hX.prod hY).subset (support_mapBifunctor_tensor_subset X Y)

variable [AddMonoid I]

/-- Convolution has support contained in the pairwise sums of the original supports. -/
lemma support_tensorObj_subset (X Y : GradedObject I C) [HasTensor X Y] :
    (Monoidal.tensorObj X Y).support ⊆
      (fun ij : I × I => ij.1 + ij.2) '' (X.support ×ˢ Y.support) := by
  exact (support_mapObj_subset _ _).trans
    (Set.image_mono (support_mapBifunctor_tensor_subset X Y))

/-- The convolution tensor product preserves finite support, regardless of whether the grading
monoid itself is finite. -/
lemma HasFiniteSupport.tensorObj {X Y : GradedObject I C}
    (hX : X.HasFiniteSupport) (hY : Y.HasFiniteSupport) [HasTensor X Y] :
    (Monoidal.tensorObj X Y).HasFiniteSupport :=
  (hX.mapBifunctor_tensor hY).mapObj _

/-- Finite coproducts suffice to construct the convolution of finitely supported graded objects;
no finiteness of the fibres of addition is required. -/
lemma HasFiniteSupport.hasTensor [HasFiniteCoproducts C] {X Y : GradedObject I C}
    (hX : X.HasFiniteSupport) (hY : Y.HasFiniteSupport) : HasTensor X Y :=
  (hX.mapBifunctor_tensor hY).hasMap _

end Tensor

end CategoryTheory.GradedObject
