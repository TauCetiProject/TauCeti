/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Circle
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Suspension and loops of pointed simplicial sets

The simplicial suspension of a pointed simplicial set is its smash product with the simplicial
circle on the left.  Its right adjoint is the pointed mapping simplicial set out of that circle.
This file names these two functors and their adjunction, fixing the left-coordinate convention
used by spectra and reduced cohomology.

## Main definitions

* `PointedSSet.suspension`: the functor `X ↦ S¹ ∧ X`.
* `PointedSSet.loops`: the functor `Y ↦ Map_*(S¹, Y)`.
* `PointedSSet.suspensionLoopAdjunction`: the adjunction `S¹ ∧ - ⊣ Map_*(S¹, -)`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.PointedSSet

/-- Simplicial suspension, with the circle as the left smash factor. -/
noncomputable abbrev suspension : PointedSSet.{0} ⥤ PointedSSet.{0} :=
  tensorLeft circle

/-- The pointed simplicial loop-space functor `Map_*(S¹, -)`. -/
noncomputable abbrev loops : PointedSSet.{0} ⥤ PointedSSet.{0} :=
  PointedSSet.ihom circle

/-- Smash with the simplicial circle is left adjoint to the pointed mapping simplicial set out
of the circle. -/
noncomputable abbrev suspensionLoopAdjunction : suspension ⊣ loops :=
  ihom.adjunction circle

/-- The hom-set equivalence of the suspension-loop adjunction is the smash-hom currying
equivalence specialized to the simplicial circle. -/
lemma suspensionLoopAdjunction_homEquiv (X Y : PointedSSet.{0}) :
    suspensionLoopAdjunction.homEquiv X Y = tensorHomEquiv circle X Y :=
  homEquiv_def circle X Y

@[simp]
lemma suspensionLoopAdjunction_homEquiv_apply_right_app_coe_app_apply
    {X Y : PointedSSet.{0}} (f : suspension.obj X ⟶ Y)
    {n m : SimplexCategoryᵒᵖ} (x : X.right.obj n) (g : n ⟶ m)
    (s : circle.right.obj m) :
    dsimp% ((suspensionLoopAdjunction.homEquiv X Y f).right.app n x :
      (basedMaps circle Y).obj n).1.app m g s =
      f.right.app m (smashMk s (X.right.map g x)) := by
  rw [suspensionLoopAdjunction_homEquiv]
  exact tensorHomEquiv_apply_right_app_coe_app_apply f x g s

@[simp]
lemma suspensionLoopAdjunction_homEquiv_symm_apply_right_app_smashMk
    {X Y : PointedSSet.{0}} (f : X ⟶ loops.obj Y)
    {n : SimplexCategoryᵒᵖ} (s : circle.right.obj n) (x : X.right.obj n) :
    dsimp% ((suspensionLoopAdjunction.homEquiv X Y).symm f).right.app n (smashMk s x) =
      (f.right.app n x : (basedMaps circle Y).obj n).1.app n (𝟙 n) s := by
  rw [suspensionLoopAdjunction_homEquiv]
  exact tensorHomEquiv_symm_apply_right_app_smashMk f s x

end TauCeti.PointedSSet
