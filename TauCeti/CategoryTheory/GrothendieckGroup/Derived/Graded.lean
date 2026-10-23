/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Derived.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Graded
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Functor

/-!
# Grading-compatible bounded-derived K₀ comparison

The comparison between abelian K₀ and the K₀ of the bounded derived category is natural for
exact functors. Applying this to an internal grading-shift autoequivalence identifies the two
integer grading actions, in both directions. The internal shift is the actual termwise derived
action; it remains distinct from the cohomological suspension, whose K₀ action is the sign.

The comparison is `AbelianK0.boundedDerivedK0Equiv`, and the actions are the existing
`AbelianK0.shiftZPow` and `TriangulatedK0.shiftZPow`. This file equips that comparison with
compatibility equations rather than introducing another Grothendieck group.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the bounded-derived Grothendieck-group comparison.
-/

public section

namespace TauCeti.AbelianK0

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₁' w₂' w₁'' w₂'' v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EssentiallySmall.{w₁} A]
  [HasDerivedCategory.{w₁'} A] [EssentiallySmall.{w₁''} (DerivedCategory.Bounded A)]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EssentiallySmall.{w₂} B]
  [HasDerivedCategory.{w₂'} B] [EssentiallySmall.{w₂''} (DerivedCategory.Bounded B)]

/-- The canonical comparison to bounded-derived K₀ is natural for exact functors. -/
@[simp]
theorem map_comp_toBoundedDerivedK0 (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (TriangulatedK0.map F.mapBoundedDerivedCategory).comp toBoundedDerivedK0 =
      toBoundedDerivedK0.comp (map F) := by
  apply hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, toBoundedDerivedK0_of, TriangulatedK0.map_of, map_of]
  exact TriangulatedK0.of_congr ((F.mapBoundedDerivedCategorySingleFunctor 0).app X)

/-- Naturality of the comparison equivalence for the actual bounded-derived action. -/
@[simp]
theorem boundedDerivedK0Equiv_map (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (x : AbelianK0 A) :
    boundedDerivedK0Equiv B (map F x) =
      TriangulatedK0.map F.mapBoundedDerivedCategory (boundedDerivedK0Equiv A x) := by
  calc
    boundedDerivedK0Equiv B (map F x) = toBoundedDerivedK0 (map F x) :=
      DFunLike.congr_fun (boundedDerivedK0Equiv_toAddMonoidHom (A := B)) _
    _ = TriangulatedK0.map F.mapBoundedDerivedCategory (toBoundedDerivedK0 x) :=
      (DFunLike.congr_fun (map_comp_toBoundedDerivedK0 F) x).symm
    _ = _ := congrArg _
      (DFunLike.congr_fun (boundedDerivedK0Equiv_toAddMonoidHom (A := A)) x).symm

/-- The alternating cohomology-class inverse comparison is natural for exact functors. -/
@[simp]
theorem boundedDerivedK0Equiv_symm_map (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (x : TriangulatedK0 (DerivedCategory.Bounded A)) :
    (boundedDerivedK0Equiv B).symm (TriangulatedK0.map F.mapBoundedDerivedCategory x) =
      map F ((boundedDerivedK0Equiv A).symm x) := by
  apply (boundedDerivedK0Equiv B).injective
  rw [AddEquiv.apply_symm_apply, boundedDerivedK0Equiv_map, AddEquiv.apply_symm_apply]

/-- An additive equivalence acts compatibly with the bounded-derived K₀ comparison. -/
@[simp]
theorem boundedDerivedK0Equiv_mapEquiv (e : A ≌ B) [e.functor.Additive]
    (x : AbelianK0 A) :
    boundedDerivedK0Equiv B (mapEquiv e x) =
      TriangulatedK0.mapEquiv e.mapBoundedDerivedCategory (boundedDerivedK0Equiv A x) := by
  have h : (mapEquiv e : AbelianK0 A →+ AbelianK0 B) = map e.functor :=
    hom_ext fun X ↦ by simp
  have hx : mapEquiv e x = map e.functor x := DFunLike.congr_fun h x
  have hd : TriangulatedK0.mapEquiv e.mapBoundedDerivedCategory (boundedDerivedK0Equiv A x) =
      TriangulatedK0.map e.mapBoundedDerivedCategory.functor (boundedDerivedK0Equiv A x) :=
    DFunLike.congr_fun (TriangulatedK0.mapEquiv_toAddMonoidHom (e := e.mapBoundedDerivedCategory)) _
  rw [hx, hd, boundedDerivedK0Equiv_map]
  exact DFunLike.congr_fun (TriangulatedK0.map_congr e.functor.mapBoundedDerivedCategory
    (F' := e.mapBoundedDerivedCategory.functor) fun X ↦
    ⟨eqToIso (congrArg (fun F ↦ F.obj X) e.mapBoundedDerivedCategory_functor.symm)⟩) _

/-- The inverse comparison also commutes with the equivalence induced on bounded-derived K₀. -/
@[simp]
theorem boundedDerivedK0Equiv_symm_mapEquiv (e : A ≌ B) [e.functor.Additive]
    (x : TriangulatedK0 (DerivedCategory.Bounded A)) :
    (boundedDerivedK0Equiv B).symm (TriangulatedK0.mapEquiv e.mapBoundedDerivedCategory x) =
      mapEquiv e ((boundedDerivedK0Equiv A).symm x) := by
  apply (boundedDerivedK0Equiv B).injective
  rw [AddEquiv.apply_symm_apply, boundedDerivedK0Equiv_mapEquiv, AddEquiv.apply_symm_apply]

/-- The comparison intertwines the inverse of an additive equivalence. -/
@[simp]
theorem boundedDerivedK0Equiv_mapEquiv_symm (e : A ≌ B) [e.functor.Additive]
    (x : AbelianK0 B) :
    boundedDerivedK0Equiv A ((mapEquiv e).symm x) =
      (TriangulatedK0.mapEquiv e.mapBoundedDerivedCategory).symm (boundedDerivedK0Equiv B x) := by
  apply (TriangulatedK0.mapEquiv e.mapBoundedDerivedCategory).injective
  rw [← boundedDerivedK0Equiv_mapEquiv, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

section Shift

variable (e : A ≌ A) [e.functor.Additive]

/-- The bounded-derived comparison intertwines the whole integer internal grading action. -/
@[simp↓]
theorem boundedDerivedK0Equiv_shiftZPow (n : ℤ) (x : AbelianK0 A) :
    boundedDerivedK0Equiv A (shiftZPow e n x) =
      TriangulatedK0.shiftZPow e.mapBoundedDerivedCategory n (boundedDerivedK0Equiv A x) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [shiftZPow_add_one_apply, boundedDerivedK0Equiv_mapEquiv, ih,
        TriangulatedK0.shiftZPow_add_one_apply]
  | pred k ih =>
      rw [shiftZPow_sub_one_apply, boundedDerivedK0Equiv_mapEquiv_symm, ih,
        TriangulatedK0.shiftZPow_sub_one_apply]

/-- The alternating cohomology-class inverse comparison intertwines every integer grading shift. -/
@[simp↓]
theorem boundedDerivedK0Equiv_symm_shiftZPow (n : ℤ)
    (x : TriangulatedK0 (DerivedCategory.Bounded A)) :
    (boundedDerivedK0Equiv A).symm (TriangulatedK0.shiftZPow e.mapBoundedDerivedCategory n x) =
      shiftZPow e n ((boundedDerivedK0Equiv A).symm x) := by
  apply (boundedDerivedK0Equiv A).injective
  rw [AddEquiv.apply_symm_apply, boundedDerivedK0Equiv_shiftZPow, AddEquiv.apply_symm_apply]

end Shift

end TauCeti.AbelianK0
