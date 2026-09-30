/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import Mathlib.GroupTheory.Coprod.Basic

import TauCeti.AlgebraicTopology.FundamentalGroup.CoverGeneration
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
import TauCeti.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import TauCeti.CategoryTheory.Groupoid.SingleObj

/-!
# The based Seifert--van Kampen theorem for a simply connected overlap

Suppose that the interiors of two path-connected subsets `A` and `B` cover a space `X`, both
contain a basepoint `x`, and `A ∩ B` is simply connected. This file proves that the canonical map

`π₁(A, x) ∗ π₁(B, x) →* π₁(X, x)`

is an isomorphism. The inverse is constructed from the fundamental-groupoid gluing theorem. Local
functors on `A` and `B` send chosen connecting paths back to the basepoint; a gauge conjugation on
the second functor makes the two functors agree strictly on the overlap. Gluing then supplies the
inverse. Surjectivity is the existing generation half of van Kampen.

## Main declarations

* `FundamentalGroup.vanKampenLift`: the canonical homomorphism from the free product.
* `FundamentalGroup.vanKampenLift_bijective`: the canonical homomorphism is bijective.
* `FundamentalGroup.vanKampenEquiv`: the resulting multiplicative equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, Section 6.7.
-/

public section

open CategoryTheory Set Topology
open scoped FundamentalGroupoid Monoid.Coprod

namespace FundamentalGroup

private noncomputable def basedFunctor {C : Type*} [CategoryTheory.Groupoid C] (x₀ : C)
    (τ : ∀ y : C, x₀ ⟶ y) {G : Type*} [Group G] (f : End x₀ →* G) : C ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map {x y} g := f (τ x ≫ g ≫ inv (τ y))
  map_id x := by
    change f (τ x ≫ 𝟙 x ≫ inv (τ x)) = (1 : G)
    simpa [Category.assoc] using map_one f
  map_comp {x y z} g h := by
    rw [SingleObj.comp_as_mul, ← map_mul]
    congr 1
    simp [End.mul_def, Category.assoc]

private noncomputable def connectingHom {C : Type*} [CategoryTheory.Groupoid C] (x₀ : C)
    (h : ∀ y : C, Nonempty (x₀ ⟶ y)) (y : C) : x₀ ⟶ y :=
  by
    classical
    exact if hy : y = x₀ then eqToHom hy.symm else (h y).some

@[simp]
private theorem connectingHom_self {C : Type*} [CategoryTheory.Groupoid C] (x₀ : C)
    (h : ∀ y : C, Nonempty (x₀ ⟶ y)) : connectingHom x₀ h x₀ = 𝟙 x₀ := by
  simp [connectingHom]

variable {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}

private def leftBase (hxA : x ∈ A) : A := ⟨x, hxA⟩
private def rightBase (hxB : x ∈ B) : B := ⟨x, hxB⟩
private def interBase (hxA : x ∈ A) (hxB : x ∈ B) : ↥(A ∩ B) :=
  ⟨x, show x ∈ A ∩ B from ⟨hxA, hxB⟩⟩

private def interOfRight (z : B) (hz : z.1 ∈ A) : ↥(A ∩ B) :=
  ⟨z.1, show z.1 ∈ A ∩ B from ⟨hz, z.2⟩⟩

private def swapInter : C(↥(B ∩ A), ↥(A ∩ B)) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩

omit [TopologicalSpace X] in
@[simp]
private theorem interOfRight_base (hxA : x ∈ A) (hxB : x ∈ B) :
    interOfRight (rightBase hxB) hxA = interBase hxA hxB := by
  rfl

omit [TopologicalSpace X] in
@[simp]
private theorem interOfRight_inter (z : ↥(A ∩ B)) :
    interOfRight (⟨z.1, z.2.2⟩ : B) z.2.1 = z := by
  rfl

private noncomputable def leftHom (hA : IsPathConnected A) (hxA : x ∈ A)
    (z : FundamentalGroupoid A) :
    FundamentalGroupoid.mk (leftBase hxA) ⟶ z := by
  letI : PathConnectedSpace ↥A := isPathConnected_iff_pathConnectedSpace.mp hA
  exact connectingHom _ (FundamentalGroupoid.nonempty_hom _) z

private noncomputable def rightHom (hB : IsPathConnected B) (hxB : x ∈ B)
    (z : FundamentalGroupoid B) :
    FundamentalGroupoid.mk (rightBase hxB) ⟶ z := by
  letI : PathConnectedSpace ↥B := isPathConnected_iff_pathConnectedSpace.mp hB
  exact connectingHom _ (FundamentalGroupoid.nonempty_hom _) z

@[simp]
private theorem leftHom_base (hA : IsPathConnected A) (hxA : x ∈ A) :
    leftHom hA hxA (FundamentalGroupoid.mk (leftBase hxA)) = 𝟙 _ := by
  simp [leftHom]

@[simp]
private theorem rightHom_base (hB : IsPathConnected B) (hxB : x ∈ B) :
    rightHom hB hxB (FundamentalGroupoid.mk (rightBase hxB)) = 𝟙 _ := by
  simp [rightHom]

private noncomputable def gaugeConjugate {C : Type*} [CategoryTheory.Groupoid C]
    {G : Type*} [Group G] (F : C ⥤ SingleObj G)
    (k : ∀ z : C, F.obj z ⟶ SingleObj.star G) : C ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map {y z} g := inv (k y) ≫ F.map g ≫ k z
  map_id y := by simp
  map_comp {y z w} g h := by simp [Category.assoc]

private noncomputable def leftFunctor (hA : IsPathConnected A) (hxA : x ∈ A) (hxB : x ∈ B) :
    FundamentalGroupoid A ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  basedFunctor _ (leftHom hA hxA) Monoid.Coprod.inl

private noncomputable def rightFunctor (hB : IsPathConnected B) (hxA : x ∈ A) (hxB : x ∈ B) :
    FundamentalGroupoid B ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  basedFunctor _ (rightHom hB hxB) Monoid.Coprod.inr

private noncomputable def leftOverlapFunctor (hA : IsPathConnected A) (hxA : x ∈ A)
    (hxB : x ∈ B) : FundamentalGroupoid ↥(A ∩ B) ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left) ⋙
    leftFunctor hA hxA hxB

private noncomputable def rightOverlapFunctor (hB : IsPathConnected B) (hxA : x ∈ A)
    (hxB : x ∈ B) : FundamentalGroupoid ↥(A ∩ B) ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right) ⋙
    rightFunctor hB hxA hxB

private noncomputable def overlapGauge (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (z : FundamentalGroupoid ↥(A ∩ B)) :
    (rightOverlapFunctor hB hxA hxB).obj z ⟶
      (leftOverlapFunctor hA hxA hxB).obj z := by
  let _ : SimplyConnectedSpace ↥(A ∩ B) := hAB.simplyConnectedSpace
  let d : FundamentalGroupoid.mk (interBase hxA hxB) ⟶ z := default
  exact inv ((rightOverlapFunctor hB hxA hxB).map d) ≫
    (leftOverlapFunctor hA hxA hxB).map d

@[simp]
private theorem overlapGauge_base (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B) :
    overlapGauge hA hB hAB hxA hxB
      (FundamentalGroupoid.mk (interBase hxA hxB)) = 𝟙 _ := by
  let _ : SimplyConnectedSpace ↥(A ∩ B) := hAB.simplyConnectedSpace
  dsimp only [overlapGauge]
  have hr : (rightOverlapFunctor hB hxA hxB).map
      (default : FundamentalGroupoid.mk (interBase hxA hxB) ⟶
        FundamentalGroupoid.mk (interBase hxA hxB)) =
      (rightOverlapFunctor hB hxA hxB).map (𝟙 _) := congrArg _ (Subsingleton.elim _ _)
  have hl : (leftOverlapFunctor hA hxA hxB).map
      (default : FundamentalGroupoid.mk (interBase hxA hxB) ⟶
        FundamentalGroupoid.mk (interBase hxA hxB)) =
      (leftOverlapFunctor hA hxA hxB).map (𝟙 _) := congrArg _ (Subsingleton.elim _ _)
  simp only [hr, hl]
  simp
  rfl

private theorem overlapGauge_naturality (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    {y z : FundamentalGroupoid ↥(A ∩ B)} (g : y ⟶ z) :
    (rightOverlapFunctor hB hxA hxB).map g ≫ overlapGauge hA hB hAB hxA hxB z =
      overlapGauge hA hB hAB hxA hxB y ≫ (leftOverlapFunctor hA hxA hxB).map g := by
  let _ : SimplyConnectedSpace ↥(A ∩ B) := hAB.simplyConnectedSpace
  let y₀ := FundamentalGroupoid.mk (interBase hxA hxB)
  let dy : y₀ ⟶ y := default
  let dz : y₀ ⟶ z := default
  have hdy : dy ≫ g = dz := Subsingleton.elim _ _
  dsimp only [overlapGauge]
  change (rightOverlapFunctor hB hxA hxB).map g ≫
      inv ((rightOverlapFunctor hB hxA hxB).map dz) ≫
        (leftOverlapFunctor hA hxA hxB).map dz =
    (inv ((rightOverlapFunctor hB hxA hxB).map dy) ≫
        (leftOverlapFunctor hA hxA hxB).map dy) ≫
      (leftOverlapFunctor hA hxA hxB).map g
  rw [← hdy]
  simp [Category.assoc]

private noncomputable def rightGauge (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (z : FundamentalGroupoid B) :
    (rightFunctor hB hxA hxB).obj z ⟶
      SingleObj.star (FundamentalGroup A (leftBase hxA) ∗
        FundamentalGroup B (rightBase hxB)) := by
  classical
  exact if hz : z.as.1 ∈ A then
    overlapGauge hA hB hAB hxA hxB
      (FundamentalGroupoid.mk (interOfRight z.as hz)) else 𝟙 _

private noncomputable def adjustedRightFunctor (hA : IsPathConnected A)
    (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) : FundamentalGroupoid B ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  gaugeConjugate (rightFunctor hB hxA hxB) (rightGauge hA hB hAB hxA hxB)

private theorem rightGauge_inter (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (z : FundamentalGroupoid ↥(A ∩ B)) :
    rightGauge hA hB hAB hxA hxB
        ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right)).obj z) =
      overlapGauge hA hB hAB hxA hxB z := by
  classical
  unfold rightGauge
  split
  · congr 1
  · exfalso
    apply ‹¬_›
    exact z.as.2.1

@[simp]
private theorem rightGauge_base (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B) :
    rightGauge hA hB hAB hxA hxB (FundamentalGroupoid.mk (rightBase hxB)) = 𝟙 _ := by
  change rightGauge hA hB hAB hxA hxB
    ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right)).obj
      (FundamentalGroupoid.mk (interBase hxA hxB))) = _
  rw [rightGauge_inter, overlapGauge_base]
  rfl

private theorem overlapCompatibility (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B) :
    FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left) ⋙
        leftFunctor hA hxA hxB =
      FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right) ⋙
        adjustedRightFunctor hA hB hAB hxA hxB := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun y z g => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [Functor.comp_map, adjustedRightFunctor, gaugeConjugate,
    SingleObj.comp_as_mul, SingleObj.inv_as_inv]
  have h := overlapGauge_naturality hA hB hAB hxA hxB g
  simp only [SingleObj.comp_as_mul] at h
  rw [rightGauge_inter, rightGauge_inter]
  let P := FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)
  change (show P from overlapGauge hA hB hAB hxA hxB z) *
      (show P from (rightFunctor hB hxA hxB).map
        ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right)).map g)) =
    (show P from (leftFunctor hA hxA hxB).map
        ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left)).map g)) *
      (show P from overlapGauge hA hB hAB hxA hxB y) at h
  rw [h]
  change (show P from (leftFunctor hA hxA hxB).map
      ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left)).map g)) =
    ((show P from (leftFunctor hA hxA hxB).map
        ((FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left)).map g)) *
      (show P from overlapGauge hA hB hAB hxA hxB y)) *
        (show P from overlapGauge hA hB hAB hxA hxB y)⁻¹
  rw [mul_assoc, mul_inv_cancel, mul_one]

private def twoOpenCover (A B : Set X) : Bool → Set X := fun b => Bool.rec B A b

private noncomputable def localFunctor (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B) :
    ∀ b, FundamentalGroupoid (twoOpenCover A B b) ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  fun b => Bool.rec (adjustedRightFunctor hA hB hAB hxA hxB) (leftFunctor hA hxA hxB) b

private theorem localFunctor_compatibility (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsSimplyConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B) (i j : Bool) :
    FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_left :
            twoOpenCover A B i ∩ twoOpenCover A B j ⊆ twoOpenCover A B i)) ⋙
        localFunctor hA hB hAB hxA hxB i =
      FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_right :
            twoOpenCover A B i ∩ twoOpenCover A B j ⊆ twoOpenCover A B j)) ⋙
        localFunctor hA hB hAB hxA hxB j := by
  cases i <;> cases j
  · rfl
  · change FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_left : B ∩ A ⊆ B)) ⋙
        adjustedRightFunctor hA hB hAB hxA hxB =
      FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_right : B ∩ A ⊆ A)) ⋙
        leftFunctor hA hxA hxB
    have hr : FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_left : B ∩ A ⊆ B)) =
        FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙
          FundamentalGroupoid.map
            (ContinuousMap.inclusion (inter_subset_right : A ∩ B ⊆ B)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    have hl : FundamentalGroupoid.map
          (ContinuousMap.inclusion (inter_subset_right : B ∩ A ⊆ A)) =
        FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙
          FundamentalGroupoid.map
            (ContinuousMap.inclusion (inter_subset_left : A ∩ B ⊆ A)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    have h := congrArg
      (fun F => FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙ F)
      (overlapCompatibility hA hB hAB hxA hxB).symm
    rw [hr, hl]
    exact h
  · exact overlapCompatibility hA hB hAB hxA hxB
  · rfl

private theorem exists_twoOpenCover_mem_nhds (hCover : interior A ∪ interior B = univ) (y : X) :
    ∃ b, twoOpenCover A B b ∈ 𝓝 y := by
  rcases (hCover ▸ mem_univ y : y ∈ interior A ∪ interior B) with hy | hy
  · exact ⟨true, mem_interior_iff_mem_nhds.1 hy⟩
  · exact ⟨false, mem_interior_iff_mem_nhds.1 hy⟩

private noncomputable def gluedFunctor (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) : FundamentalGroupoid X ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  TauCeti.FundamentalGroupoid.glue (U := twoOpenCover A B)
    (exists_twoOpenCover_mem_nhds hCover)
    (localFunctor hA hB hAB hxA hxB)
    (localFunctor_compatibility hA hB hAB hxA hxB)

/-- The canonical homomorphism from the free product of the fundamental groups of two
subspaces to the fundamental group of the ambient space. -/
@[expose] noncomputable def vanKampenLift (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B) :
    (_root_.FundamentalGroup A ⟨x, hxA⟩ ∗ _root_.FundamentalGroup B ⟨x, hxB⟩) →*
      _root_.FundamentalGroup X x :=
  Monoid.Coprod.lift
    (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩)
    (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩)

/-- `vanKampenLift` restricts on the left factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_inl (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    (g : _root_.FundamentalGroup A ⟨x, hxA⟩) :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inl g) =
      _root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩ g :=
  rfl

/-- `vanKampenLift` restricts on the right factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_inr (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    (g : _root_.FundamentalGroup B ⟨x, hxB⟩) :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inr g) =
      _root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩ g :=
  rfl

private noncomputable def vanKampenInverse (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) : _root_.FundamentalGroup X x →*
      (_root_.FundamentalGroup A (leftBase hxA) ∗
        _root_.FundamentalGroup B (rightBase hxB)) :=
  (SingleObj.mapHom _ _).symm
    (TauCeti.Groupoid.singleObjFunctor (_root_.FundamentalGroupoid.mk x) ⋙
      gluedFunctor hCover hA hB hAB hxA hxB)

private theorem vanKampenInverse_map_left (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (g : _root_.FundamentalGroup A (leftBase hxA)) :
    vanKampenInverse hCover hA hB hAB hxA hxB
        (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) (leftBase hxA) g) =
      Monoid.Coprod.inl g := by
  change (gluedFunctor hCover hA hB hAB hxA hxB).map
      ((FundamentalGroupoid.map (ContinuousMap.subtypeVal A)).map g) = _
  change (FundamentalGroupoid.map (ContinuousMap.subtypeVal A) ⋙
    gluedFunctor hCover hA hB hAB hxA hxB).map g = _
  unfold gluedFunctor
  have h := Functor.congr_hom (TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue
    (exists_twoOpenCover_mem_nhds hCover) (localFunctor hA hB hAB hxA hxB)
      (localFunctor_compatibility hA hB hAB hxA hxB) true) g
  simp only [twoOpenCover, localFunctor, leftFunctor, basedFunctor, eqToHom_refl, leftHom_base,
    IsIso.inv_id, Category.comp_id, Category.id_comp] at h
  change (TauCeti.FundamentalGroupoid.glue (exists_twoOpenCover_mem_nhds hCover)
      (localFunctor hA hB hAB hxA hxB) (localFunctor_compatibility hA hB hAB hxA hxB)).map
    ((FundamentalGroupoid.map (ContinuousMap.subtypeVal A)).map g) = _ at h
  exact h

private theorem vanKampenInverse_map_right (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (g : _root_.FundamentalGroup B (rightBase hxB)) :
    vanKampenInverse hCover hA hB hAB hxA hxB
        (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) (rightBase hxB) g) =
      Monoid.Coprod.inr g := by
  change (gluedFunctor hCover hA hB hAB hxA hxB).map
      ((FundamentalGroupoid.map (ContinuousMap.subtypeVal B)).map g) = _
  change (FundamentalGroupoid.map (ContinuousMap.subtypeVal B) ⋙
    gluedFunctor hCover hA hB hAB hxA hxB).map g = _
  unfold gluedFunctor
  have h := Functor.congr_hom (TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue
    (exists_twoOpenCover_mem_nhds hCover) (localFunctor hA hB hAB hxA hxB)
      (localFunctor_compatibility hA hB hAB hxA hxB) false) g
  simp only [twoOpenCover, localFunctor, adjustedRightFunctor, gaugeConjugate, rightFunctor,
    basedFunctor, eqToHom_refl, rightGauge_base, IsIso.inv_id, rightHom_base, Category.comp_id,
    Category.id_comp] at h
  change (TauCeti.FundamentalGroupoid.glue (exists_twoOpenCover_mem_nhds hCover)
      (localFunctor hA hB hAB hxA hxB) (localFunctor_compatibility hA hB hAB hxA hxB)).map
    ((FundamentalGroupoid.map (ContinuousMap.subtypeVal B)).map g) = _ at h
  exact h

/-- **The based Seifert--van Kampen theorem for a simply connected overlap.**

If the interiors of two path-connected sets cover `X`, their intersection is simply connected,
and both contain the basepoint, then the canonical homomorphism from the free product of their
fundamental groups to the fundamental group of `X` is bijective. -/
theorem vanKampenLift_bijective (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    Function.Bijective (vanKampenLift A B x hxA hxB) := by
  have hleft : (vanKampenInverse hCover hA hB hAB hxA hxB).comp
      (vanKampenLift A B x hxA hxB) = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · ext g
      exact vanKampenInverse_map_left hCover hA hB hAB hxA hxB g
    · ext g
      exact vanKampenInverse_map_right hCover hA hB hAB hxA hxB g
  constructor
  · exact Function.LeftInverse.injective fun g ↦ DFunLike.congr_fun hleft g
  · rw [← MonoidHom.range_eq_top, Monoid.Coprod.range_eq]
    change ((_root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).range ⊔
      (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩).range) = ⊤
    exact TauCeti.FundamentalGroup.range_map_subtypeVal_sup_eq_top hCover hA hB
      hAB.isPathConnected hxA hxB

/-- The equivalence in the based Seifert--van Kampen theorem for two path-connected sets with
simply connected intersection. Its underlying homomorphism is `vanKampenLift`. -/
@[expose] noncomputable def vanKampenEquiv (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    (_root_.FundamentalGroup A ⟨x, hxA⟩ ∗ _root_.FundamentalGroup B ⟨x, hxB⟩) ≃*
      _root_.FundamentalGroup X x :=
  MulEquiv.ofBijective (vanKampenLift A B x hxA hxB)
    (vanKampenLift_bijective hCover hA hB hAB hxA hxB)

/-- The homomorphism underlying `vanKampenEquiv` is `vanKampenLift`. -/
@[simp]
theorem vanKampenEquiv_toMonoidHom (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    (↑(vanKampenEquiv hCover hA hB hAB hxA hxB) :
      (_root_.FundamentalGroup A ⟨x, hxA⟩ ∗ _root_.FundamentalGroup B ⟨x, hxB⟩) →*
        _root_.FundamentalGroup X x) =
      vanKampenLift A B x hxA hxB :=
  rfl

end FundamentalGroup
