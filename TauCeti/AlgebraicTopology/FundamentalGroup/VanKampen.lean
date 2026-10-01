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
the second functor (`CategoryTheory.Functor.copyObj`) makes the two functors agree strictly on the
overlap. Gluing then supplies the inverse. Surjectivity is the existing generation half of van
Kampen.

## Main declarations

* `TauCeti.vanKampenLift`: the canonical homomorphism from the free product.
* `TauCeti.vanKampenLift_bijective`: the canonical homomorphism is bijective.
* `TauCeti.vanKampenEquiv`: the resulting multiplicative equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, Section 6.7.
-/

public section

open CategoryTheory Set Topology
open scoped FundamentalGroupoid Monoid.Coprod

namespace TauCeti

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

private abbrev leftBase (hxA : x ∈ A) : A := ⟨x, hxA⟩
private abbrev rightBase (hxB : x ∈ B) : B := ⟨x, hxB⟩
private def interBase (hxA : x ∈ A) (hxB : x ∈ B) : ↥(A ∩ B) :=
  ⟨x, show x ∈ A ∩ B from ⟨hxA, hxB⟩⟩

private def interOfRight (z : B) (hz : z.1 ∈ A) : ↥(A ∩ B) :=
  ⟨z.1, show z.1 ∈ A ∩ B from ⟨hz, z.2⟩⟩

private def swapInter : C(↥(B ∩ A), ↥(A ∩ B)) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩

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

private noncomputable def leftFunctor (hA : IsPathConnected A) (hxA : x ∈ A) (hxB : x ∈ B) :
    FundamentalGroupoid A ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  TauCeti.Groupoid.functorOfEndHom _ (leftHom hA hxA) Monoid.Coprod.inl

private noncomputable def rightFunctor (hB : IsPathConnected B) (hxA : x ∈ A) (hxB : x ∈ B) :
    FundamentalGroupoid B ⥤
      SingleObj (FundamentalGroup A (leftBase hxA) ∗ FundamentalGroup B (rightBase hxB)) :=
  TauCeti.Groupoid.functorOfEndHom _ (rightHom hB hxB) Monoid.Coprod.inr

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
  have hd : (default : FundamentalGroupoid.mk (interBase hxA hxB) ⟶ y) ≫ g = default :=
    Subsingleton.elim _ _
  simp only [overlapGauge, ← hd, Functor.map_comp, IsIso.inv_comp, Category.assoc,
    IsIso.hom_inv_id_assoc]

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
  (rightFunctor hB hxA hxB).copyObj (fun _ ↦ SingleObj.star _)
    fun z ↦ asIso (rightGauge hA hB hAB hxA hxB z)

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
  -- The base point of `B` is, definitionally, the image of the base point of the overlap.
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
  have h := overlapGauge_naturality hA hB hAB hxA hxB g
  simp only [rightOverlapFunctor, leftOverlapFunctor, Functor.comp_map] at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.comp_map,
    adjustedRightFunctor, Functor.copyObj, asIso_hom, asIso_inv, rightGauge_inter, h,
    IsIso.inv_hom_id_assoc]

private abbrev twoOpenCover (A B : Set X) : Bool → Set X := fun b => Bool.rec B A b

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
  · have hr : FundamentalGroupoid.map
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

private noncomputable def vanKampenInverse (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) : _root_.FundamentalGroup X x →*
      (_root_.FundamentalGroup A (leftBase hxA) ∗
        _root_.FundamentalGroup B (rightBase hxB)) :=
  (SingleObj.mapHom _ _).symm
    (TauCeti.Groupoid.singleObjFunctor (_root_.FundamentalGroupoid.mk x) ⋙
      gluedFunctor hCover hA hB hAB hxA hxB)

/-- The inverse restricts on each cover member to the corresponding local functor. -/
private theorem vanKampenInverse_map_subtypeVal (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (b : Bool) (hx : x ∈ twoOpenCover A B b)
    (g : _root_.FundamentalGroup (twoOpenCover A B b) ⟨x, hx⟩) :
    vanKampenInverse hCover hA hB hAB hxA hxB
        (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal _) ⟨x, hx⟩ g) =
      (localFunctor hA hB hAB hxA hxB b).map g := by
  have h := Functor.congr_hom (TauCeti.FundamentalGroupoid.map_subtypeVal_comp_glue
    (exists_twoOpenCover_mem_nhds hCover) (localFunctor hA hB hAB hxA hxB)
      (localFunctor_compatibility hA hB hAB hxA hxB) b) g
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at h
  -- `SingleObj.mapHom` has no evaluation lemma: its inverse evaluates a functor on a loop.
  change (gluedFunctor hCover hA hB hAB hxA hxB).map
      ((FundamentalGroupoid.map (ContinuousMap.subtypeVal _)).map g) = _
  exact h

private theorem vanKampenInverse_map_left (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (g : _root_.FundamentalGroup A (leftBase hxA)) :
    vanKampenInverse hCover hA hB hAB hxA hxB
        (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) (leftBase hxA) g) =
      Monoid.Coprod.inl g := by
  refine (vanKampenInverse_map_subtypeVal hCover hA hB hAB hxA hxB true hxA g).trans ?_
  simp [localFunctor, leftFunctor]

private theorem vanKampenInverse_map_right (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (g : _root_.FundamentalGroup B (rightBase hxB)) :
    vanKampenInverse hCover hA hB hAB hxA hxB
        (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) (rightBase hxB) g) =
      Monoid.Coprod.inr g := by
  refine (vanKampenInverse_map_subtypeVal hCover hA hB hAB hxA hxB false hxB g).trans ?_
  simp only [localFunctor, adjustedRightFunctor, Functor.copyObj, rightFunctor, asIso_inv,
    asIso_hom, rightGauge_base, IsIso.inv_id, Groupoid.functorOfEndHom_map, rightHom_base,
    Category.comp_id, Category.id_comp]
  -- The remaining identity is on an object of the form `(functorOfEndHom _ _ _).obj _`, which
  -- `simp` does not match against `Monoid.Coprod.inr g : SingleObj.star _ ⟶ SingleObj.star _`.
  exact Category.id_comp _

/-- The canonical homomorphism from the free product of the fundamental groups of two
subspaces to the fundamental group of the ambient space. -/
noncomputable def vanKampenLift (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B) :
    (_root_.FundamentalGroup A ⟨x, hxA⟩ ∗ _root_.FundamentalGroup B ⟨x, hxB⟩) →*
      _root_.FundamentalGroup X x :=
  Monoid.Coprod.lift
    (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩)
    (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩)

/-- `vanKampenLift` restricts on the left factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_apply_inl (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    {g : _root_.FundamentalGroup A ⟨x, hxA⟩} :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inl g) =
      _root_.FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩ g :=
  (rfl)

/-- `vanKampenLift` restricts on the right factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_apply_inr (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    {g : _root_.FundamentalGroup B ⟨x, hxB⟩} :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inr g) =
      _root_.FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩ g :=
  (rfl)

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
  · rw [← MonoidHom.range_eq_top]
    exact (Monoid.Coprod.range_lift _ _).trans <|
      TauCeti.FundamentalGroup.range_map_subtypeVal_sup_eq_top hCover hA hB
        hAB.isPathConnected hxA hxB

/-- The equivalence in the based Seifert--van Kampen theorem for two path-connected sets with
simply connected intersection. Its underlying homomorphism is `vanKampenLift`. -/
noncomputable def vanKampenEquiv (hCover : interior A ∪ interior B = univ)
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
  (rfl)

end TauCeti
