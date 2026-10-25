/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Step
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.OpenCell
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# CW approximation of path-connected spaces

Every path-connected space `X` is the target of a weak homotopy equivalence from a CW complex
(Hatcher, Proposition 4.13). This file builds one, `TauCeti.cwApproximationMap X x`, out of the
CW complex `TauCeti.cwApproximation X x`, by attaching cells dimension by dimension, starting from
a point `x` of `X`. The tower of stages starts with the empty space, and:

* stage `1` is a single `0`-cell, sent to `x`;
* stage `2` attaches a circle at the vertex for every loop of `X` at `x`, sent onto that loop, so
  that the map is surjective on `π₁`;
* stage `n + 2`, for `n ≥ 1`, is the inductive step `TauCeti.cwApproximationStep` applied to stage
  `n + 1`: it attaches `(n + 1)`-cells killing the kernel of the map on `πₙ`, and
  `(n + 1)`-spheres sent onto representatives of every class of `πₙ₊₁(X, x)`.

So step `m` of the tower attaches `m`-cells, and the tower is a CW complex in Mathlib's categorical
sense (`TauCeti.cwApproximationCWComplex`). The space `TauCeti.cwApproximation X x` is its colimit.
It is Hausdorff, has CW type (`TauCeti.cwType_cwApproximation`), and is path-connected, for every
`X`.

Let `k ≥ 1`. Stage `k + 2` carries the cells of dimension at most `k + 1`, so it maps onto `πₖ` of
the colimit (Hatcher, Corollary 4.12). Its map to `X` is injective on `πₖ` by the inductive step,
and surjective on `πₖ` because it extends the map of stage `k + 1`. So the map from the colimit is
bijective on `πₖ`, and it is a weak homotopy equivalence when `X` is path-connected
(`TauCeti.isWeakHomotopyEquivalence_cwApproximationMap`).

## Main definitions

* `TauCeti.cwApproximationStage X x m`: stage `m + 1` of the tower, with its base point and its
  map to `X`.
* `TauCeti.cwApproximationTower X x`: the tower, as a functor `ℕ ⥤ TopCat`, starting with the empty
  space.
* `TauCeti.cwApproximation X x`: its colimit, with the map `TauCeti.cwApproximationMap X x` to `X`
  and the base point `TauCeti.cwApproximationBasepoint X x`, which the map sends to `x`.
* `TauCeti.cwApproximationCWComplex X x`: the categorical CW structure of the colimit.

## Main results

* `TauCeti.cwType_cwApproximation`: the colimit has CW type.
* `TauCeti.isWeakHomotopyEquivalence_cwApproximationMap`: for path-connected `X`, the map to `X`
  is a weak homotopy equivalence.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.13 (CW approximation) and Corollary 4.12.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Topology HomotopicalAlgebra
open scoped Topology.Homotopy unitInterval

namespace TauCeti

variable (X : TopCat.{u}) (x : X)

/-- The attaching map of the single `0`-cell of the CW approximation: the empty map out of the
empty boundary of the `0`-disk into the empty space. -/
@[expose] def cwApproximationVertexAttachingMap :
    PUnit.{u + 1} → (TopCat.diskBoundary.{u} 0 ⟶ ⊥_ TopCat.{u}) :=
  fun _ ↦ TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩

/-- The attaching maps of the circles of the CW approximation: the constant map at the vertex `y`,
once for every loop of `X` at the image of `y` under `g`. -/
@[expose] def cwApproximationCircleAttachingMap {Y : TopCat.{u}} (g : Y ⟶ X) (y : Y) :
    Ω^ (Fin 1) X (g y) → (TopCat.diskBoundary.{u} 1 ⟶ Y) :=
  fun _ ↦ TopCat.ofHom (ContinuousMap.const _ y)

/-- The stages of the tower of the CW approximation of `X` built from `x`, each with a base point
and a map to `X`. `cwApproximationStage X x m` is stage `m + 1` of the tower, which starts with the
empty space:

* stage `1` is a single `0`-cell, sent to `x`;
* stage `2` attaches a circle at the vertex for every loop of `X` at the image of the vertex, sent
  onto that loop;
* stage `n + 2` is `TauCeti.cwApproximationStep` applied to stage `n + 1`, for `n ≥ 1`.

The body is exposed so that each stage is a cell attachment to the previous one by definition. -/
@[expose] def cwApproximationStage : ℕ → Σ Y : TopCat.{u}, Y × (Y ⟶ X)
  | 0 => ⟨cellAttachment cwApproximationVertexAttachingMap,
      cellAttachmentCell cwApproximationVertexAttachingMap PUnit.unit
        (ULift.up ⟨0, Metric.mem_closedBall_self zero_le_one⟩),
      cellAttachmentLift _ (initial.to X) (fun _ ↦ TopCat.ofHom (ContinuousMap.const _ x))
        fun _ ↦ by ext s; exact isEmptyElim s⟩
  | 1 =>
    let s := cwApproximationStage 0
    ⟨cellAttachment (cwApproximationCircleAttachingMap X s.2.2 s.2.1),
      cellAttachmentIncl _ s.2.1,
      cellAttachmentLift _ s.2.2 GenLoop.diskMap
        fun γ ↦ (GenLoop.diskBoundaryInclusion_comp_diskMap γ).symm⟩
  | k + 2 =>
    let s := cwApproximationStage (k + 1)
    ⟨cwApproximationStep s.2.2 s.2.1 (k + 1), cwApproximationStepIncl _ _ _ s.2.1,
      cwApproximationStepMap _ _ _⟩

/-- The inclusion of each stage of the tower into the next. The body is exposed so that the tower
is a sequence of cell attachments by definition. -/
@[expose] def cwApproximationStageIncl :
    (m : ℕ) → ((cwApproximationStage X x m).1 ⟶ (cwApproximationStage X x (m + 1)).1)
  | 0 => cellAttachmentIncl _
  | _ + 1 => cwApproximationStepIncl _ _ _

/-- The inclusion of each stage into the next preserves the base points. -/
@[simp]
lemma cwApproximationStageIncl_basepoint (m : ℕ) :
    cwApproximationStageIncl X x m (cwApproximationStage X x m).2.1 =
      (cwApproximationStage X x (m + 1)).2.1 := by
  cases m <;> rfl

/-- The map of each stage to `X` extends the map of the previous stage. -/
@[reassoc (attr := simp)]
lemma cwApproximationStageIncl_comp (m : ℕ) :
    cwApproximationStageIncl X x m ≫ (cwApproximationStage X x (m + 1)).2.2 =
      (cwApproximationStage X x m).2.2 := by
  cases m with
  | zero => exact cellAttachmentIncl_lift _ _ _ _
  | succ m => exact cwApproximationStepIncl_comp_cwApproximationStepMap _ _ _

/-- The tower of the CW approximation of `X` built from `x`, as a functor `ℕ ⥤ TopCat`: the empty
space, followed by the stages `TauCeti.cwApproximationStage X x` and their inclusions. The body is
exposed so that its objects are the stages by definition. -/
@[expose] def cwApproximationTower : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (X := fun | 0 => ⊥_ TopCat.{u} | m + 1 => (cwApproximationStage X x m).1)
    fun | 0 => initial.to _ | m + 1 => cwApproximationStageIncl X x m

/-- The step from stage `m + 1` to stage `m + 2` of the tower is the inclusion of the stages. -/
@[simp]
lemma cwApproximationTower_map_homOfLE_succ (m : ℕ) :
    (cwApproximationTower X x).map (homOfLE (Order.le_succ (m + 1))) =
      cwApproximationStageIncl X x m :=
  Functor.ofSequence_map_homOfLE_succ _ (m + 1)

/-- The CW approximation of `X` built from `x`: the colimit of the tower
`TauCeti.cwApproximationTower X x`. The body is exposed so that the colimit inclusions of the
stages are maps into this space by definition. -/
@[expose] def cwApproximation : TopCat.{u} :=
  colimit (cwApproximationTower X x)

/-- The maps of the tower to `X`. -/
private def towerToX : (m : ℕ) → ((cwApproximationTower X x).obj m ⟶ X)
  | 0 => initial.to X
  | m + 1 => (cwApproximationStage X x m).2.2

/-- The maps of the stages to `X`, as a cocone on the tower. -/
private def towerCocone : Cocone (cwApproximationTower X x) where
  pt := X
  ι := NatTrans.ofSequence (towerToX X x) fun m ↦ by
    cases m with
    | zero => exact initial.hom_ext _ _
    | succ m =>
      -- `Order.succ (m + 1)` is `m + 2` on `ℕ`, so the tower lemma applies up to unfolding.
      refine (congrArg (· ≫ towerToX X x (m + 2))
        (cwApproximationTower_map_homOfLE_succ X x m)).trans ?_
      exact (cwApproximationStageIncl_comp X x m).trans (Category.comp_id _).symm

/-- The map from the CW approximation `TauCeti.cwApproximation X x` to `X`, induced by the maps of
the stages. -/
def cwApproximationMap : cwApproximation X x ⟶ X :=
  colimit.desc _ (towerCocone X x)

/-- On each stage, the map `TauCeti.cwApproximationMap X x` is the map of the stage. -/
@[simp, reassoc]
lemma colimit_ι_cwApproximationMap (m : ℕ) :
    colimit.ι (cwApproximationTower X x) (m + 1) ≫ cwApproximationMap X x =
      (cwApproximationStage X x m).2.2 :=
  colimit.ι_desc (towerCocone X x) (m + 1)

/-- The step `m` of the tower attaches `m`-cells. -/
private def towerAttachCells : (m : ℕ) →
    AttachCells.{u} (TopCat.RelativeCWComplex.basicCell m)
      ((cwApproximationTower X x).map (homOfLE (Order.le_succ m)))
  | 0 => (cellAttachmentAttachCells cwApproximationVertexAttachingMap).ofArrowIso
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (initial.hom_ext _ _))
  | 1 => (cellAttachmentAttachCells _).ofArrowIso
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
        rw [cwApproximationTower_map_homOfLE_succ]
        exact (Category.id_comp _).trans (Category.comp_id _).symm))
  | k + 2 => (cellAttachmentAttachCells _).ofArrowIso
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
        rw [cwApproximationTower_map_homOfLE_succ]
        exact (Category.id_comp _).trans (Category.comp_id _).symm))

/-- **The CW approximation is a CW complex**, in Mathlib's categorical sense: step `m` of its tower
attaches `m`-cells to the previous stage. -/
def cwApproximationCWComplex : TopCat.CWComplex (cwApproximation X x) where
  F := cwApproximationTower X x
  isoBot := Iso.refl _
  incl := (colimit.cocone (cwApproximationTower X x)).ι
  isColimit := colimit.isColimit _
  fac := initial.hom_ext _ _
  attachCells m _ := towerAttachCells X x m

/-- `TauCeti.cwApproximation X x` is Hausdorff. -/
instance instT2SpaceCWApproximation : T2Space (cwApproximation X x) :=
  (cwApproximationCWComplex X x).t2Space

/-- **The CW approximation has CW type.** -/
instance cwType_cwApproximation : CWType (cwApproximation X x) :=
  (cwApproximationCWComplex X x).cwType

/-- Every stage of the tower is Hausdorff, as a closed subspace of the colimit. -/
instance instT2SpaceCWApproximationStage (m : ℕ) :
    T2Space (cwApproximationStage X x m).1 :=
  have h : IsClosedEmbedding (Y := cwApproximation X x)
      (colimit.ι (cwApproximationTower X x) (m + 1)) :=
    (cwApproximationCWComplex X x).isClosedEmbedding_incl_app (m + 1)
  h.isEmbedding.t2Space

/-- The map of each stage to `X` sends the base point of the stage to `x`. -/
@[simp]
lemma cwApproximationStage_map_basepoint (m : ℕ) :
    (cwApproximationStage X x m).2.2 (cwApproximationStage X x m).2.1 = x := by
  induction m with
  | zero => exact ConcreteCategory.congr_hom (cellAttachmentCell_lift _ _ _ _ PUnit.unit) _
  | succ m ih =>
    rw [← cwApproximationStageIncl_basepoint, ← ConcreteCategory.comp_apply,
      cwApproximationStageIncl_comp, ih]

/-- The base point of the CW approximation `TauCeti.cwApproximation X x`: the image of the vertex
of stage `1`. -/
def cwApproximationBasepoint : cwApproximation X x :=
  colimit.ι (cwApproximationTower X x) 1 (cwApproximationStage X x 0).2.1

/-- The base point of each stage goes to the base point of the CW approximation. -/
@[simp]
lemma colimit_ι_cwApproximationBasepoint (m : ℕ) :
    colimit.ι (cwApproximationTower X x) (m + 1) (cwApproximationStage X x m).2.1 =
      cwApproximationBasepoint X x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih, ← colimit.w (cwApproximationTower X x) (homOfLE (Order.le_succ (m + 1))),
      cwApproximationTower_map_homOfLE_succ, ← cwApproximationStageIncl_basepoint]
    -- Both sides evaluate the composite of the stage inclusion and the colimit inclusion.
    rfl

/-- The map `TauCeti.cwApproximationMap X x` sends the base point of the CW approximation to
`x`. -/
@[simp]
lemma cwApproximationMap_cwApproximationBasepoint :
    cwApproximationMap X x (cwApproximationBasepoint X x) = x :=
  (ConcreteCategory.congr_hom (colimit_ι_cwApproximationMap X x 0) _).trans
    (cwApproximationStage_map_basepoint X x 0)

/-- The first stage, a single `0`-cell, is a point. -/
private instance instSubsingletonCWApproximationStageZero :
    Subsingleton (cwApproximationStage X x 0).1 := by
  have : Subsingleton (TopCat.disk.{u} 0) := (diskHomeomorphCube.{u} 0).injective.subsingleton
  -- Every point lies in the cell, since the old space is empty.
  have h := (cellAttachmentAttachCells
    cwApproximationVertexAttachingMap).compl_range_eq_iUnion_image_cell
  rw [Set.range_eq_empty, Set.compl_empty] at h
  have hsurj (a : (cwApproximationStage X x 0).1) :
      ∃ d, cellAttachmentCell cwApproximationVertexAttachingMap PUnit.unit d = a := by
    obtain ⟨i, d, -, hd⟩ := Set.mem_iUnion.1 (h.subset (Set.mem_univ a))
    exact ⟨d, (cellAttachmentAttachCells_cell _ i).symm ▸ hd⟩
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨d, rfl⟩ := hsurj a
  obtain ⟨d', rfl⟩ := hsurj b
  rw [Subsingleton.elim d d']

/-- **The CW approximation is path-connected**: its only `0`-cell is the vertex. -/
instance instPathConnectedSpaceCWApproximation : PathConnectedSpace (cwApproximation X x) := by
  -- The vertex carries the cells of dimension at most `0`, so it maps onto `π₀` of the colimit.
  have hsurj := (cwApproximationCWComplex X x).surjective_homotopyGroupMap_incl_app
    (n := 0) (N := Fin 0) (by simp) (cwApproximationStage X x 0).2.1
  have : Subsingleton (π_ 0 (cwApproximation X x) (cwApproximationBasepoint X x)) := by
    rw [← colimit_ι_cwApproximationBasepoint X x 0]
    exact Function.Surjective.subsingleton (α := π_ 0 (cwApproximationStage X x 0).1 _) hsurj
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨⟦cwApproximationBasepoint X x⟧⟩,
      (HomotopyGroup.pi0EquivZerothHomotopy (x := cwApproximationBasepoint X x)).symm.subsingleton⟩

/-- Stage `k + 2` of the tower maps onto `πₖ₊₁(X)`: stage `2` by its circles, and stage `k + 3` by
its spheres. -/
private lemma surjective_homotopyGroupMap_cwApproximationStage (k : ℕ) {b : X}
    (h : (cwApproximationStage X x (k + 1)).2.2 (cwApproximationStage X x (k + 1)).2.1 = b) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin (k + 1)) (cwApproximationStage X x (k + 1)).2.2.hom h) := by
  cases k with
  | zero =>
    obtain rfl := h.symm.trans (ConcreteCategory.congr_hom (cellAttachmentIncl_lift _ _ _ _) _)
    exact Quotient.ind fun γ ↦ mk_mem_range_homotopyGroupMap_of_cellAttachmentCell_comp _ rfl _ _ γ
      (cellAttachmentCell_lift _ _ _ _ γ)
  | succ k =>
    obtain rfl := h.symm.trans (cwApproximationStepMap_cwApproximationStepIncl_apply _ _ _ _)
    exact surjective_homotopyGroupMap_cwApproximationStepMap_succ _ _ _

/-- Stage `k + 3` of the tower still maps onto `πₖ₊₁(X)`, since its map extends that of stage
`k + 2`. -/
private lemma surjective_homotopyGroupMap_cwApproximationStage_succ (k : ℕ) {b : X}
    (h : (cwApproximationStage X x (k + 2)).2.2 (cwApproximationStage X x (k + 2)).2.1 = b) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin (k + 1)) (cwApproximationStage X x (k + 2)).2.2.hom h) := by
  have h' : (cwApproximationStage X x (k + 1)).2.2 (cwApproximationStage X x (k + 1)).2.1 = b :=
    (ConcreteCategory.congr_hom (cwApproximationStageIncl_comp X x (k + 1)) _).symm.trans h
  have hcomp : HomotopyGroup.map (N := Fin (k + 1)) (cwApproximationStage X x (k + 2)).2.2.hom h ∘
      HomotopyGroup.map (cwApproximationStageIncl X x (k + 1)).hom
        (cwApproximationStageIncl_basepoint X x (k + 1)) =
      HomotopyGroup.map (cwApproximationStage X x (k + 1)).2.2.hom h' :=
    HomotopyGroup.map_comp_map_of_comp_eq
      (congrArg TopCat.Hom.hom (cwApproximationStageIncl_comp X x (k + 1))) _ _ _
  exact Function.Surjective.of_comp
    (hcomp ▸ surjective_homotopyGroupMap_cwApproximationStage X x k h')

/-- The map of stage `k + 3` of the tower to `X` is injective on `πₖ₊₁`: its `(k + 2)`-cells kill
the kernel. -/
private lemma injective_homotopyGroupMap_cwApproximationStage (k : ℕ) {b : X}
    (h : (cwApproximationStage X x (k + 2)).2.2 (cwApproximationStage X x (k + 2)).2.1 = b) :
    Function.Injective
      (HomotopyGroup.map (N := Fin (k + 1)) (cwApproximationStage X x (k + 2)).2.2.hom h) := by
  obtain rfl := h.symm.trans (cwApproximationStepMap_cwApproximationStepIncl_apply _ _ _ _)
  exact injective_homotopyGroupMap_cwApproximationStepMap _ _ _

/-- **CW approximation** (Hatcher, Proposition 4.13). For a path-connected space `X`, the map
`TauCeti.cwApproximationMap X x` from the CW complex `TauCeti.cwApproximation X x` to `X` is a weak
homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_cwApproximationMap [PathConnectedSpace X] :
    (cwApproximationMap X x).hom.IsWeakHomotopyEquivalence := by
  refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective
    (cwApproximationBasepoint X x)).2 fun j ↦ ?_
  cases j with
  | zero =>
    -- Both spaces are path-connected, so both sets of path components are points.
    have : Subsingleton (π_ 0 X (cwApproximationMap X x (cwApproximationBasepoint X x))) :=
      HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    have : Subsingleton (π_ 0 (cwApproximation X x) (cwApproximationBasepoint X x)) :=
      HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨⟦GenLoop.const⟧, Subsingleton.elim _ _⟩⟩
  | succ k =>
    -- Stage `k + 3` carries the cells of dimension at most `k + 2`, so it maps onto `πₖ₊₁` of the
    -- colimit, and its map to `X` is bijective on `πₖ₊₁`.
    rw [← colimit_ι_cwApproximationBasepoint X x (k + 2)]
    have hsurj := (cwApproximationCWComplex X x).surjective_homotopyGroupMap_incl_app
      (n := k + 2) (N := Fin (k + 1)) (by simp) (cwApproximationStage X x (k + 2)).2.1
    have hcomp : HomotopyGroup.map (N := Fin (k + 1)) (cwApproximationMap X x).hom rfl ∘
        HomotopyGroup.map (x := (cwApproximationStage X x (k + 2)).2.1)
          (colimit.ι (cwApproximationTower X x) (k + 2 + 1)).hom rfl =
        HomotopyGroup.map (cwApproximationStage X x (k + 2)).2.2.hom
          (ConcreteCategory.congr_hom (colimit_ι_cwApproximationMap X x (k + 2)) _).symm :=
      HomotopyGroup.map_comp_map_of_comp_eq
        (congrArg TopCat.Hom.hom (colimit_ι_cwApproximationMap X x (k + 2))) _ _ _
    exact ⟨Function.Injective.of_comp_right
        (hcomp ▸ injective_homotopyGroupMap_cwApproximationStage X x k _) hsurj,
      Function.Surjective.of_comp
        (hcomp ▸ surjective_homotopyGroupMap_cwApproximationStage_succ X x k _)⟩

end TauCeti
