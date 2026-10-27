/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.Homotopy.CellAttachment
public import TauCeti.Topology.CWComplex.Abstract.Trans
public import TauCeti.Topology.CWComplex.Classical.CWType

/-!
# Killing the homotopy groups of a space from a given dimension on

Let `X` be a Hausdorff space with a base point `x`, and let `n ≥ 1`. Attaching `(n + 1)`-cells
along every generalized loop of dimension `n` at `x` kills `πₙ` without changing the lower homotopy
groups (`TauCeti.subsingleton_homotopyGroup_cellAttachment`). Iterating, and attaching cells of
dimension `k + 1` along every generalized loop of dimension `k` at the image of `x` for
`k = n, n + 1, …` in turn, gives an expanding sequence of spaces, the tower
`TauCeti.killingTower n X x`. Its colimit `TauCeti.killHomotopyGroups n X x` contains `X`, and

* the inclusion `X ⟶ killHomotopyGroups n X x` induces a bijection on `πₖ` for `k < n`
  (`TauCeti.bijective_homotopyGroupMap_killHomotopyGroupsIncl`);
* `πₖ` of `killHomotopyGroups n X x` at the image of `x` vanishes for `k ≥ n`
  (`TauCeti.subsingleton_homotopyGroup_killHomotopyGroups`).

For `n = 2` and a path-connected `X` this makes `killHomotopyGroups 2 X x` an Eilenberg--Mac Lane
space of type `K(π₁(X, x), 1)` containing `X`
(`TauCeti.isEilenbergMacLaneSpaceOne_killHomotopyGroups`). This is Hatcher's construction of a
`K(G, 1)` from a presentation complex of `G`, carried out here for an arbitrary Hausdorff space.

The cells attached at step `m` of the tower have dimension `m`, so the tower is a categorical
relative CW complex in Mathlib's sense, relative to `X`
(`TauCeti.killHomotopyGroupsRelativeCWComplex`). This is what controls the colimit: it is
Hausdorff, `X` and every stage are closed subspaces, the stage after step `m` is the classical
skeleton of dimension `m`, and Hatcher's Corollary 4.12 identifies the homotopy groups of the
colimit in each dimension with those of a finite stage
(`TopCat.RelativeCWComplex.surjective_homotopyGroupMap_incl_app`,
`TopCat.RelativeCWComplex.bijective_homotopyGroupMap`).

When `X` is itself a Hausdorff CW complex with no cells of dimension greater than `n`, this
relative CW structure, read classically, composes with the CW structure of `X`
(`TopCat.RelativeCWComplex.cwComplexTrans`): the cells of the tower have dimension greater than
`n`, so their boundaries meet `X` inside its skeleton below their dimension. So
`killHomotopyGroups n X x` is then a CW complex (`TauCeti.killHomotopyGroupsCWComplex`), whose
cells are those of `X` and those of the tower, and in particular it has CW type
(`TauCeti.cwType_killHomotopyGroups`).

Maps out of the colimit are built in the same way, stage by stage. Every cell of the tower is
attached along a based map, so a map `f : X ⟶ Z` into a space whose homotopy groups `πₖ(Z, f x)`
vanish for `k ≥ n` extends over each new cell, and these extensions form a cocone on the tower: `f`
extends over `killHomotopyGroups n X x`
(`TopCat.Hom.exists_killHomotopyGroupsIncl_comp_eq`). For `n ≥ 2` the extension induces on `π₁` the
map induced by `f` (`TauCeti.exists_mapOfEq_comp_killHomotopyGroupsFundamentalGroupMulEquiv`). In
particular, for `n = 2` every map from `X` into a `K(H, 1)` space extends over
`killHomotopyGroups 2 X x`, realizing the same homomorphism of fundamental groups; for a Hausdorff,
path-connected `X` that space is a `K(π₁(X, x), 1)`.

## Main definitions

* `TauCeti.killingStage n X x m`: the pointed space after the first `m` steps.
* `TauCeti.killingTower n X x`: the tower of stages, as a functor `ℕ ⥤ TopCat`.
* `TauCeti.killHomotopyGroups n X x`: its colimit, with the inclusion
  `TauCeti.killHomotopyGroupsIncl n X x` of `X`.
* `TauCeti.killHomotopyGroupsRelativeCWComplex n X x`: the relative CW structure.
* `TauCeti.killHomotopyGroupsFundamentalGroupMulEquiv n X x`: for `n ≥ 2`, the isomorphism of
  fundamental groups induced by the inclusion.
* `TauCeti.killHomotopyGroupsCWComplex n X x hX`: for a Hausdorff CW complex `X` without cells of
  dimension greater than `n`, the CW structure on the colimit, with its cells described by
  `TauCeti.killHomotopyGroupsCWComplexCellEquiv`.

## Main results

* `TauCeti.bijective_homotopyGroupMap_killHomotopyGroupsIncl`: the homotopy groups below
  dimension `n` are unchanged.
* `TauCeti.subsingleton_homotopyGroup_killHomotopyGroups`: the homotopy groups from dimension `n`
  on vanish.
* `TauCeti.isEilenbergMacLaneSpaceOne_killHomotopyGroups`: for `n = 2` and path-connected `X`,
  the colimit is a `K(π₁(X, x), 1)`.
* `TauCeti.cwType_killHomotopyGroups`: for a Hausdorff CW complex `X` without cells of dimension
  greater than `n`, the colimit has CW type.
* `TopCat.Hom.exists_killHomotopyGroupsIncl_comp_eq`: maps into a space whose homotopy groups
  vanish from dimension `n` on extend over the colimit.
* `TauCeti.exists_mapOfEq_comp_killHomotopyGroupsFundamentalGroupMulEquiv`: for `n ≥ 2`, the
  extension induces the given map on fundamental groups.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, the construction of a `K(G, 1)` from a presentation complex, and Section 4.1,
  Corollary 4.12 and Example 4.16 on killing homotopy groups by attaching cells, and Lemma 4.7
  and Proposition 1B.9 on extending maps over cells into a space without higher homotopy.
-/

public section

noncomputable section

universe u v

open CategoryTheory Limits Topology
open scoped Topology.Homotopy

namespace TauCeti

variable (n : ℕ) [NeZero n]

/-- The attaching maps of the cells attached at step `m` of the tower killing the homotopy groups
of a pointed space `(Y, y)` from dimension `n` on. At step `0` no cell is attached. At step
`k + 1` one `(k + 1)`-cell is attached along every generalized loop of dimension `k` at `y` when
`n ≤ k`, and no cell otherwise. The body is exposed so that the stages of the tower are cell
attachments by definition. -/
@[expose] def killingAttachingMaps (Y : TopCat.{u}) (y : Y) :
    (m : ℕ) → Σ ι : Type u, ι → (TopCat.diskBoundary m ⟶ Y)
  | 0 => ⟨PEmpty, PEmpty.elim⟩
  | k + 1 => ⟨Subtype fun _ : Ω^ (Fin k) Y y ↦ n ≤ k, fun q ↦
      haveI : NeZero k := ⟨((NeZero.pos n).trans_le q.2).ne'⟩
      GenLoop.diskBoundaryMap q.1⟩

/-- The stages of the tower killing the homotopy groups of `(X, x)` from dimension `n` on:
`killingStage n X x m` is the pointed space obtained from `(X, x)` by the first `m` steps, each
attaching cells along the maps `TauCeti.killingAttachingMaps`. The body is exposed so that each
stage is the cell attachment to the previous one by definition. -/
@[expose] def killingStage (X : TopCat.{u}) (x : X) : ℕ → Σ Y : TopCat.{u}, Y
  | 0 => ⟨X, x⟩
  | m + 1 =>
    ⟨cellAttachment (killingAttachingMaps n (killingStage X x m).1 (killingStage X x m).2 m).2,
      cellAttachmentIncl _ (killingStage X x m).2⟩

variable (X : TopCat.{u}) (x : X)

/-- The inclusion of each stage of the tower into the next. -/
def killingStageIncl (m : ℕ) : (killingStage n X x m).1 ⟶ (killingStage n X x (m + 1)).1 :=
  cellAttachmentIncl _

/-- The inclusion of each stage of the tower into the next is the inclusion of the cell
attachment. -/
lemma killingStageIncl_def (m : ℕ) :
    killingStageIncl n X x m =
      cellAttachmentIncl (killingAttachingMaps n (killingStage n X x m).1
        (killingStage n X x m).2 m).2 :=
  (rfl)

/-- The inclusion of each stage of the tower into the next preserves the base points. -/
@[simp]
lemma killingStageIncl_basepoint (m : ℕ) :
    killingStageIncl n X x m (killingStage n X x m).2 = (killingStage n X x (m + 1)).2 :=
  (rfl)

/-- The tower killing the homotopy groups of `(X, x)` from dimension `n` on, as a sequence of
spaces and inclusions. The body is exposed so that its objects are the stages
`TauCeti.killingStage n X x m` by definition. -/
@[expose] def killingTower : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence (killingStageIncl n X x)

/-- The space obtained from `X` by killing its homotopy groups at `x` from dimension `n` on: the
colimit of the tower `TauCeti.killingTower n X x`. The body is exposed so that the colimit
inclusions of the stages are maps into this space by definition. -/
@[expose] def killHomotopyGroups : TopCat.{u} :=
  colimit (killingTower n X x)

/-- The inclusion of `X` into `TauCeti.killHomotopyGroups n X x`: the colimit inclusion of stage
`0`. The body is exposed so that the relative CW structure below is a structure on this map. -/
@[expose] def killHomotopyGroupsIncl : X ⟶ killHomotopyGroups n X x :=
  colimit.ι (killingTower n X x) 0

/-- The step from stage `m` to stage `m + 1` of the tower is the inclusion of the cell
attachment. -/
@[simp]
lemma killingTower_map_homOfLE_succ (m : ℕ) :
    (killingTower n X x).map (homOfLE (Order.le_succ m)) = killingStageIncl n X x m :=
  Functor.ofSequence_map_homOfLE_succ _ m

/-- **The tower is a relative CW complex**: the step from stage `m` to stage `m + 1` attaches
`m`-cells, along the maps `TauCeti.killingAttachingMaps`. The body is exposed so that its stages
and their inclusions are those of the tower by definition, as recorded by
`killHomotopyGroupsRelativeCWComplex_F` and `killHomotopyGroupsRelativeCWComplex_incl_app`. -/
@[expose] def killHomotopyGroupsRelativeCWComplex :
    TopCat.RelativeCWComplex (killHomotopyGroupsIncl n X x) where
  F := killingTower n X x
  isoBot := Iso.refl _
  incl := (colimit.cocone (killingTower n X x)).ι
  isColimit := colimit.isColimit _
  fac := Category.id_comp _
  -- `Order.succ m` is `m + 1` on `ℕ`, and `Functor.ofSequence` has the stages as its objects by
  -- definition, so the source and target of step `m` of the tower are by definition those of the
  -- cell attachment, and identity isomorphisms identify the two arrows.
  attachCells m _ := (cellAttachmentAttachCells _).ofArrowIso
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      rw [killingTower_map_homOfLE_succ]
      exact (Category.id_comp _).trans (Category.comp_id _).symm))

/-- The stages of the relative CW complex are the stages of the tower. -/
lemma killHomotopyGroupsRelativeCWComplex_F :
    (killHomotopyGroupsRelativeCWComplex n X x).F = killingTower n X x :=
  (rfl)

/-- The inclusions of the stages of the relative CW complex are the colimit inclusions. -/
lemma killHomotopyGroupsRelativeCWComplex_incl_app (m : ℕ) :
    (killHomotopyGroupsRelativeCWComplex n X x).incl.app m = colimit.ι (killingTower n X x) m :=
  (rfl)

/-- The cells attached at step `m` of the relative CW complex are indexed as in
`TauCeti.killingAttachingMaps`. -/
lemma killHomotopyGroupsRelativeCWComplex_attachCells_ι (m : ℕ) :
    ((killHomotopyGroupsRelativeCWComplex n X x).attachCells m (not_isMax m)).ι =
      (killingAttachingMaps n (killingStage n X x m).1 (killingStage n X x m).2 m).1 :=
  (rfl)

/-- The base point of each stage goes to the image of `x` in the colimit. -/
@[simp]
lemma colimit_ι_killingStage_basepoint (m : ℕ) :
    colimit.ι (killingTower n X x) m (killingStage n X x m).2 = killHomotopyGroupsIncl n X x x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih, ← colimit.w (killingTower n X x) (homOfLE (Order.le_succ m)),
      killingTower_map_homOfLE_succ]
    -- `Order.succ m` is `m + 1`, and the base point of stage `m + 1` is by definition the image
    -- of the base point of stage `m`; the rewrite `ConcreteCategory.comp_apply` does not apply
    -- because the two presentations of stage `m + 1` agree only up to unfolding.
    rfl

/-- Every stage of the tower over a Hausdorff space is Hausdorff. -/
instance instT2SpaceKillingStage [T2Space X] (m : ℕ) : T2Space (killingStage n X x m).1 := by
  induction m with
  | zero => assumption
  | succ m ih => exact instT2SpaceCellAttachment _

/-- No cells of dimension at most `n` are attached in the tower. -/
lemma isEmpty_killHomotopyGroupsRelativeCWComplex_attachCells_ι {m : ℕ} (hm : m ≤ n) :
    IsEmpty ((killHomotopyGroupsRelativeCWComplex n X x).attachCells m (not_isMax m)).ι := by
  rw [killHomotopyGroupsRelativeCWComplex_attachCells_ι]
  match m, hm with
  | 0, _ => exact inferInstanceAs (IsEmpty PEmpty)
  | k + 1, hk => exact ⟨fun p ↦ absurd p.2 (by omega)⟩

/-- `TauCeti.killHomotopyGroups n X x` is Hausdorff when `X` is. -/
instance instT2SpaceKillHomotopyGroups [T2Space X] : T2Space (killHomotopyGroups n X x) :=
  (killHomotopyGroupsRelativeCWComplex n X x).t2Space

/-- The inclusion of `X` into `TauCeti.killHomotopyGroups n X x` is a closed embedding. -/
theorem isClosedEmbedding_killHomotopyGroupsIncl :
    IsClosedEmbedding (killHomotopyGroupsIncl n X x) :=
  (killHomotopyGroupsRelativeCWComplex n X x).isClosedEmbedding

/-- **Killing the homotopy groups from dimension `n` on does not change them below `n`.** For a
Hausdorff space `X`, the inclusion `X ⟶ killHomotopyGroups n X x` induces a bijection on `πₖ` at
`x`, where `k = Nat.card N < n`. -/
theorem bijective_homotopyGroupMap_killHomotopyGroupsIncl [T2Space X] {N : Type v} [Finite N]
    (hN : Nat.card N < n) :
    Function.Bijective
      (HomotopyGroup.map (N := N) (x := x) (killHomotopyGroupsIncl n X x).hom rfl) :=
  (killHomotopyGroupsRelativeCWComplex n X x).bijective_homotopyGroupMap
    (fun _ hm ↦ isEmpty_killHomotopyGroupsRelativeCWComplex_attachCells_ι n X x hm) hN x

/-- **The homotopy groups of `killHomotopyGroups n X x` vanish from dimension `n` on**, at the
image of `x`, for a Hausdorff space `X`. -/
theorem subsingleton_homotopyGroup_killHomotopyGroups [T2Space X] {k : ℕ} (hk : n ≤ k) :
    Subsingleton (π_ k (killHomotopyGroups n X x) (killHomotopyGroupsIncl n X x x)) := by
  have : NeZero k := ⟨((NeZero.pos n).trans_le hk).ne'⟩
  -- Step `k + 1` attaches a cell along every generalized loop of dimension `k`, killing `πₖ`.
  have hkill : Subsingleton (π_ k (killingStage n X x (k + 2)).1 (killingStage n X x (k + 2)).2) :=
    subsingleton_homotopyGroup_cellAttachment (X := (killingStage n X x (k + 1)).1)
      (p := fun q : Subtype fun _ : Ω^ (Fin k) _ (killingStage n X x (k + 1)).2 ↦ n ≤ k ↦ q.1) (by
        refine eq_top_iff.2 fun g _ ↦ Subgroup.subset_normalClosure ?_
        induction g using Quotient.inductionOn with
        | h q => exact ⟨⟨q, hk⟩, rfl⟩)
  -- The stage after step `k + 1` carries the cells of dimension at most `k + 1`, so it is
  -- surjective on `πₖ`.
  have hsurj := (killHomotopyGroupsRelativeCWComplex n X x).surjective_homotopyGroupMap_incl_app
    (n := k + 1) (N := Fin k) (by simp) (killingStage n X x (k + 2)).2
  rw [← colimit_ι_killingStage_basepoint n X x (k + 2)]
  exact Function.Surjective.subsingleton (α := π_ k (killingStage n X x (k + 2)).1 _) hsurj

/-- `TauCeti.killHomotopyGroups n X x` is path-connected when `X` is Hausdorff and path-connected:
attaching cells of positive dimension creates no new path components. -/
instance instPathConnectedSpaceKillHomotopyGroups [T2Space X] [PathConnectedSpace X] :
    PathConnectedSpace (killHomotopyGroups n X x) := by
  have hsurj := (bijective_homotopyGroupMap_killHomotopyGroupsIncl n X x (N := Fin 0)
    (by simpa using NeZero.pos n)).2
  have : Subsingleton (π_ 0 X x) := HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  have : Subsingleton (π_ 0 (killHomotopyGroups n X x) (killHomotopyGroupsIncl n X x x)) :=
    hsurj.subsingleton
  have e := HomotopyGroup.pi0EquivZerothHomotopy (x := killHomotopyGroupsIncl n X x x)
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨⟦killHomotopyGroupsIncl n X x x⟧⟩, e.symm.subsingleton⟩

/-- For `n ≥ 2`, the inclusion of `X` into `TauCeti.killHomotopyGroups n X x` induces an
isomorphism of fundamental groups at `x`. -/
def killHomotopyGroupsFundamentalGroupMulEquiv [T2Space X] (hn : 1 < n) :
    FundamentalGroup X x ≃*
      FundamentalGroup (killHomotopyGroups n X x) (killHomotopyGroupsIncl n X x x) :=
  MulEquiv.ofBijective (FundamentalGroup.mapOfEq (killHomotopyGroupsIncl n X x).hom rfl)
    ((HomotopyGroup.bijective_map_iff_bijective_mapOfEq _ rfl).1
      (bijective_homotopyGroupMap_killHomotopyGroupsIncl n X x (N := Fin 1) (by simpa using hn)))

/-- The isomorphism of fundamental groups is the map induced by the inclusion of `X`. -/
@[simp]
lemma killHomotopyGroupsFundamentalGroupMulEquiv_apply [T2Space X] (hn : 1 < n)
    (g : FundamentalGroup X x) :
    killHomotopyGroupsFundamentalGroupMulEquiv n X x hn g =
      FundamentalGroup.mapOfEq (killHomotopyGroupsIncl n X x).hom rfl g :=
  (rfl)

/-- **Killing the higher homotopy groups of a path-connected space gives a `K(π₁, 1)`.** For a
Hausdorff, path-connected space `X`, the space `TauCeti.killHomotopyGroups 2 X x` obtained by
attaching cells of dimension at least `3` is aspherical, and the inclusion of `X` identifies its
fundamental group with `π₁(X, x)`. -/
theorem isEilenbergMacLaneSpaceOne_killHomotopyGroups [T2Space X] [PathConnectedSpace X] :
    IsEilenbergMacLaneSpaceOne (FundamentalGroup X x) (killHomotopyGroups 2 X x)
      (killHomotopyGroupsIncl 2 X x x) :=
  isEilenbergMacLaneSpaceOne_iff.2
    ⟨.mk inferInstance fun k ↦ subsingleton_homotopyGroup_killHomotopyGroups 2 X x (by omega),
      ⟨(killHomotopyGroupsFundamentalGroupMulEquiv 2 X x one_lt_two).symm⟩⟩

/-! ### The CW structure on the colimit -/

section CWComplex

open Topology Topology.RelCWComplex

variable [T2Space X] [CWComplex (Set.univ : Set X)]
  (hX : ∀ m, n < m → IsEmpty (cell (Set.univ : Set X) m))

include hX in
/-- **The colimit of the tower is a CW complex.** If `X` is a Hausdorff CW complex all of whose
cells have dimension at most `n`, then `TauCeti.killHomotopyGroups n X x` is a CW complex. Its
`m`-cells are the `m`-cells of `X`, included by `TauCeti.killHomotopyGroupsIncl n X x`, and the
cells attached at step `m` of the tower, which all have dimension greater than `n`
(`TauCeti.killHomotopyGroupsCWComplexCellEquiv`). -/
@[instance_reducible]
def killHomotopyGroupsCWComplex : CWComplex (Set.univ : Set (killHomotopyGroups n X x)) :=
  (killHomotopyGroupsRelativeCWComplex n X x).cwComplexTrans hX fun _ hm ↦
    isEmpty_killHomotopyGroupsRelativeCWComplex_attachCells_ι n X x (Nat.le_of_lt_succ hm)

/-- The `m`-cells of `TauCeti.killHomotopyGroupsCWComplex` are the `m`-cells of `X` together with
the cells attached at step `m` of the tower. -/
def killHomotopyGroupsCWComplexCellEquiv (m : ℕ) :
    @cell _ _ (Set.univ : Set (killHomotopyGroups n X x)) ∅
      (killHomotopyGroupsCWComplex n X x hX).instRelCWComplex m ≃
      cell (Set.univ : Set X) m ⊕
        ((killHomotopyGroupsRelativeCWComplex n X x).attachCells m (not_isMax m)).ι :=
  TopCat.RelativeCWComplex.cwComplexTransCellEquiv _ _ _ m

/-- The characteristic map of an `m`-cell of `X`, as a cell of
`TauCeti.killHomotopyGroupsCWComplex`, is its characteristic map in `X` followed by the inclusion
`TauCeti.killHomotopyGroupsIncl n X x`. -/
@[simp]
lemma coe_map_killHomotopyGroupsCWComplexCellEquiv_symm_inl (m : ℕ)
    (i : cell (Set.univ : Set X) m) :
    ⇑(@map _ _ (Set.univ : Set (killHomotopyGroups n X x)) ∅
      (killHomotopyGroupsCWComplex n X x hX).instRelCWComplex m
        ((killHomotopyGroupsCWComplexCellEquiv n X x hX m).symm (.inl i))) =
      killHomotopyGroupsIncl n X x ∘ map m i :=
  TopCat.RelativeCWComplex.coe_map_cwComplexTransCellEquiv_symm_inl _ _ _ m i

/-- The characteristic map of a cell attached at step `m` of the tower, as a cell of
`TauCeti.killHomotopyGroupsCWComplex`, is the inclusion of the attached disk, read on the closed
unit ball of the sup norm through the radial homeomorphism `TauCeti.diskHomeomorphClosedBall`. -/
@[simp]
lemma map_killHomotopyGroupsCWComplexCellEquiv_symm_inr (m : ℕ)
    (i : ((killHomotopyGroupsRelativeCWComplex n X x).attachCells m (not_isMax m)).ι)
    (y : Metric.closedBall (0 : Fin m → ℝ) 1) :
    @map _ _ (Set.univ : Set (killHomotopyGroups n X x)) ∅
      (killHomotopyGroupsCWComplex n X x hX).instRelCWComplex m
        ((killHomotopyGroupsCWComplexCellEquiv n X x hX m).symm (.inr i)) y =
      (⟨m, not_isMax m, i⟩ : (killHomotopyGroupsRelativeCWComplex n X x).Cells).ι
        ((diskHomeomorphClosedBall m).symm y) :=
  TopCat.RelativeCWComplex.map_cwComplexTransCellEquiv_symm_inr _ _ _ m i y

include hX in
/-- If `X` is a Hausdorff CW complex all of whose cells have dimension at most `n`, then
`TauCeti.killHomotopyGroups n X x` has CW type. -/
theorem cwType_killHomotopyGroups : CWType (killHomotopyGroups n X x) :=
  letI := killHomotopyGroupsCWComplex n X x hX
  inferInstance

end CWComplex

/-! ### Extending maps over the tower -/

section Extension

variable {n X x} {Z : TopCat.{u}}

/-- At every step of the tower the cells are attached along based maps: the composite of an
attaching map at the base point `y` with a based map `g : Y ⟶ Z` is null-homotopic when the
homotopy group of `Z` in the dimension of the attaching spheres vanishes. -/
private lemma nullhomotopic_killingAttachingMaps_comp {Y : TopCat.{u}} {y : Y} {m : ℕ}
    (g : Y ⟶ Z) (hZ : ∀ k, m = k + 1 → n ≤ k → Subsingleton (π_ k Z (g y)))
    (i : (killingAttachingMaps n Y y m).1) :
    ((killingAttachingMaps n Y y m).2 i ≫ g).hom.Nullhomotopic :=
  -- At step `0` no cell is attached, so only the successor case remains.
  match m, i with
  | k + 1, q => by
    have : NeZero k := ⟨((NeZero.pos n).trans_le q.2).ne'⟩
    -- The image of the attaching loop is trivial in `πₖ(Z, g y)`.
    exact (HomotopyGroup.map_mk_eq_one_iff_nullhomotopic_diskBoundaryMap_comp g rfl q.1).1
      ((hZ k rfl q.2).elim _ _)

/-- **A based map extends over one step of the tower.** If the homotopy group of `Z` vanishes in
the dimension of the spheres attached at step `m`, every map `g` out of stage `m` extends over
stage `m + 1`. -/
theorem _root_.TopCat.Hom.exists_killingStageIncl_comp_eq {m : ℕ}
    (g : (killingStage n X x m).1 ⟶ Z)
    (hZ : ∀ k, m = k + 1 → n ≤ k → Subsingleton (π_ k Z (g (killingStage n X x m).2))) :
    ∃ g' : (killingStage n X x (m + 1)).1 ⟶ Z, killingStageIncl n X x m ≫ g' = g := by
  choose F hF using fun i ↦
    (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq _).1
      (nullhomotopic_killingAttachingMaps_comp (m := m) g hZ i)
  exact ⟨cellAttachmentLift _ g F fun i ↦ (hF i).symm, cellAttachmentIncl_lift _ _ _ _⟩

/-- The extensions of a map `f : X ⟶ Z` over the successive stages of the tower, each extending
the previous one by `TopCat.Hom.exists_killingStageIncl_comp_eq`. They all send the base point of
their stage to `f x`. -/
private def killingStageExtension (f : X ⟶ Z) (hZ : ∀ k, n ≤ k → Subsingleton (π_ k Z (f x))) :
    (m : ℕ) → {g : (killingStage n X x m).1 ⟶ Z // g (killingStage n X x m).2 = f x}
  | 0 => ⟨f, rfl⟩
  | m + 1 =>
    have hm := (killingStageExtension f hZ m).2
    have h := (killingStageExtension f hZ m).1.exists_killingStageIncl_comp_eq
      (by rw [hm]; exact fun k _ ↦ hZ k)
    ⟨h.choose, by
      rw [← killingStageIncl_basepoint, ← ConcreteCategory.comp_apply, h.choose_spec, hm]⟩

/-- Each extension in `TauCeti.killingStageExtension` extends the previous one. -/
private lemma killingStageIncl_comp_killingStageExtension (f : X ⟶ Z)
    (hZ : ∀ k, n ≤ k → Subsingleton (π_ k Z (f x))) (m : ℕ) :
    killingStageIncl n X x m ≫ (killingStageExtension f hZ (m + 1)).1 =
      (killingStageExtension f hZ m).1 :=
  ((killingStageExtension f hZ m).1.exists_killingStageIncl_comp_eq
    (by rw [(killingStageExtension f hZ m).2]; exact fun k _ ↦ hZ k)).choose_spec

/-- **Maps into a space without homotopy from dimension `n` on extend over
`TauCeti.killHomotopyGroups n X x`.** If the homotopy groups `πₖ(Z, f x)` vanish for every
`k ≥ n`, then `f : X ⟶ Z` extends along the inclusion `X ⟶ killHomotopyGroups n X x`. Only the
homotopy groups at the base point `f x` enter, because every cell of the tower is attached along
a based map. -/
theorem _root_.TopCat.Hom.exists_killHomotopyGroupsIncl_comp_eq (f : X ⟶ Z)
    (hZ : ∀ k, n ≤ k → Subsingleton (π_ k Z (f x))) :
    ∃ F : killHomotopyGroups n X x ⟶ Z, killHomotopyGroupsIncl n X x ≫ F = f := by
  -- The extensions over the stages are compatible, so they form a cocone on the tower.
  let c : Cocone (killingTower n X x) :=
    ⟨Z, NatTrans.ofSequence (fun m ↦ (killingStageExtension f hZ m).1) fun m ↦ by
      simp only [killingTower, Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (killingStageIncl_comp_killingStageExtension f hZ m).trans (Category.comp_id _).symm⟩
  exact ⟨colimit.desc _ c, colimit.ι_desc c 0⟩

/-- **The extension realizes the map on fundamental groups.** For `n ≥ 2` and a Hausdorff space
`X`, if the homotopy groups `πₖ(Z, f x)` vanish for every `k ≥ n`, then `f : X ⟶ Z` extends to a
based map `F` out of `TauCeti.killHomotopyGroups n X x` that induces on `π₁` the map induced by
`f`, read through the isomorphism `TauCeti.killHomotopyGroupsFundamentalGroupMulEquiv`. -/
theorem exists_mapOfEq_comp_killHomotopyGroupsFundamentalGroupMulEquiv [T2Space X] (hn : 1 < n)
    (f : X ⟶ Z) (hZ : ∀ k, n ≤ k → Subsingleton (π_ k Z (f x))) :
    ∃ (F : killHomotopyGroups n X x ⟶ Z) (hF : F (killHomotopyGroupsIncl n X x x) = f x),
      (FundamentalGroup.mapOfEq F.hom hF).comp
          (killHomotopyGroupsFundamentalGroupMulEquiv n X x hn).toMonoidHom =
        FundamentalGroup.mapOfEq f.hom rfl := by
  obtain ⟨F, hF⟩ := f.exists_killHomotopyGroupsIncl_comp_eq hZ
  have hFx : F (killHomotopyGroupsIncl n X x x) = f x := by
    rw [← ConcreteCategory.comp_apply, hF]
  refine ⟨F, hFx, MonoidHom.ext fun g ↦ ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    killHomotopyGroupsFundamentalGroupMulEquiv_apply, TauCeti.FundamentalGroup.mapOfEq_comp]
  exact TauCeti.FundamentalGroup.mapOfEq_congr (congrArg TopCat.Hom.hom hF) _ _ g

end Extension

end TauCeti
