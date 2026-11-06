/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Classical.Sigma

/-!
# The disk as a relative CW complex over its boundary

The disk `TopCat.disk n` is a relative CW complex over its boundary sphere with exactly one
relative cell, of dimension `n` (`TauCeti.diskBoundaryRelCW`). Its characteristic map
`TauCeti.diskCellMap` is the inverse of the radial homeomorphism
`TauCeti.diskHomeomorphClosedBall` from the Euclidean disk onto the closed unit ball of the sup
norm, the domain of characteristic maps of Mathlib's classical CW complexes. The open cell is
the complement of the boundary and the cell frontier is the boundary itself. For `n = 0` the
boundary is empty and the disk is a single `0`-cell.

More generally, a disjoint union `Σ i, TopCat.disk (n i)` of disks is a relative CW complex
over the disjoint union of their boundaries, with one `n i`-cell for each index `i`
(`TauCeti.diskSigmaRelCW`). Its base is homeomorphic to `Σ i, TopCat.diskBoundary (n i)`
(`TauCeti.diskSigmaBoundaryHomeomorph`), so that a family of maps
`α i : TopCat.diskBoundary (n i) → Z` becomes a single map out of the base
(`TauCeti.diskSigmaAttachingMap`). This is the input of the adjunction space `Z ∪_α ⨆ᵢ Dⁿⁱ`
formed by attaching one cell along each `α i`, as in the attachment of handles across a critical
level of a Morse function.

## Main definitions

* `TauCeti.diskBoundarySubset n`: the boundary sphere of `TopCat.disk n`, as a subset.
* `TauCeti.diskBoundarySubsetHomeomorph n`: it is homeomorphic to `TopCat.diskBoundary n`.
* `TauCeti.diskCellMap n`: the characteristic map of the top cell of the disk.
* `TauCeti.diskBoundaryRelCW n`: the relative CW structure on the disk over its boundary.
* `TauCeti.diskSigmaRelCW n`: the relative CW structure on a disjoint union of disks.
* `TauCeti.diskSigmaAttachingMap n α`: a family of maps out of the boundary spheres, as a map
  out of the base of `TauCeti.diskSigmaRelCW n`.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (cell complexes).
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section Disk

variable (n : ℕ)

/-- The boundary sphere of the disk `TopCat.disk n`, as a subset of the disk: the range of the
boundary inclusion `TopCat.diskBoundaryInclusion n`. -/
def diskBoundarySubset : Set (TopCat.disk.{u} n) :=
  range (TopCat.diskBoundaryInclusion n)

variable {n} in
/-- A point of the disk lies on its boundary exactly when it has norm one. -/
theorem mem_diskBoundarySubset_iff (z : TopCat.disk.{u} n) :
    z ∈ diskBoundarySubset n ↔
      ‖((z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
        EuclideanSpace ℝ (Fin n))‖ = 1 :=
  mem_range_diskBoundaryInclusion_iff z

/-- The boundary of the disk is closed. -/
theorem isClosed_diskBoundarySubset : IsClosed (diskBoundarySubset.{u} n) :=
  (TopCat.isClosedEmbedding_diskBoundaryInclusion n).isClosed_range

/-- The `0`-disk has empty boundary. -/
@[simp]
theorem diskBoundarySubset_zero : diskBoundarySubset.{u} 0 = ∅ :=
  range_eq_empty _

/-- The boundary subset of the disk is homeomorphic to Mathlib's boundary sphere
`TopCat.diskBoundary n`, through the boundary inclusion. -/
def diskBoundarySubsetHomeomorph : diskBoundarySubset.{u} n ≃ₜ TopCat.diskBoundary.{u} n :=
  (TopCat.isClosedEmbedding_diskBoundaryInclusion n).isEmbedding.toHomeomorph.symm

@[simp]
theorem coe_diskBoundarySubsetHomeomorph_symm_apply (s : TopCat.diskBoundary.{u} n) :
    ((diskBoundarySubsetHomeomorph n).symm s : TopCat.disk.{u} n) =
      TopCat.diskBoundaryInclusion n s :=
  (rfl)

@[simp]
theorem diskBoundaryInclusion_diskBoundarySubsetHomeomorph (z : diskBoundarySubset.{u} n) :
    TopCat.diskBoundaryInclusion n (diskBoundarySubsetHomeomorph n z) = z :=
  (coe_diskBoundarySubsetHomeomorph_symm_apply n _).symm.trans
    (congrArg Subtype.val ((diskBoundarySubsetHomeomorph n).symm_apply_apply z))

open scoped Classical in
/-- The characteristic map of the top cell of the disk `TopCat.disk n`: on the closed unit ball
of the sup norm on `Fin n → ℝ` it is the inverse of the radial homeomorphism
`TauCeti.diskHomeomorphClosedBall`, and it sends the open unit ball bijectively onto the
complement of the boundary. Outside the closed ball its value is irrelevant. -/
def diskCellMap : PartialEquiv (Fin n → ℝ) (TopCat.disk.{u} n) where
  toFun x := if hx : x ∈ closedBall 0 1 then (diskHomeomorphClosedBall n).symm ⟨x, hx⟩
    else diskCenter n
  invFun z := diskHomeomorphClosedBall n z
  source := ball 0 1
  target := (diskBoundarySubset n)ᶜ
  map_source' x hx := by
    rw [dite_eq_left (ball_subset_closedBall hx)]
    exact (diskHomeomorphClosedBall_mem_ball_iff _).1 (by rwa [Homeomorph.apply_symm_apply])
  map_target' z hz := (diskHomeomorphClosedBall_mem_ball_iff z).2 hz
  left_inv' x hx := by
    simp only [dite_eq_left (ball_subset_closedBall hx), Homeomorph.apply_symm_apply]
  right_inv' z _ := by
    simp only [dite_eq_left (diskHomeomorphClosedBall n z).2, Subtype.coe_eta,
      Homeomorph.symm_apply_apply]

@[simp]
theorem diskCellMap_source : (diskCellMap.{u} n).source = ball 0 1 :=
  (rfl)

@[simp]
theorem diskCellMap_target : (diskCellMap.{u} n).target = (diskBoundarySubset n)ᶜ :=
  (rfl)

/-- On the closed unit ball, the characteristic map of the disk is the inverse of
`TauCeti.diskHomeomorphClosedBall`. -/
theorem diskCellMap_apply (x : closedBall (0 : Fin n → ℝ) 1) :
    diskCellMap.{u} n x = (diskHomeomorphClosedBall n).symm x :=
  dite_eq_left x.2

@[simp]
theorem diskCellMap_symm_apply (z : TopCat.disk.{u} n) :
    (diskCellMap n).symm z = diskHomeomorphClosedBall n z :=
  (rfl)

/-- The characteristic map of the disk is a left inverse of `TauCeti.diskHomeomorphClosedBall`. -/
theorem diskCellMap_diskHomeomorphClosedBall (z : TopCat.disk.{u} n) :
    diskCellMap n (diskHomeomorphClosedBall n z) = z := by
  rw [diskCellMap_apply, Homeomorph.symm_apply_apply]

variable {n} in
/-- The characteristic map of the disk sends the unit sphere of the sup norm to the boundary. -/
theorem diskCellMap_mem_diskBoundarySubset {x : Fin n → ℝ} (hx : x ∈ sphere 0 1) :
    diskCellMap.{u} n x ∈ diskBoundarySubset n := by
  rw [diskCellMap_apply n ⟨x, sphere_subset_closedBall hx⟩]
  refine (norm_diskHomeomorphClosedBall_eq_one_iff _).1 ?_
  rw [Homeomorph.apply_symm_apply]
  exact mem_sphere_zero_iff_norm.1 hx

/-- The characteristic map of the disk is continuous on the closed unit ball. -/
theorem continuousOn_diskCellMap : ContinuousOn (diskCellMap.{u} n) (closedBall 0 1) :=
  continuousOn_iff_continuous_domRestrict.2 <|
    (diskHomeomorphClosedBall n).symm.continuous.congr fun x ↦ (diskCellMap_apply n x).symm

/-- The inverse of the characteristic map of the disk is continuous. -/
theorem continuous_diskCellMap_symm : Continuous (diskCellMap.{u} n).symm :=
  continuous_subtype_val.comp (diskHomeomorphClosedBall n).continuous

/-- The cells of dimension `m` of the disk `TopCat.disk n` relative to its boundary: one if
`m = n`, none otherwise. -/
private abbrev DiskCell (m : ℕ) : Type u := ULift.{u} (PLift (m = n))

/-- The characteristic maps of the disk relative to its boundary. -/
private def diskRelCWMap :
    (m : ℕ) → DiskCell.{u} n m → PartialEquiv (Fin m → ℝ) (TopCat.disk.{u} n)
  | _, ⟨⟨rfl⟩⟩ => diskCellMap n

/-- **The disk relative to its boundary.** The disk `TopCat.disk n` is a finite relative CW
complex over its boundary sphere `TauCeti.diskBoundarySubset n`, with exactly one relative cell,
of dimension `n` (`TauCeti.diskBoundaryRelCWCellEquiv`), whose characteristic map is
`TauCeti.diskCellMap n` (`TauCeti.map_diskBoundaryRelCW`).

This is not an instance, since the base of a relative CW structure is an output parameter. -/
@[instance_reducible]
def diskBoundaryRelCW : RelCWComplex (univ : Set (TopCat.disk.{u} n)) (diskBoundarySubset n) :=
  RelCWComplex.mkFinite univ (diskBoundarySubset n) (DiskCell.{u} n) (diskRelCWMap n)
    (Filter.eventually_atTop.2 ⟨n + 1, fun _ hm ↦ ⟨fun ⟨⟨h⟩⟩ ↦ by omega⟩⟩)
    (fun _ ↦ inferInstance)
    (fun _ i ↦ by obtain ⟨⟨h⟩⟩ := i; subst h; rfl)
    (fun _ i ↦ by obtain ⟨⟨h⟩⟩ := i; subst h; exact continuousOn_diskCellMap _)
    (fun _ i ↦ by obtain ⟨⟨h⟩⟩ := i; subst h; exact (continuous_diskCellMap_symm _).continuousOn)
    (by
      rintro ⟨_, ⟨⟨h⟩⟩⟩ - ⟨_, ⟨⟨h'⟩⟩⟩ - hne
      subst h h'
      exact absurd rfl hne)
    (fun _ i ↦ by
      obtain ⟨⟨h⟩⟩ := i
      subst h
      refine disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (diskCellMap _).map_source hx)
    (fun _ i ↦ by
      obtain ⟨⟨h⟩⟩ := i
      subst h
      exact fun x hx ↦ Or.inl (diskCellMap_mem_diskBoundarySubset hx))
    (isClosed_diskBoundarySubset n)
    (eq_univ_of_forall fun z ↦ Or.inr <| mem_iUnion₂.2
      ⟨n, ⟨⟨rfl⟩⟩, diskHomeomorphClosedBall n z, (diskHomeomorphClosedBall n z).2,
        diskCellMap_diskHomeomorphClosedBall n z⟩)

/-- The relative CW complex `TauCeti.diskBoundaryRelCW n` is finite. -/
instance finite_diskBoundaryRelCW :
    @RelCWComplex.Finite (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) :=
  let := diskBoundaryRelCW.{u} n
  { eventually_isEmpty_cell :=
      Filter.eventually_atTop.2 ⟨n + 1, fun _ hm ↦
        ⟨fun i : DiskCell.{u} n _ ↦ by have := i.down.down; omega⟩⟩
    finite_cell := fun m ↦ inferInstanceAs (Finite (DiskCell.{u} n m)) }

/-- The disk has one relative `m`-cell over its boundary if `m = n`, and none otherwise. -/
def diskBoundaryRelCWCellEquiv (m : ℕ) :
    @cell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) m ≃ PLift (m = n) :=
  Equiv.ulift

/-- The characteristic map of the top cell of `TauCeti.diskBoundaryRelCW n` is
`TauCeti.diskCellMap n`. -/
@[simp]
theorem map_diskBoundaryRelCW (i : @cell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n) :
    @map (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n i = diskCellMap n := by
  rcases i with ⟨⟨h⟩⟩
  rfl

/-- The open top cell of the disk is the complement of its boundary. -/
@[simp]
theorem openCell_diskBoundaryRelCW
    (i : @cell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n) :
    @openCell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n i = (diskBoundarySubset n)ᶜ := by
  let := diskBoundaryRelCW.{u} n
  rw [openCell, map_diskBoundaryRelCW, ← diskCellMap_source, PartialEquiv.image_source_eq_target,
    diskCellMap_target]

/-- The closed top cell of the disk is the whole disk. -/
@[simp]
theorem closedCell_diskBoundaryRelCW
    (i : @cell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n) :
    @closedCell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n i = univ := by
  let := diskBoundaryRelCW.{u} n
  rw [closedCell, map_diskBoundaryRelCW]
  exact eq_univ_of_forall fun z ↦ ⟨_, (diskHomeomorphClosedBall n z).2,
    diskCellMap_diskHomeomorphClosedBall n z⟩

/-- The frontier of the top cell of the disk is its boundary. -/
@[simp]
theorem cellFrontier_diskBoundaryRelCW
    (i : @cell (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n) :
    @cellFrontier (TopCat.disk.{u} n) _ _ _ (diskBoundaryRelCW n) n i = diskBoundarySubset n := by
  let := diskBoundaryRelCW.{u} n
  rw [cellFrontier, map_diskBoundaryRelCW]
  refine subset_antisymm (image_subset_iff.2 fun x hx ↦ diskCellMap_mem_diskBoundarySubset hx)
    fun z hz ↦ ⟨_, ?_, diskCellMap_diskHomeomorphClosedBall n z⟩
  exact mem_sphere_zero_iff_norm.2 ((norm_diskHomeomorphClosedBall_eq_one_iff z).2 hz)

end Disk

section Sigma

variable {ι : Type u} (n : ι → ℕ)

/-- **A disjoint union of disks relative to their boundaries.** The disjoint union
`Σ i, TopCat.disk (n i)` is a relative CW complex over the disjoint union of the boundary spheres,
with one `n i`-cell for each index `i` (`TauCeti.diskSigmaRelCWCellEquiv`), whose
characteristic map is that of `TopCat.disk (n i)` followed by the inclusion of the summand
(`TauCeti.diskSigmaRelCW_map_apply`).

This is not an instance, since the base of a relative CW structure is an output parameter. -/
@[instance_reducible]
def diskSigmaRelCW : RelCWComplex (univ : Set (Σ i, TopCat.disk.{u} (n i)))
    (univ.sigma fun i ↦ diskBoundarySubset (n i)) :=
  let S := @RelCWComplex.sigma ι (fun i ↦ TopCat.disk.{u} (n i)) _ (fun _ ↦ univ)
    (fun i ↦ diskBoundarySubset (n i)) fun i ↦ diskBoundaryRelCW (n i)
  { S with
    closed' A _ hA := S.closed' A (by simp) hA
    union' := by simpa using S.union' }

/-- The relative `m`-cells of a disjoint union of disks are the indices `i` with `n i = m`. -/
def diskSigmaRelCWCellEquiv (m : ℕ) :
    @cell (Σ i, TopCat.disk.{u} (n i)) _ _ _ (diskSigmaRelCW n) m ≃ {i // n i = m} :=
  (@RelCWComplex.sigmaCellEquiv ι (fun i ↦ TopCat.disk.{u} (n i)) _ (fun _ ↦ univ)
    (fun i ↦ diskBoundarySubset (n i)) (fun i ↦ diskBoundaryRelCW (n i)) m).trans <|
      ((Equiv.sigmaCongrRight fun i ↦ diskBoundaryRelCWCellEquiv (n i) m).trans
        (Equiv.sigmaPLiftEquivSubtype _)).trans (Equiv.subtypeEquivRight fun _ ↦ eq_comm)

/-- A disjoint union of finitely many disks is a finite relative CW complex. -/
instance finite_diskSigmaRelCW [Finite ι] :
    @RelCWComplex.Finite (Σ i, TopCat.disk.{u} (n i)) _ _ _ (diskSigmaRelCW n) := by
  let := diskSigmaRelCW.{u} n
  obtain ⟨N, hN⟩ := (finite_range n).bddAbove
  exact
    { eventually_isEmpty_cell := Filter.eventually_atTop.2 ⟨N + 1, fun m hm ↦
        ⟨fun c ↦ by
          have h := (diskSigmaRelCWCellEquiv n m c).2
          have := hN ⟨(diskSigmaRelCWCellEquiv n m c).1, rfl⟩
          omega⟩⟩
      finite_cell := fun m ↦ Finite.of_equiv _ (diskSigmaRelCWCellEquiv n m).symm }

/-- The characteristic map of the cell of a disjoint union of disks at the index `i` is the
characteristic map of the disk `TopCat.disk (n i)`, followed by the inclusion of the summand. -/
theorem diskSigmaRelCW_map_apply (i : ι) (x : closedBall (0 : Fin (n i) → ℝ) 1) :
    @map (Σ i, TopCat.disk.{u} (n i)) _ _ _ (diskSigmaRelCW n) (n i)
        ((diskSigmaRelCWCellEquiv n (n i)).symm ⟨i, rfl⟩) x =
      ⟨i, (diskHomeomorphClosedBall (n i)).symm x⟩ := by
  have h := congrFun (@RelCWComplex.coe_map_sigma ι (fun i ↦ TopCat.disk.{u} (n i)) _
    (fun _ ↦ univ) (fun i ↦ diskBoundarySubset (n i)) (fun i ↦ diskBoundaryRelCW (n i)) (n i) i
    ((diskBoundaryRelCWCellEquiv (n i) (n i)).symm ⟨rfl⟩)) x
  rw [map_diskBoundaryRelCW] at h
  rw [← diskCellMap_apply]
  exact h

/-- The disjoint union of the boundary inclusions of the disks. -/
private abbrev diskBoundarySigmaInclusion :
    (Σ i, TopCat.diskBoundary.{u} (n i)) → Σ i, TopCat.disk.{u} (n i) :=
  @Sigma.map ι ι (fun i ↦ TopCat.diskBoundary.{u} (n i)) (fun i ↦ TopCat.disk.{u} (n i)) id
    fun i ↦ TopCat.diskBoundaryInclusion (n i)

private theorem isEmbedding_diskBoundarySigmaInclusion :
    IsEmbedding (diskBoundarySigmaInclusion.{u} n) :=
  (isEmbedding_sigmaMap Function.injective_id).2 fun i ↦
    (TopCat.isClosedEmbedding_diskBoundaryInclusion (n i)).isEmbedding

private theorem range_diskBoundarySigmaInclusion :
    range (diskBoundarySigmaInclusion.{u} n) =
      univ.sigma fun i ↦ diskBoundarySubset (n i) := by
  ext ⟨i, z⟩
  constructor
  · rintro ⟨⟨j, s⟩, h⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    exact ⟨mem_univ _, s, eq_of_heq h⟩
  · rintro ⟨-, s, hs⟩
    exact ⟨⟨i, s⟩, congrArg (Sigma.mk i) hs⟩

/-- The base of `TauCeti.diskSigmaRelCW n` is homeomorphic to the disjoint union of the boundary
spheres `TopCat.diskBoundary (n i)`, through the boundary inclusions. -/
def diskSigmaBoundaryHomeomorph :
    (univ.sigma fun i ↦ diskBoundarySubset.{u} (n i)) ≃ₜ Σ i, TopCat.diskBoundary.{u} (n i) :=
  ((isEmbedding_diskBoundarySigmaInclusion n).toHomeomorph.trans
    (Homeomorph.setCongr (range_diskBoundarySigmaInclusion n))).symm

@[simp]
theorem coe_diskSigmaBoundaryHomeomorph_symm_apply (i : ι) (s : TopCat.diskBoundary.{u} (n i)) :
    ((diskSigmaBoundaryHomeomorph n).symm ⟨i, s⟩ : Σ i, TopCat.disk.{u} (n i)) =
      ⟨i, TopCat.diskBoundaryInclusion (n i) s⟩ :=
  (rfl)

/-- The point of the base of `TauCeti.diskSigmaRelCW n` given by a point `s` of the boundary of
the `i`-th disk corresponds to `⟨i, s⟩`. -/
theorem diskSigmaBoundaryHomeomorph_apply (i : ι) (s : TopCat.diskBoundary.{u} (n i))
    (h : (⟨i, TopCat.diskBoundaryInclusion (n i) s⟩ : Σ i, TopCat.disk.{u} (n i)) ∈
      univ.sigma fun i ↦ diskBoundarySubset (n i)) :
    diskSigmaBoundaryHomeomorph n ⟨_, h⟩ = ⟨i, s⟩ :=
  (diskSigmaBoundaryHomeomorph n).toEquiv.eq_symm_apply.1
    (Subtype.ext (coe_diskSigmaBoundaryHomeomorph_symm_apply n i s).symm)

/-- The map out of the base of `TauCeti.diskSigmaRelCW n` given by a family of maps
`α i : TopCat.diskBoundary (n i) → Z`, one attaching map for each disk: the input of the
adjunction space obtained by attaching the disk `TopCat.disk (n i)` to `Z` along `α i` for every
`i`. -/
def diskSigmaAttachingMap {Z : Type*} [TopologicalSpace Z]
    (α : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) :
    C(univ.sigma fun i ↦ diskBoundarySubset.{u} (n i), Z) :=
  (ContinuousMap.sigma α).comp (diskSigmaBoundaryHomeomorph n)

/-- The map out of the base given by a family of attaching maps restricts on the boundary of the
`i`-th disk to the `i`-th attaching map. -/
@[simp]
theorem diskSigmaAttachingMap_apply {Z : Type*} [TopologicalSpace Z]
    (α : ∀ i, C(TopCat.diskBoundary.{u} (n i), Z)) (i : ι) (s : TopCat.diskBoundary.{u} (n i))
    (h : (⟨i, TopCat.diskBoundaryInclusion (n i) s⟩ : Σ i, TopCat.disk.{u} (n i)) ∈
      univ.sigma fun i ↦ diskBoundarySubset (n i)) :
    diskSigmaAttachingMap n α ⟨_, h⟩ = α i s :=
  congrArg (ContinuousMap.sigma α) (diskSigmaBoundaryHomeomorph_apply n i s h)

end Sigma

end TauCeti
