/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# Characteristic and attaching maps of a cell on the Euclidean disk

The characteristic map of an `n`-cell of a relative CW complex `C` is defined on the closed unit
ball of the sup norm on `Fin n → ℝ`.  Read on the Euclidean disk `𝔻 n` of `TopCat` through the
radial homeomorphism `TauCeti.diskHomeomorphClosedBall`, it is a morphism
`TauCeti.cellDiskHom` to the skeleton `skeletonLT C (n + 1)`, and its restriction to the boundary
sphere `∂𝔻 n` is the attaching map `TauCeti.cellAttachingMap` to `skeletonLT C n`.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2 and Appendix.
-/

public section

noncomputable section

open Metric Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} {C : Set X} [RelCWComplex C D]
  {n : ℕ}

/-- The characteristic map of an `n`-cell, read on the Euclidean disk `𝔻 n` through
`TauCeti.diskHomeomorphClosedBall`, as a morphism to the `n`-skeleton `skeletonLT C (n + 1)`. -/
def cellDiskHom (j : cell C n) : TopCat.disk.{w} n ⟶ skeletonObj C (n + 1) :=
  TopCat.ofHom
    { toFun z := ⟨map n j (diskHomeomorphClosedBall n z),
        map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 (diskHomeomorphClosedBall n z).2)⟩
      continuous_toFun := ((continuous_map_closedBall j).comp
        (diskHomeomorphClosedBall n).continuous).subtype_mk _ }

lemma coe_cellDiskHom_apply (j : cell C n) (z : TopCat.disk.{w} n) :
    (cellDiskHom j z : X) = map n j (diskHomeomorphClosedBall n z) :=
  (rfl)

/-- A point of the boundary of the disk is sent to the unit sphere of the sup norm. -/
private lemma diskHomeomorphClosedBall_diskBoundaryInclusion_mem_sphere
    (z : TopCat.diskBoundary.{w} n) :
    (diskHomeomorphClosedBall n (TopCat.diskBoundaryInclusion n z) : Fin n → ℝ) ∈
      sphere (0 : Fin n → ℝ) 1 :=
  mem_sphere_zero_iff_norm.2 <| (norm_diskHomeomorphClosedBall_eq_one_iff _).2 ⟨z, rfl⟩

/-- The attaching map of an `n`-cell: its characteristic map restricted to the boundary sphere
`∂𝔻 n`, as a morphism to `skeletonLT C n`. -/
def cellAttachingMap (j : cell C n) : TopCat.diskBoundary.{w} n ⟶ skeletonObj C n :=
  TopCat.ofHom
    { toFun z := ⟨map n j (diskHomeomorphClosedBall n (TopCat.diskBoundaryInclusion n z)),
        cellFrontier_subset_skeletonLT n j
          ⟨_, diskHomeomorphClosedBall_diskBoundaryInclusion_mem_sphere z, rfl⟩⟩
      continuous_toFun := ((continuous_map_closedBall j).comp
        ((diskHomeomorphClosedBall n).continuous.comp
          (TopCat.diskBoundaryInclusion n).hom.continuous)).subtype_mk _ }

lemma coe_cellAttachingMap_apply (j : cell C n) (z : TopCat.diskBoundary.{w} n) :
    (cellAttachingMap j z : X) =
      map n j (diskHomeomorphClosedBall n (TopCat.diskBoundaryInclusion n z)) :=
  (rfl)

/-- The attaching map of a cell maps the boundary sphere onto the frontier of the cell. -/
@[simp]
lemma range_cellAttachingMap (j : cell C n) :
    Set.range (fun z ↦ (cellAttachingMap j z : X)) = cellFrontier n j := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, diskHomeomorphClosedBall_diskBoundaryInclusion_mem_sphere z, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    set q := (diskHomeomorphClosedBall n).symm ⟨p, sphere_subset_closedBall hp⟩
    have hq : diskHomeomorphClosedBall n q = ⟨p, sphere_subset_closedBall hp⟩ :=
      Homeomorph.apply_symm_apply _ _
    obtain ⟨z, hz⟩ := (norm_diskHomeomorphClosedBall_eq_one_iff q).1
      (by rw [hq]; exact mem_sphere_zero_iff_norm.1 hp)
    exact ⟨z, (coe_cellAttachingMap_apply j z).trans (by rw [hz, hq])⟩

end TauCeti
