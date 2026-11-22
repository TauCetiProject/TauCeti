/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import TauCeti.LowDimTopology.Surface.Basic

/-!
# The closed disk as a surface

The closed unit disk `D = closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1`, a manifold with boundary
modelled on the half-plane (`TauCeti.instChartedSpaceClosedBallEuclideanSpace`), is a compact
connected surface. Its interior is the open unit disk
(`TauCeti.closedDiskInteriorHomeomorph`), which is contractible, so it is orientable. This file
records the disk with a chosen orientation and no punctures (`TauCeti.closedDisk`), and the disk
punctured at its centre (`TauCeti.puncturedDisk`), as surfaces in the sense of
`TauCeti.PuncturedSurface`.

## Main definitions

* `TauCeti.closedDiskInteriorHomeomorph`: the interior of the closed unit disk is homeomorphic
  to the open unit disk.
* `TauCeti.closedDiskOrientation`: an orientation of the closed unit disk.
* `TauCeti.closedDisk`: the closed unit disk as a surface without punctures.
* `TauCeti.puncturedDisk`: the closed unit disk punctured at its centre.
-/

public section

noncomputable section

open Set Metric Module Topology

open scoped Manifold

namespace TauCeti

/-- The closed unit disk of the Euclidean plane. -/
local notation "𝔻" => closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The Euclidean plane has dimension two, as the closed-ball charts require. -/
local instance factFinrankEuclideanPlane : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The closed unit disk is a compact connected surface. -/
theorem isCompactConnectedSurface_closedDisk : IsCompactConnectedSurface 𝔻 :=
  have : ConnectedSpace 𝔻 := isConnected_iff_connectedSpace.mp
    ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).isConnected
      (nonempty_closedBall.2 zero_le_one))
  isCompactConnectedSurface 𝔻

/-- The points of the open unit disk are exactly the interior points of the closed unit disk. -/
theorem range_val_interior_closedDisk :
    range (fun x : (𝓡∂ 2).interior 𝔻 ↦ (x.val : EuclideanSpace ℝ (Fin 2))) = ball 0 1 := by
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    have hx : (𝓡∂ 2).IsInteriorPoint x.val := x.property
    simpa only [mem_ball_zero_iff] using isInteriorPoint_closedBall_iff.1 hx
  · have hy' : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
    have hyD : y ∈ 𝔻 := mem_closedBall_zero_iff.2 hy'.le
    exact ⟨⟨⟨y, hyD⟩, isInteriorPoint_closedBall_iff.2 hy'⟩, rfl⟩

/-- **The interior of the closed unit disk is the open unit disk.** -/
@[expose] def closedDiskInteriorHomeomorph :
    (𝓡∂ 2).interior 𝔻 ≃ₜ ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr range_val_interior_closedDisk)

@[simp]
theorem coe_closedDiskInteriorHomeomorph_apply (x : (𝓡∂ 2).interior 𝔻) :
    (closedDiskInteriorHomeomorph x : EuclideanSpace ℝ (Fin 2)) = x.val :=
  rfl

/-- The interior of the closed unit disk is contractible. -/
instance contractibleSpace_interior_closedDisk : ContractibleSpace ((𝓡∂ 2).interior 𝔻) :=
  have := (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
    (nonempty_ball.2 zero_lt_one)
  closedDiskInteriorHomeomorph.contractibleSpace

/-- An orientation of the closed unit disk, an orientation of its interior, which exists because
the interior is simply connected. -/
def closedDiskOrientation :
    HomologicalOrientation ((𝓡∂ 2).interior 𝔻) (EuclideanSpace ℝ (Fin 2)) 2 :=
  have : Nonempty ((𝓡∂ 2).interior 𝔻) := ⟨closedDiskInteriorHomeomorph.symm ⟨0, by simp⟩⟩
  (HomologicalOrientation.nonempty_of_simplyConnectedSpace finrank_euclideanSpace_fin).some

/-- **The closed unit disk** as a surface without punctures. -/
@[expose] def closedDisk : PuncturedSurface 𝔻 where
  isCompactConnectedSurface := isCompactConnectedSurface_closedDisk
  orientation := closedDiskOrientation
  punctures := ∅
  punctures_subset_interior := by simp

@[simp]
theorem numPunctures_closedDisk : closedDisk.numPunctures = 0 :=
  rfl

/-- The centre of the closed unit disk. -/
@[expose] def closedDiskCenter : 𝔻 :=
  ⟨0, by simp⟩

/-- **The closed unit disk punctured at its centre.** -/
@[expose] def puncturedDisk : PuncturedSurface 𝔻 where
  isCompactConnectedSurface := isCompactConnectedSurface_closedDisk
  orientation := closedDiskOrientation
  punctures := {closedDiskCenter}
  punctures_subset_interior := by
    simp only [Finset.coe_singleton, singleton_subset_iff]
    exact isInteriorPoint_closedBall_iff.2 (by simp [closedDiskCenter])

@[simp]
theorem numPunctures_puncturedDisk : puncturedDisk.numPunctures = 1 :=
  rfl

/-- The boundary of the punctured disk is the unit circle. -/
theorem image_boundary_puncturedDisk :
    Subtype.val '' (𝓡∂ 2).boundary puncturedDisk.carrier =
      Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [puncturedDisk.image_boundary_carrier, boundary_closedBall]

end TauCeti
