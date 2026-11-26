/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Interior
public import TauCeti.LowDimTopology.Surface.Basic

/-!
# The closed disk as a surface

The closed unit disk `D = closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1`, a manifold with boundary
modelled on the half-plane (`TauCeti.instChartedSpaceClosedBallEuclideanSpace`), is a compact
connected surface. Its interior is homeomorphic to the open unit disk
(`TauCeti.closedBallInteriorHomeomorph`), which is contractible, so it is orientable. This file
records the disk with a chosen orientation and no punctures
(`TauCeti.PuncturedSurface.closedDisk`), and the disk punctured at its centre
(`TauCeti.PuncturedSurface.puncturedDisk`), as surfaces in the sense of
`TauCeti.PuncturedSurface`.

## Main definitions

* `TauCeti.closedDiskOrientation`: an orientation of the closed unit disk.
* `TauCeti.PuncturedSurface.closedDisk`: the closed unit disk as a surface without punctures.
* `TauCeti.PuncturedSurface.puncturedDisk`: the closed unit disk punctured at its centre.
-/

public section

noncomputable section

open Set Metric Module Topology

open scoped Manifold EuclideanSpace

namespace TauCeti

/-- The closed unit disk of the Euclidean plane. -/
local notation "𝕔𝔻" => closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The closed unit disk is a compact connected surface. -/
theorem isCompactConnectedSurface_closedDisk : IsCompactConnectedSurface 𝕔𝔻 :=
  have : ConnectedSpace 𝕔𝔻 :=
    isConnected_iff_connectedSpace.mp (isConnected_closedBall zero_le_one)
  isCompactConnectedSurface 𝕔𝔻

/-- An orientation of the closed unit disk, an orientation of its interior, which exists because
the interior is simply connected. -/
def closedDiskOrientation :
    HomologicalOrientation ((𝓡∂ 2).interior 𝕔𝔻) (EuclideanSpace ℝ (Fin 2)) 2 :=
  have : Nonempty ((𝓡∂ 2).interior 𝕔𝔻) :=
    ⟨(closedBallInteriorHomeomorph 2 _).symm ⟨0, by simp⟩⟩
  (HomologicalOrientation.nonempty_of_simplyConnectedSpace finrank_euclideanSpace_fin).some

namespace PuncturedSurface

/-- **The closed unit disk** as a surface without punctures. -/
def closedDisk : PuncturedSurface 𝕔𝔻 where
  isCompactConnectedSurface := isCompactConnectedSurface_closedDisk
  orientation := closedDiskOrientation
  punctures := ∅
  punctures_subset_interior := by simp

@[simp]
theorem orientation_closedDisk : closedDisk.orientation = closedDiskOrientation :=
  (rfl)

@[simp]
theorem punctures_closedDisk : closedDisk.punctures = ∅ :=
  (rfl)

@[simp]
theorem numPunctures_closedDisk : closedDisk.numPunctures = 0 := by
  rw [PuncturedSurface.numPunctures_def, punctures_closedDisk]
  exact Finset.card_empty

/-- **The closed unit disk punctured at its centre** `TauCeti.diskCenter`. -/
def puncturedDisk : PuncturedSurface 𝕔𝔻 where
  isCompactConnectedSurface := isCompactConnectedSurface_closedDisk
  orientation := closedDiskOrientation
  punctures := {(diskCenter.{0} 2).down}
  punctures_subset_interior := by
    simp only [Finset.coe_singleton, singleton_subset_iff]
    exact isInteriorPoint_closedBall_iff.2 (by simp)

@[simp]
theorem orientation_puncturedDisk : puncturedDisk.orientation = closedDiskOrientation :=
  (rfl)

@[simp]
theorem punctures_puncturedDisk : puncturedDisk.punctures = {(diskCenter.{0} 2).down} :=
  (rfl)

@[simp]
theorem numPunctures_puncturedDisk : puncturedDisk.numPunctures = 1 := by
  rw [PuncturedSurface.numPunctures_def, punctures_puncturedDisk]
  exact Finset.card_singleton _

/-- The boundary of the punctured disk is the unit circle. -/
theorem image_boundary_puncturedDisk :
    Subtype.val '' (𝓡∂ 2).boundary puncturedDisk.carrier =
      Subtype.val ⁻¹' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [puncturedDisk.image_boundary_carrier, boundary_closedBall]

end PuncturedSurface

end TauCeti
