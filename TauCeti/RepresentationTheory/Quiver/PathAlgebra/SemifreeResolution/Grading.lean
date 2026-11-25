/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.SemifreeResolution.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BimoduleResolution.Grading

/-!
# Graded differentials of the small path-algebra resolution

The envelope differential on vertex tensors and the twisted differential on arrow tensors
raise total arrow weight by one when the path-algebra differential kills the vertex idempotents.
-/

public section

namespace TauCeti.PathAlgebra

universe u v w

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q] [Fintype Q]
  (wt : ∀ {i j : Q}, (i ⟶ j) → ℤ) (d : pathAlgebra k Q →ₗ[k] pathAlgebra k Q)
  (hd : IsDGAlgebra (gradeBy k wt) d) (hdε : ∀ i, d (vertexIdempotent k i) = 0)

include hd hdε

/-- The differential on the vertex term raises total arrow weight by one. -/
theorem isHomogeneous_vertexTensorBimoduleDifferential :
    LinearMap.IsHomogeneous (vertexTensorBimoduleDifferential wt d)
      (vertexTensorGrading k Q wt).piece (vertexTensorGrading k Q wt).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  rw [mem_vertexTensorGrading_piece_iff, coe_vertexTensorBimoduleDifferential hd hdε]
  have h := isHomogeneous_envelopeDifferential
    (InternalGrading.mk (gradeBy k wt) (isInternal_gradeBy k wt)) rfl
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ hd.map_mem hx) 0
  exact h.map_mem ((mem_vertexTensorGrading_piece_iff k Q wt).mp hx)

variable [DecidableEq Q] [∀ i j : Q, DecidableEq (i ⟶ j)]

/-- The twisted differential on the arrow term raises total arrow weight by one. -/
theorem isHomogeneous_arrowTensorBimoduleDifferential :
    LinearMap.IsHomogeneous (arrowTensorBimoduleDifferential wt d)
      (arrowTensorGrading k Q wt).piece (arrowTensorGrading k Q wt).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n x hx
  rw [mem_arrowTensorGrading_piece_iff,
    coe_arrowTensorDifferential_arrowTensorBimoduleDifferential hd hdε]
  have h := (isHomogeneous_vertexTensorBimoduleDifferential k Q wt d hd hdε).map_mem
    ((isHomogeneous_arrowTensorDifferential k Q wt).map_mem hx)
  simpa only [add_zero, mem_vertexTensorGrading_piece_iff,
    coe_vertexTensorBimoduleDifferential hd hdε] using h

end TauCeti.PathAlgebra
