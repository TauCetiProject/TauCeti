/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Unit

/-!
# Graded unit identifications for balanced tensor products

The regular bimodule of a graded algebra is a unit for balanced tensor products of graded
modules. The action identifications `A ⊗_A N ≃ N` and `M ⊗_A A ≃ M` carry each total-degree
piece onto the corresponding module piece. Their inverses insert the degree-zero unit.
These equalities allow the unit identifications to be restricted to homogeneous pieces,
and hence to the terms of the underlying complexes of DG modules.

## Main results

* `map_lid_grading_piece`: the left action identifies each tensor piece with the module piece.
* `map_rid_grading_piece`: the right action identifies each tensor piece with the module piece.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open MulOpposite

namespace TauCeti.BalancedTensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

section Left

variable {N : Type*} [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N] (H : InternalGrading R N) [SetLike.GradedSMul 𝒜 H.piece]

local instance unitGradedRight :
    SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- The left unit identification carries the total-degree tensor piece onto the module piece. -/
theorem map_lid_grading_piece (p : ℤ) :
    ((grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition 𝒜) H).piece p).map
      (lid R A N).toLinearMap = H.piece p := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, grading_piece_eq_iSup]
    refine iSup_le fun q ↦ Submodule.map₂_le.mpr fun a ha n hn ↦ ?_
    rw [Submodule.mem_comap, mk_apply, LinearEquiv.coe_coe, lid_tmul]
    rw [InternalGrading.ofDecomposition_piece] at ha
    simpa only [vadd_eq_add, add_sub_cancel] using SetLike.GradedSMul.smul_mem ha hn
  · intro n hn
    refine Submodule.mem_map.mpr ⟨(lid R A N).symm n, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [lid_symm_apply]
    have h := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition 𝒜) H
      (by simpa only [InternalGrading.ofDecomposition_piece] using SetLike.one_mem_graded 𝒜) hn
    simpa only [zero_add] using h

end Left

section Right

variable {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  [IsScalarTower R Aᵐᵒᵖ M] (G : InternalGrading R M)
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece G.piece]

local instance unitGradedLeft : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- The right unit identification carries the total-degree tensor piece onto the module piece. -/
theorem map_rid_grading_piece (p : ℤ) :
    ((grading (𝒜 := 𝒜) G (InternalGrading.ofDecomposition 𝒜)).piece p).map
      (rid R A M).toLinearMap = G.piece p := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, grading_piece_eq_iSup]
    refine iSup_le fun q ↦ Submodule.map₂_le.mpr fun m hm a ha ↦ ?_
    rw [Submodule.mem_comap, mk_apply, LinearEquiv.coe_coe, rid_tmul]
    have hop : op a ∈ (InternalGrading.ofDecomposition 𝒜).opposite.piece (p - q) :=
      (InternalGrading.op_mem_opposite_piece_iff _ _ _).mpr ha
    simpa only [vadd_eq_add, sub_add_cancel] using SetLike.GradedSMul.smul_mem hop hm
  · intro m hm
    refine Submodule.mem_map.mpr ⟨(rid R A M).symm m, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [rid_symm_apply]
    have h := tmul_mem_grading (𝒜 := 𝒜) G (InternalGrading.ofDecomposition 𝒜) hm
      (by simpa only [InternalGrading.ofDecomposition_piece] using SetLike.one_mem_graded 𝒜)
    simpa only [add_zero] using h

end Right

end TauCeti.BalancedTensorProduct
