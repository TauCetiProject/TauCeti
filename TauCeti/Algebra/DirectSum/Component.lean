/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Whole-component selection on an internally decomposed module

For a family of submodules with a direct-sum decomposition, selecting a whole
homogeneous piece is an endomorphism of the ambient module: the `η`-component
of the decomposition, included back into the module. These projections are
idempotent and pairwise orthogonal, and they act as the identity on their own
piece and as zero on every other piece. Concrete decompositions (histories,
filtrations, graded coefficient modules) use this endomorphism to express
final projections without unfolding the decomposition.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
`Mei/Algebra/DirectSum/Component.lean`.
-/

public noncomputable section

namespace TauCeti

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Selection of a whole homogeneous piece as an endomorphism of the ambient
module: the `η`-component of the direct-sum decomposition, included back into
`M`. -/
def homogeneousComponent (η : ι) : Module.End R M :=
  (ℳ η).subtype.comp
    ((DirectSum.component R ι (fun i => ℳ i) η).comp
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap)

/-- Selecting a piece takes the corresponding component of the decomposition. -/
@[simp]
theorem homogeneousComponent_apply (η : ι) (a : M) :
    homogeneousComponent ℳ η a = (DirectSum.decompose ℳ a η : M) := (rfl)

/-- Every selected output lies in the selected piece. -/
theorem homogeneousComponent_mem (η : ι) (a : M) :
    homogeneousComponent ℳ η a ∈ ℳ η :=
  Subtype.property _

/-- Selection is the identity on its own homogeneous piece. -/
theorem homogeneousComponent_apply_of_mem {η : ι} {a : M} (ha : a ∈ ℳ η) :
    homogeneousComponent ℳ η a = a :=
  DirectSum.decompose_of_mem_same ℳ ha

/-- A homogeneous input of a different piece is annihilated by the selection. -/
theorem homogeneousComponent_apply_of_mem_ne {i η : ι} {a : M} (ha : a ∈ ℳ i)
    (h : i ≠ η) :
    homogeneousComponent ℳ η a = 0 := by
  rw [homogeneousComponent_apply, DirectSum.decompose_of_mem_ne ℳ ha h]

/-- Piece selection is a projection: selecting the same piece twice has no
further effect. -/
@[simp]
theorem homogeneousComponent_idem (η : ι) :
    (homogeneousComponent ℳ η).comp (homogeneousComponent ℳ η) =
      homogeneousComponent ℳ η := by
  ext a
  simp only [LinearMap.comp_apply, homogeneousComponent_apply]
  exact DirectSum.decompose_of_mem_same ℳ (Subtype.property (DirectSum.decompose ℳ a η))

/-- Selections of two different pieces are orthogonal. -/
@[simp]
theorem homogeneousComponent_comp_of_ne {i j : ι} (h : i ≠ j) :
    (homogeneousComponent ℳ i).comp (homogeneousComponent ℳ j) = 0 := by
  ext a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact homogeneousComponent_apply_of_mem_ne ℳ (homogeneousComponent_mem ℳ j a) (Ne.symm h)

end TauCeti
