/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic

/-!
# Raising closure of submodules in a minuscule weight basis

At a negative simple-coroot coordinate, subtracting a basis vector from its image under the
positive root matrix at parameter one recovers the reflected basis vector.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (T : MinusculeWeightTable B ι)

/-- A submodule containing a basis vector and its raised image contains the reflected vector. -/
theorem single_reflection_mem_of_mulVec_mem (W : Submodule R (ι → R)) (i : B) (a : ι)
    (ha : T.weight a i = -1) (hv : Pi.single a (1 : R) ∈ W)
    (hroot : (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) *ᵥ
      Pi.single a (1 : R) ∈ W) :
    Pi.single (T.reflection i a) (1 : R) ∈ W := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_single_one,
    T.raisingMatrix_map_col, ite_eq_left ha] at hroot
  simpa only [add_sub_cancel_left] using W.sub_mem hroot hv

end TauCeti.MinusculeWeightTable
