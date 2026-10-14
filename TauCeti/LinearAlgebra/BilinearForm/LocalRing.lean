/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Bilinear forms over local rings

This file records consequences of a unit Gram determinant over a local ring that do not require
symmetry, including the existence of a unit off-diagonal entry when a diagonal entry is not a
unit.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  (B : BilinForm R M)

/-- In a positive-rank unimodular form over a local ring, if the first basis vector has
nonunit self-pairing, it pairs to a unit with a different basis vector. -/
theorem exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det
    {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (hdiag : ¬ IsUnit (B (b 0) (b 0)))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ i : Fin (n + 1), i.val ≠ 0 ∧
      IsUnit (B (b 0) (b i)) := by
  obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum
    (Matrix.det_succ_row_zero (B.toMatrix b) ▸ hdet)
  have hu : IsUnit (B (b 0) (b j)) := by
    simpa only [toMatrix_apply] using
      isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hj)
  have hj0 : j.val ≠ 0 := by
    intro hj0
    have hj0' : j = 0 := Fin.ext hj0
    subst j
    exact hdiag hu
  exact ⟨j, hj0, hu⟩

end LinearMap.BilinForm

end
