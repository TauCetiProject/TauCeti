/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Real projective classes of unit vectors

Two real unit vectors span the same line exactly when they are equal or antipodal.
This identifies the fibres of the unit-sphere projection to real projective space,
without a finite-dimensionality assumption.
-/

public section

namespace Projectivization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Real unit vectors represent the same projective point exactly when they are equal
or antipodal. -/
theorem mk_eq_mk_iff_of_norm_eq_one {v w : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    mk ℝ v (norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)) =
      mk ℝ w (norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)) ↔
        v = w ∨ v = -w := by
  rw [mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have habs : |a| = 1 := by
      have h := congrArg norm ha
      simpa [norm_smul, hv, hw] using h
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp habs with h | h
    · left
      simpa [h] using ha.symm
    · right
      simpa [h] using ha.symm
  · rintro (h | h)
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨-1, by simpa using h.symm⟩

end Projectivization
