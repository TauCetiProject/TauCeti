/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Quaternion.Fuchsian.RealSplitting
import TauCeti.Algebra.Quaternion.Split

/-!
# Real splittings over `ℚ`

Two quaternion algebras over `ℚ`, which has a single real place:

* the split algebra `ℍ[ℚ,1,1] ≃ M₂(ℚ)` has a real splitting, sending `i` to `diag(1, -1)` and `j`
  to `!![0, 1; 1, 0]`; the ramification condition is empty because `ℚ` has no other real place;
* the rational Hamilton quaternions `ℍ[ℚ,-1,-1]` have no real splitting, since a real splitting
  would make the real Hamilton quaternions, a division algebra, isomorphic to `M₂(ℝ)`.
-/

public noncomputable section

open scoped Quaternion

namespace TauCeti.RealSplittingExample

/-- The real splitting of `ℍ[ℚ,1,1]` at the real place of `ℚ`: coefficients are read in `ℝ` and
`ℍ[ℝ,1,1]` is identified with `M₂(ℝ)` by `i ↦ diag(1, -1)` and `j ↦ !![0, 1; 1, 0]`. -/
def ratOneOne : RealSplitting ℚ 1 1 where
  place := Rat.castHom ℝ
  a_ne_zero := one_ne_zero
  b_ne_zero := one_ne_zero
  ramified σ hσ := (hσ (Subsingleton.elim _ _)).elim
  splitting := (QuaternionAlgebra.oneEquivMatrix (1 : ℝˣ)).toRingHom.comp
    (QuaternionAlgebra.map 1 0 1 (Rat.castHom ℝ) (map_one _) (map_zero _) (by simp))
  splitting_algebraMap x := by
    ext i j
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv]
    rw [QuaternionAlgebra.oneEquivMatrix_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]

/-- The splitting of `ℍ[ℚ,1,1]` in coordinates. -/
theorem ratOneOne_splitting_apply (q : ℍ[ℚ,1,1]) :
    ratOneOne.splitting q =
      !![(q.re : ℝ) + q.imI, (q.imJ : ℝ) + q.imK; (q.imJ : ℝ) - q.imK, (q.re : ℝ) - q.imI] := by
  simp only [ratOneOne, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  rw [QuaternionAlgebra.oneEquivMatrix_apply]
  simp

-- The splitting sends `i` to `diag(1, -1)` and `j` to `!![0, 1; 1, 0]`.
example : ratOneOne.splitting ⟨0, 1, 0, 0⟩ = !![1, 0; 0, -1] := by
  simp [ratOneOne_splitting_apply]

example : ratOneOne.splitting ⟨0, 0, 1, 0⟩ = !![0, 1; 1, 0] := by
  simp [ratOneOne_splitting_apply]

-- The quaternion `1 + i + k` has reduced norm one, and its image `!![2, 1; -1, 0]` has
-- determinant one.
example : ratOneOne.splitting ⟨1, 1, 0, 1⟩ = !![2, 1; -1, 0] := by
  norm_num [ratOneOne_splitting_apply]

example : (ratOneOne.splitting ⟨1, 1, 0, 1⟩).det = 1 := by
  rw [RealSplitting.det_splitting, QuaternionAlgebra.normForm_apply_coordinates]
  norm_num

/-- The rational Hamilton quaternions `ℍ[ℚ,-1,-1]` have no real splitting: both structure
constants are negative at the real place of `ℚ`. -/
theorem isEmpty_neg_one_neg_one : IsEmpty (RealSplitting ℚ (-1) (-1)) :=
  ⟨fun S ↦ by
    have h := S.zero_lt_place_or_zero_lt_place
    simp only [map_neg, map_one, or_self] at h
    linarith⟩

end TauCeti.RealSplittingExample
