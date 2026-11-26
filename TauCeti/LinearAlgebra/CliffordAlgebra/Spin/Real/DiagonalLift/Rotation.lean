/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.DiagonalLift.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Rotation

/-!
# Coordinate-plane rotations for the compact real diagonal Spin lift

For distinct coordinate indices `i, j : Fin k`, the diagonal lift
`TauCeti.realCliffordSpinDiagonalLift k` sends the rotation induced by
`spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1) t` to the commuting product
of the two `spinRotation` elements in the first and second `k`-blocks of `ℝ^(k + k)`, with
Clifford expansion
`(cos t + sin t · ι e_i ι e_j) * (cos t + sin t · ι e_{k + i} ι e_{k + j})`, which closes to `1`
at Spin angle `t = π` (a full `2π` rotation in `SO(k)`).

## Main results

* `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation`,
  `TauCeti.coe_realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation`, and
  `TauCeti.realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation_pi`: coordinate-plane
  rotation formula, Clifford-algebra expansion, and full-turn closure.
-/

public section

open QuadraticMap

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-- **Coordinate-plane rotation formula for `realCliffordSpinDiagonalLift`**: the diagonal lift of
a rotation in the `(i, j)` coordinate plane of `ℝ^k` (`i ≠ j`) is the commuting product of the
corresponding `spinRotation` elements in the first and second `k`-blocks of `ℝ^(k + k)`. -/
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) (t : ℝ) :
    realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t)) =
      spinRotation (realCliffordForm (k + k) 0)
          (Pi.single (Fin.castAdd k i) 1) (Pi.single (Fin.castAdd k j) 1)
          (realCliffordForm_zero_single_one (k + k) (Fin.castAdd k i))
          (realCliffordForm_zero_single_one (k + k) (Fin.castAdd k j))
          (isOrtho_realCliffordForm_single (p := k + k) (q := 0)
            ((Fin.castAdd_injective k k).ne hij) 1 1) t *
        spinRotation (realCliffordForm (k + k) 0)
          (Pi.single (Fin.natAdd k i) 1) (Pi.single (Fin.natAdd k j) 1)
          (realCliffordForm_zero_single_one (k + k) (Fin.natAdd k i))
          (realCliffordForm_zero_single_one (k + k) (Fin.natAdd k j))
          (isOrtho_realCliffordForm_single (p := k + k) (q := 0)
            ((Fin.natAdd_injective k k).ne hij) 1 1) t := by
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_eq_mul,
    (realCliffordSpinBlockInlIsometry k k).spinGroupMap_spinRotation
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t,
    (realCliffordSpinBlockInrIsometry k k).spinGroupMap_spinRotation
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t]
  simp only [realCliffordSpinBlockInlIsometry_apply, realCliffordSpinBlockInrIsometry_apply,
    Fin.append_single_zero, Fin.append_zero_single]

/-- **Explicit Clifford-algebra expansion of the doubled coordinate-plane rotation**:
`(cos t + sin t · ι e_i ι e_j) * (cos t + sin t · ι e_{k + i} ι e_{k + j})`. -/
theorem coe_realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) (t : ℝ) :
    (realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) t)) :
        _root_.CliffordAlgebra (realCliffordForm (k + k) 0)) =
      (algebraMap ℝ _ (Real.cos t) +
          Real.sin t •
            (ι (realCliffordForm (k + k) 0) (Pi.single (Fin.castAdd k i) 1) *
              ι (realCliffordForm (k + k) 0) (Pi.single (Fin.castAdd k j) 1))) *
        (algebraMap ℝ _ (Real.cos t) +
          Real.sin t •
            (ι (realCliffordForm (k + k) 0) (Pi.single (Fin.natAdd k i) 1) *
              ι (realCliffordForm (k + k) 0) (Pi.single (Fin.natAdd k j) 1))) := by
  rw [realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation hij t,
    Submonoid.coe_mul, spinRotation_eq_spinCircle, spinRotation_eq_spinCircle,
    coe_spinCircle, coe_spinCircle]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- At Spin angle `π` (a full `2π` rotation in `SO(k)`), the diagonal lift of a coordinate-plane
rotation closes to `1` in `Spin(k + k)`. -/
theorem realCliffordSpinDiagonalLift_spinToSpecialOrthogonal_spinRotation_pi {k : ℕ}
    {i j : Fin k} (hij : i ≠ j) :
    realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) Real.pi)) = 1 := by
  rw [spinRotation_pi, spinGroup.spinToSpecialOrthogonal_negOne, map_one]

end

end TauCeti
