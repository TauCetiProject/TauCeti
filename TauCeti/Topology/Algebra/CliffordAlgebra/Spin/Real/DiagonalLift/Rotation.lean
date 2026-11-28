/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.DiagonalLift.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# Closed full-turn rotation loop for the compact real diagonal Spin lift

A full `2π` coordinate-plane rotation loop lifts under
`TauCeti.realCliffordSpinDiagonalLift k` to a closed loop (`1` to `1`) in `Spin(k + k)`,
contrasting with the open path (`1` to `-1`) under the left one-block embedding
`TauCeti.realCliffordSpinBlockInlRotationPath` in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization.Rotation`.

## Main definitions

* `TauCeti.realCliffordSpinDiagonalLiftRotationLoop`: explicit closed loop lift (`1` to `1`) of a
  full `2π` coordinate-plane rotation under the diagonal lift.

## Main results

* `TauCeti.realCliffordSpinDiagonalLiftRotationLoop_apply` and
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinDiagonalLiftRotationLoop`: evaluation and
  projection of the closed diagonal rotation loop.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§2 and 6.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-- **Closed loop lift of a full `2π` coordinate-plane rotation under the diagonal Spin lift**:
in the ordered `(e_i, e_j)` coordinate plane (where `Q(e_i) = Q(e_j) = 1`, so `spinRotation` at
Spin angle `π t` projects to `R(−2π t)`), the path in `Spin(k + k)` lifting
`t ↦ diag(R(−2π t), R(−2π t))` starts and ends at `1`. -/
def realCliffordSpinDiagonalLiftRotationLoop {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    Path (1 : realCliffordSpinGroupZero (k + k)) 1 :=
  ((spinRotationPath (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)).map
    ((continuous_realCliffordSpinDiagonalLift k).comp
      (continuous_spinToSpecialOrthogonal_pi (realCliffordForm k 0)))).cast
    (by simp) (by simp)

/-- Evaluating `realCliffordSpinDiagonalLiftRotationLoop` at `t` gives the diagonal lift of the
coordinate-plane rotation at Spin angle `π t`. -/
@[simp]
theorem realCliffordSpinDiagonalLiftRotationLoop_apply {k : ℕ} {i j : Fin k} (hij : i ≠ j)
    (t : unitInterval) :
    realCliffordSpinDiagonalLiftRotationLoop hij t =
      realCliffordSpinDiagonalLift k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)))) := by
  simp [realCliffordSpinDiagonalLiftRotationLoop]

/-- The closed loop `realCliffordSpinDiagonalLiftRotationLoop` projects to the diagonal block sum
of the coordinate-plane rotation loop. -/
theorem spinToSpecialOrthogonal_realCliffordSpinDiagonalLiftRotationLoop {k : ℕ} {i j : Fin k}
    (hij : i ≠ j) (t : unitInterval) :
    spinToSpecialOrthogonal (realCliffordForm (k + k) 0)
        (realCliffordSpinDiagonalLiftRotationLoop hij t) =
      realCliffordSpecialOrthogonalBlockSum k k
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ))),
          spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)))) := by
  rw [realCliffordSpinDiagonalLiftRotationLoop_apply,
    spinToSpecialOrthogonal_realCliffordSpinDiagonalLift]

end

end TauCeti
