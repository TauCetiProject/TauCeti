/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# Open one-block rotation path in compact real Spin stabilization

Under the left one-block embedding `g ↦ diag(g, I_m)` into `SO(k + m)`, a full `2π` rotation loop
in the ordered `(e_i, e_j)` coordinate plane lifts to an explicit continuous path in `Spin(k + m)`
starting at `1` and ending at `-1 ≠ 1`.

## Main definitions

* `TauCeti.realCliffordSpinBlockInlRotationPath`: explicit open path lift from `1` to `-1` of a
  full `2π` coordinate-plane rotation under the left one-block embedding `g ↦ diag(g, I_m)`.

## Main results

* `TauCeti.realCliffordSpinBlockInlRotationPath_apply` and
  `TauCeti.spinToSpecialOrthogonal_realCliffordSpinBlockInlRotationPath`: evaluation and projection
  of the open left one-block rotation path lift.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-- **Open path lift of a full `2π` coordinate-plane rotation under the left one-block embedding
`g ↦ diag(g, I_m)`**: starting at `1`, the lifted path in `Spin(k + m)` ends at `-1 ≠ 1`. -/
def realCliffordSpinBlockInlRotationPath {k : ℕ} (m : ℕ) {i j : Fin k} (hij : i ≠ j) :
    Path (1 : realCliffordSpinGroupZero (k + m))
      (spinGroup.negOne (realCliffordForm (k + m) 0) (by
        have : NeZero (k + m) := ⟨Nat.add_pos_left (Fin.pos i) m |>.ne'⟩
        exact (nondegenerate_realCliffordForm (k + m) 0).ne_zero)) :=
  ((spinRotationPath (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
      (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
      (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1)).map
    (f := fun x ↦ realCliffordSpinBlockSum k m (x, 1))
    ((continuous_realCliffordSpinBlockSum k m).comp
      (continuous_id.prodMk continuous_const))).cast
    (map_one (realCliffordSpinBlockSum k m)).symm (by
      rw [realCliffordSpinBlockSum_mk_one]
      exact ((realCliffordSpinBlockInlIsometry k m).spinGroupMap_negOne _).symm)

/-- Evaluating `realCliffordSpinBlockInlRotationPath` at `t` embeds the coordinate-plane rotation
at Spin angle `π t` into the left block of `Spin(k + m)`. -/
@[simp]
theorem realCliffordSpinBlockInlRotationPath_apply {k : ℕ} (m : ℕ) {i j : Fin k} (hij : i ≠ j)
    (t : unitInterval) :
    realCliffordSpinBlockInlRotationPath m hij t =
      realCliffordSpinBlockSum k m
        (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
          (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
          (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ)), 1) := by
  simp [realCliffordSpinBlockInlRotationPath]

/-- The open path `realCliffordSpinBlockInlRotationPath` projects to the left one-block embedding
`t ↦ diag(R(−2π t), I_m)` of the full-turn rotation loop in the ordered `(e_i, e_j)` coordinate
plane (where `Q(e_i) = Q(e_j) = 1`, so `spinRotation` at Spin angle `π t` projects to
`R(−2π t)`). -/
theorem spinToSpecialOrthogonal_realCliffordSpinBlockInlRotationPath {k : ℕ} (m : ℕ)
    {i j : Fin k} (hij : i ≠ j) (t : unitInterval) :
    spinToSpecialOrthogonal (realCliffordForm (k + m) 0)
        (realCliffordSpinBlockInlRotationPath m hij t) =
      realCliffordSpecialOrthogonalBlockSum k m
        (spinToSpecialOrthogonal (realCliffordForm k 0)
          (spinRotation (realCliffordForm k 0) (Pi.single i 1) (Pi.single j 1)
            (realCliffordForm_zero_single_one k i) (realCliffordForm_zero_single_one k j)
            (isOrtho_realCliffordForm_single (p := k) (q := 0) hij 1 1) (Real.pi * (t : ℝ))),
          1) := by
  rw [realCliffordSpinBlockInlRotationPath_apply, spinToSpecialOrthogonal_realCliffordSpinBlockSum,
    map_one]

end

end TauCeti
