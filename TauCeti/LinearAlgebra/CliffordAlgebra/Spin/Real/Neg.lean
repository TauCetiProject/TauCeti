/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic

/-!
# The compact Spin group in the negative-definite Clifford algebra

The compact Spin group `Spin(n)` is `CliffordAlgebra.realCliffordSpinGroupZero n`, the Spin group
of the positive-definite form `realCliffordForm n 0`. Geometric Clifford multiplication instead uses
the negative-definite form, for which `c(v)² = -|v|²`; its coordinate model is
`realCliffordForm 0 n`. This file transports `Spin(n)` into the Clifford algebra of that model.

The isomorphism `CliffordAlgebra.realCliffordSpinZeroEquivNeg n` is
`CliffordAlgebra.spinGroupEquivNeg`, followed by the coordinate isometry
`realCliffordFormNegIsometry n 0` from `-realCliffordForm n 0` to `realCliffordForm 0 n`. It sends a
positive-form bivector `ι a * ι b` to minus the corresponding negative-form bivector. It intertwines
the two vector actions through the coordinate isometry, and it sends `-1` to `-1`.

## Main results

* `CliffordAlgebra.realCliffordSpinZeroEquivNeg`: the isomorphism
  `Spin(n) ≃* spinGroup (realCliffordForm 0 n)`.
* `CliffordAlgebra.coe_realCliffordSpinZeroEquivNeg_apply_of_coe_eq_ι_mul_ι`: the bivector
  sign.
* `CliffordAlgebra.spinVectorAction_realCliffordSpinZeroEquivNeg`: the vector actions agree
  under the coordinate isometry.
* `CliffordAlgebra.realCliffordSpinZeroEquivNeg_negOne`: the central element `-1` goes to `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable (n : ℕ)

/-- The compact Spin group `Spin(n)` of the positive-definite form, transported into the Clifford
algebra of the negative-definite coordinate form `realCliffordForm 0 n`. -/
noncomputable def realCliffordSpinZeroEquivNeg :
    realCliffordSpinGroupZero n ≃* realCliffordSpinGroup 0 n :=
  (spinGroupEquivNeg (realCliffordForm n 0)).trans
    (realCliffordFormNegIsometry n 0).spinGroupEquiv

/-- The Clifford value of `realCliffordSpinZeroEquivNeg n x` is obtained by applying
`evenEquivEvenNeg` and then the coordinate isometry. -/
theorem coe_realCliffordSpinZeroEquivNeg_apply (x : realCliffordSpinGroupZero n) :
    (realCliffordSpinZeroEquivNeg n x : CliffordAlgebra (realCliffordForm 0 n)) =
      map (realCliffordFormNegIsometry n 0).toIsometry
        (evenEquivEvenNeg (realCliffordForm n 0) (spinGroupToEven (realCliffordForm n 0) x)) := by
  rw [realCliffordSpinZeroEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupEquivNeg_apply]

/-- A positive-form bivector `ι a * ι b` in `Spin(n)` goes to minus the negative-form bivector of
the transported vectors. -/
theorem coe_realCliffordSpinZeroEquivNeg_apply_of_coe_eq_ι_mul_ι
    {x : realCliffordSpinGroupZero n} {a b : Fin (n + 0) → ℝ}
    (hx : (x : CliffordAlgebra (realCliffordForm n 0)) =
      ι (realCliffordForm n 0) a * ι (realCliffordForm n 0) b) :
    (realCliffordSpinZeroEquivNeg n x : CliffordAlgebra (realCliffordForm 0 n)) =
      -(ι (realCliffordForm 0 n) (realCliffordFormNegIsometry n 0 a) *
        ι (realCliffordForm 0 n) (realCliffordFormNegIsometry n 0 b)) := by
  rw [realCliffordSpinZeroEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι _ hx, map_neg, map_mul, map_apply_ι, map_apply_ι,
    QuadraticMap.IsometryEquiv.toIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply]

/-- Under `realCliffordSpinZeroEquivNeg`, the vector actions of `Spin(n)` and of the negative-form
Spin group correspond through the coordinate isometry `realCliffordFormNegIsometry n 0`. -/
@[simp]
theorem spinVectorAction_realCliffordSpinZeroEquivNeg (x : realCliffordSpinGroupZero n)
    (v : Fin (n + 0) → ℝ) :
    spinVectorAction (realCliffordForm 0 n) (realCliffordSpinZeroEquivNeg n x)
        (realCliffordFormNegIsometry n 0 v) =
      realCliffordFormNegIsometry n 0 (spinVectorAction (realCliffordForm n 0) x v) := by
  rw [realCliffordSpinZeroEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply]
  exact (QuadraticMap.Isometry.spinGroupMap_spinVectorAction _ _ v).trans
    (congrArg _ (LinearEquiv.congr_fun (spinVectorAction_spinGroupEquivNeg _ x) v))

/-- In positive dimension, `realCliffordSpinZeroEquivNeg` sends the central element `-1` of
`Spin(n)` to `-1`. -/
@[simp]
theorem realCliffordSpinZeroEquivNeg_negOne [NeZero n] :
    realCliffordSpinZeroEquivNeg n
        (spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero) =
      spinGroup.negOne (realCliffordForm 0 n) (nondegenerate_realCliffordForm 0 n).ne_zero := by
  rw [realCliffordSpinZeroEquivNeg, MulEquiv.trans_apply, spinGroupEquivNeg_negOne,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.spinGroupMap_negOne]

end CliffordAlgebra
