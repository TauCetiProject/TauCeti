/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Neg
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic

/-!
# Real Spin groups in the Clifford algebra of the negated signature

Negating the coordinate form `realCliffordForm p q` gives, up to the coordinate isometry
`realCliffordFormNegIsometry p q`, the form `realCliffordForm q p`. This file transports the Spin
group of signature `(p, q)` into the Clifford algebra of signature `(q, p)`.

The main case is the compact Spin group `Spin(n)`, which is `realCliffordSpinGroup n 0`, the Spin
group of the positive-definite form `realCliffordForm n 0`. Geometric Clifford multiplication
instead uses the negative-definite form, for which `c(v)² = -|v|²`; its coordinate model is
`realCliffordForm 0 n`. Taking `p = n` and `q = 0` transports `Spin(n)` into the Clifford algebra of
that model.

The isomorphism `CliffordAlgebra.realCliffordSpinGroupEquivNeg p q` is
`CliffordAlgebra.spinGroupEquivNeg`, followed by the coordinate isometry
`realCliffordFormNegIsometry p q` from `-realCliffordForm p q` to `realCliffordForm q p`. It sends a
bivector `ι a * ι b` to minus the corresponding bivector of the negated signature. It intertwines
the two vector actions through the coordinate isometry, and it sends `-1` to `-1`.

## Main results

* `CliffordAlgebra.realCliffordSpinGroupEquivNeg`: the isomorphism
  `realCliffordSpinGroup p q ≃* realCliffordSpinGroup q p`.
* `CliffordAlgebra.coe_realCliffordSpinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι`: the bivector
  sign.
* `CliffordAlgebra.spinVectorAction_realCliffordSpinGroupEquivNeg`: the vector actions agree
  under the coordinate isometry.
* `CliffordAlgebra.realCliffordSpinGroupEquivNeg_negOne`: the central element `-1` goes to `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable (p q : ℕ)

/-- The Spin group of signature `(p, q)`, transported into the Clifford algebra of the negated
signature `(q, p)`. For `p = n` and `q = 0` this is the compact Spin group `Spin(n)` in the Clifford
algebra of the negative-definite coordinate form `realCliffordForm 0 n`. -/
noncomputable def realCliffordSpinGroupEquivNeg :
    realCliffordSpinGroup p q ≃* realCliffordSpinGroup q p :=
  (spinGroupEquivNeg (realCliffordForm p q)).trans
    (realCliffordFormNegIsometry p q).spinGroupEquiv

/-- The Clifford value of `realCliffordSpinGroupEquivNeg p q x` is obtained by applying
`evenEquivEvenNeg` and then the coordinate isometry. -/
theorem coe_realCliffordSpinGroupEquivNeg_apply (x : realCliffordSpinGroup p q) :
    (realCliffordSpinGroupEquivNeg p q x : CliffordAlgebra (realCliffordForm q p)) =
      map (realCliffordFormNegIsometry p q).toIsometry
        (evenEquivEvenNeg (realCliffordForm p q) (spinGroupToEven (realCliffordForm p q) x)) := by
  rw [realCliffordSpinGroupEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupEquivNeg_apply]

/-- A bivector `ι a * ι b` in the Spin group of signature `(p, q)` goes to minus the bivector of the
transported vectors in signature `(q, p)`. -/
theorem coe_realCliffordSpinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι
    {x : realCliffordSpinGroup p q} {a b : Fin (p + q) → ℝ}
    (hx : (x : CliffordAlgebra (realCliffordForm p q)) =
      ι (realCliffordForm p q) a * ι (realCliffordForm p q) b) :
    (realCliffordSpinGroupEquivNeg p q x : CliffordAlgebra (realCliffordForm q p)) =
      -(ι (realCliffordForm q p) (realCliffordFormNegIsometry p q a) *
        ι (realCliffordForm q p) (realCliffordFormNegIsometry p q b)) := by
  rw [realCliffordSpinGroupEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupEquivNeg_apply_of_coe_eq_ι_mul_ι _ hx, map_neg, map_mul, map_apply_ι, map_apply_ι,
    QuadraticMap.IsometryEquiv.toIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply]

/-- Under `realCliffordSpinGroupEquivNeg`, the vector actions of the Spin groups of signatures
`(p, q)` and `(q, p)` correspond through the coordinate isometry
`realCliffordFormNegIsometry p q`. -/
@[simp]
theorem spinVectorAction_realCliffordSpinGroupEquivNeg (x : realCliffordSpinGroup p q)
    (v : Fin (p + q) → ℝ) :
    spinVectorAction (realCliffordForm q p) (realCliffordSpinGroupEquivNeg p q x)
        (realCliffordFormNegIsometry p q v) =
      realCliffordFormNegIsometry p q (spinVectorAction (realCliffordForm p q) x v) := by
  rw [realCliffordSpinGroupEquivNeg, MulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply]
  exact (QuadraticMap.Isometry.spinGroupMap_spinVectorAction _ _ v).trans
    (congrArg _ (LinearEquiv.congr_fun (spinVectorAction_spinGroupEquivNeg _ x) v))

/-- In positive dimension, i.e. given `NeZero (p + q)`, `realCliffordSpinGroupEquivNeg` sends the
central element `-1` to `-1`. -/
@[simp]
theorem realCliffordSpinGroupEquivNeg_negOne [NeZero (p + q)] :
    realCliffordSpinGroupEquivNeg p q
        (spinGroup.negOne (realCliffordForm p q) (nondegenerate_realCliffordForm p q).ne_zero) =
      spinGroup.negOne (realCliffordForm q p)
        (haveI : NeZero (q + p) := ⟨by rw [add_comm]; exact NeZero.ne _⟩
        (nondegenerate_realCliffordForm q p).ne_zero) := by
  rw [realCliffordSpinGroupEquivNeg, MulEquiv.trans_apply, spinGroupEquivNeg_negOne,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.spinGroupMap_negOne]

end CliffordAlgebra
