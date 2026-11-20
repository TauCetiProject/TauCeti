/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Neg

/-!
# Real Spin groups of opposite signatures as topological groups

The isomorphism `CliffordAlgebra.realCliffordSpinGroupEquivNeg p q` from the real Spin group of
signature `(p, q)` to that of signature `(q, p)` is the comparison
`CliffordAlgebra.spinGroupEquivNeg` of the Spin groups of `realCliffordForm p q` and of its
negative, followed by the Spin isomorphism of the coordinate isometry
`realCliffordFormNegIsometry p q`. Both are isomorphisms of topological groups for the subtype
topologies inside the Clifford algebras (`CliffordAlgebra.spinGroupContinuousMulEquivNeg` and
`QuadraticMap.IsometryEquiv.spinGroupContinuousMulEquiv`), so this file upgrades
`realCliffordSpinGroupEquivNeg p q` to an isomorphism of topological groups.

For `p = n` and `q = 0` this identifies the compact Spin group `Spin(n)`, the Spin group of the
positive-definite form `realCliffordForm n 0`, with the Spin group of the negative-definite form
`realCliffordForm 0 n` used for geometric Clifford multiplication, as topological groups. The
subtype topology on `Spin(n)` agrees with the topology it inherits from the Clifford units
(`CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange`).

## Main definitions

* `CliffordAlgebra.realCliffordSpinGroupContinuousMulEquivNeg p q`: the isomorphism
  `realCliffordSpinGroupEquivNeg p q` of topological groups.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

namespace CliffordAlgebra

open TauCeti TauCeti.CliffordAlgebra

variable (p q : ℕ)

/-- The isomorphism `realCliffordSpinGroupEquivNeg p q` from the real Spin group of signature
`(p, q)` to that of signature `(q, p)`, as an isomorphism of topological groups for the subtype
topologies: the topological comparison `spinGroupContinuousMulEquivNeg` of the Spin groups of a
form and of its negative, followed by that of the coordinate isometry
`realCliffordFormNegIsometry p q`. -/
noncomputable def realCliffordSpinGroupContinuousMulEquivNeg :
    realCliffordSpinGroup p q ≃ₜ* realCliffordSpinGroup q p :=
  (spinGroupContinuousMulEquivNeg (realCliffordForm p q)).trans
    (realCliffordFormNegIsometry p q).spinGroupContinuousMulEquiv

/-- The topological isomorphism `realCliffordSpinGroupContinuousMulEquivNeg p q` evaluates as
`realCliffordSpinGroupEquivNeg p q`. -/
@[simp]
theorem coe_realCliffordSpinGroupContinuousMulEquivNeg :
    ⇑(realCliffordSpinGroupContinuousMulEquivNeg p q) = realCliffordSpinGroupEquivNeg p q := by
  funext x
  apply Subtype.ext
  rw [coe_realCliffordSpinGroupEquivNeg_apply, realCliffordEvenToNeg_apply,
    realCliffordSpinGroupContinuousMulEquivNeg, ContinuousMulEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.coe_spinGroupContinuousMulEquiv,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_apply, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupContinuousMulEquivNeg, coe_spinGroupEquivNeg_apply]

/-- The inverse of `realCliffordSpinGroupContinuousMulEquivNeg p q` evaluates as the inverse of
`realCliffordSpinGroupEquivNeg p q`. -/
@[simp]
theorem coe_realCliffordSpinGroupContinuousMulEquivNeg_symm :
    ⇑(realCliffordSpinGroupContinuousMulEquivNeg p q).symm =
      (realCliffordSpinGroupEquivNeg p q).symm := by
  funext y
  apply (realCliffordSpinGroupEquivNeg p q).injective
  rw [MulEquiv.apply_symm_apply, ← coe_realCliffordSpinGroupContinuousMulEquivNeg,
    ContinuousMulEquiv.apply_symm_apply]

end CliffordAlgebra
