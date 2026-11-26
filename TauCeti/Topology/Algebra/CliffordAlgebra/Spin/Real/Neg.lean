/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Neg
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

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

The comparison `OrthonormalBasis.realSpinGroupEquiv b hQ` of `Spin(n)` with the Spin group of a form
`Q v = -‖v‖²` along an orthonormal frame `b` is continuous with continuous inverse, since it is
the composite of the topological isomorphisms `CliffordAlgebra.spinGroupContinuousMulEquivNeg` and
`QuadraticMap.IsometryEquiv.spinGroupContinuousMulEquiv`. On representatives the `Spinᶜ` frame
comparison `OrthonormalBasis.realSpinCGroupHom` and the inverse of the `Spinᶜ` frame isomorphism
apply these maps, so both are continuous for the quotient topologies.

## Main definitions

* `CliffordAlgebra.realCliffordSpinGroupContinuousMulEquivNeg p q`: the isomorphism
  `realCliffordSpinGroupEquivNeg p q` of topological groups.

## Main results

* `OrthonormalBasis.continuous_realSpinGroupEquiv` and
  `OrthonormalBasis.continuous_realSpinGroupEquiv_symm`: the Spin frame comparison and its inverse
  are continuous.
* `OrthonormalBasis.continuous_realSpinCGroupHom` and
  `OrthonormalBasis.continuous_realSpinCGroupEquiv_symm`: the `Spinᶜ` frame comparison and its
  inverse are continuous.

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

namespace OrthonormalBasis

open CliffordAlgebra TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The Spin frame comparison is continuous. -/
@[fun_prop]
theorem continuous_realSpinGroupEquiv : Continuous (b.realSpinGroupEquiv hQ) := by
  rw [coe_realSpinGroupEquiv, ← coe_spinGroupContinuousMulEquivNeg,
    ← QuadraticMap.IsometryEquiv.coe_spinGroupContinuousMulEquiv]
  fun_prop

/-- The inverse of the Spin frame comparison is continuous. -/
@[fun_prop]
theorem continuous_realSpinGroupEquiv_symm : Continuous (b.realSpinGroupEquiv hQ).symm := by
  rw [coe_realSpinGroupEquiv_symm, ← coe_spinGroupContinuousMulEquivNeg_symm,
    QuadraticMap.IsometryEquiv.spinGroupEquiv_symm,
    ← QuadraticMap.IsometryEquiv.coe_spinGroupContinuousMulEquiv]
  fun_prop

variable (hpos : realCliffordForm n 0 ≠ 0) (hQ₀ : Q ≠ 0)

/-- The `Spinᶜ` frame comparison is continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_realSpinCGroupHom : Continuous (b.realSpinCGroupHom hQ hpos hQ₀) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel _ hpos)).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, realSpinCGroupHom_mk]
  exact (spinCGroup.continuous_mk Q hQ₀).comp
    (((b.continuous_realSpinGroupEquiv hQ).comp continuous_fst).prodMk continuous_snd)

/-- The inverse of the `Spinᶜ` frame isomorphism is continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_realSpinCGroupEquiv_symm :
    Continuous (b.realSpinCGroupEquiv hQ hpos hQ₀).symm := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ₀)).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, realSpinCGroupEquiv_symm_mk]
  exact (spinCGroup.continuous_mk _ hpos).comp
    (((b.continuous_realSpinGroupEquiv_symm hQ).comp continuous_fst).prodMk continuous_snd)

end OrthonormalBasis
