/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DoubleCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

/-!
# The Spin cover of the spinor-norm kernel

Over a general field, the Spin action need not be surjective onto the whole special orthogonal
group. Its image is exactly the kernel of the spinor norm. `SpinorNorm.Basic` corestricts the
action to that kernel; this file packages the resulting short exact sequence as a group extension.

## Main definitions and results

* `CliffordAlgebra.spinDoubleCoverSpinorNormKernel` packages the short exact sequence with kernel
  `Multiplicative (ZMod 2)`.
* `CliffordAlgebra.spinDoubleCoverSpinorNormKernel_inl_ofAdd_one` and
  `CliffordAlgebra.spinDoubleCoverSpinorNormKernel_rightHom` identify its two maps.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2. This is the
spinor-norm-kernel analogue of the Spin extension in
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DoubleCover`.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- For a positive-dimensional finite nondegenerate quadratic space over a field in which `2` is
invertible, the Spin group is an extension of the spinor-norm kernel by `ZMod 2`. -/
noncomputable def spinDoubleCoverSpinorNormKernel [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (MonoidHom.ker (spinorNorm Q hQ)) :=
  GroupExtension.ofMulEquivKer
    (spinToSpinorNormKernel_surjective Q hQ)
    ((zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).trans <|
      MulEquiv.subgroupCongr (ker_spinToSpinorNormKernel Q hQ).symm)

/-- The inclusion in the Spin cover of the spinor-norm kernel sends the generator to the scalar
`-1`. -/
@[simp]
theorem spinDoubleCoverSpinorNormKernel_inl_ofAdd_one [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCoverSpinorNormKernel Q hQ).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q hQ.ne_zero := by
  rw [spinDoubleCoverSpinorNormKernel, GroupExtension.ofMulEquivKer_inl,
    MonoidHom.comp_apply]
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.subtype_apply] using congrArg Subtype.val
      (zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one Q hQ)

/-- The projection in the Spin cover of the spinor-norm kernel is the corestricted Spin action. -/
@[simp]
theorem spinDoubleCoverSpinorNormKernel_rightHom [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCoverSpinorNormKernel Q hQ).rightHom = spinToSpinorNormKernel Q hQ := by
  rw [spinDoubleCoverSpinorNormKernel, GroupExtension.ofMulEquivKer_rightHom]

end CliffordAlgebra
