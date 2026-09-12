/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.DoubleCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm

/-!
# The Spin cover of the spinor-norm kernel

Over a general field, the Spin action need not be surjective onto the whole special orthogonal
group. Its image is exactly the kernel of the spinor norm. This file corestricts the action to
that kernel and packages the resulting short exact sequence as a group extension.

## Main definitions and results

* `CliffordAlgebra.spinToSpinorNormKernel` is the Spin action with codomain restricted to the
  spinor-norm kernel.
* `CliffordAlgebra.spinToSpinorNormKernel_surjective` proves that this restricted action is
  surjective.
* `CliffordAlgebra.spinDoubleCoverSpinorNormKernel` packages the short exact sequence with kernel
  `Multiplicative (ZMod 2)`.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- The Spin action with codomain restricted to the kernel of the spinor norm. -/
noncomputable def spinToSpinorNormKernel
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    spinGroup Q →* MonoidHom.ker (spinorNorm Q hQ) :=
  (spinToSpecialOrthogonal Q).codRestrict _ fun x ↦
    MonoidHom.mem_ker.mpr (spinorNorm_spinToSpecialOrthogonal Q hQ x)

/-- After inclusion into the special orthogonal group, `spinToSpinorNormKernel` is the usual Spin
action. -/
@[simp]
theorem coe_spinToSpinorNormKernel_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (x : spinGroup Q) :
    ((spinToSpinorNormKernel Q hQ x : MonoidHom.ker (spinorNorm Q hQ)) :
      QuadraticMap.specialOrthogonalGroup Q) = spinToSpecialOrthogonal Q x :=
  by rw [spinToSpinorNormKernel, MonoidHom.codRestrict_apply]

/-- The Spin action is surjective onto the kernel of the spinor norm. -/
theorem spinToSpinorNormKernel_surjective
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (spinToSpinorNormKernel Q hQ) := by
  intro g
  have hg : (g : QuadraticMap.specialOrthogonalGroup Q) ∈
      MonoidHom.range (spinToSpecialOrthogonal Q) := by
    rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

/-- For a positive-dimensional finite nondegenerate quadratic space over a field in which `2` is
invertible, the Spin group is an extension of the spinor-norm kernel by `ZMod 2`. -/
noncomputable def spinDoubleCoverSpinorNormKernel [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    GroupExtension (Multiplicative (ZMod 2)) (spinGroup Q)
      (MonoidHom.ker (spinorNorm Q hQ)) :=
  GroupExtension.ofMulEquivKer
    (spinToSpinorNormKernel_surjective Q hQ)
    ((zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).trans <|
      MulEquiv.subgroupCongr
        (MonoidHom.ker_codRestrict (spinToSpecialOrthogonal Q)
          (MonoidHom.ker (spinorNorm Q hQ))
          (fun x ↦ MonoidHom.mem_ker.mpr
            (spinorNorm_spinToSpecialOrthogonal Q hQ x))).symm)

/-- The inclusion in the Spin cover of the spinor-norm kernel sends the generator to the scalar
`-1`. -/
@[simp]
theorem spinDoubleCoverSpinorNormKernel_inl_ofAdd_one [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCoverSpinorNormKernel Q hQ).inl (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q hQ.ne_zero := by
  rw [spinDoubleCoverSpinorNormKernel, GroupExtension.ofMulEquivKer_inl,
    MonoidHom.comp_apply]
  exact congrArg Subtype.val
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one Q hQ)

/-- The projection in the Spin cover of the spinor-norm kernel is the corestricted Spin action. -/
@[simp]
theorem spinDoubleCoverSpinorNormKernel_rightHom [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (spinDoubleCoverSpinorNormKernel Q hQ).rightHom = spinToSpinorNormKernel Q hQ := by
  rw [spinDoubleCoverSpinorNormKernel, GroupExtension.ofMulEquivKer_rightHom]

end CliffordAlgebra
