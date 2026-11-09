/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Neg
-- Private: the coordinate restriction of an algebra map out of a product and the injectivity of
-- ring maps out of a simple ring are used only inside proofs.
import Mathlib.RingTheory.SimpleRing.Basic
import TauCeti.Algebra.Algebra.Prod
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation

/-!
# The chirality labels of the two factors of compact `Spin(4)`

The compact Spin group in dimension four is built from the positive-definite coordinate form
`realCliffordForm 4 0` and splits as a product of two unit-quaternion groups,
`TauCeti.realSpinFourEquivQuaternionUnitaryProd : Spin(4) ≃ U(ℍ) × U(ℍ)`, or as
`TauCeti.realSpinFourEquivSpecialUnitaryProd : Spin(4) ≃ SU(2) × SU(2)`. The spinor modules of an
oriented four-dimensional real inner product space `V` instead use the negative-definite form
`Q v = -‖v‖²` and split by the chirality element `Γ = -c(e₁) c(e₂) c(e₃) c(e₄)`
(`CliffordAlgebra.chirality`) into the half-spinors `W⁺` and `W⁻`. This file determines which
factor acts on which half.

The half-spinors are compared with the coordinate model along a positively oriented orthonormal
basis `b` of `V`, through the frame comparison `OrthonormalBasis.realSpinGroupEquiv` of the
coordinate Spin group with `spinGroup Q` and its even Clifford algebra counterpart
`OrthonormalBasis.realEvenCliffordEquiv`. The comparison depends on the frame; the results below
hold for every positively oriented frame.

The computation is that `Γ` has quaternion-pair coordinates `(-1, 1)`
(`CliffordAlgebra.chirality_eq_realEvenCliffordEquiv`): in the even Clifford algebra of the
coordinate form, `Γ` is minus the product of the bivectors `e₀ e₁` and `e₂ e₃`, which have
coordinates `(-k, -k)` and `(k, -k)`. Hence the central idempotent `(1 + Γ) / 2` projecting onto
`W⁺` has coordinates `(0, 1)` and `(1 - Γ) / 2` has `(1, 0)`. Consequently:

* the **second** quaternion factor acts on `W⁺` and the first acts trivially there: an element of
  `Spin(4)` acts trivially on a nonzero `W⁺` exactly when its second quaternion is `1`
  (`CliffordAlgebra.halfSpinRep_one_realSpinGroupEquiv_eq_one_iff`);
* the **first** quaternion factor acts on `W⁻` and the second acts trivially there
  (`CliffordAlgebra.halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff`).

The same holds for the two `SU(2)` factors of `TauCeti.realSpinFourEquivSpecialUnitaryProd`. So
in the `Γ` convention of the Seiberg–Witten equations, `SU(2)₊` is the second factor and `SU(2)₋`
the first; the factor order of the coordinate equivalence does not by itself say which half-spinor
module a factor acts on. The nontriviality hypotheses on the half-spinors are necessary for the
converse directions. They hold for the Fock model of an oriented four-space, where both halves
have complex dimension two
(`TauCeti.AlmostComplexStructure.finrank_positiveHalfSpinors_realFockAction`).

## Main results

* `CliffordAlgebra.chirality_eq_realEvenCliffordEquiv`: for a positively oriented `b`, the
  chirality element has quaternion-pair coordinates `(-1, 1)`.
* `CliffordAlgebra.halfSpinRep_one_realSpinGroupEquiv_eq_one_iff`,
  `CliffordAlgebra.halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff`: the kernels of the
  half-spin representations on `W⁺` and `W⁻` are the first and the second quaternion factor.
* `CliffordAlgebra.halfSpinRep_one_realSpinGroupEquiv_eq_one_iff_specialUnitary`,
  `CliffordAlgebra.halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff_specialUnitary`: the same
  for the two `SU(2)` factors.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4 and §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open Module Module.End CliffordAlgebra TauCeti
open scoped Quaternion

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (b : OrthonormalBasis (Fin 4) ℝ V)

include hQ in
/-- **The chirality element has quaternion-pair coordinates `(-1, 1)`**: for every positively
oriented orthonormal basis `b`, the frame comparison of even Clifford algebras sends the element
with coordinates `(-1, 1)` under `TauCeti.realCliffordFourZeroEvenEquivQuaternionProd` to
`Γ = -c(b₀) c(b₁) c(b₂) c(b₃)`. -/
theorem chirality_eq_realEvenCliffordEquiv (hb : b.toBasis.orientation = o) :
    chirality Q o = b.realEvenCliffordEquiv hQ
      (realCliffordFourZeroEvenEquivQuaternionProd.symm (-1, 1)) := by
  rw [realCliffordFourZeroEvenEquivQuaternionProd_symm_neg_one_one, map_neg, map_mul,
    OrthonormalBasis.realEvenCliffordEquiv_ι, OrthonormalBasis.realEvenCliffordEquiv_ι,
    chirality_eq o hQ b hb]
  simp [coe_even_ι_bilin, mul_assoc]

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- The action of `ℍ × ℍ` on an eigenspace of `Γ`, through the quaternion-pair coordinates of the
compact even Clifford algebra and the frame comparison along `b`. -/
private def quaternionProdAction (ε : ℂ) :
    ℍ[ℝ] × ℍ[ℝ] →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) ε) :=
  (evenHalfSpinAction o ρ ε).comp
    ((b.realEvenCliffordEquiv hQ).toAlgHom.comp
      realCliffordFourZeroEvenEquivQuaternionProd.symm.toAlgHom)

include hQ in
/-- The half-spin representation of a frame-compared Spin element is the quaternion-pair action
of its two unit quaternions. -/
private theorem halfSpinRep_realSpinGroupEquiv (ε : ℂ) (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ ε (b.realSpinGroupEquiv hQ s) =
      quaternionProdAction o hQ b ρ ε
        ((realSpinFourEquivQuaternionUnitaryProd s).1,
          (realSpinFourEquivQuaternionUnitaryProd s).2) := by
  rw [coe_realSpinFourEquivQuaternionUnitaryProd_apply,
    evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply, halfSpinRep_apply,
    OrthonormalBasis.spinGroupToEven_realSpinGroupEquiv]
  simp [quaternionProdAction]

include hQ in
/-- On the `ε`-eigenspace of `Γ`, the element with quaternion-pair coordinates `(-1, 1)` acts by
`ε`. -/
private theorem quaternionProdAction_neg_one_one (hb : b.toBasis.orientation = o) (ε : ℂ) :
    quaternionProdAction o hQ b ρ ε (-1, 1) = algebraMap ℂ _ ε := by
  ext ψ
  simp only [quaternionProdAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    coe_evenHalfSpinAction_apply, ← chirality_eq_realEvenCliffordEquiv o hQ b hb,
    mem_eigenspace_iff.1 ψ.2]
  simp [Algebra.algebraMap_eq_smul_one]

/-- `(1, 0) = (1 - (-1, 1)) / 2` in `ℍ × ℍ`. -/
private theorem quaternionProd_one_zero :
    ((1, 0) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 - (-1, 1)) := by
  ext <;> simp
  norm_num

/-- `(0, 1) = (1 + (-1, 1)) / 2` in `ℍ × ℍ`. -/
private theorem quaternionProd_zero_one :
    ((0, 1) : ℍ[ℝ] × ℍ[ℝ]) = (2 : ℝ)⁻¹ • (1 + (-1, 1)) := by
  ext <;> simp
  norm_num

include hQ in
/-- **The second quaternion factor of compact `Spin(4)` acts on the positive half-spinors**: for a
positively oriented orthonormal basis `b` and a Clifford module with nonzero `W⁺`, an element of
`Spin(4)` acts trivially on `W⁺` exactly when its second unit quaternion is `1`. So the first
factor of `TauCeti.realSpinFourEquivQuaternionUnitaryProd` is the kernel of the half-spin
representation on `W⁺`. -/
theorem halfSpinRep_one_realSpinGroupEquiv_eq_one_iff
    [Nontrivial (eigenspace (ρ (chirality Q o)) 1)] (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s) = 1 ↔
      (realSpinFourEquivQuaternionUnitaryProd s).2 = 1 := by
  -- Swap the factors so that the factor acting on `W⁺` comes first.
  let φ := (quaternionProdAction o hQ b ρ 1).comp
    ((AlgHom.snd ℝ ℍ[ℝ] ℍ[ℝ]).prod (AlgHom.fst ℝ ℍ[ℝ] ℍ[ℝ]))
  have hφ : φ (1, 0) = 1 := by
    simp only [φ, AlgHom.comp_apply, AlgHom.prod_apply, AlgHom.fst_apply, AlgHom.snd_apply]
    rw [quaternionProd_zero_one, map_smul, map_add, map_one,
      quaternionProdAction_neg_one_one o hQ b ρ hb, map_one]
    module
  have h : quaternionProdAction o hQ b ρ 1
      ((realSpinFourEquivQuaternionUnitaryProd s).1, (realSpinFourEquivQuaternionUnitaryProd s).2) =
        AlgHom.prodFirst φ hφ (realSpinFourEquivQuaternionUnitaryProd s).2 := by
    rw [AlgHom.prodFirst_apply, ← AlgHom.map_eq_map_fst φ hφ
      ((realSpinFourEquivQuaternionUnitaryProd s).2, (realSpinFourEquivQuaternionUnitaryProd s).1)]
    simp [φ]
  have hinj : Function.Injective (AlgHom.prodFirst φ hφ) :=
    (AlgHom.prodFirst φ hφ).toRingHom.injective
  rw [halfSpinRep_realSpinGroupEquiv, h, ← map_one (AlgHom.prodFirst φ hφ), hinj.eq_iff]
  exact OneMemClass.coe_eq_one

include hQ in
/-- **The first quaternion factor of compact `Spin(4)` acts on the negative half-spinors**: for a
positively oriented orthonormal basis `b` and a Clifford module with nonzero `W⁻`, an element of
`Spin(4)` acts trivially on `W⁻` exactly when its first unit quaternion is `1`. So the second
factor of `TauCeti.realSpinFourEquivQuaternionUnitaryProd` is the kernel of the half-spin
representation on `W⁻`. -/
theorem halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff
    [Nontrivial (eigenspace (ρ (chirality Q o)) (-1))] (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s) = 1 ↔
      (realSpinFourEquivQuaternionUnitaryProd s).1 = 1 := by
  let φ := quaternionProdAction o hQ b ρ (-1)
  have hφ : φ (1, 0) = 1 := by
    rw [quaternionProd_one_zero, map_smul, map_sub, map_one,
      quaternionProdAction_neg_one_one o hQ b ρ hb, map_neg, map_one]
    module
  have hinj : Function.Injective (AlgHom.prodFirst φ hφ) :=
    (AlgHom.prodFirst φ hφ).toRingHom.injective
  rw [halfSpinRep_realSpinGroupEquiv, AlgHom.map_eq_map_fst φ hφ, ← AlgHom.prodFirst_apply φ hφ,
    ← map_one (AlgHom.prodFirst φ hφ), hinj.eq_iff]
  exact OneMemClass.coe_eq_one

include hQ in
/-- **The second `SU(2)` factor of compact `Spin(4)` acts on the positive half-spinors**: an
element of `Spin(4)` acts trivially on a nonzero `W⁺` exactly when its second matrix under
`TauCeti.realSpinFourEquivSpecialUnitaryProd` is `1`. -/
theorem halfSpinRep_one_realSpinGroupEquiv_eq_one_iff_specialUnitary
    [Nontrivial (eigenspace (ρ (chirality Q o)) 1)] (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ 1 (b.realSpinGroupEquiv hQ s) = 1 ↔
      (realSpinFourEquivSpecialUnitaryProd s).2 = 1 := by
  have h : ((realSpinFourEquivSpecialUnitaryProd s).2 : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).2 :=
    congrArg Prod.snd (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [halfSpinRep_one_realSpinGroupEquiv_eq_one_iff o hQ b ρ hb, ← OneMemClass.coe_eq_one,
    ← OneMemClass.coe_eq_one (x := (realSpinFourEquivSpecialUnitaryProd s).2), h,
    ← map_one Quaternion.toComplexMatrix, Quaternion.toComplexMatrix_injective.eq_iff]

include hQ in
/-- **The first `SU(2)` factor of compact `Spin(4)` acts on the negative half-spinors**: an
element of `Spin(4)` acts trivially on a nonzero `W⁻` exactly when its first matrix under
`TauCeti.realSpinFourEquivSpecialUnitaryProd` is `1`. -/
theorem halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff_specialUnitary
    [Nontrivial (eigenspace (ρ (chirality Q o)) (-1))] (hb : b.toBasis.orientation = o)
    (s : spinGroup (realCliffordForm 4 0)) :
    halfSpinRep o ρ (-1) (b.realSpinGroupEquiv hQ s) = 1 ↔
      (realSpinFourEquivSpecialUnitaryProd s).1 = 1 := by
  have h : ((realSpinFourEquivSpecialUnitaryProd s).1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (realSpinFourEquivQuaternionUnitaryProd s).1 :=
    congrArg Prod.fst (coe_realSpinFourEquivSpecialUnitaryProd_apply s)
  rw [halfSpinRep_neg_one_realSpinGroupEquiv_eq_one_iff o hQ b ρ hb, ← OneMemClass.coe_eq_one,
    ← OneMemClass.coe_eq_one (x := (realSpinFourEquivSpecialUnitaryProd s).1), h,
    ← map_one Quaternion.toComplexMatrix, Quaternion.toComplexMatrix_injective.eq_iff]

end CliffordAlgebra
