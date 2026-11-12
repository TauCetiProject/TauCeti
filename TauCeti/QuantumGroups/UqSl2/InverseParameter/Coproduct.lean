/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.InverseParameter.Basic
public import TauCeti.QuantumGroups.UqSl2.Hopf
import TauCeti.QuantumGroups.UqSl2.PBW
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Coproduct under inversion of the quantum parameter

The algebra isomorphism `inverseParameterEquiv q` fixes `E, F` and exchanges `K, K⁻¹`.
Transporting the coproduct from `UqSl2 q⁻¹` therefore gives
`E ↦ E ⊗ 1 + K⁻¹ ⊗ E`, `F ↦ F ⊗ K + 1 ⊗ F` and `K ↦ K ⊗ K`.
The counit is unchanged. These formulas specify the tensor action when comparing modules
through parameter inversion; using the standard coproduct at `q` would give a different action.

We construct the transported algebra homomorphism, prove its coassociativity and counit laws,
and use PBW coefficients to show that it differs from the standard coproduct for every nonzero
parameter, including the roots of unity. In particular the algebra isomorphism is not a
bialgebra isomorphism for the standard structures.

The construction uses `inverseParameterEquiv`, the native Hopf structure of `UqSl2`, and its
`pbwBasis`. The presentation and coproduct conventions follow A. Virelizier, *Quantum groups*,
Sections 2.3--2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- The coproduct on `UqSl2 q` transported from the parameter `q⁻¹` through
`inverseParameterEquiv q`. It has the same group-like weight generators but the opposite
choices of weight generator in the skew-primitive formulas. -/
noncomputable def inverseParameterComul : UqSl2 q →ₐ[ℂ] UqSl2 q ⊗[ℂ] UqSl2 q :=
  (Algebra.TensorProduct.map (inverseParameterEquiv q).toAlgHom
    (inverseParameterEquiv q).toAlgHom).comp
      ((Bialgebra.comulAlgHom ℂ (UqSl2 q⁻¹)).comp (inverseParameterEquiv q).symm.toAlgHom)

/-- The transport formula for the inverted-parameter coproduct. -/
theorem inverseParameterComul_apply (x : UqSl2 q) :
    inverseParameterComul q x =
      Algebra.TensorProduct.map (inverseParameterEquiv q).toAlgHom
        (inverseParameterEquiv q).toAlgHom
        (Coalgebra.comul ((inverseParameterEquiv q).symm x)) := (rfl)

/-- Parameter inversion intertwines the source coproduct with the transported coproduct. -/
@[simp]
theorem inverseParameterComul_inverseParameterEquiv (x : UqSl2 q⁻¹) :
    inverseParameterComul q (inverseParameterEquiv q x) =
      Algebra.TensorProduct.map (inverseParameterEquiv q).toAlgHom
        (inverseParameterEquiv q).toAlgHom (Coalgebra.comul x) := by
  rw [inverseParameterComul_apply, AlgEquiv.symm_apply_apply]

/-- In the transported coproduct, `E` is skew primitive relative to `K⁻¹`. -/
@[simp]
theorem inverseParameterComul_e :
    inverseParameterComul q (e q) = e q ⊗ₜ[ℂ] 1 + kInv q ⊗ₜ[ℂ] e q := by
  simp [inverseParameterComul_apply]

/-- In the transported coproduct, `F` is skew primitive relative to `K`. -/
@[simp]
theorem inverseParameterComul_f :
    inverseParameterComul q (f q) = f q ⊗ₜ[ℂ] k q + 1 ⊗ₜ[ℂ] f q := by
  simp [inverseParameterComul_apply]

/-- The weight generator remains group-like in the transported coproduct. -/
@[simp]
theorem inverseParameterComul_k :
    inverseParameterComul q (k q) = k q ⊗ₜ[ℂ] k q := by
  simp [inverseParameterComul_apply]

/-- The inverse weight generator remains group-like in the transported coproduct. -/
@[simp]
theorem inverseParameterComul_kInv :
    inverseParameterComul q (kInv q) = kInv q ⊗ₜ[ℂ] kInv q := by
  simp [inverseParameterComul_apply]

/-- The standard counits at `q⁻¹` and `q` agree under the parameter isomorphism. -/
@[simp]
theorem counit_inverseParameterEquiv (x : UqSl2 q⁻¹) :
    Coalgebra.counit (R := ℂ) (inverseParameterEquiv q x) = Coalgebra.counit x := by
  have h : (Bialgebra.counitAlgHom ℂ (UqSl2 q)).comp
      (inverseParameterEquiv q).toAlgHom = Bialgebra.counitAlgHom ℂ (UqSl2 q⁻¹) := by
    apply hom_ext <;> simp
  exact DFunLike.congr_fun h x

/-- The inverted-parameter coproduct is coassociative, with the native tensor associator. -/
theorem inverseParameterComul_coassoc :
    (Algebra.TensorProduct.assoc ℂ ℂ ℂ (UqSl2 q) (UqSl2 q) (UqSl2 q)).toAlgHom.comp
        ((Algebra.TensorProduct.map (inverseParameterComul q) (AlgHom.id ℂ (UqSl2 q))).comp
          (inverseParameterComul q)) =
      (Algebra.TensorProduct.map (AlgHom.id ℂ (UqSl2 q)) (inverseParameterComul q)).comp
        (inverseParameterComul q) := by
  apply hom_ext <;>
    simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
      Algebra.TensorProduct.one_def]

/-- Applying the counit on the first leg gives the native left unit identification. -/
theorem rTensor_counit_comp_inverseParameterComul :
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom ℂ (UqSl2 q))
      (AlgHom.id ℂ (UqSl2 q))).comp (inverseParameterComul q) =
        (Algebra.TensorProduct.lid ℂ (UqSl2 q)).symm.toAlgHom := by
  apply hom_ext <;> simp

/-- Applying the counit on the second leg gives the native right unit identification. -/
theorem lTensor_counit_comp_inverseParameterComul :
    (Algebra.TensorProduct.map (AlgHom.id ℂ (UqSl2 q))
      (Bialgebra.counitAlgHom ℂ (UqSl2 q))).comp (inverseParameterComul q) =
        (Algebra.TensorProduct.rid ℂ ℂ (UqSl2 q)).symm.toAlgHom := by
  apply hom_ext <;> simp

/-- Parameter inversion fails to preserve the standard coproduct already on `E`, for every
nonzero parameter. This includes `q = 1`: in the denominator presentation `K` and `K⁻¹` are
still distinct PBW monomials. -/
theorem inverseParameterComul_e_ne_comul :
    inverseParameterComul q (e q) ≠ Coalgebra.comul (R := ℂ) (e q) := by
  intro h
  rw [inverseParameterComul_e, comul_e, add_right_inj] at h
  -- The coefficient of `K ⊗ E` is zero on the left and one on the right.
  have he : pbwBasis q (0, 0, 1) = e q := by simp
  have hk : pbwBasis q (0, 1, 0) = k q := by simp
  have hki : pbwBasis q (0, -1, 0) = kInv q := by simp
  have hc := congrArg (fun z => ((pbwBasis q).tensorProduct (pbwBasis q)).repr z
    ((0, 1, 0), (0, 0, 1))) h
  rw [← he, ← hk, ← hki] at hc
  simp only [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self] at hc
  norm_num [Finsupp.single_apply] at hc

/-- The coproduct transported through parameter inversion differs from the standard one. -/
theorem inverseParameterComul_ne_comul :
    inverseParameterComul q ≠ Bialgebra.comulAlgHom ℂ (UqSl2 q) := by
  intro h
  exact inverseParameterComul_e_ne_comul q (DFunLike.congr_fun h (e q))

end TauCeti.UqSl2
