/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Basic

/-!
# Inverting the parameter of the quantized enveloping algebra of sl₂

The presentations at `q⁻¹` and `q` are isomorphic: fixing `E` and `F` while exchanging `K`
and `K⁻¹` preserves all the defining relations.  This file constructs that algebra isomorphism
and records its action, in both directions, on the four generators.

This comparison is algebraic.  No compatibility with the standard coproduct is asserted here;
transporting that coproduct gives a separate comparison.

## References

* A. Virelizier, *Quantum groups*, Section 2.3, for the rank-one presentation conventions.
-/

public section

namespace TauCeti.UqSl2

private noncomputable def inverseParameterTuple (q : ℂ) : GeneratorTuple q⁻¹ (UqSl2 q) where
  e := e q
  f := f q
  k := kInv q
  kInv := k q
  k_mul_kInv := kInv_mul_k
  kInv_mul_k := k_mul_kInv
  k_mul_e := by simpa only using kInv_mul_e (q := q)
  k_mul_f := by simpa only [inv_inv] using kInv_mul_f (q := q)
  e_mul_f_sub_f_mul_e := by
    rw [e_mul_f_sub_f_mul_e]
    rw [inv_inv]
    rw [show q⁻¹ - q = -(q - q⁻¹) by ring]
    rw [show kInv q - k q = -(k q - kInv q) by abel]
    rw [inv_neg, neg_smul, smul_neg, neg_neg]

private noncomputable def inverseParameterHom (q : ℂ) : UqSl2 q⁻¹ →ₐ[ℂ] UqSl2 q :=
  liftEquiv.symm (inverseParameterTuple q)

@[simp]
private theorem inverseParameterHom_e (q : ℂ) :
    inverseParameterHom q (e q⁻¹) = e q := by
  rw [← liftEquiv_apply_e]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_f (q : ℂ) :
    inverseParameterHom q (f q⁻¹) = f q := by
  rw [← liftEquiv_apply_f]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_k (q : ℂ) :
    inverseParameterHom q (k q⁻¹) = kInv q := by
  rw [← liftEquiv_apply_k]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_kInv (q : ℂ) :
    inverseParameterHom q (kInv q⁻¹) = k q := by
  rw [← liftEquiv_apply_kInv]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

private noncomputable def inverseParameterInvTuple (q : ℂ) : GeneratorTuple q (UqSl2 q⁻¹) where
  e := e q⁻¹
  f := f q⁻¹
  k := kInv q⁻¹
  kInv := k q⁻¹
  k_mul_kInv := kInv_mul_k
  kInv_mul_k := k_mul_kInv
  k_mul_e := by simpa only [inv_inv] using kInv_mul_e (q := q⁻¹)
  k_mul_f := by simpa only [inv_inv] using kInv_mul_f (q := q⁻¹)
  e_mul_f_sub_f_mul_e := by
    rw [e_mul_f_sub_f_mul_e]
    rw [inv_inv]
    rw [show q⁻¹ - q = -(q - q⁻¹) by ring]
    rw [show k q⁻¹ - kInv q⁻¹ = -(kInv q⁻¹ - k q⁻¹) by abel]
    rw [inv_neg, neg_smul, smul_neg, neg_neg]

private noncomputable def inverseParameterInvHom (q : ℂ) : UqSl2 q →ₐ[ℂ] UqSl2 q⁻¹ :=
  liftEquiv.symm (inverseParameterInvTuple q)

@[simp]
private theorem inverseParameterInvHom_e (q : ℂ) :
    inverseParameterInvHom q (e q) = e q⁻¹ := by
  rw [← liftEquiv_apply_e]
  rw [inverseParameterInvHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterInvHom_f (q : ℂ) :
    inverseParameterInvHom q (f q) = f q⁻¹ := by
  rw [← liftEquiv_apply_f]
  rw [inverseParameterInvHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterInvHom_k (q : ℂ) :
    inverseParameterInvHom q (k q) = kInv q⁻¹ := by
  rw [← liftEquiv_apply_k]
  rw [inverseParameterInvHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterInvHom_kInv (q : ℂ) :
    inverseParameterInvHom q (kInv q) = k q⁻¹ := by
  rw [← liftEquiv_apply_kInv]
  rw [inverseParameterInvHom, Equiv.apply_symm_apply]
  rfl

private theorem inverseParameterHom_comp_invHom (q : ℂ) :
    (inverseParameterHom q).comp (inverseParameterInvHom q) = AlgHom.id ℂ (UqSl2 q) := by
  apply hom_ext <;> simp

private theorem inverseParameterInvHom_comp_hom (q : ℂ) :
    (inverseParameterInvHom q).comp (inverseParameterHom q) = AlgHom.id ℂ (UqSl2 q⁻¹) := by
  apply hom_ext <;> simp

/-- The complex algebra isomorphism `UqSl2 q⁻¹ ≃ UqSl2 q` fixing `E` and `F` and
exchanging `K` with `K⁻¹`. -/
noncomputable def inverseParameterEquiv (q : ℂ) : UqSl2 q⁻¹ ≃ₐ[ℂ] UqSl2 q :=
  AlgEquiv.ofAlgHom (inverseParameterHom q) (inverseParameterInvHom q)
    (inverseParameterHom_comp_invHom q) (inverseParameterInvHom_comp_hom q)

/-- Parameter inversion fixes the raising generator `E`. -/
@[simp]
theorem inverseParameterEquiv_apply_e (q : ℂ) :
    inverseParameterEquiv q (e q⁻¹) = e q := by
  exact inverseParameterHom_e q

/-- Parameter inversion fixes the lowering generator `F`. -/
@[simp]
theorem inverseParameterEquiv_apply_f (q : ℂ) :
    inverseParameterEquiv q (f q⁻¹) = f q := by
  exact inverseParameterHom_f q

/-- Parameter inversion sends the source weight generator `K` to `K⁻¹`. -/
@[simp]
theorem inverseParameterEquiv_apply_k (q : ℂ) :
    inverseParameterEquiv q (k q⁻¹) = kInv q := by
  exact inverseParameterHom_k q

/-- Parameter inversion sends the source inverse weight generator `K⁻¹` to `K`. -/
@[simp]
theorem inverseParameterEquiv_apply_kInv (q : ℂ) :
    inverseParameterEquiv q (kInv q⁻¹) = k q := by
  exact inverseParameterHom_kInv q

/-- The inverse parameter isomorphism fixes the raising generator `E`. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_e (q : ℂ) :
    (inverseParameterEquiv q).symm (e q) = e q⁻¹ := by
  exact inverseParameterInvHom_e q

/-- The inverse parameter isomorphism fixes the lowering generator `F`. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_f (q : ℂ) :
    (inverseParameterEquiv q).symm (f q) = f q⁻¹ := by
  exact inverseParameterInvHom_f q

/-- The inverse parameter isomorphism sends `K` to the inverse weight generator. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_k (q : ℂ) :
    (inverseParameterEquiv q).symm (k q) = kInv q⁻¹ := by
  exact inverseParameterInvHom_k q

/-- The inverse parameter isomorphism sends `K⁻¹` to the weight generator. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_kInv (q : ℂ) :
    (inverseParameterEquiv q).symm (kInv q) = k q⁻¹ := by
  exact inverseParameterInvHom_kInv q

end TauCeti.UqSl2
