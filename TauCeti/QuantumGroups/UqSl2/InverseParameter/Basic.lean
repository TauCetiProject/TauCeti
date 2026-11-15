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

The coproduct transported through this algebra isomorphism is developed in
`TauCeti.QuantumGroups.UqSl2.InverseParameter.Coproduct`.

## References

* A. Virelizier, *Quantum groups*, Section 2.3, for the rank-one presentation conventions.
-/

public section

namespace TauCeti.UqSl2

/-- A nonzero quantum parameter has a nonzero inverse, so the native Hopf structure
at the inverse parameter is available to importers. -/
instance instFactInvNeZero (q : ℂ) [Fact (q ≠ 0)] : Fact (q⁻¹ ≠ 0) :=
  ⟨inv_ne_zero Fact.out⟩

/-- The generators of `UqSl2 q`, with `K` and `K⁻¹` exchanged, satisfy the relations at any
parameter `p = q⁻¹`.  Taking `p` general lets the same tuple serve both directions. -/
private noncomputable def inverseParameterTuple (p q : ℂ) (hpq : p = q⁻¹) :
    GeneratorTuple p (UqSl2 q) where
  e := e q
  f := f q
  k := kInv q
  kInv := k q
  k_mul_kInv := kInv_mul_k
  kInv_mul_k := k_mul_kInv
  k_mul_e := by simpa only [hpq] using kInv_mul_e (q := q)
  k_mul_f := by simpa only [hpq, inv_inv] using kInv_mul_f (q := q)
  e_mul_f_sub_f_mul_e := by
    -- Both the scalar denominator and the difference of weight generators change sign.
    rw [e_mul_f_sub_f_mul_e, hpq, inv_inv, ← neg_sub q, ← neg_sub (k q), inv_neg, neg_smul_neg]

private noncomputable def inverseParameterHom (p q : ℂ) (hpq : p = q⁻¹) :
    UqSl2 p →ₐ[ℂ] UqSl2 q :=
  liftEquiv.symm (inverseParameterTuple p q hpq)

@[simp]
private theorem inverseParameterHom_e (p q : ℂ) (hpq : p = q⁻¹) :
    inverseParameterHom p q hpq (e p) = e q := by
  rw [← liftEquiv_apply_e]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_f (p q : ℂ) (hpq : p = q⁻¹) :
    inverseParameterHom p q hpq (f p) = f q := by
  rw [← liftEquiv_apply_f]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_k (p q : ℂ) (hpq : p = q⁻¹) :
    inverseParameterHom p q hpq (k p) = kInv q := by
  rw [← liftEquiv_apply_k]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem inverseParameterHom_kInv (p q : ℂ) (hpq : p = q⁻¹) :
    inverseParameterHom p q hpq (kInv p) = k q := by
  rw [← liftEquiv_apply_kInv]
  rw [inverseParameterHom, Equiv.apply_symm_apply]
  rfl

private theorem inverseParameterHom_rightInverse (q : ℂ) :
    (inverseParameterHom q⁻¹ q rfl).comp (inverseParameterHom q q⁻¹ (inv_inv q).symm) =
      AlgHom.id ℂ (UqSl2 q) := by
  apply hom_ext <;> simp

private theorem inverseParameterHom_leftInverse (q : ℂ) :
    (inverseParameterHom q q⁻¹ (inv_inv q).symm).comp (inverseParameterHom q⁻¹ q rfl) =
      AlgHom.id ℂ (UqSl2 q⁻¹) := by
  apply hom_ext <;> simp

/-- The complex algebra isomorphism `UqSl2 q⁻¹ ≃ UqSl2 q` fixing `E` and `F` and
exchanging `K` with `K⁻¹`. -/
noncomputable def inverseParameterEquiv (q : ℂ) : UqSl2 q⁻¹ ≃ₐ[ℂ] UqSl2 q :=
  AlgEquiv.ofAlgHom (inverseParameterHom q⁻¹ q rfl) (inverseParameterHom q q⁻¹ (inv_inv q).symm)
    (inverseParameterHom_rightInverse q) (inverseParameterHom_leftInverse q)

/-- Parameter inversion fixes the raising generator `E`. -/
@[simp]
theorem inverseParameterEquiv_apply_e (q : ℂ) :
    inverseParameterEquiv q (e q⁻¹) = e q := by
  exact inverseParameterHom_e q⁻¹ q rfl

/-- Parameter inversion fixes the lowering generator `F`. -/
@[simp]
theorem inverseParameterEquiv_apply_f (q : ℂ) :
    inverseParameterEquiv q (f q⁻¹) = f q := by
  exact inverseParameterHom_f q⁻¹ q rfl

/-- Parameter inversion sends the source weight generator `K` to `K⁻¹`. -/
@[simp]
theorem inverseParameterEquiv_apply_k (q : ℂ) :
    inverseParameterEquiv q (k q⁻¹) = kInv q := by
  exact inverseParameterHom_k q⁻¹ q rfl

/-- Parameter inversion sends the source inverse weight generator `K⁻¹` to `K`. -/
@[simp]
theorem inverseParameterEquiv_apply_kInv (q : ℂ) :
    inverseParameterEquiv q (kInv q⁻¹) = k q := by
  exact inverseParameterHom_kInv q⁻¹ q rfl

/-- The inverse parameter isomorphism fixes the raising generator `E`. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_e (q : ℂ) :
    (inverseParameterEquiv q).symm (e q) = e q⁻¹ := by
  exact inverseParameterHom_e q q⁻¹ (inv_inv q).symm

/-- The inverse parameter isomorphism fixes the lowering generator `F`. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_f (q : ℂ) :
    (inverseParameterEquiv q).symm (f q) = f q⁻¹ := by
  exact inverseParameterHom_f q q⁻¹ (inv_inv q).symm

/-- The inverse parameter isomorphism sends `K` to the inverse weight generator. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_k (q : ℂ) :
    (inverseParameterEquiv q).symm (k q) = kInv q⁻¹ := by
  exact inverseParameterHom_k q q⁻¹ (inv_inv q).symm

/-- The inverse parameter isomorphism sends `K⁻¹` to the weight generator. -/
@[simp]
theorem inverseParameterEquiv_symm_apply_kInv (q : ℂ) :
    (inverseParameterEquiv q).symm (kInv q) = k q⁻¹ := by
  exact inverseParameterHom_kInv q q⁻¹ (inv_inv q).symm

end TauCeti.UqSl2
