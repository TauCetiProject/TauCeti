/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.QuantumGroups.UqSl2.Basic

import Mathlib.Tactic.NormNum

/-!
# Rescaling automorphisms of U_q(sl₂)

The assignments `E ↦ t E`, `F ↦ t⁻¹ F`, `K ↦ K`, `K⁻¹ ↦ K⁻¹` preserve the
rank-one presentation. They give a multiplicative family of algebra automorphisms
`UqSl2.rescale`, parametrized by complex units. No restriction on `q` is needed.

These automorphisms record the freedom to normalize raising and lowering operators
without changing the weight operator. On an ordered monomial `F^a K^b E^c`, the
rescaling factor is `t⁻ᵃ tᶜ`; the integer power of `K` is unchanged.

For nonzero `q`, conjugation by `K` is the rescaling automorphism with parameter `q²`, so
conjugation by `K ^ b` multiplies `E` by `q ^ (2b)`.
-/

public section

namespace TauCeti.UqSl2

variable (q : ℂ)

private def rescaleAlgHom (t : ℂˣ) : UqSl2 q →ₐ[ℂ] UqSl2 q :=
  lift
    { e := (t : ℂ) • e q
      f := ((t⁻¹ : ℂˣ) : ℂ) • f q
      k := k q
      kInv := kInv q
      k_mul_kInv := k_mul_kInv
      kInv_mul_k := kInv_mul_k
      k_mul_e := by rw [mul_smul_comm, k_mul_e, smul_mul_assoc, smul_comm]
      k_mul_f := by rw [mul_smul_comm, k_mul_f, smul_mul_assoc, smul_comm]
      e_mul_f_sub_f_mul_e := by
        simp [smul_smul, e_mul_f_sub_f_mul_e] }

/- `lift_generator` returns `GeneratorTuple.toFun`, whose body and equations are not exposed
downstream. The four proofs below use the public `liftEquiv` equations to access tuple fields;
the reverse rewrites put the goal in the form of `liftEquiv.apply_symm_apply`. -/
@[simp] private theorem rescaleAlgHom_e (t : ℂˣ) :
    rescaleAlgHom q t (e q) = (t : ℂ) • e q := by
  unfold rescaleAlgHom
  rw [← liftEquiv_symm_apply, ← liftEquiv_apply_e]
  exact congrArg GeneratorTuple.e (liftEquiv.apply_symm_apply _)

@[simp] private theorem rescaleAlgHom_f (t : ℂˣ) :
    rescaleAlgHom q t (f q) = ((t⁻¹ : ℂˣ) : ℂ) • f q := by
  unfold rescaleAlgHom
  rw [← liftEquiv_symm_apply, ← liftEquiv_apply_f]
  exact congrArg GeneratorTuple.f (liftEquiv.apply_symm_apply _)

@[simp] private theorem rescaleAlgHom_k (t : ℂˣ) :
    rescaleAlgHom q t (k q) = k q := by
  unfold rescaleAlgHom
  rw [← liftEquiv_symm_apply, ← liftEquiv_apply_k]
  exact congrArg GeneratorTuple.k (liftEquiv.apply_symm_apply _)

@[simp] private theorem rescaleAlgHom_kInv (t : ℂˣ) :
    rescaleAlgHom q t (kInv q) = kInv q := by
  unfold rescaleAlgHom
  rw [← liftEquiv_symm_apply, ← liftEquiv_apply_kInv]
  exact congrArg GeneratorTuple.kInv (liftEquiv.apply_symm_apply _)

private theorem rescaleAlgHom_one : rescaleAlgHom q 1 = AlgHom.id ℂ (UqSl2 q) := by
  apply hom_ext <;> simp

private theorem rescaleAlgHom_mul (s t : ℂˣ) :
    rescaleAlgHom q (s * t) = (rescaleAlgHom q s).comp (rescaleAlgHom q t) := by
  apply hom_ext <;> simp [smul_smul, mul_comm]

/-- Rescale `E` by a complex unit and `F` by its inverse, fixing `K` and `K⁻¹`.
Multiplication of parameters corresponds to composition of algebra automorphisms. -/
def rescale : ℂˣ →* (UqSl2 q ≃ₐ[ℂ] UqSl2 q) where
  toFun t := AlgEquiv.ofAlgHom (rescaleAlgHom q t) (rescaleAlgHom q t⁻¹)
    (by rw [← rescaleAlgHom_mul, mul_inv_cancel, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, inv_mul_cancel, rescaleAlgHom_one])
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact rescaleAlgHom_one q
  map_mul' s t := by
    apply AlgEquiv.coe_toAlgHom_injective
    exact rescaleAlgHom_mul q s t

variable {q}

/-- The rescaling automorphism multiplies the raising generator by its parameter. -/
@[simp] theorem rescale_e (t : ℂˣ) : rescale q t (e q) = (t : ℂ) • e q :=
  rescaleAlgHom_e q t

/-- The rescaling automorphism multiplies the lowering generator by the inverse parameter. -/
@[simp] theorem rescale_f (t : ℂˣ) :
    rescale q t (f q) = ((t⁻¹ : ℂˣ) : ℂ) • f q :=
  rescaleAlgHom_f q t

/-- Rescaling fixes the weight generator. -/
@[simp] theorem rescale_k (t : ℂˣ) : rescale q t (k q) = k q :=
  rescaleAlgHom_k q t

/-- Rescaling fixes the inverse weight generator. -/
@[simp] theorem rescale_kInv (t : ℂˣ) : rescale q t (kInv q) = kInv q :=
  rescaleAlgHom_kInv q t

/-- Rescaling fixes every integer power of the distinguished weight unit. -/
@[simp] theorem rescale_kUnit_zpow (t : ℂˣ) (b : ℤ) :
    rescale q t ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) := by
  let φ : UqSl2 q →* UqSl2 q := (rescale q t : UqSl2 q →ₐ[ℂ] UqSl2 q)
  have h : Units.map φ (kUnit q) = kUnit q := by
    ext
    simp [φ]
  simpa only [h, Units.coe_map, φ, AlgHom.coe_toMonoidHom, AlgEquiv.coe_toAlgHom] using
    congrArg (fun u : (UqSl2 q)ˣ => (u : UqSl2 q))
      ((Units.map φ).map_zpow (kUnit q) b)

/-- An ordered monomial has rescaling weight `c - a`, independently of its `K` exponent.
This formula does not assume linear independence of the ordered monomials. -/
theorem rescale_orderedMonomial (t : ℂˣ) (a c : ℕ) (b : ℤ) :
    rescale q t (f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q ^ c) =
      (((t⁻¹ : ℂˣ) : ℂ) ^ a * (t : ℂ) ^ c) •
        (f q ^ a * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q ^ c) := by
  simp [smul_pow, smul_smul, mul_comm]

variable [Fact (q ≠ 0)]

/-- Conjugation by `K` is the rescaling automorphism with parameter `q²`. -/
theorem toAlgEquiv_conjAct_kUnit :
    MulSemiringAction.toAlgEquiv ℂ (UqSl2 q) (ConjAct.toConjAct (kUnit q)) =
      rescale q (Units.mk0 q Fact.out ^ 2) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply hom_ext
  · simp [ConjAct.units_smul_def, k_mul_e, mul_assoc, smul_smul, sq]
  · simp [ConjAct.units_smul_def, k_mul_f, mul_assoc, smul_smul, sq]
  · simp [ConjAct.units_smul_def, mul_assoc]
  · simp [ConjAct.units_smul_def]

/-- Conjugation by an integer power of `K` rescales `E`. -/
theorem kUnit_zpow_mul_e_mul_inv (b : ℤ) :
    ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q * ((kUnit q ^ b)⁻¹ : (UqSl2 q)ˣ) =
      q ^ (2 * b) • e q := by
  have h : MulSemiringAction.toAlgAut (ConjAct (UqSl2 q)ˣ) ℂ (UqSl2 q)
      (ConjAct.toConjAct (kUnit q ^ b)) = rescale q ((Units.mk0 q Fact.out ^ 2) ^ b) := by
    rw [map_zpow, map_zpow, MulSemiringAction.toAlgAut_apply, toAlgEquiv_conjAct_kUnit,
      map_zpow]
  have he := congrArg (fun φ : UqSl2 q ≃ₐ[ℂ] UqSl2 q => φ (e q)) h
  simp only [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply,
    ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, rescale_e] at he
  rw [he, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← zpow_natCast,
    ← zpow_mul]
  norm_num

/-- Commuting `E` past an integer power of `K` multiplies by `q ^ (-2b)`. -/
theorem e_mul_kUnit_zpow (b : ℤ) :
    e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      q ^ (-2 * b) • (((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) * e q) := by
  have h := kUnit_zpow_mul_e_mul_inv (q := q) (-b)
  rw [zpow_neg, inv_inv] at h
  have hconj : e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) =
      ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q) *
        (((kUnit q ^ b)⁻¹ : (UqSl2 q)ˣ) * e q * ((kUnit q ^ b : (UqSl2 q)ˣ) : UqSl2 q)) := by
    rw [mul_assoc, Units.mul_inv_cancel_left]
  rw [hconj, h, mul_smul_comm, mul_neg, neg_mul]

end TauCeti.UqSl2
