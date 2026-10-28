/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Dual.Basic
public import TauCeti.QuantumGroups.UqSl2.LadderModule

/-!
# Contragredients of the signed ladder modules

For a generic parameter, each signed simple `L_m^ε` is isomorphic to its contragredient
with action `(a φ)(v) = φ(S(a)v)`. The isomorphism sends the highest vector to the coordinate
functional of the lowest vector. Its other values are the normalized lowering string of that
functional. An explicit finite-product formula gives all matrix entries, including the zero
entries outside the reversed diagonal.

The construction uses `AlgHom.hopfDual` and the highest-vector universal property
`LadderModule.lift`. The dual action is installed only locally; the exported equivalence is
complex-linear and its intertwining theorem specifies the representation explicitly.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the antipode convention.
-/

public noncomputable section

open Module

namespace TauCeti.UqSl2.LadderModule

variable {q : ℂ} [Fact (q ≠ 0)] {m : ℕ} {ε : ℤˣ}

/-- The lowering operator on the contragredient, evaluated on a ladder vector. -/
theorem hopfDual_f_apply_vec (φ : Dual ℂ (LadderModule q m ε)) (i : ℤ) :
    (rep q m ε).hopfDual (f q) φ (vec q m ε i) =
      (-(ε : ℂ) * q ^ ((m : ℤ) - 2 * i) * quantumInteger q (i + 1)) *
        φ (vec q m ε (i + 1)) := by
  rw [AlgHom.hopfDual_apply, antipode_f]
  simp only [map_neg, map_mul, LinearMap.neg_apply, Module.End.mul_apply, ← smul_def]
  rw [k_smul_vec, smul_comm, f_smul_vec]
  simp only [map_smul, smul_eq_mul]
  ring

private theorem hopfDual_e_apply_vec (φ : Dual ℂ (LadderModule q m ε)) (i : ℤ) :
    (rep q m ε).hopfDual (e q) φ (vec q m ε i) =
      (-(ε * quantumInteger q (m - i + 1)) * (ε * q ^ (2 * (i - 1) - m))) *
        φ (vec q m ε (i - 1)) := by
  rw [AlgHom.hopfDual_apply, antipode_e]
  simp only [map_neg, map_mul, LinearMap.neg_apply, Module.End.mul_apply, ← smul_def]
  rw [e_smul_vec, smul_comm, kInv_smul_vec]
  simp only [map_smul, smul_eq_mul]
  ring

/-- The powers of the contragredient lowering operator have explicit finite-product entries. -/
theorem hopfDual_f_pow_apply_vec (φ : Dual ℂ (LadderModule q m ε)) (n : ℕ) (i : ℤ) :
    (rep q m ε).hopfDual (f q ^ n) φ (vec q m ε i) =
      (∏ t ∈ Finset.range n,
        (-(ε : ℂ) * q ^ ((m : ℤ) - 2 * (i + t)) * quantumInteger q (i + t + 1))) *
        φ (vec q m ε (i + n)) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, ih, hopfDual_f_apply_vec,
      Finset.prod_range_succ, Nat.cast_succ]
    simp only [mul_assoc, add_assoc]

private local instance dualModule : Module (UqSl2 q) (Dual ℂ (LadderModule q m ε)) :=
  Module.compHom _ (rep q m ε).hopfDual.toRingHom

private theorem dual_smul_def (a : UqSl2 q) (φ : Dual ℂ (LadderModule q m ε)) :
    a • φ = (rep q m ε).hopfDual a φ := (rfl)

private local instance dualTower :
    IsScalarTower ℂ (UqSl2 q) (Dual ℂ (LadderModule q m ε)) where
  smul_assoc c a φ := by
    rw [dual_smul_def, dual_smul_def, map_smul, LinearMap.smul_apply]

omit [Fact (q ≠ 0)] in
private theorem coord_last_vec (i : ℤ) :
    (basis q m ε).coord (Fin.last m) (vec q m ε i) = if (m : ℤ) = i then 1 else 0 := by
  simp [Basis.coord_apply]

private theorem coord_last_weight :
    (basis q m ε).coord (Fin.last m) ∈
      weightSpace q (Dual ℂ (LadderModule q m ε)) (ε * q ^ m) := by
  rw [mem_weightSpace_iff]
  apply (basis q m ε).ext
  intro i
  simp only [dual_smul_def, AlgHom.hopfDual_apply, antipode_k, ← smul_def,
    ← vec_coe, kInv_smul_vec, map_smul, coord_last_vec, LinearMap.smul_apply,
    smul_eq_mul]
  split_ifs with hi
  · congr 2
    norm_cast at hi
    simp [hi, two_mul]
  · simp

private theorem e_smul_coord_last :
    e q • (basis q m ε).coord (Fin.last m) = 0 := by
  apply (basis q m ε).ext
  intro i
  rw [dual_smul_def, ← vec_coe, hopfDual_e_apply_vec, coord_last_vec]
  simp [show (m : ℤ) ≠ (i : ℤ) - 1 by omega]

private theorem f_pow_smul_coord_last :
    f q ^ (m + 1) • (basis q m ε).coord (Fin.last m) = 0 := by
  apply (basis q m ε).ext
  intro i
  rw [dual_smul_def, ← vec_coe, hopfDual_f_pow_apply_vec,
    vec_eq_zero_of_lt (by omega), map_zero, mul_zero, LinearMap.zero_apply]

private def dualHighestHom (hq : IsGenericQuantumParameter q) :
    LadderModule q m ε →ₗ[UqSl2 q] Dual ℂ (LadderModule q m ε) :=
  lift hq coord_last_weight e_smul_coord_last f_pow_smul_coord_last

private theorem dualHighestHom_vec (hq : IsGenericQuantumParameter q) (j : ℕ) :
    dualHighestHom (m := m) (ε := ε) hq (vec q m ε j) =
      (∏ t ∈ Finset.range j, quantumInteger q (t + 1))⁻¹ •
        (rep q m ε).hopfDual (f q ^ j) ((basis q m ε).coord (Fin.last m)) :=
  lift_vec hq coord_last_weight e_smul_coord_last f_pow_smul_coord_last j

private theorem dualHighestHom_injective (hq : IsGenericQuantumParameter q) :
    Function.Injective (dualHighestHom (m := m) (ε := ε) hq) := by
  apply lift_injective
  intro h
  have := LinearMap.congr_fun h (vec q m ε m)
  simp at this

/-- The signed simple module is isomorphic to its antipode contragredient. The highest vector
maps to the coordinate functional of the lowest vector. -/
def contragredientEquiv (hq : IsGenericQuantumParameter q) :
    LadderModule q m ε ≃ₗ[ℂ] Dual ℂ (LadderModule q m ε) :=
  LinearMap.linearEquivOfInjective ((dualHighestHom hq).restrictScalars ℂ)
    (dualHighestHom_injective hq) (Subspace.dual_finrank_eq.symm)

private theorem contragredientEquiv_apply (hq : IsGenericQuantumParameter q)
    (v : LadderModule q m ε) : contragredientEquiv hq v = dualHighestHom hq v := (rfl)

/-- The highest vector maps to the lowest-coordinate functional, fixing the normalization. -/
@[simp]
theorem contragredientEquiv_vec_zero (hq : IsGenericQuantumParameter q) :
    contragredientEquiv (m := m) (ε := ε) hq (vec q m ε 0) =
      (basis q m ε).coord (Fin.last m) := by
  rw [contragredientEquiv_apply, dualHighestHom, lift_vec_zero]

/-- Every ladder vector maps to the normalized contragredient lowering string. -/
theorem contragredientEquiv_vec (hq : IsGenericQuantumParameter q) (j : ℕ) :
    contragredientEquiv (m := m) (ε := ε) hq (vec q m ε j) =
      (∏ t ∈ Finset.range j, quantumInteger q (t + 1))⁻¹ •
        (rep q m ε).hopfDual (f q ^ j) ((basis q m ε).coord (Fin.last m)) := by
  rw [contragredientEquiv_apply, dualHighestHom_vec]

/-- The matrix entries of the isomorphism vanish off the reversed diagonal; on that diagonal
they are the finite product forced by the antipode action and the normalized lowering ladder. -/
theorem contragredientEquiv_vec_apply_vec (hq : IsGenericQuantumParameter q) (j : ℕ) (i : ℤ) :
    contragredientEquiv (m := m) (ε := ε) hq (vec q m ε j) (vec q m ε i) =
      (∏ t ∈ Finset.range j, quantumInteger q (t + 1))⁻¹ *
        (∏ t ∈ Finset.range j,
          (-(ε : ℂ) * q ^ ((m : ℤ) - 2 * (i + t)) * quantumInteger q (i + t + 1))) *
        (if (m : ℤ) = i + j then 1 else 0) := by
  rw [contragredientEquiv_vec, LinearMap.smul_apply, smul_eq_mul,
    hopfDual_f_pow_apply_vec, coord_last_vec, mul_assoc]

/-- The equivalence intertwines the given action and the actual antipode contragredient. -/
theorem contragredientEquiv_intertwines (hq : IsGenericQuantumParameter q) (a : UqSl2 q)
    (v : LadderModule q m ε) :
    contragredientEquiv hq (rep q m ε a v) =
      (rep q m ε).hopfDual a (contragredientEquiv hq v) := by
  simpa only [contragredientEquiv_apply, smul_def, dual_smul_def] using
    (dualHighestHom (m := m) (ε := ε) hq).map_smul a v

/-- The inverse equivalence also intertwines the contragredient and the original action. -/
theorem contragredientEquiv_symm_intertwines (hq : IsGenericQuantumParameter q) (a : UqSl2 q)
    (φ : Dual ℂ (LadderModule q m ε)) :
    (contragredientEquiv hq).symm ((rep q m ε).hopfDual a φ) =
      rep q m ε a ((contragredientEquiv hq).symm φ) := by
  apply (contragredientEquiv hq).injective
  simp [contragredientEquiv_intertwines]

end TauCeti.UqSl2.LadderModule
