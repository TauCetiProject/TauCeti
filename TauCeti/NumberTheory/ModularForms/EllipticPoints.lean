/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Forced zeros at the elliptic points `i` and `ρ`

The matrix `S` fixes `i` and `S * T` fixes `ρ`, with automorphy factors `i` and `ρ + 1` there.
These are primitive fourth and sixth roots of unity, so the transformation law of a form of
weight `k` at the fixed point reads `f z = ζᵏ f z`. Hence a form invariant under `S` vanishes at
`i` unless `4 ∣ k`, and one invariant under `S * T` vanishes at `ρ` unless `6 ∣ k`.

## Main results

* `TauCeti.ModularForm.apply_I_eq_zero_of_not_dvd`: a form of weight `k` for a group
  containing `S` vanishes at `i` unless `4 ∣ k`.
* `TauCeti.ModularForm.apply_ρ_eq_zero_of_not_dvd`: a form of weight `k` for a group
  containing `S * T` vanishes at `ρ` unless `6 ∣ k`.

## References

* J.-P. Serre, *A Course in Arithmetic*, VII.3.
-/

public section

open UpperHalfPlane ModularGroup MatrixGroups Matrix.SpecialLinearGroup

namespace TauCeti.ModularForm

/-- The automorphy factor of `S` at its fixed point `i` is `i`. -/
private lemma denom_S_I : denom (mapGL ℝ S) I = Complex.I := by
  simp [denom, coe_S, mapGL_coe_matrix]

/-- The automorphy factor of `S * T` at its fixed point `ρ` is `ρ + 1`. -/
private lemma denom_S_mul_T_ρ : denom (mapGL ℝ (S * T)) ρ = ρ + 1 := by
  simp [denom, coe_S, coe_T, mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- A form of weight `k` for a group containing `S` vanishes at the elliptic point `i` unless
`4 ∣ k`. -/
theorem apply_I_eq_zero_of_not_dvd {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} [SlashInvariantFormClass F Γ k] (hS : mapGL ℝ S ∈ Γ) (f : F)
    (hk : ¬ (4 : ℤ) ∣ k) : f I = 0 := by
  have hSI : mapGL ℝ S • I = I := by
    rw [← MulAction.compHom_smul_def]
    exact stabilizer_I.mpr (by simp)
  have h := SlashInvariantForm.slash_action_eqn_of_det_pos f hS
    (det_pos_of_mem_slGL ⟨S, rfl⟩) I
  rw [hSI, denom_S_I] at h
  simp at h
  by_contra hf
  exact hk ((Complex.isPrimitiveRoot_I.zpow_eq_one_iff_dvd k).mp ((mul_eq_right₀ hf).mp h.symm))

/-- A form of weight `k` for a group containing `S * T` vanishes at the elliptic point `ρ`
unless `6 ∣ k`. -/
theorem apply_ρ_eq_zero_of_not_dvd {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} [SlashInvariantFormClass F Γ k] (hST : mapGL ℝ (S * T) ∈ Γ)
    (f : F) (hk : ¬ (6 : ℤ) ∣ k) : f ρ = 0 := by
  have hSTρ : mapGL ℝ (S * T) • ρ = ρ := by
    rw [← MulAction.compHom_smul_def]
    exact stabilizer_ρ.mpr (by simp)
  have h := SlashInvariantForm.slash_action_eqn_of_det_pos f hST
    (det_pos_of_mem_slGL ⟨S * T, rfl⟩) ρ
  rw [hSTρ, denom_S_mul_T_ρ] at h
  simp at h
  by_contra hf
  exact hk ((isPrimitiveRoot_ρ_add_one.zpow_eq_one_iff_dvd k).mp ((mul_eq_right₀ hf).mp h.symm))

end TauCeti.ModularForm
