/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Modular
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
import TauCeti.NumberTheory.Modular.Relations

/-!
# Conjugates of integral translations

For `γ = [a,b;c,d]` in `SL₂(ℤ)`, the conjugate `γ Tʲ γ⁻¹` depends only on the first
column `(a,c)`. Its lower-left entry is `-j c²`. This calculation describes the
translations fixing the rational cusp `γ ∞` and turns congruence-subgroup membership
into a divisibility condition on the translation exponent. An element of `SL₂(ℤ)` with
vanishing lower-left entry, that is one fixing `∞` itself, is a signed translation `±Tʲ`.

In `PSL(2, ℤ)`, distinct integer powers of `T` are pairwise non-conjugate
(`TauCeti.ModularGroup.eq_of_conj_coe_T_zpow_eq`), containment of a conjugate of `⟨T ^ a⟩` in
`⟨T ^ b⟩` forces `b ∣ a` (`TauCeti.ModularGroup.dvd_of_conj_zpowers_coe_T_zpow_le`), and every
cyclic translation subgroup `⟨T ^ k⟩` has infinite index
(`TauCeti.ModularGroup.index_zpowers_coe_T_zpow`).

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.4.
-/

public section

open Matrix
open scoped MatrixGroups Pointwise

namespace TauCeti

/-- Conjugating the translation `Tʲ` by `γ = [a,b;c,d]` gives
`[1-jac, ja²; -jc², 1+jac]`. -/
theorem _root_.Matrix.SpecialLinearGroup.coe_conj_T_zpow (γ : SL(2, ℤ)) (j : ℤ) :
    (↑(γ * ModularGroup.T ^ j * γ⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - j * γ 0 0 * γ 1 0, j * γ 0 0 ^ 2;
        -j * γ 1 0 ^ 2, 1 + j * γ 0 0 * γ 1 0] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [det_fin_two] using γ.det_coe
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T_zpow, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> nlinarith [hdet]

/-- An element of `SL₂(ℤ)` with vanishing lower-left entry fixes the cusp `∞`, so it is a
translation up to sign: `Tᵇ` when its diagonal entries are `1`, and `-T⁻ᵇ` when they are `-1`,
where `b` is its upper-right entry. Adapted from the proof of
`ModularGroup.exists_eq_T_zpow_of_c_eq_zero` in Mathlib. -/
theorem ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero {g : SL(2, ℤ)}
    (hc : g 1 0 = 0) :
    g = ModularGroup.T ^ g 0 1 ∨ g = -ModularGroup.T ^ (-g 0 1) := by
  have had : g 0 0 * g 1 1 = 1 := by
    simpa only [det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, ModularGroup.coe_T_zpow]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, ModularGroup.coe_T_zpow]

/-- Distinct integer powers of `T` are pairwise non-conjugate in `PSL(2, ℤ)`: since elements of
`SL(2, ℤ)` have determinant `+1`, any element conjugating a nontrivial power of `T` into `⟨T⟩`
fixes `∞` and hence centralizes `T`. -/
theorem ModularGroup.eq_of_conj_coe_T_zpow_eq {a c : ℤ} {g : PSL(2, ℤ)}
    (h : g * (_root_.ModularGroup.T : PSL(2, ℤ)) ^ a * g⁻¹ =
      (_root_.ModularGroup.T : PSL(2, ℤ)) ^ c) :
    a = c := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zpow_zero, mul_one, mul_inv_cancel, eq_comm, ModularGroup.coe_T_zpow_eq_one_iff] at h
    exact h.symm
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  have hpsl : ((γ * _root_.ModularGroup.T ^ a * γ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) =
      ((_root_.ModularGroup.T ^ c : SL(2, ℤ)) : PSL(2, ℤ)) := by
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow] using h
  have hc0 : γ 1 0 = 0 := by
    rcases Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff.mp hpsl with hmat | hmat
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [_root_.ModularGroup.coe_T_zpow, γ.coe_conj_T_zpow] at h10
      simp at h10
      exact h10.resolve_left ha
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [_root_.ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
        γ.coe_conj_T_zpow] at h10
      simp at h10
      exact h10.resolve_left ha
  have had : γ 0 0 * γ 1 1 = 1 := by
    simpa only [det_fin_two, hc0, mul_zero, sub_zero] using γ.det_coe
  have ha2 : γ 0 0 ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨h0, _⟩ | ⟨h0, _⟩ <;> simp [h0]
  rcases Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff.mp hpsl with hmat | hmat
  · have h01 := congr_fun (congr_fun
      (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 1
    rw [_root_.ModularGroup.coe_T_zpow, γ.coe_conj_T_zpow, ha2, mul_one] at h01
    simpa using h01.symm
  · have h00 := congr_fun (congr_fun
      (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 0
    rw [_root_.ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
      γ.coe_conj_T_zpow, hc0] at h00
    simp at h00

/-- If a conjugate of `⟨T ^ a⟩` in `PSL(2, ℤ)` is contained in `⟨T ^ b⟩`, then `b ∣ a`. -/
theorem ModularGroup.dvd_of_conj_zpowers_coe_T_zpow_le {a b : ℤ} {g : ConjAct PSL(2, ℤ)}
    (h : g • Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ a) ≤
      Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ b)) : b ∣ a := by
  have hmem :
      ConjAct.ofConjAct g * (_root_.ModularGroup.T : PSL(2, ℤ)) ^ a * (ConjAct.ofConjAct g)⁻¹ ∈
        Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ b) :=
    h ⟨(_root_.ModularGroup.T : PSL(2, ℤ)) ^ a, Subgroup.mem_zpowers _, ConjAct.smul_def _ _⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mul] at hk
  exact ⟨k, ModularGroup.eq_of_conj_coe_T_zpow_eq hk.symm⟩

/-- Every cyclic translation subgroup `⟨T ^ k⟩` has infinite index (`index = 0`) in `PSL(2, ℤ)`. -/
theorem ModularGroup.index_zpowers_coe_T_zpow (k : ℤ) :
    (Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ k)).index = 0 := by
  have : Infinite (PSL(2, ℤ) ⧸ Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ k)) := by
    refine Infinite.of_injective
      (fun j : ℕ ↦ (((_root_.ModularGroup.T ^ (j : ℤ) * _root_.ModularGroup.S : SL(2, ℤ)) :
        PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Subgroup.zpowers ((_root_.ModularGroup.T : PSL(2, ℤ)) ^ k)))
      fun i j hij ↦ ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp hij)
    have hconj : (_root_.ModularGroup.T ^ (i : ℤ) * _root_.ModularGroup.S)⁻¹ *
        (_root_.ModularGroup.T ^ (j : ℤ) * _root_.ModularGroup.S) =
        _root_.ModularGroup.S⁻¹ * _root_.ModularGroup.T ^ ((j : ℤ) - i) *
          (_root_.ModularGroup.S⁻¹)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc (_root_.ModularGroup.T ^ (i : ℤ))⁻¹,
        ← zpow_neg, ← zpow_add, sub_eq_neg_add, mul_assoc]
    have hpsl : ((_root_.ModularGroup.S⁻¹ * _root_.ModularGroup.T ^ ((j : ℤ) - i) *
        (_root_.ModularGroup.S⁻¹)⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) =
        ((_root_.ModularGroup.T ^ (k * m) : SL(2, ℤ)) : PSL(2, ℤ)) := by
      rw [← hconj, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hm, ← zpow_mul,
        QuotientGroup.mk_zpow]
    have hS0 : (_root_.ModularGroup.S⁻¹ : SL(2, ℤ)) 0 0 = 0 := by decide
    have hS1 : (_root_.ModularGroup.S⁻¹ : SL(2, ℤ)) 1 0 = -1 := by decide
    rcases Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff.mp hpsl with hmat | hmat
    · have h10 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 1) 0
      rw [_root_.ModularGroup.coe_T_zpow, (_root_.ModularGroup.S⁻¹).coe_conj_T_zpow, hS1] at h10
      simp at h10
      omega
    · have h00 := congr_fun (congr_fun
        (congrArg (↑· : SL(2, ℤ) → Matrix (Fin 2) (Fin 2) ℤ) hmat) 0) 0
      rw [_root_.ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
        (_root_.ModularGroup.S⁻¹).coe_conj_T_zpow, hS0] at h00
      simp at h00
  rw [Subgroup.index_eq_card]
  exact Nat.card_eq_zero_of_infinite

end TauCeti
