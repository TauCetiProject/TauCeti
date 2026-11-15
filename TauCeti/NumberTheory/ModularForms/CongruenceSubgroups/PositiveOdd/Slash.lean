/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd

/-!
# Slash laws on congruence subgroups from matrices with positive odd entries

Transformation formulas proved by evaluating quadratic Gauss sums, such as those of theta series
of lattices, apply at first only to a matrix `A = [a, b; c, d]` with `c > 0` and `a` positive and
odd: the Gauss sums are evaluated by the Jacobi symbol `(· / a)`, which needs `a` odd and
positive. This file extends such a law from those matrices to the whole congruence subgroup, by
the normalizations of `TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd`.

* On `Γ₀(N)`, a nebentypus law `f ∣[k] A = χ(d) • f`, for a Dirichlet character `χ` modulo `N`
  with `χ(-1) = (-1)^k` and a function `f` invariant under `T`, holds for every `A ∈ Γ₀(N)` once
  it holds for those with `c > 0` and `a` positive and odd
  (`TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd`). Negating `A` multiplies both
  sides by `(-1)^k = χ(-1)` (`TauCeti.ModularForm.SL_slash_neg`), a left translation `T^j`
  changes neither side, and the matrices with `c = 0` are the signed translations `±T^b`.
* On `Γ(N)`, invariance `f ∣[k] A = f`, for `f` invariant under `T^N`, holds for every
  `A ∈ Γ(N)` once it holds for those with `c > 0` and `a` positive and odd, provided `-I` acts
  trivially on `f` whenever it lies in `Γ(N)`, that is whenever `N ∣ 2`
  (`TauCeti.ModularForm.slash_eq_self_of_mem_Gamma_of_pos_odd`). Here `-A` is generally not in
  `Γ(N)`, so inversion takes the place of negation, and the translations are by multiples of `N`.

Both parity hypotheses follow from the conclusions (the first for nonzero `f`): `-I` lies in
`Γ₀(N)`, and in `Γ(N)` when `N ∣ 2`, acts on weight `k` by `(-1)^k`, and has lower-right entry
`-1`. Since its lower-left entry is `0`, the normalized matrices never supply them.

## Main statements

* `TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd`: the nebentypus law on `Γ₀(N)`
  from the matrices with positive lower-left and positive odd upper-left entries.
* `TauCeti.ModularForm.slash_eq_self_of_mem_Gamma_of_pos_odd`: invariance under `Γ(N)` from
  the same matrices of `Γ(N)`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm UpperHalfPlane

namespace TauCeti.ModularForm

variable {k : ℤ} {f : ℍ → ℂ}

/-- **The nebentypus law on `Γ₀(N)` from matrices with positive odd upper-left entry.** Let `χ`
be a Dirichlet character modulo `N` with `χ(-1) = (-1)^k`, and let `f` be invariant under `T` in
weight `k`. If `f ∣[k] B = χ(d_B) • f` for every `B ∈ Γ₀(N)` whose lower-left entry is positive
and whose upper-left entry is positive and odd, then `f ∣[k] A = χ(d_A) • f` for every
`A ∈ Γ₀(N)`. -/
theorem slash_eq_smul_of_mem_Gamma0_of_pos_odd {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = (-1 : ℂ) ^ k) (hT : f ∣[k] T = f)
    (h : ∀ B ∈ Gamma0 N, 0 < B 1 0 → 0 < B 0 0 → Odd (B 0 0) → f ∣[k] B = χ (B 1 1) • f)
    {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) : f ∣[k] A = χ (A 1 1) • f := by
  have hTj (j : ℤ) : f ∣[k] (T ^ j) = f := SL_slash_zpow_eq_self_of_slash_eq hT j
  -- Negation multiplies both sides of the law by `(-1)^k = χ(-1)`.
  have hneg (B : SL(2, ℤ)) (hB : f ∣[k] (-B) = χ ((-B) 1 1) • f) :
      f ∣[k] B = χ (B 1 1) • f := by
    have hχB : χ ((-B) 1 1 : ℤ) = (-1 : ℂ) ^ k * χ (B 1 1 : ℤ) := by
      rw [← hχ, ← map_mul, neg_one_mul]
      simp [coe_neg]
    rw [SL_slash_neg, hχB, mul_smul] at hB
    exact (smul_right_inj (zpow_ne_zero k (by norm_num))).mp hB
  by_cases hc : A 1 0 = 0
  · -- A matrix fixing `∞` is a signed translation `±T^b`, with lower-right entry `±1`.
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hA' | hA'
    · rw [hA', hTj]
      simp [coe_T_zpow]
    · refine hneg A ?_
      rw [hA', neg_neg, hTj]
      simp [coe_T_zpow]
  · -- Otherwise `T^j A` or `T^j (-A)` is normalized, with the same lower row up to sign.
    obtain ⟨B, hB, hBc, hBa, hBo, j, hBA | hBA⟩ := exists_pos_odd_of_mem_Gamma0 hA hc
    · have hlaw := h B hB hBc hBa hBo
      rwa [hBA, SlashAction.slash_mul, hTj, congrFun (T_pow_mul_apply_one _ A) 1] at hlaw
    · have hlaw := h B hB hBc hBa hBo
      rw [hBA, SlashAction.slash_mul, hTj, congrFun (T_pow_mul_apply_one _ (-A)) 1] at hlaw
      exact hneg A hlaw

/-- **Invariance under `Γ(N)` from matrices with positive odd upper-left entry.** Let `f` be
invariant under `T^N` in weight `k`, and under `-I` when `N ∣ 2`, the levels at which `-I`
lies in `Γ(N)`. If `f ∣[k] B = f` for every `B ∈ Γ(N)` whose lower-left entry is positive and
whose upper-left entry is positive and odd, then `f ∣[k] A = f` for every `A ∈ Γ(N)`. -/
theorem slash_eq_self_of_mem_Gamma_of_pos_odd {N : ℕ} (hT : f ∣[k] (T ^ (N : ℤ)) = f)
    (hI : N ∣ 2 → f ∣[k] (-1 : SL(2, ℤ)) = f)
    (h : ∀ B ∈ Gamma N, 0 < B 1 0 → 0 < B 0 0 → Odd (B 0 0) → f ∣[k] B = f)
    {A : SL(2, ℤ)} (hA : A ∈ Gamma N) : f ∣[k] A = f := by
  have hTj (j : ℤ) : f ∣[k] (T ^ (j * N)) = f := by
    rw [mul_comm, zpow_mul]
    exact SL_slash_zpow_eq_self_of_slash_eq hT j
  by_cases hc : A 1 0 = 0
  · -- A matrix of `Γ(N)` fixing `∞` is `T^b` with `N ∣ b`, or `-T^b` when also `N ∣ 2`.
    obtain ⟨⟨m, hm⟩, hA' | ⟨h2, hA'⟩⟩ :=
      dvd_and_eq_T_zpow_or_eq_neg_T_zpow_of_mem_Gamma_of_c_eq_zero hA hc
    · rw [hA', hm, mul_comm, hTj]
    · rw [hA', ← neg_one_mul, SlashAction.slash_mul, hI h2, hm, ← mul_neg, mul_comm, hTj]
  · -- Otherwise `T^(jN) A` or `T^(jN) A⁻¹` is normalized; invariance under `A⁻¹` gives it
    -- under `A`.
    obtain ⟨B, hB, hBc, hBa, hBo, j, hBA | hBA⟩ := exists_pos_odd_of_mem_Gamma hA hc
    · have hlaw := h B hB hBc hBa hBo
      rwa [hBA, SlashAction.slash_mul, hTj] at hlaw
    · have hlaw := h B hB hBc hBa hBo
      rw [hBA, SlashAction.slash_mul, hTj] at hlaw
      calc f ∣[k] A = (f ∣[k] A⁻¹) ∣[k] A := by rw [hlaw]
        _ = f := by rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

end TauCeti.ModularForm
