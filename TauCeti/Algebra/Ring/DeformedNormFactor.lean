/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute

/-!
# Factoring deformed-norm families through the group norm

For a multiplicative homomorphism `ρ` from a finite product of finite groups `∏ j, Γ j` into a
ring `R`, a ring homomorphism `σ : R →+* R'`, and a family `N : Finset J → R` satisfying
`N ∅ = ∑ g, ρ g` and `N S = N' * Nm_j`, `N (insert j S) = N' * der j` for `j ∉ S`, this file
shows that powers of `δ = n ^ 2 • δ'` factor `N S` through the global norm `∑ g, ρ g` modulo
`σ` whenever `n • der j * (g - 1) ≡ Nm_j * Z` with `δ' * Nm * Z = 0`.

## Main results

* `TauCeti.nsmul_eq_mul_norm`: if `∑ g⁻¹ * Ψ * g = n` and `A * ρ g = A`, then
  `n • A = A * Ψ * ∑ g, ρ g`.
* `TauCeti.map_nsmul_eq_mul_norm`: if `σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0` on each factor,
  then `σ (n • A) = σ (A * Ψ * ∑ g, ρ g)`.
* `TauCeti.exists_map_pow_mul_family_eq_mul_norm`: for `i ≥ #S`, `(n ^ 2 • δ') ^ i * N S` is
  congruent under `σ` to `Y * ∑ g, ρ g` for some `Y`, with `Y = (n ^ 2 • δ') ^ i` when `S = ∅`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/OnePrime.lean` (`New.Patching.nsmul_eq_mul_norm`,
`New.Patching.map_nsmul_eq_mul_norm`, `New.Patching.exists_map_pow_mul_family_eq_mul_norm`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset

/-- If `∑ g, ρ g⁻¹ * Ψ * ρ g = n` and `A * ρ g = A` for all `g : Γ`, then
`n • A = A * Ψ * ∑ g, ρ g`. -/
theorem nsmul_eq_mul_norm {Γ R : Type*} [Group Γ] [Fintype Γ] [Ring R] (ρ : Γ →* R) {Ψ A : R}
    {n : ℕ} (hΨ : ∑ g : Γ, ρ g⁻¹ * Ψ * ρ g = n) (hA : ∀ g : Γ, A * ρ g = A) :
    n • A = A * Ψ * ∑ g : Γ, ρ g :=
  calc n • A = A * ∑ g, ρ g⁻¹ * Ψ * ρ g := by rw [hΨ, nsmul_eq_mul']
    _ = A * Ψ * ∑ g, ρ g := by simp only [mul_sum, ← mul_assoc, hA]

/-- If `ρ : (∀ j : J, Γ j) →* R` satisfies `∑ g, ρ g⁻¹ * Ψ * ρ g = n` and
`σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0` on every factor `Γ j`, then
`σ (n • A) = σ (A * Ψ * ∑ g, ρ g)`. -/
theorem map_nsmul_eq_mul_norm {J R R' : Type*} [Fintype J] [DecidableEq J] [Ring R] [Ring R']
    {σ : R →+* R'} {Γ : J → Type*} [∀ j : J, Group (Γ j)] [∀ j : J, Fintype (Γ j)]
    (ρ : (∀ j : J, Γ j) →* R) {Ψ A : R} {n : ℕ}
    (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hA : ∀ (j : J) (g : Γ j), σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0) :
    σ (n • A) = σ (A * Ψ * ∑ g : (j : J) → Γ j, ρ g) := by
  have invariant (g : ∀ j, Γ j) : σ A * σ (ρ g) = σ A := by
    have h_single (j : J) (x : Γ j) : σ A * σ (ρ (Pi.mulSingle j x)) = σ A := by
      rw [← map_mul, ← sub_eq_zero, ← map_sub, ← mul_sub_one, hA]
    have h_ind : ∀ S : Finset J, ∀ f : ∀ j, Γ j, (∀ j, j ∉ S → f j = 1) → σ A * σ (ρ f) = σ A := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro f hf
        have hf1 : f = 1 := funext fun j ↦ hf j (notMem_empty j)
        simp [hf1]
      | @insert j S hj ih =>
        intro f hf
        let f' : ∀ i, Γ i := Function.update f j 1
        have hf_eq : f = f' * Pi.mulSingle j (f j) := by
          ext i
          by_cases hi : i = j
          · subst hi; simp [f']
          · simp [f', hi]
        have hf'_supp : ∀ i, i ∉ S → f' i = 1 := fun i hi ↦ by
          by_cases hij : i = j
          · subst hij; simp [f']
          · simp [f', hij, hf i (by simp [hi, hij])]
        rw [hf_eq, map_mul, map_mul, ← mul_assoc, ih f' hf'_supp, h_single]
    exact h_ind univ g fun j hj ↦ (hj (mem_univ j)).elim
  rw [map_nsmul, map_mul, map_mul, map_sum]
  exact nsmul_eq_mul_norm (σ.toMonoidHom.comp ρ) (by simpa using congrArg σ hΨ) invariant

/-- For a family `N : Finset J → R` with `N ∅ = ∑ g, ρ g` and factorization
`N S = N' * Nm_j`, `N (insert j S) = N' * der j` for `j ∉ S`, if `∑ g⁻¹ * Ψ * g = n`, `δ'`
commutes with `ρ g` and `N S`, and each `g : Γ j` admits `Z` with
`σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) = σ (Nm_j * Z)` and `δ' * Nm * Z = 0`, then for
every `i ≥ #S` there is `Y` with `σ ((n ^ 2 • δ') ^ i * N S) = σ (Y * ∑ g, ρ g)` and
`S = ∅ → Y = (n ^ 2 • δ') ^ i`. -/
theorem exists_map_pow_mul_family_eq_mul_norm {J R R' : Type*} [Fintype J] [DecidableEq J]
    [Ring R] [Ring R'] {σ : R →+* R'} {Γ : J → Type*} [∀ j : J, Group (Γ j)]
    [∀ j : J, Fintype (Γ j)] {ρ : (∀ j : J, Γ j) →* R} {N : Finset J → R} {der : J → R}
    {Ψ δ' : R} {n : ℕ} (hΨ : ∑ g : (j : J) → Γ j, ρ g⁻¹ * Ψ * ρ g = n)
    (hδ'ρ : ∀ g : (j : J) → Γ j, Commute δ' (ρ g)) (hδ'N : ∀ S : Finset J, Commute δ' (N S))
    (h_empty : N ∅ = ∑ g : (j : J) → Γ j, ρ g)
    (h_factor : ∀ (j : J) (S : Finset J), j ∉ S → ∃ N' : R,
      N S = N' * ∑ g : Γ j, ρ (Pi.mulSingle j g) ∧ N (insert j S) = N' * der j)
    (h_der : ∀ (j : J) (g : Γ j), ∃ Z : R,
      σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) = σ ((∑ k : Γ j, ρ (Pi.mulSingle j k)) * Z) ∧
        δ' * (∑ k : (j : J) → Γ j, ρ k) * Z = 0)
    (S : Finset J) {i : ℕ} (hi : #S ≤ i) :
    ∃ Y : R,
      σ ((n ^ 2 • δ') ^ i * N S) = σ (Y * ∑ g : (j : J) → Γ j, ρ g) ∧
      (S = ∅ → Y = (n ^ 2 • δ') ^ i) := by
  set δ : R := n ^ 2 • δ'
  have hδ'δ : Commute δ' δ := (Commute.refl δ').smul_right (n ^ 2)
  have hδ'_norm : Commute δ' (∑ g, ρ g) := .sum_right univ ρ δ' fun g _ ↦ hδ'ρ g
  induction S using Finset.strongInduction generalizing i with | _ S ih
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨δ ^ i, by rw [h_empty], fun _ ↦ rfl⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, i = e + 1 := ⟨i - 1, by have := hS.card_pos; omega⟩
  set A : R := n • (δ' * δ ^ e * N S) with hA
  have invariant (j : J) (g : Γ j) : σ (A * (ρ (Pi.mulSingle j g) - 1)) = 0 := by
    by_cases hj : j ∈ S
    · obtain ⟨N', h_erase, h_S⟩ : ∃ N' : R,
          N (S.erase j) = N' * ∑ k : Γ j, ρ (Pi.mulSingle j k) ∧ N S = N' * der j := by
        simpa only [insert_erase hj] using h_factor j (S.erase j) (notMem_erase j S)
      obtain ⟨Z, hZ, hZ_zero⟩ := h_der j g
      obtain ⟨Y, hY, -⟩ := ih (S.erase j) (erase_ssubset hj) (i := e)
        (by rw [card_erase_of_mem hj]; omega)
      have h_move : δ' * δ ^ e * N (S.erase j) = δ ^ e * N (S.erase j) * δ' := by
        rw [mul_assoc, ((hδ'δ.pow_right e).mul_right (hδ'N _)).eq]
      calc σ (A * (ρ (Pi.mulSingle j g) - 1))
          = σ (δ' * δ ^ e * N') * σ (n • (der j * (ρ (Pi.mulSingle j g) - 1))) := by
            simp only [hA, h_S, ← map_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = σ (δ' * δ ^ e * N (S.erase j)) * σ Z := by
            simp only [hZ, h_erase, map_mul, mul_assoc]
        _ = σ (Y * (δ' * (∑ g, ρ g) * Z)) := by
            rw [h_move, map_mul, hY, ← map_mul, ← map_mul, mul_assoc Y, ← hδ'_norm.eq]
            simp only [mul_assoc]
        _ = 0 := by rw [hZ_zero, mul_zero, map_zero]
    · obtain ⟨N', h_S, -⟩ := h_factor j S hj
      have norm_inv : (∑ k : Γ j, ρ (Pi.mulSingle j k)) * ρ (Pi.mulSingle j g) =
          ∑ k : Γ j, ρ (Pi.mulSingle j k) := by
        simp only [sum_mul, ← map_mul, ← Pi.mulSingle_mul]
        exact Fintype.sum_bijective (· * g) ⟨mul_left_injective g, fun x ↦ ⟨x * g⁻¹, by simp⟩⟩
          _ _ fun _ ↦ rfl
      simp only [hA, h_S, smul_mul_assoc, mul_assoc, mul_sub_one, norm_inv, sub_self, map_zero]
  have pow_mul_eq : δ ^ (e + 1) * N S = n • A := by
    rw [hA, smul_smul, ← sq, pow_succ', ← smul_mul_assoc, ← smul_mul_assoc]
  refine ⟨A * Ψ, ?_, fun h ↦ absurd h hS.ne_empty⟩
  rw [pow_mul_eq, map_nsmul_eq_mul_norm ρ hΨ invariant]

end TauCeti
