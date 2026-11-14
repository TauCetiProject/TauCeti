/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Embedding
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import TauCeti.GroupTheory.Perm.DistErr.Basic
import Mathlib.Tactic.NormNum

/-!
# Invariances, separation, and degree-mismatch bounds for the distance with errors

This file develops the algebraic invariances, separation properties, and degree-mismatch lower
bounds of Chapman and Lubotzky's cross-degree distance `Equiv.Perm.distErr`.

Main results:

* `Equiv.Perm.agreeCount_inv_inv` and `Equiv.Perm.distErr_inv_inv`: inverting both permutations
  preserves the number of agreements and the distance with errors, even when their degrees differ.
  Consequently, `Equiv.Perm.distErr_inv_mul_inv` shows that reversing an edge inverts both the
  permutation label and the gauge quotient `g * h⁻¹` without changing the edge cost.
* `Equiv.Perm.distErr_mul_left`, `Equiv.Perm.distErr_mul_right`, and
  `Equiv.Perm.mul_distErr_mul_inv`: in equal degree `n ≠ 0`, `distErr` is bi-invariant and
  `n * distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h)`.
* `Equiv.Perm.distErr_mul_viaEmbedding_left`, `Equiv.Perm.distErr_mul_viaEmbedding_right`, and
  `Equiv.Perm.distErr_conj_mul_inv`: when `n ≤ m`, multiplying in degree `n` and simultaneously
  acting in degree `m` via `Fin.castLEEmb` preserves `agreeCount` and `distErr`.
* `Equiv.Perm.distErr_eq_zero_iff` and `Equiv.Perm.distErr_pos_of_ne_degree`: when not both degrees
  are zero, `distErr` vanishes only on equal permutations of equal degree, and is strictly positive
  across distinct degrees.
* `Equiv.Perm.one_div_three_le_distErr_three_two`,
  `Equiv.Perm.one_div_four_le_distErr_three_of_four_le`, and
  `Equiv.Perm.one_div_four_le_distErr_three_of_ne`: explicit lower bounds comparing permutations of
  degree `3` against permutations of any unequal degree `m ≥ 2`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, equations (2.8)–(2.9).
* J. Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every k≥4*,
  version 7, Proposition 10.
-/

public section

open Finset

namespace Equiv.Perm

variable {n m : ℕ}

/-! ### Inversion invariance across arbitrary degrees -/

private theorem agreeCount_inv_inv_le (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ⁻¹ τ⁻¹ ≤ agreeCount σ τ := by
  rw [agreeCount_def, agreeCount_def]
  set h₁ := min_le_left n m
  set h₂ := min_le_right n m
  let f (k : Fin (min n m)) : Fin (min n m) :=
    ⟨if (σ⁻¹ (k.castLE h₁) : ℕ) < min n m then (σ⁻¹ (k.castLE h₁) : ℕ) else 0,
      by split_ifs with hk; exacts [hk, Nat.zero_lt_of_lt k.isLt]⟩
  have hf {k : Fin (min n m)} (hlt : (σ⁻¹ (k.castLE h₁) : ℕ) < min n m) :
      (f k : ℕ) = (σ⁻¹ (k.castLE h₁) : ℕ) := by dsimp only [f]; split_ifs; rfl
  refine card_le_card_of_injOn f (fun k hk => ?_) (fun k₁ hk₁ k₂ hk₂ h => ?_)
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at hk ⊢
    have hlt : (σ⁻¹ (k.castLE h₁) : ℕ) < min n m :=
      lt_min (σ⁻¹ (k.castLE h₁)).isLt (hk ▸ (τ⁻¹ (k.castLE h₂)).isLt)
    have hc₁ : (f k).castLE h₁ = σ⁻¹ (k.castLE h₁) := Fin.ext (hf hlt)
    have hc₂ : (f k).castLE h₂ = τ⁻¹ (k.castLE h₂) := Fin.ext ((hf hlt).trans hk)
    simp [hc₁, hc₂]
  · simp only [mem_coe, mem_filter, mem_univ, true_and] at hk₁ hk₂
    have hlt₁ : (σ⁻¹ (k₁.castLE h₁) : ℕ) < min n m :=
      lt_min (σ⁻¹ (k₁.castLE h₁)).isLt (hk₁ ▸ (τ⁻¹ (k₁.castLE h₂)).isLt)
    have hlt₂ : (σ⁻¹ (k₂.castLE h₁) : ℕ) < min n m :=
      lt_min (σ⁻¹ (k₂.castLE h₁)).isLt (hk₂ ▸ (τ⁻¹ (k₂.castLE h₂)).isLt)
    have hval : (σ⁻¹ (k₁.castLE h₁) : ℕ) = (σ⁻¹ (k₂.castLE h₁) : ℕ) :=
      (hf hlt₁).symm.trans ((congrArg Fin.val h).trans (hf hlt₂))
    exact Fin.castLE_injective h₁ (σ⁻¹.injective (Fin.ext hval))

/-- Inverting both permutations preserves the number of agreements, even when `n ≠ m`. -/
@[simp]
theorem agreeCount_inv_inv (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ⁻¹ τ⁻¹ = agreeCount σ τ :=
  le_antisymm (agreeCount_inv_inv_le σ τ) (by simpa using agreeCount_inv_inv_le σ⁻¹ τ⁻¹)

/-- Inverting both permutations preserves the distance with errors, even when `n ≠ m`. -/
@[simp]
theorem distErr_inv_inv (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    distErr σ⁻¹ τ⁻¹ = distErr σ τ := by
  simp [distErr_def]

/-- Inverting the target permutation and swapping the factors of a quotient preserves the agreement
count across arbitrary degrees. -/
theorem agreeCount_inv_mul_inv (σ : Perm (Fin n)) (g h : Perm (Fin m)) :
    agreeCount σ⁻¹ (h * g⁻¹) = agreeCount σ (g * h⁻¹) := by
  rw [← agreeCount_inv_inv σ (g * h⁻¹), mul_inv_rev, inv_inv]

/-- Inverting the target permutation and swapping the factors of a quotient preserves the distance
with errors across arbitrary degrees. -/
theorem distErr_inv_mul_inv (σ : Perm (Fin n)) (g h : Perm (Fin m)) :
    distErr σ⁻¹ (h * g⁻¹) = distErr σ (g * h⁻¹) := by
  rw [← distErr_inv_inv σ (g * h⁻¹), mul_inv_rev, inv_inv]

/-! ### Equal-degree bi-invariance and gauge quotients -/

/-- A permutation of degree `n` agrees with itself at all `n` indices, including `n = 0`. -/
@[simp]
theorem agreeCount_self (σ : Perm (Fin n)) : agreeCount σ σ = n := by
  simpa using agreeCount_add_hammingDist σ σ

/-- Left multiplication in equal degree preserves the agreement count. -/
@[simp]
theorem agreeCount_mul_left (ρ σ τ : Perm (Fin n)) :
    agreeCount (ρ * σ) (ρ * τ) = agreeCount σ τ := by
  simp [agreeCount_eq_card_eq]

/-- Right multiplication in equal degree preserves the agreement count. -/
@[simp]
theorem agreeCount_mul_right (σ τ ρ : Perm (Fin n)) :
    agreeCount (σ * ρ) (τ * ρ) = agreeCount σ τ := by
  rw [← agreeCount_inv_inv (σ * ρ) (τ * ρ), mul_inv_rev, mul_inv_rev, agreeCount_mul_left,
    agreeCount_inv_inv]

/-- Left multiplication in equal degree preserves the distance with errors. -/
@[simp]
theorem distErr_mul_left (ρ σ τ : Perm (Fin n)) :
    distErr (ρ * σ) (ρ * τ) = distErr σ τ := by
  simp [distErr_def]

/-- Right multiplication in equal degree preserves the distance with errors. -/
@[simp]
theorem distErr_mul_right (σ τ ρ : Perm (Fin n)) :
    distErr (σ * ρ) (τ * ρ) = distErr σ τ := by
  simp [distErr_def]

/-- In equal nonzero degree, the distance with errors between `σ` and `g * h⁻¹` is the normalized
moved-point norm of the gauge-transformed element `g⁻¹ * σ * h`. -/
theorem distErr_mul_inv_eq_movedNorm_div [NeZero n] (σ g h : Perm (Fin n)) :
    distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h) / n := by
  have h1 : distErr σ (g * h⁻¹) = distErr (g⁻¹ * σ * h) (1 : Perm (Fin n)) := by
    rw [← distErr_mul_left g⁻¹ σ (g * h⁻¹), ← distErr_mul_right _ _ h]
    simp [mul_assoc]
  rw [h1, distErr_comm, distErr_eq_movedNorm_div, inv_one, one_mul]

/-- Rescaling the equal-degree distance with errors by the degree recovers the moved-point norm of
`g⁻¹ * σ * h`. -/
theorem mul_distErr_mul_inv [NeZero n] (σ g h : Perm (Fin n)) :
    (n : ℝ) * distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [distErr_mul_inv_eq_movedNorm_div, mul_div_cancel₀ _ hn]

/-! ### Cross-degree invariance under initial-segment embeddings -/

/-- When `n ≤ m`, left-multiplying `σ : Perm (Fin n)` by `ρ` and `τ : Perm (Fin m)` by the
initial-segment extension `ρ.viaEmbedding (Fin.castLEEmb hnm)` preserves the agreement count. -/
theorem agreeCount_mul_viaEmbedding_left (ρ σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    agreeCount (ρ * σ) (ρ.viaEmbedding (Fin.castLEEmb hnm) * τ) = agreeCount σ τ := by
  rw [agreeCount_def, agreeCount_def]
  refine congrArg card (filter_congr fun j _ => ?_)
  simp only [mul_apply]
  let x : Fin n := σ (j.castLE (min_le_left n m))
  let y : Fin m := τ (j.castLE (min_le_right n m))
  by_cases hy : (y : ℕ) < n
  · have hy_eq : (ρ.viaEmbedding (Fin.castLEEmb hnm) y : ℕ) = ρ ⟨y, hy⟩ := by
      have hcast : Fin.castLEEmb hnm ⟨y, hy⟩ = y := Fin.ext rfl
      exact congrArg Fin.val ((congrArg _ hcast.symm).trans (viaEmbedding_apply _ _ _))
    rw [hy_eq]
    exact ⟨fun h => congrArg Fin.val (ρ.injective (Fin.ext h)),
      fun h => congrArg Fin.val (congrArg ρ (Fin.ext h))⟩
  · have hnotMem : y ∉ Set.range (Fin.castLEEmb hnm) := by
      rintro ⟨z, hz⟩
      exact hy (hz ▸ z.isLt)
    have hy_eq : ρ.viaEmbedding (Fin.castLEEmb hnm) y = y :=
      viaEmbedding_apply_of_notMem _ _ _ hnotMem
    rw [hy_eq]
    exact ⟨fun h => absurd (h ▸ (ρ x).isLt) hy, fun h => absurd (h ▸ x.isLt) hy⟩

/-- When `n ≤ m`, right-multiplying `σ : Perm (Fin n)` by `ρ` and `τ : Perm (Fin m)` by
`ρ.viaEmbedding (Fin.castLEEmb hnm)` preserves the agreement count. -/
theorem agreeCount_mul_viaEmbedding_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    agreeCount (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) = agreeCount σ τ := by
  have hinv : (ρ.viaEmbedding (Fin.castLEEmb hnm))⁻¹ = ρ⁻¹.viaEmbedding (Fin.castLEEmb hnm) :=
    (map_inv (viaEmbeddingHom (Fin.castLEEmb hnm)) ρ).symm
  rw [← agreeCount_inv_inv (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)),
    mul_inv_rev, mul_inv_rev, hinv, agreeCount_mul_viaEmbedding_left _ _ _ hnm, agreeCount_inv_inv]

/-- When `n ≤ m`, left-multiplying in degree `n` and simultaneously via `Fin.castLEEmb hnm` in
degree `m` preserves the distance with errors. -/
theorem distErr_mul_viaEmbedding_left (ρ σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (ρ * σ) (ρ.viaEmbedding (Fin.castLEEmb hnm) * τ) = distErr σ τ := by
  simp [distErr_def, agreeCount_mul_viaEmbedding_left _ _ _ hnm]

/-- When `n ≤ m`, right-multiplying in degree `n` and simultaneously via `Fin.castLEEmb hnm` in
degree `m` preserves the distance with errors. -/
theorem distErr_mul_viaEmbedding_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) = distErr σ τ := by
  simp [distErr_def, agreeCount_mul_viaEmbedding_right _ _ _ hnm]

/-- When `n ≤ m`, transforming `σ : Perm (Fin n)` to `γ₁⁻¹ * σ * γ₂` can be absorbed into a
degree-`m` quotient `g * h⁻¹` by left-multiplying `g` and `h` via `Fin.castLEEmb hnm`. -/
theorem distErr_conj_mul_inv (σ γ₁ γ₂ : Perm (Fin n)) (g h : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (γ₁⁻¹ * σ * γ₂) (g * h⁻¹) =
      distErr σ ((γ₁.viaEmbedding (Fin.castLEEmb hnm) * g) *
        (γ₂.viaEmbedding (Fin.castLEEmb hnm) * h)⁻¹) := by
  have hinv₂ : (γ₂.viaEmbedding (Fin.castLEEmb hnm))⁻¹ = γ₂⁻¹.viaEmbedding (Fin.castLEEmb hnm) :=
    (map_inv (viaEmbeddingHom (Fin.castLEEmb hnm)) γ₂).symm
  rw [← distErr_mul_viaEmbedding_left γ₁ (γ₁⁻¹ * σ * γ₂) (g * h⁻¹) hnm,
    ← distErr_mul_viaEmbedding_right _ γ₂⁻¹ _ hnm]
  simp [mul_assoc, hinv₂]

/-! ### Separation and positivity -/

/-- Two permutations of equal degree agree at all `n` indices if and only if they are equal. -/
@[simp]
theorem agreeCount_eq_self {σ τ : Perm (Fin n)} : agreeCount σ τ = n ↔ σ = τ := by
  constructor
  · intro h
    have hdist : hammingDist ⇑σ ⇑τ = 0 := by
      have hsum := agreeCount_add_hammingDist σ τ
      omega
    exact DFunLike.coe_injective (hammingDist_eq_zero.mp hdist)
  · rintro rfl
    exact agreeCount_self σ

/-- The number of agreements reaches `max n m` if and only if the degrees coincide and the two
permutations are equal. -/
theorem agreeCount_eq_max_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    agreeCount σ τ = max n m ↔ n = m ∧ HEq σ τ := by
  constructor
  · intro h
    have hle := agreeCount_le_min σ τ
    have hnm : n = m := by omega
    subst hnm
    rw [max_self, agreeCount_eq_self] at h
    exact ⟨rfl, heq_of_eq h⟩
  · rintro ⟨rfl, h⟩
    rcases eq_of_heq h with rfl
    simp

/-- When at least one degree is nonzero, the distance with errors vanishes if and only if the
degrees coincide and the permutations are equal. -/
theorem distErr_eq_zero_iff (σ : Perm (Fin n)) (τ : Perm (Fin m)) (h : max n m ≠ 0) :
    distErr σ τ = 0 ↔ n = m ∧ HEq σ τ := by
  have hmax : ((max n m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [distErr_def, sub_eq_zero, eq_comm, div_eq_one_iff_eq hmax]
  norm_cast
  exact agreeCount_eq_max_iff σ τ

/-- In nonzero equal degree, the distance with errors vanishes if and only if the two permutations
are equal. -/
@[simp]
theorem distErr_eq_zero [NeZero n] {σ τ : Perm (Fin n)} : distErr σ τ = 0 ↔ σ = τ := by
  have hmax : max n n ≠ 0 := by simp [NeZero.ne n]
  rw [distErr_eq_zero_iff σ τ hmax]
  simp

/-- Permutations of distinct degrees have strictly positive distance with errors. -/
theorem distErr_pos_of_ne_degree (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≠ m) :
    0 < distErr σ τ := by
  have hmax : max n m ≠ 0 := by omega
  refine lt_of_le_of_ne (distErr_nonneg σ τ) ?_
  intro h0
  exact hnm ((distErr_eq_zero_iff σ τ hmax).mp h0.symm).1

/-- Distinct permutations of the same nonzero degree have strictly positive distance with errors. -/
theorem distErr_pos_of_ne [NeZero n] {σ τ : Perm (Fin n)} (h : σ ≠ τ) : 0 < distErr σ τ :=
  lt_of_le_of_ne (distErr_nonneg σ τ) (mt distErr_eq_zero.mp h ∘ Eq.symm)

/-! ### Degree-mismatch baselines and degree-three comparisons -/

/-- When `n ≤ m`, the distance with errors is at least `1 - n / m`. -/
theorem one_sub_div_le_distErr_of_le (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    1 - (n : ℝ) / m ≤ distErr σ τ := by
  have h := one_sub_min_div_max_le_distErr σ τ
  rwa [← Nat.cast_min, Nat.min_eq_left hnm, Nat.max_eq_right hnm] at h

/-- When `m ≤ n`, the distance with errors is at least `1 - m / n`. -/
theorem one_sub_div_le_distErr_of_ge (σ : Perm (Fin n)) (τ : Perm (Fin m)) (hmn : m ≤ n) :
    1 - (m : ℝ) / n ≤ distErr σ τ := by
  have h := one_sub_min_div_max_le_distErr σ τ
  rwa [← Nat.cast_min, Nat.min_eq_right hmn, Nat.max_eq_left hmn] at h

/-- A permutation of degree `3` and a permutation of degree `2` have distance with errors at least
`1 / 3`. -/
theorem one_div_three_le_distErr_three_two (σ : Perm (Fin 3)) (τ : Perm (Fin 2)) :
    (1 : ℝ) / 3 ≤ distErr σ τ := by
  have h := one_sub_div_le_distErr_of_ge σ τ (by decide)
  norm_num at h ⊢
  exact h

/-- A permutation of degree `2` and a permutation of degree `3` have distance with errors at least
`1 / 3`. -/
theorem one_div_three_le_distErr_two_three (σ : Perm (Fin 2)) (τ : Perm (Fin 3)) :
    (1 : ℝ) / 3 ≤ distErr σ τ := by
  rw [distErr_comm]
  exact one_div_three_le_distErr_three_two τ σ

/-- A permutation of degree `3` and a permutation of degree `m ≥ 4` have distance with errors at
least `1 / 4`. -/
theorem one_div_four_le_distErr_three_of_four_le (σ : Perm (Fin 3)) (τ : Perm (Fin m))
    (hm : 4 ≤ m) : (1 : ℝ) / 4 ≤ distErr σ τ := by
  have hbase := one_sub_div_le_distErr_of_le σ τ (by omega)
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : (3 : ℝ) / m ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- A permutation of degree `3` and a permutation of degree `m ≥ 5` have distance with errors at
least `2 / 5`. -/
theorem two_div_five_le_distErr_three_of_five_le (σ : Perm (Fin 3)) (τ : Perm (Fin m))
    (hm : 5 ≤ m) : (2 : ℝ) / 5 ≤ distErr σ τ := by
  have hbase := one_sub_div_le_distErr_of_le σ τ (by omega)
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : (3 : ℝ) / m ≤ 3 / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- A permutation of degree `3` and a permutation of any unequal degree `m ≥ 2` have distance with
errors at least `1 / 4`. -/
theorem one_div_four_le_distErr_three_of_ne (σ : Perm (Fin 3)) (τ : Perm (Fin m))
    (hm : 2 ≤ m) (hne : m ≠ 3) : (1 : ℝ) / 4 ≤ distErr σ τ := by
  by_cases hm2 : m = 2
  · subst hm2
    linarith [one_div_three_le_distErr_three_two σ τ]
  · exact one_div_four_le_distErr_three_of_four_le σ τ (by omega)

end Equiv.Perm

end
