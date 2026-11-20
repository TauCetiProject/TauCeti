/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Embedding
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import TauCeti.GroupTheory.Perm.DistErr.Basic

/-!
# Invariances of the distance with errors

This file develops the algebraic invariances of Chapman and Lubotzky's cross-degree distance
`Equiv.Perm.distErr` under inversion, equal-degree left and right multiplication, and cross-degree
initial-segment extension via `Fin.castLEEmb`.

Main results:

* `Equiv.Perm.agreeCount_inv_inv`, `Equiv.Perm.distErr_inv_inv`, and
  `Equiv.Perm.distErr_inv_one`: inverting both permutations (or inverting one permutation against
  `1`) preserves the number of agreements and the distance with errors across arbitrary degrees.
  Consequently, `Equiv.Perm.distErr_inv_mul_inv` shows that reversing an edge inverts both the
  permutation label and the gauge quotient `g * h⁻¹` without changing the edge cost.
* `Equiv.Perm.distErr_mul_left`, `Equiv.Perm.distErr_mul_right`, and
  `Equiv.Perm.mul_distErr_mul_inv_eq_movedNorm`: in equal degree, `distErr` is bi-invariant and
  `(n : ℝ) * distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h)`.
* `Equiv.Perm.distErr_mul_viaEmbedding_left`, `Equiv.Perm.distErr_mul_viaEmbedding_right`,
  `Equiv.Perm.distErr_viaEmbedding_mul_left`, `Equiv.Perm.distErr_viaEmbedding_mul_right`,
  `Equiv.Perm.distErr_viaEmbedding_right`, `Equiv.Perm.distErr_self_viaEmbedding_right`, and
  `Equiv.Perm.distErr_inv_mul_mul_mul_inv`: when `n ≤ m`, multiplying in degree `n` and
  simultaneously acting in degree `m` via `Fin.castLEEmb` preserves `agreeCount` and `distErr`,
  and extending one argument via `Fin.castLEEmb` preserves `agreeCount` and evaluates `distErr` as
  `1 - n / m + movedNorm (Fin n) (σ⁻¹ * τ) / m`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, equations (2.8)–(2.9).
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

/-- Inverting the left permutation preserves the number of agreements with `1`, across arbitrary
degrees. -/
@[simp]
theorem agreeCount_inv_one (σ : Perm (Fin n)) :
    agreeCount σ⁻¹ (1 : Perm (Fin m)) = agreeCount σ (1 : Perm (Fin m)) := by
  simpa using agreeCount_inv_inv σ (1 : Perm (Fin m))

/-- Inverting the right permutation preserves the number of agreements with `1`, across arbitrary
degrees. -/
@[simp]
theorem agreeCount_one_inv (τ : Perm (Fin m)) :
    agreeCount (1 : Perm (Fin n)) τ⁻¹ = agreeCount (1 : Perm (Fin n)) τ := by
  simpa using agreeCount_inv_inv (1 : Perm (Fin n)) τ

/-- Inverting the left permutation preserves the distance with errors from `1`, across arbitrary
degrees. -/
@[simp]
theorem distErr_inv_one (σ : Perm (Fin n)) :
    distErr σ⁻¹ (1 : Perm (Fin m)) = distErr σ (1 : Perm (Fin m)) := by
  simp [distErr_def]

/-- Inverting the right permutation preserves the distance with errors from `1`, across arbitrary
degrees. -/
@[simp]
theorem distErr_one_inv (τ : Perm (Fin m)) :
    distErr (1 : Perm (Fin n)) τ⁻¹ = distErr (1 : Perm (Fin n)) τ := by
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
  rw [← distErr_mul_left g⁻¹ σ (g * h⁻¹), ← distErr_mul_right _ _ h]
  simpa [mul_assoc] using distErr_one_right (g⁻¹ * σ * h)

/-- Rescaling the equal-degree distance with errors by the degree recovers the moved-point norm of
`g⁻¹ * σ * h` for every `n : ℕ`, including `n = 0`. -/
theorem mul_distErr_mul_inv_eq_movedNorm (σ g h : Perm (Fin n)) :
    (n : ℝ) * distErr σ (g * h⁻¹) = movedNorm (Fin n) (g⁻¹ * σ * h) := by
  rw [← distErr_mul_left g⁻¹ σ (g * h⁻¹), ← distErr_mul_right _ _ h]
  simpa [mul_assoc, distErr_comm] using mul_distErr_eq_movedNorm (1 : Perm (Fin n)) (g⁻¹ * σ * h)

/-! ### Cross-degree invariance under initial-segment embeddings -/

/-- When `n ≤ m`, left-multiplying `σ : Perm (Fin n)` by `ρ` and `τ : Perm (Fin m)` by the
initial-segment extension `ρ.viaEmbedding (Fin.castLEEmb hnm)` preserves the agreement count. -/
@[simp]
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
@[simp]
theorem agreeCount_mul_viaEmbedding_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    agreeCount (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) = agreeCount σ τ := by
  have hinv : (ρ.viaEmbedding (Fin.castLEEmb hnm))⁻¹ = ρ⁻¹.viaEmbedding (Fin.castLEEmb hnm) :=
    (map_inv (viaEmbeddingHom (Fin.castLEEmb hnm)) ρ).symm
  rw [← agreeCount_inv_inv (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)),
    mul_inv_rev, mul_inv_rev, hinv, agreeCount_mul_viaEmbedding_left _ _ _ hnm, agreeCount_inv_inv]

/-- When `n ≤ m`, left-multiplying `τ : Perm (Fin m)` by `ρ.viaEmbedding (Fin.castLEEmb hnm)` and
`σ : Perm (Fin n)` by `ρ` preserves the agreement count. -/
@[simp]
theorem agreeCount_viaEmbedding_mul_left (ρ σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    agreeCount (ρ.viaEmbedding (Fin.castLEEmb hnm) * τ) (ρ * σ) = agreeCount τ σ :=
  (agreeCount_comm _ _).trans
    ((agreeCount_mul_viaEmbedding_left ρ σ τ hnm).trans (agreeCount_comm σ τ))

/-- When `n ≤ m`, right-multiplying `τ : Perm (Fin m)` by `ρ.viaEmbedding (Fin.castLEEmb hnm)` and
`σ : Perm (Fin n)` by `ρ` preserves the agreement count. -/
@[simp]
theorem agreeCount_viaEmbedding_mul_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    agreeCount (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) (σ * ρ) = agreeCount τ σ :=
  (agreeCount_comm _ _).trans
    ((agreeCount_mul_viaEmbedding_right σ ρ τ hnm).trans (agreeCount_comm σ τ))

/-- Extending the right permutation from degree `n` to degree `m ≥ n` along `Fin.castLEEmb`
preserves the agreement count with any permutation of degree `n`. -/
@[simp]
theorem agreeCount_viaEmbedding_right (σ τ : Perm (Fin n)) (hnm : n ≤ m) :
    agreeCount σ (τ.viaEmbedding (Fin.castLEEmb hnm)) = agreeCount σ τ := by
  have h1 : agreeCount σ (τ.viaEmbedding (Fin.castLEEmb hnm)) =
      agreeCount (τ⁻¹ * σ) (1 : Perm (Fin m)) := by
    simpa using agreeCount_mul_viaEmbedding_left τ (τ⁻¹ * σ) 1 hnm
  rw [h1, agreeCount_one_right_of_le _ hnm, ← agreeCount_one_right_of_le _ le_rfl]
  simpa using (agreeCount_mul_left τ (τ⁻¹ * σ) 1).symm

/-- Extending the left permutation from degree `n` to degree `m ≥ n` along `Fin.castLEEmb`
preserves the agreement count with any permutation of degree `n`. -/
@[simp]
theorem agreeCount_viaEmbedding_left (σ τ : Perm (Fin n)) (hnm : n ≤ m) :
    agreeCount (σ.viaEmbedding (Fin.castLEEmb hnm)) τ = agreeCount σ τ :=
  (agreeCount_comm _ τ).trans
    ((agreeCount_viaEmbedding_right τ σ hnm).trans (agreeCount_comm τ σ))

/-- When `n ≤ m`, left-multiplying in degree `n` and simultaneously via `Fin.castLEEmb hnm` in
degree `m` preserves the distance with errors. -/
@[simp]
theorem distErr_mul_viaEmbedding_left (ρ σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (ρ * σ) (ρ.viaEmbedding (Fin.castLEEmb hnm) * τ) = distErr σ τ := by
  simp [distErr_def, agreeCount_mul_viaEmbedding_left _ _ _ hnm]

/-- When `n ≤ m`, right-multiplying in degree `n` and simultaneously via `Fin.castLEEmb hnm` in
degree `m` preserves the distance with errors. -/
@[simp]
theorem distErr_mul_viaEmbedding_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (σ * ρ) (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) = distErr σ τ := by
  simp [distErr_def, agreeCount_mul_viaEmbedding_right _ _ _ hnm]

/-- When `n ≤ m`, left-multiplying via `Fin.castLEEmb hnm` in degree `m` and simultaneously in
degree `n` preserves the distance with errors. -/
@[simp]
theorem distErr_viaEmbedding_mul_left (ρ σ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (ρ.viaEmbedding (Fin.castLEEmb hnm) * τ) (ρ * σ) = distErr τ σ := by
  simp [distErr_def, agreeCount_viaEmbedding_mul_left _ _ _ hnm]

/-- When `n ≤ m`, right-multiplying via `Fin.castLEEmb hnm` in degree `m` and simultaneously in
degree `n` preserves the distance with errors. -/
@[simp]
theorem distErr_viaEmbedding_mul_right (σ ρ : Perm (Fin n)) (τ : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (τ * ρ.viaEmbedding (Fin.castLEEmb hnm)) (σ * ρ) = distErr τ σ := by
  simp [distErr_def, agreeCount_viaEmbedding_mul_right _ _ _ hnm]

/-- Extending `τ : Perm (Fin n)` to degree `m ≥ n` along `Fin.castLEEmb` gives distance with
errors `1 - n / m + movedNorm (Fin n) (σ⁻¹ * τ) / m` from `σ : Perm (Fin n)`. -/
theorem distErr_viaEmbedding_right (σ τ : Perm (Fin n)) (hnm : n ≤ m) :
    distErr σ (τ.viaEmbedding (Fin.castLEEmb hnm)) =
      1 - (n : ℝ) / m + movedNorm (Fin n) (σ⁻¹ * τ) / m := by
  have h1 : distErr σ (τ.viaEmbedding (Fin.castLEEmb hnm)) =
      distErr (τ⁻¹ * σ) (1 : Perm (Fin m)) := by
    simpa using distErr_mul_viaEmbedding_left τ (τ⁻¹ * σ) 1 hnm
  rw [h1, ← distErr_inv_one (τ⁻¹ * σ), mul_inv_rev, inv_inv, distErr_one_right_of_le _ hnm]

/-- Extending `σ : Perm (Fin n)` to degree `m ≥ n` along `Fin.castLEEmb` gives distance with
errors `1 - n / m + movedNorm (Fin n) (σ⁻¹ * τ) / m` from `τ : Perm (Fin n)`. -/
theorem distErr_viaEmbedding_left (σ τ : Perm (Fin n)) (hnm : n ≤ m) :
    distErr (σ.viaEmbedding (Fin.castLEEmb hnm)) τ =
      1 - (n : ℝ) / m + movedNorm (Fin n) (σ⁻¹ * τ) / m := by
  have h1 : distErr (σ.viaEmbedding (Fin.castLEEmb hnm)) τ =
      distErr (1 : Perm (Fin m)) (σ⁻¹ * τ) := by
    simpa using distErr_viaEmbedding_mul_left σ (σ⁻¹ * τ) 1 hnm
  rw [h1, distErr_one_left_of_ge _ hnm]

/-- A permutation of degree `n` has distance with errors `1 - n / m` from its initial-segment
extension to degree `m ≥ n`. -/
@[simp]
theorem distErr_self_viaEmbedding_right (ρ : Perm (Fin n)) (hnm : n ≤ m) :
    distErr ρ (ρ.viaEmbedding (Fin.castLEEmb hnm)) = 1 - (n : ℝ) / m := by
  simp [distErr_viaEmbedding_right ρ ρ hnm]

/-- The initial-segment extension of `ρ : Perm (Fin n)` to degree `m ≥ n` has distance with errors
`1 - n / m` from `ρ`. -/
@[simp]
theorem distErr_self_viaEmbedding_left (ρ : Perm (Fin n)) (hnm : n ≤ m) :
    distErr (ρ.viaEmbedding (Fin.castLEEmb hnm)) ρ = 1 - (n : ℝ) / m := by
  simp [distErr_viaEmbedding_left ρ ρ hnm]

/-- When `n ≤ m`, transforming `σ : Perm (Fin n)` by two-sided multiplication `γ₁⁻¹ * σ * γ₂` can be
absorbed into a degree-`m` quotient `g * h⁻¹` by left-multiplying `g` and `h` via
`Fin.castLEEmb hnm`. -/
theorem distErr_inv_mul_mul_mul_inv (σ γ₁ γ₂ : Perm (Fin n)) (g h : Perm (Fin m)) (hnm : n ≤ m) :
    distErr (γ₁⁻¹ * σ * γ₂) (g * h⁻¹) =
      distErr σ ((γ₁.viaEmbedding (Fin.castLEEmb hnm) * g) *
        (γ₂.viaEmbedding (Fin.castLEEmb hnm) * h)⁻¹) := by
  have hinv₂ : (γ₂.viaEmbedding (Fin.castLEEmb hnm))⁻¹ = γ₂⁻¹.viaEmbedding (Fin.castLEEmb hnm) :=
    (map_inv (viaEmbeddingHom (Fin.castLEEmb hnm)) γ₂).symm
  rw [← distErr_mul_viaEmbedding_left γ₁ (γ₁⁻¹ * σ * γ₂) (g * h⁻¹) hnm,
    ← distErr_mul_viaEmbedding_right _ γ₂⁻¹ _ hnm]
  simp [mul_assoc, hinv₂]

end Equiv.Perm

end
