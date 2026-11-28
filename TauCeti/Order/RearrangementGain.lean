/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Tactic.Linarith

/-!
# Quantitative rearrangement inequality with a separation gain

If `o` reverses the order of `b` with a uniform gap `δ ≥ 0` (meaning `o x + δ ≤ o y` whenever
`b y < b x`), then permuting `b` by `w : Equiv.Perm n` increases the dot product `o ⬝ᵥ b` by at
least `δ * |b i - b (w i)|` for every index `i` (`TauCeti.dotProduct_add_mul_abs_sub_le_comp_perm`).
Specializing to `ℤ` with `δ = 1` gives `o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ (b ∘ w)` whenever `o`
strictly reverses `b` (`TauCeti.dotProduct_add_abs_sub_le_comp_perm_int`). When `0 < δ`, equality
`o ⬝ᵥ (b ∘ w) = o ⬝ᵥ b` forces `b (w i) = b i` for every `i`
(`TauCeti.apply_perm_eq_of_dotProduct_eq`).

## Main results

* `TauCeti.dotProduct_add_mul_abs_sub_le_comp_perm`: quantitative rearrangement inequality with
  uniform gap `δ ≥ 0` over a linearly ordered commutative ring.
* `TauCeti.dotProduct_add_abs_sub_le_comp_perm_int`: integer specialization with gap `1`.
* `TauCeti.apply_perm_eq_of_dotProduct_eq`: equality rigidity when `0 < δ`.

## Provenance

Adapted from `New.Orbital.dotProduct_add_gain_le_comp_perm` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/DiscreteSeries/Character/FormalDegree.lean`).
-/

public section

namespace TauCeti

open Equiv

variable {n R : Type*} [Fintype n]

/-- **Quantitative rearrangement inequality with a separation gain.** If `o` reverses the order of
`b` with uniform gap `δ ≥ 0` (so `o x + δ ≤ o y` whenever `b y < b x`), then permuting `b` by
`w` increases `o ⬝ᵥ b` by at least `δ * |b i - b (w i)|` for every `i`. -/
theorem dotProduct_add_mul_abs_sub_le_comp_perm [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {o b : n → R} {δ : R} (hδ : 0 ≤ δ) (ho : ∀ x y : n, b y < b x → o x + δ ≤ o y)
    (w : Perm n) (i : n) :
    o ⬝ᵥ b + δ * |b i - b (w i)| ≤ o ⬝ᵥ (b ∘ w) := by
  classical
  have rearr (c : R) (hc : c = δ ∨ c = -δ) :
      (o + Pi.single i c) ⬝ᵥ b ≤ (o + Pi.single i c) ⬝ᵥ (b ∘ w) := by
    refine Antivary.sum_mul_le_sum_mul_comp_perm fun x y hxy ↦ ?_
    have hgap := ho y x hxy
    by_cases hx : x = i
    · subst hx
      by_cases hy : y = x
      · subst hy; exact absurd hxy (lt_irrefl _)
      · rcases hc with rfl | rfl <;> simp [hy] <;> linarith
    · by_cases hy : y = i
      · subst hy; rcases hc with rfl | rfl <;> simp [hx] <;> linarith
      · rcases hc with rfl | rfl <;> simp [hx, hy] <;> linarith
  have hup : o ⬝ᵥ b + δ * b i ≤ o ⬝ᵥ (b ∘ w) + δ * b (w i) := by
    simpa [add_dotProduct] using rearr δ (.inl rfl)
  have hdown : o ⬝ᵥ b + (-δ) * b i ≤ o ⬝ᵥ (b ∘ w) + (-δ) * b (w i) := by
    simpa [add_dotProduct] using rearr (-δ) (.inr rfl)
  rcases abs_cases (b i - b (w i)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- **Integer rearrangement inequality with unit gain.** If `o : n → ℤ` strictly reverses the order
of `b : n → ℤ`, then permuting `b` by `w` raises `o ⬝ᵥ b` by at least `|b i - b (w i)|`. -/
theorem dotProduct_add_abs_sub_le_comp_perm_int {o b : n → ℤ}
    (ho : ∀ x y : n, b y < b x → o x < o y) (w : Perm n) (i : n) :
    o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ (b ∘ w) := by
  simpa using dotProduct_add_mul_abs_sub_le_comp_perm (δ := (1 : ℤ)) zero_le_one
    (fun x y hxy ↦ Int.add_one_le_of_lt (ho x y hxy)) w i

/-- If `o` reverses `b` with strictly positive gap `0 < δ`, then any permutation `w` achieving
`o ⬝ᵥ (b ∘ w) = o ⬝ᵥ b` must preserve every value of `b`. -/
theorem apply_perm_eq_of_dotProduct_eq [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {o b : n → R} {δ : R} (hδ : 0 < δ) (ho : ∀ x y : n, b y < b x → o x + δ ≤ o y)
    {w : Perm n} (heq : o ⬝ᵥ (b ∘ w) = o ⬝ᵥ b) (i : n) :
    b (w i) = b i := by
  have hle := dotProduct_add_mul_abs_sub_le_comp_perm hδ.le ho w i
  rw [heq] at hle
  have hmul : δ * |b i - b (w i)| ≤ 0 := by linarith
  have habs : |b i - b (w i)| ≤ 0 := nonpos_of_mul_nonpos_right hmul hδ
  exact (sub_eq_zero.mp (abs_nonpos_iff.mp habs)).symm

end TauCeti
