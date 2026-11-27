/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Good torus sizes

For a real `θ`, the good torus sizes `W_θ` are the integers `n ≥ 1` such that `θ` is at distance
more than `n^{-3/2}` from every point `πj/n`, `j ∈ ℤ`. On an `n₁ × n₂` torus with liquid type
weights, the twisted Riemann sums of the dimer model avoid the zeros of the characteristic function
when `n₁ ∈ W_{θ₀}`, so these are the torus sizes along which the torus measures converge to the
determinantal Gibbs measure.

The main result is that if `θ ∉ πℤ` then, for all large `n`, `n ∈ W_θ` or `n + 1 ∈ W_θ`
(`TauCeti.eventually_mem_goodTorusSizes_or_add_one`). The proof: if `n` and `n + 1` both fail,
with witnesses `j` and `j'`, then `θ - π(j' - j) = (n + 1)(θ - πj'/(n + 1)) - n(θ - πj/n)` has
absolute value at most `(2n + 1) n^{-3/2} ≤ 3/√n`, which is smaller than the distance from `θ` to
`πℤ` once `n` is large.

`n + 1` cannot be replaced by `n + 2`: for `θ = π/2` no even `n` is good.

## Main definitions and results

* `TauCeti.goodTorusSizes θ`: the set `W_θ`.
* `TauCeti.eventually_mem_goodTorusSizes_or_add_one`: for `θ ∉ πℤ`, eventually `n ∈ W_θ` or
  `n + 1 ∈ W_θ`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lemma 4.7, whose conclusion `n` or `n + 2` is corrected here to `n` or `n + 1`.
* R. Kenyon, A. Okounkov, S. Sheffield, *Dimers and amoebae*, Ann. of Math. 163 (2006),
  for the convergence of the torus measures.
-/

public section

open Filter Real

namespace TauCeti

/-- The good torus sizes `W_θ = {n ≥ 1 : |θ - πj/n| > n^{-3/2} for every j ∈ ℤ}`, with
`n^{-3/2}` written `(n √n)⁻¹`. -/
def goodTorusSizes (θ : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∀ j : ℤ, ((n : ℝ) * √n)⁻¹ < |θ - π * j / n|}

/-- Membership in `goodTorusSizes θ`. -/
@[simp]
theorem mem_goodTorusSizes {θ : ℝ} {n : ℕ} :
    n ∈ goodTorusSizes θ ↔ 1 ≤ n ∧ ∀ j : ℤ, ((n : ℝ) * √n)⁻¹ < |θ - π * j / n| :=
  Iff.rfl

/-- If neither `n` nor `n + 1` is a good torus size, with `n ≥ 1`, then `θ` is within `3/√n` of a
point of `πℤ`. -/
theorem exists_abs_sub_mul_le_of_notMem_goodTorusSizes {θ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h₀ : n ∉ goodTorusSizes θ) (h₁ : n + 1 ∉ goodTorusSizes θ) :
    ∃ k : ℤ, |θ - π * k| ≤ 3 / √n := by
  simp only [mem_goodTorusSizes, not_and, not_forall, not_lt] at h₀ h₁
  obtain ⟨j, hj⟩ := h₀ hn
  obtain ⟨j', hj'⟩ := h₁ (by omega)
  refine ⟨j' - j, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < √(n : ℝ) := sqrt_pos.2 hn0
  have hs1 : √(n : ℝ) ≤ √((n + 1 : ℕ) : ℝ) := sqrt_le_sqrt (by push_cast; linarith)
  have hm : (n : ℝ) * √n ≤ ((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) :=
    mul_le_mul (by push_cast; linarith) hs1 hs0.le (by positivity)
  have hj'' : |θ - π * j' / (n + 1 : ℕ)| ≤ ((n : ℝ) * √n)⁻¹ :=
    hj'.trans (inv_anti₀ (by positivity) hm)
  have hid : θ - π * ((j' - j : ℤ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (θ - π * j' / (n + 1 : ℕ)) - n * (θ - π * j / n) := by
    push_cast
    field_simp
    ring
  rw [hid]
  calc |((n + 1 : ℕ) : ℝ) * (θ - π * j' / (n + 1 : ℕ)) - n * (θ - π * j / n)|
      ≤ ((n + 1 : ℕ) : ℝ) * ((n : ℝ) * √n)⁻¹ + n * ((n : ℝ) * √n)⁻¹ := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
          rw [abs_mul, abs_of_nonneg (by positivity)]
        · exact mul_le_mul_of_nonneg_left hj'' (by positivity)
        · exact mul_le_mul_of_nonneg_left hj (by positivity)
    _ ≤ 3 / √n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [← add_mul, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hs0]
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 this) hs0.le]

/-- **Good torus sizes.** If `θ ∉ πℤ` then, for all large `n`, `n` or `n + 1` is a good torus
size. -/
theorem eventually_mem_goodTorusSizes_or_add_one {θ : ℝ} (hθ : ∀ k : ℤ, θ ≠ π * k) :
    ∀ᶠ n in atTop, n ∈ goodTorusSizes θ ∨ n + 1 ∈ goodTorusSizes θ := by
  set δ := |θ / π - round (θ / π)| with hδ
  have hδ0 : 0 < δ := by
    refine abs_pos.2 fun h => hθ (round (θ / π)) ?_
    rw [sub_eq_zero] at h
    rw [← h]
    field_simp
  have hlim : Tendsto (fun n : ℕ => 3 / √(n : ℝ)) atTop (nhds 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul (3 : ℝ)
    simpa [div_eq_mul_inv] using this
  filter_upwards [hlim.eventually (gt_mem_nhds (mul_pos pi_pos hδ0)), eventually_ge_atTop 1]
    with n hn h1
  by_contra! h
  obtain ⟨k, hk⟩ := exists_abs_sub_mul_le_of_notMem_goodTorusSizes h1 h.1 h.2
  have hround : π * δ ≤ |θ - π * k| := by
    have hπδ : π * δ = |π * (θ / π - round (θ / π))| := by rw [hδ, abs_mul, abs_of_pos pi_pos]
    rw [hπδ]
    calc |π * (θ / π - round (θ / π))| ≤ |π * (θ / π - k)| := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (round_le _ _) (abs_nonneg _)
      _ = |θ - π * k| := by
          congr 1
          field_simp
  linarith

end TauCeti
