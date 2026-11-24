/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi

/-!
# Zeros of Tricomi's function in its parameter

For a fixed real argument `x ≤ 0`, this file locates the real zeros of the parameter function
`a ↦ γ*(a, x)` of Tricomi's entire incomplete Gamma function (DLMF §8.13(iii)).

* At `x = 0`, `γ*(a, 0) = 1 / Γ(a + 1)` vanishes exactly at `a = −1, −2, …`; this holds for
  complex `a`.
* For `x < 0`, `γ*(·, x)` has exactly one real zero in each interval `−(k + 1) < a < −k`,
  `k ∈ ℕ`. Grouping these intervals in pairs gives DLMF §8.13(iii)(a): exactly two zeros in each
  interval `−2n < a < 2 − 2n`, `n ≥ 1`.

For `x = −y < 0` and real `a ∉ −ℕ`, the series DLMF 8.7.1 reads
`Γ(a) γ*(a, x) = ∑ yᵏ / (k! (a + k))`, whose terms are real, positive multiples of `1 / (a + k)`.
On each interval `−(k + 1) < a < −k` every term is strictly decreasing in `a`, so the sum is
strictly decreasing there, which gives uniqueness. Existence follows from the intermediate value
theorem applied to `γ*(·, x)` on `[−(k + 1), −k]`, since `γ*(−n, x) = xⁿ` (DLMF 8.4.12) has
opposite signs at the two endpoints.

## Main results

* `Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff`: `γ*(a, 0) = 0` if and only if
  `a = −(n + 1)` for some `n : ℕ`.
* `Complex.existsUnique_tricomiIncompleteGamma_eq_zero_of_neg`: for `x < 0` and `k : ℕ`,
  `γ*(·, x)` has exactly one zero `a` with `−(k + 1) < a < −k`.
* `Complex.tricomiIncompleteGamma_param_zeros_of_neg`: for `x < 0` and `n ≥ 1`, the zeros of
  `γ*(·, x)` in `−2n < a < 2 − 2n` are exactly two points `a₁ < 1 − 2n < a₂`.

## References

* NIST Digital Library of Mathematical Functions, §8.13(iii), <https://dlmf.nist.gov/8.13>.
* K. S. Kölbig, *On the zeros of the incomplete gamma function*, Math. Comp. 26 (1972),
  751–755.
-/

public section

noncomputable section

open Set
open scoped Nat

namespace Complex

/-- Tricomi's function at `z = 0` vanishes exactly at the parameters `a = −1, −2, …`, the poles
of `Γ(a + 1)` (DLMF 8.4.2). -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff {a : ℂ} :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, a = -(n + 1) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Gamma_eq_zero_iff]
  exact exists_congr fun n => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- At a nonpositive integer `a = −n`, `γ*(a, x) = xⁿ` (DLMF 8.4.12) does not vanish for real
`x ≠ 0`. -/
private theorem tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast {x : ℝ} (hx : x ≠ 0)
    {a : ℝ} {n : ℕ} (ha : a = -n) : tricomiIncompleteGamma a x ≠ 0 := by
  rw [ha, ofReal_neg, ofReal_natCast, tricomiIncompleteGamma_neg_natCast]
  exact pow_ne_zero _ (ofReal_ne_zero.2 hx)

/-- For `x < 0`, the real sum `∑ (−x)ᵏ / (k! (a + k))` is strictly decreasing in `a` on each
interval `−(k + 1) < a < −k`: every term is a positive multiple of `1 / (a + j)`, and `a + j` keeps
its sign there. -/
private theorem hasSum_lt_of_mem_Ioo {x : ℝ} (hx : x < 0) {k : ℕ} {a b : ℝ}
    (ha : a ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hb : b ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hab : a < b)
    {sa sb : ℝ} (hsa : HasSum (fun j : ℕ => (-x) ^ j / (j ! * (a + j))) sa)
    (hsb : HasSum (fun j : ℕ => (-x) ^ j / (j ! * (b + j))) sb) : sb < sa := by
  have hlt : ∀ j : ℕ, (-x) ^ j / (j ! * (b + j)) < (-x) ^ j / (j ! * (a + j)) := fun j => by
    have hp : 0 < (a + j) * (b + j) := by
      rcases le_or_gt j k with hj | hj
      · have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
        exact mul_pos_of_neg_of_neg (by linarith [ha.2]) (by linarith [hb.2])
      · have hj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hj
        exact mul_pos (by linarith [ha.1]) (by linarith [hb.1])
    have hpow : 0 < (-x) ^ j := pow_pos (by linarith) j
    rw [← sub_neg, show (-x) ^ j / (j ! * (b + j)) - (-x) ^ j / (j ! * (a + j)) =
        (-x) ^ j / j ! * ((a - b) / ((a + j) * (b + j))) by
      field_simp [left_ne_zero_of_mul hp.ne', right_ne_zero_of_mul hp.ne']
      ring]
    exact mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos (by linarith) hp)
  exact hasSum_lt (fun j => (hlt j).le) (hlt 0) hsb hsa

/-- Existence of a zero of `γ*(·, x)` in `−(k + 1) < a < −k` for `x < 0`, by the intermediate
value theorem: `γ*(−n, x) = xⁿ` has opposite signs at the two endpoints. -/
private theorem exists_mem_Ioo_tricomiIncompleteGamma_eq_zero {x : ℝ} (hx : x < 0) (k : ℕ) :
    ∃ a ∈ Ioo (-(k + 1 : ℝ)) (-k), tricomiIncompleteGamma a x = 0 := by
  -- the real part of `γ*(·, x)` on the real line, which is `xⁿ` at `−n`
  set f : ℝ → ℝ := fun a => (tricomiIncompleteGamma a x).re with hf_def
  have hf : Continuous f := continuous_re.comp
    ((differentiable_tricomiIncompleteGamma_left x).continuous.comp continuous_ofReal)
  have hval : ∀ n : ℕ, f (-n) = x ^ n := fun n => by
    simp [hf_def, ← ofReal_pow]
  have hx0 : x ≠ 0 := hx.ne
  have hsign : (0 : ℝ) ∈ uIcc (f (-(k + 1 : ℕ))) (f (-k)) := by
    rw [hval, hval, mem_uIcc, pow_succ]
    rcases Nat.even_or_odd k with hk | hk
    · have := hk.pow_pos hx0
      exact Or.inl ⟨by nlinarith, this.le⟩
    · have := hk.pow_neg hx
      exact Or.inr ⟨this.le, by nlinarith⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf.continuousOn hsign
  -- `γ*(c, x)` is real, so the vanishing of its real part is enough
  have hre : (tricomiIncompleteGamma c x).re = 0 := hfc
  have hc0 : tricomiIncompleteGamma c x = 0 := by
    rw [← ofReal_tricomiIncompleteGamma_ofReal_re, hre, ofReal_zero]
  have hle : (-(k + 1 : ℕ) : ℝ) ≤ -k := by push_cast; linarith
  rw [uIcc_of_le hle] at hc
  refine ⟨c, ⟨lt_of_le_of_ne (by exact_mod_cast hc.1) ?_, lt_of_le_of_ne hc.2 ?_⟩, hc0⟩
  · rintro rfl
    exact tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx0 (n := k + 1)
      (by push_cast; ring) hc0
  · rintro rfl
    exact tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx0 rfl hc0

/-- Uniqueness of the zero of `γ*(·, x)` in `−(k + 1) < a < −k` for `x < 0`: there
`∑ (−x)ʲ / (j! (a + j)) = Γ(a) γ*(a, x)`, and the sum is strictly decreasing. -/
private theorem eq_of_tricomiIncompleteGamma_eq_zero_of_mem_Ioo {x : ℝ} (hx : x < 0) {k : ℕ}
    {a b : ℝ} (ha : a ∈ Ioo (-(k + 1 : ℝ)) (-k)) (hb : b ∈ Ioo (-(k + 1 : ℝ)) (-k))
    (ha0 : tricomiIncompleteGamma a x = 0) (hb0 : tricomiIncompleteGamma b x = 0) : a = b := by
  have hsum : ∀ c ∈ Ioo (-(k + 1 : ℝ)) (-k), tricomiIncompleteGamma c x = 0 →
      HasSum (fun j : ℕ => (-x) ^ j / (j ! * (c + j))) 0 := fun c hc hc0 => by
    have h :=
      hasSum_Gamma_mul_re_tricomiIncompleteGamma_ofReal (Real.ne_neg_natCast_of_mem_Ioo hc) x
    rwa [hc0, zero_re, mul_zero] at h
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (hasSum_lt_of_mem_Ioo hx ha hb h (hsum a ha ha0) (hsum b hb hb0)) (lt_irrefl 0)
  · exact h
  · exact absurd (hasSum_lt_of_mem_Ioo hx hb ha h (hsum b hb hb0) (hsum a ha ha0)) (lt_irrefl 0)

/-- For `x < 0` and `k : ℕ`, Tricomi's function `γ*(·, x)` has exactly one zero in the interval
`−(k + 1) < a < −k`. -/
theorem existsUnique_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0) (k : ℕ) :
    ∃! a : ℝ, a ∈ Ioo (-(k + 1 : ℝ)) (-k) ∧ tricomiIncompleteGamma a x = 0 := by
  obtain ⟨a, ha, ha0⟩ := exists_mem_Ioo_tricomiIncompleteGamma_eq_zero hx k
  exact ⟨a, ⟨ha, ha0⟩, fun b ⟨hb, hb0⟩ =>
    eq_of_tricomiIncompleteGamma_eq_zero_of_mem_Ioo hx hb ha hb0 ha0⟩

/-- DLMF §8.13(iii)(a): for `x < 0` and `n ≥ 1`, Tricomi's function `γ*(·, x)` has exactly two
zeros in the interval `−2n < a < 2 − 2n`, one on each side of `a = 1 − 2n`. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {x : ℝ} (hx : x < 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ a₁ a₂ : ℝ, a₁ < 1 - 2 * n ∧ 1 - 2 * n < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * n) ∧ tricomiIncompleteGamma a x = 0} =
        {a₁, a₂} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨a₁, ⟨ha₁, ha₁0⟩, hu₁⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * m + 1)
  obtain ⟨a₂, ⟨ha₂, ha₂0⟩, hu₂⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * m)
  push_cast at ha₁ ha₂ hu₁ hu₂
  refine ⟨a₁, a₂, by push_cast; linarith [ha₁.2], by push_cast; linarith [ha₂.1],
    Set.ext fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ha0⟩
    push_cast at h₁ h₂
    rcases lt_trichotomy a (-(2 * m + 1)) with h | h | h
    · exact Or.inl (hu₁ a ⟨⟨by linarith, by linarith⟩, ha0⟩)
    · exact absurd ha0 (tricomiIncompleteGamma_ofReal_ne_zero_of_eq_neg_natCast hx.ne
        (n := 2 * m + 1) (by rw [h]; push_cast; ring))
    · exact Or.inr (hu₂ a ⟨⟨by linarith, by linarith⟩, ha0⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨by push_cast; linarith [ha₁.1], by push_cast; linarith [ha₁.2]⟩, ha₁0⟩
    · exact ⟨⟨by push_cast; linarith [ha₂.1], by push_cast; linarith [ha₂.2]⟩, ha₂0⟩

end Complex
