/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam.Analytic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.RingTheory.RootsOfUnity.Complex.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Root-of-unity values of Wenzl's parameters

This file evaluates `TauCeti.wenzlParam` at the complex roots of unity `Q = exp (± 2 π i / l)`
for `l ≥ 3` and `0 < k < l`.

## Main results

* `TauCeti.wenzlParam_exp_two_pi_mul_I_div`, `TauCeti.wenzlParam_neg_exp_two_pi_mul_I_div`,
  `TauCeti.wenzlParam_sub_exp_two_pi_mul_I_div`,
  `TauCeti.wenzlParam_exp_two_pi_mul_I_div_two_mul`, and
  `TauCeti.exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff`: the real values, complementary
  pairs `a_(l - k) = a_(-k) = 1 - a_k`, middle value `a_m = 1 / 2`, and separation of the scalar
  endpoints `k ∈ {1, l - 1}` (all of `l = 3`) from the `(0, 1)` interior cases `2 ≤ k ≤ l - 2` at
  `exp (± 2 π i / l)`.
-/

public section

open Finset

namespace TauCeti

/-! ### Roots of unity -/

section RootOfUnity

open Complex
open scoped Real

private theorem two_mul_pi_div_mul_I (l : ℕ) : 2 * (π / (l : ℂ)) * I = 2 * π * I / l := by
  ring

private theorem isPrimitiveRoot_exp_two_pi_mul_I_div {l : ℕ} (hl : l ≠ 0) :
    IsPrimitiveRoot (exp (2 * π * I / l)) l :=
  Complex.isPrimitiveRoot_exp l hl

/-- **The values at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at `Q = exp (2 π i / l)`,
`a_k(Q) = sin ((k + 1) π / l) / (2 * cos (π / l) * sin (k π / l))`, a real number. -/
theorem wenzlParam_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos (by omega)
  have hsin : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl
  have h := wenzlParam_exp_mul_I k (θ := π / l) (by exact_mod_cast hcos.ne')
    (by rw [Int.cast_natCast, ← mul_div_assoc]; exact_mod_cast hsin.ne')
  rw [two_mul_pi_div_mul_I] at h
  rw [h]
  push_cast
  ring_nf

/-- The values at the conjugate roots of unity `Q = exp (-2 π i / l)` agree with those at
`exp (2 π i / l)`. -/
theorem wenzlParam_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (-(2 * π * I / l))) =
      ↑(Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  rw [wenzlParam_exp_neg, wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl]

/-- **The negative-index values at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at
`Q = exp (2 π i / l)`, `a_(-k)(Q) = sin ((k - 1) π / l) / (2 * cos (π / l) * sin (k π / l))`. -/
theorem wenzlParam_neg_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k) (hkl : k < l) :
    wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) =
      ↑(Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos (by omega)
  have hsin : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl
  have h := wenzlParam_exp_mul_I (-(k : ℤ)) (θ := π / l) (by exact_mod_cast hcos.ne')
    (by rw [Int.cast_neg, Int.cast_natCast, neg_mul, sin_neg, neg_ne_zero, ← mul_div_assoc]
        exact_mod_cast hsin.ne')
  have hnum : (-(k : ℂ) + 1) * (π / l) = -(((k : ℂ) - 1) * π / l) := by ring
  have hden : -(k : ℂ) * (π / l) = -(k * π / l) := by ring
  rw [two_mul_pi_div_mul_I, Int.cast_neg, Int.cast_natCast, hnum, hden, sin_neg, sin_neg] at h
  rw [h]
  push_cast
  field_simp

/-- The negative-index values at `Q = exp (-2 π i / l)` agree with those at `exp (2 π i / l)`. -/
theorem wenzlParam_neg_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) =
      ↑(Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))) := by
  rw [wenzlParam_exp_neg, wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl]

/-- **Complement identity at the roots of unity.** For `l ≥ 3` and `0 < k < l`, at
`Q = exp (2 π i / l)`, `a_k(Q) + a_(-k)(Q) = 1`. -/
theorem wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) + wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) = 1 := by
  have hζ := isPrimitiveRoot_exp_two_pi_mul_I_div (l := l) (by omega)
  have hsum : ∑ i ∈ range k, exp (2 * π * I / l) ^ i ≠ 0 := by
    intro h0
    have hgeom := geom_sum_mul (exp (2 * π * I / l)) k
    rw [h0, zero_mul] at hgeom
    exact sub_ne_zero.2 (hζ.pow_ne_one_of_pos_of_lt hk₀.ne' hkl) hgeom.symm
  have hden : (1 + exp (2 * π * I / l)) * ∑ i ∈ range (k : ℤ).natAbs, exp (2 * π * I / l) ^ i ≠ 0 :=
    mul_ne_zero (one_add_exp_two_pi_mul_I_div_ne_zero hl) (by simpa using hsum)
  exact wenzlParam_add_wenzlParam_neg hden

/-- **Complementary index `l - k` at the roots of unity.** For `l ≥ 2` and `k ≤ l`, at
`Q = exp (2 π i / l)`, `a_(l - k)(Q) = a_(-k)(Q)`. -/
theorem wenzlParam_sub_exp_two_pi_mul_I_div {l k : ℕ} (hl : 2 ≤ l) (hkl : k ≤ l) :
    wenzlParam ((l - k : ℕ) : ℤ) (exp (2 * π * I / l)) =
      wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) := by
  have hζ := isPrimitiveRoot_exp_two_pi_mul_I_div (l := l) (by omega)
  rw [Nat.cast_sub hkl, sub_eq_neg_add]
  exact wenzlParam_add_of_pow_eq_one (hζ.ne_one (by omega)) hζ.pow_eq_one (-(k : ℤ))

/-- At `Q = exp (-2 π i / l)`, `a_(l - k)(Q) = a_(-k)(Q)` for `l ≥ 2` and `k ≤ l`. -/
theorem wenzlParam_sub_exp_neg_two_pi_mul_I_div {l k : ℕ} (hl : 2 ≤ l) (hkl : k ≤ l) :
    wenzlParam ((l - k : ℕ) : ℤ) (exp (-(2 * π * I / l))) =
      wenzlParam (-(k : ℤ)) (exp (-(2 * π * I / l))) := by
  simp only [wenzlParam_exp_neg, wenzlParam_sub_exp_two_pi_mul_I_div hl hkl]

/-- **The middle value.** For `l = 2 * m ≥ 4`, at `Q = exp (2 π i / l)`, `a_m(Q) = 1 / 2`. -/
theorem wenzlParam_exp_two_pi_mul_I_div_two_mul {m : ℕ} (hm : 2 ≤ m) :
    wenzlParam (m : ℤ) (exp (2 * π * I / (2 * m))) = 1 / 2 := by
  have h := wenzlParam_exp_two_pi_mul_I_div (l := 2 * m) (k := m) (by omega) (by omega) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  have hcos : Real.cos (π / (2 * m)) ≠ 0 := by
    simpa using (cos_pi_div_natCast_pos (by omega : 2 < 2 * m)).ne'
  -- With `θ = π / (2 * m)`: `sin ((m + 1) θ) = cos θ` and `sin (m θ) = 1`.
  have h₁ : (m + 1) * π / (2 * m) = π / (2 * m) + π / 2 := by field_simp; ring
  have h₂ : m * π / (2 * m) = π / 2 := by field_simp
  rw [h, h₁, h₂, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one,
    div_mul_cancel_right₀ hcos]
  norm_num

/-- At `Q = exp (2 π i / l)` with `l ≥ 3`, the first positive parameter `a_1(Q)` is `1`. -/
theorem wenzlParam_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    wenzlParam 1 (exp (2 * π * I / l)) = 1 :=
  wenzlParam_one_left (one_add_exp_two_pi_mul_I_div_ne_zero hl)

/-- At `Q = exp (2 π i / l)` with `l ≥ 2`, the last parameter `a_(l - 1)(Q)` is `0`. -/
theorem wenzlParam_sub_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 2 ≤ l) :
    wenzlParam ((l - 1 : ℕ) : ℤ) (exp (2 * π * I / l)) = 0 := by
  rw [wenzlParam_sub_exp_two_pi_mul_I_div hl (by omega), Nat.cast_one, wenzlParam_neg_one]

/-- At `Q = exp (2 π i / l)` with `l ≥ 3`, `a_(-(l - 1))(Q) = 1`. -/
theorem wenzlParam_neg_sub_one_exp_two_pi_mul_I_div {l : ℕ} (hl : 3 ≤ l) :
    wenzlParam (-((l - 1 : ℕ) : ℤ)) (exp (2 * π * I / l)) = 1 := by
  have h := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div (l := l) (k := l - 1) hl
    (by omega) (by omega)
  rwa [wenzlParam_sub_one_exp_two_pi_mul_I_div (by omega), zero_add] at h

/-- **Strict `(0, 1)` interior values for `2 ≤ k ≤ l - 2` (`l ≥ 4`).** When `2 ≤ k` and
`k + 2 ≤ l`, `a_k(exp (2 π i / l))` is a real number `η ∈ (0, 1)`, and `a_(-k)(exp (2 π i / l))` is
`1 - η ∈ (0, 1)`. -/
theorem exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div {l k : ℕ} (hk : 2 ≤ k) (hkl : k + 2 ≤ l) :
    ∃ η ∈ Set.Ioo (0 : ℝ) 1,
      wenzlParam (k : ℤ) (exp (2 * π * I / l)) = η ∧
        wenzlParam (-(k : ℤ)) (exp (2 * π * I / l)) = ↑(1 - η) := by
  have hl : 3 ≤ l := by omega
  have hk₀ : 0 < k := by omega
  have hkl₀ : k < l := by omega
  have hcos : 0 < Real.cos (π / l) := cos_pi_div_natCast_pos (by omega)
  have hsin_k : 0 < Real.sin (k * π / l) := sin_natCast_mul_pi_div_natCast_pos hk₀ hkl₀
  have hsin_add : 0 < Real.sin ((k + 1) * π / l) := by
    simpa using sin_natCast_mul_pi_div_natCast_pos (l := l) (k := k + 1) (by omega) (by omega)
  have hsin_sub : 0 < Real.sin ((k - 1) * π / l) := by
    have hk_sub : 1 ≤ k := by omega
    simpa [Nat.cast_sub hk_sub] using
      sin_natCast_mul_pi_div_natCast_pos (l := l) (k := k - 1) (by omega) (by omega)
  set r₁ := Real.sin ((k + 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))
  set r₂ := Real.sin ((k - 1) * π / l) / (2 * Real.cos (π / l) * Real.sin (k * π / l))
  have hr₁ : 0 < r₁ := by positivity
  have hr₂ : 0 < r₂ := by positivity
  have hsum_c := wenzlParam_add_wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀
  rw [wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl₀,
    wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀, ← ofReal_add, ← ofReal_one] at hsum_c
  have hsum : r₁ + r₂ = 1 := Complex.ofReal_injective hsum_c
  have hsub : 1 - r₁ = r₂ := by linarith
  refine ⟨r₁, ⟨hr₁, by linarith⟩, wenzlParam_exp_two_pi_mul_I_div hl hk₀ hkl₀, ?_⟩
  rw [wenzlParam_neg_exp_two_pi_mul_I_div hl hk₀ hkl₀, hsub]

/-- **Characterization of nontrivial root-of-unity parameters.** For `l ≥ 3` and `0 < k < l`,
`a_k(exp (2 π i / l))` lies strictly in `(0, 1)` if and only if `2 ≤ k` and `k + 2 ≤ l` (so in
particular `l ≥ 4`). -/
theorem exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    (∃ η ∈ Set.Ioo (0 : ℝ) 1, wenzlParam (k : ℤ) (exp (2 * π * I / l)) = η) ↔
      2 ≤ k ∧ k + 2 ≤ l := by
  refine ⟨fun ⟨η, hη, heq⟩ ↦ ?_, fun ⟨hk, hkl'⟩ ↦ ?_⟩
  · by_contra h
    have hk_end : k = 1 ∨ k = l - 1 := by omega
    rcases hk_end with rfl | rfl
    · rw [Nat.cast_one, wenzlParam_one_exp_two_pi_mul_I_div hl, ← ofReal_one] at heq
      exact hη.2.ne' (Complex.ofReal_injective heq)
    · rw [wenzlParam_sub_one_exp_two_pi_mul_I_div (by omega), ← ofReal_zero] at heq
      exact hη.1.ne (Complex.ofReal_injective heq)
  · obtain ⟨η, hη, h1, _⟩ := exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div hk hkl'
    exact ⟨η, hη, h1⟩

/-- **Characterization of scalar root-of-unity parameters.** For `l ≥ 3` and `0 < k < l`,
`a_k(exp (2 π i / l))` belongs to `{0, 1}` if and only if `k = 1` or `k + 1 = l`. In particular, for
`l = 3` every `0 < k < 3` gives a scalar endpoint `{0, 1}`. -/
theorem wenzlParam_exp_two_pi_mul_I_div_mem_pair_iff {l k : ℕ} (hl : 3 ≤ l) (hk₀ : 0 < k)
    (hkl : k < l) :
    wenzlParam (k : ℤ) (exp (2 * π * I / l)) ∈ ({0, 1} : Set ℂ) ↔ k = 1 ∨ k + 1 = l := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hnot
    obtain ⟨η, hη, heq, _⟩ := exists_mem_Ioo_wenzlParam_exp_two_pi_mul_I_div (l := l) (k := k)
      (by omega) (by omega)
    rw [heq, Set.mem_insert_iff, Set.mem_singleton_iff, ← ofReal_zero, ← ofReal_one] at h
    rcases h with h | h
    · exact hη.1.ne' (Complex.ofReal_injective h)
    · exact hη.2.ne (Complex.ofReal_injective h)
  · rcases h with rfl | h
    · simp [wenzlParam_one_exp_two_pi_mul_I_div hl]
    · obtain rfl : k = l - 1 := by omega
      simp [wenzlParam_sub_one_exp_two_pi_mul_I_div (l := l) (by omega)]

end RootOfUnity

end TauCeti
