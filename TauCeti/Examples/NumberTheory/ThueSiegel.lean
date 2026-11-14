/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThueSiegel

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Examples and sharpness of Thue–Siegel's lemma

Concrete instances and boundary counterexamples for `TauCeti.ThueSiegel`:

* For the single rational linear form `ξ₀ + ξ₁` in two variables with `U = 2`, `X = 1`, and
  `ℓ = 3` (`3 ^ 1 < (1 + 1) ^ 2`), `exists_ne_zero_int_vec_abs_le_of_pow_lt` produces a nonzero
  `ξ : Fin 2 → ℤ` with `|ξ₀|, |ξ₁| ≤ 1` and `|ξ₀ + ξ₁| ≤ 2 / 3`, forcing `ξ₀ + ξ₁ = 0`.
* In `exists_ne_zero_int_vec_abs_le_of_pow_lt`, the strict counting inequality
  `ℓ ^ |κ| < (X + 1) ^ |ι|` cannot be weakened to `≤`: for one variable and one form `u = 1` with
  `U = 1`, `X = 1`, and `ℓ = 2`, equality `2 ^ 1 = (1 + 1) ^ 1` holds while every nonzero `ξ` with
  `|ξ₀| ≤ 1` has `|ξ₀| = 1 > 1 / 2`.
* In `exists_ne_zero_int_vec_norm_le_of_pow_le`, the non-strict counting inequality
  `(√2 · X · exp (U + V) + 1) ^ (2 |κ|) ≤ (X + 1) ^ |ι|` is genuine even at the integer boundary
  `√2 · X · exp (U + V) = 3` (`X = 3`, `|κ| = 1`, `|ι| = 2`, where `4 ^ 2 = 4 ^ 2`), whereas
  `0 < X` and `[Nonempty ι]` are needed when `κ` is empty.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemmas 4.11 and 4.12 (pp. 132–134).
-/

public section

namespace TauCeti.ThueSiegelExample

open TauCeti.ThueSiegel

/-- Applying `exists_ne_zero_int_vec_abs_le_of_pow_lt` over `ℚ` to the single linear form
`ξ 0 + ξ 1` in two variables with `U = 2`, `X = 1`, and `ℓ = 3` (`3 < 4`) yields a nonzero
integer vector `ξ` in `[-1, 1]²` with `|ξ 0 + ξ 1| ≤ 2 / 3`, and hence `ξ 0 + ξ 1 = 0`. -/
theorem exists_ne_zero_int_vec_sum_eq_zero :
    ∃ ξ : Fin 2 → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ 1) ∧ ξ 0 + ξ 1 = 0 := by
  obtain ⟨ξ, hξ0, hξX, hξu⟩ := exists_ne_zero_int_vec_abs_le_of_pow_lt
    (fun (_ : Fin 2) (_ : Fin 1) ↦ (1 : ℚ)) (U := 2) (X := 1) (ℓ := 3)
    (fun _ ↦ by norm_num [Fin.sum_univ_two]) (by decide) (by decide)
  refine ⟨ξ, hξ0, hξX, ?_⟩
  have hle : |((ξ 0 + ξ 1 : ℤ) : ℚ)| ≤ 2 / 3 := by
    simpa [Fin.sum_univ_two] using hξu 0
  have hlt : |ξ 0 + ξ 1| < 1 := by
    exact_mod_cast hle.trans_lt (by norm_num : (2 / 3 : ℚ) < 1)
  exact Int.abs_lt_one_iff.1 hlt

/-- The strict inequality `ℓ ^ |κ| < (X + 1) ^ |ι|` in `exists_ne_zero_int_vec_abs_le_of_pow_lt`
is sharp: at `|ι| = |κ| = 1`, `u = 1`, `U = 1`, `X = 1`, and `ℓ = 2`, equality
`ℓ ^ |κ| = (X + 1) ^ |ι|` holds, yet no nonzero `ξ : Fin 1 → ℤ` with `|ξ 0| ≤ 1` satisfies
`|∑ i, u i 0 * ξ i| ≤ U * X / ℓ`. -/
theorem not_exists_ne_zero_int_vec_abs_le_of_pow_eq :
    (2 : ℕ) ^ Fintype.card (Fin 1) = (1 + 1) ^ Fintype.card (Fin 1) ∧
      ¬ ∃ ξ : Fin 1 → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ 1) ∧
        ∀ _ : Fin 1, |∑ i : Fin 1, (1 : ℝ) * ξ i| ≤ (1 : ℝ) * (1 : ℕ) / (2 : ℕ) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨ξ, hξ0, -, hξu⟩
  have h0 : ξ 0 ≠ 0 := fun h ↦ hξ0 (funext fun i ↦ Subsingleton.elim i 0 ▸ h)
  have h1 : (1 : ℝ) ≤ |(ξ 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 : |(ξ 0 : ℝ)| ≤ 1 / 2 := by simpa using hξu 0
  linarith

/-- In `exists_ne_zero_int_vec_norm_le_of_pow_le`, the hypothesis `0 < X` cannot be dropped: when
`κ = Empty` and `X = 0`, the counting inequality holds (`1 ≤ 1`), yet every `ξ` with `|ξ i| ≤ 0`
is zero. -/
theorem not_exists_ne_zero_int_vec_of_X_eq_zero (U V : ℝ) :
    (Real.sqrt 2 * (0 : ℕ) * Real.exp (U + V) + 1) ^ (2 * Fintype.card Empty) ≤
        (((0 : ℕ) : ℝ) + 1) ^ Fintype.card (Fin 1) ∧
      ¬ ∃ ξ : Fin 1 → ℤ, ξ ≠ 0 ∧ ∀ i, |ξ i| ≤ (0 : ℤ) := by
  refine ⟨by simp, ?_⟩
  rintro ⟨ξ, hξ0, hξX⟩
  exact hξ0 (funext fun i ↦ abs_nonpos_iff.1 (hξX i))

/-- In `exists_ne_zero_int_vec_norm_le_of_pow_le`, `[Nonempty ι]` cannot be dropped: when
`ι = Empty` and `κ = Empty`, the counting inequality holds (`1 ≤ 1`) for every `X`, yet the only
vector `Empty → ℤ` is zero. -/
theorem not_exists_ne_zero_int_vec_of_isEmpty (U V : ℝ) (X : ℕ) :
    (Real.sqrt 2 * X * Real.exp (U + V) + 1) ^ (2 * Fintype.card Empty) ≤
        ((X : ℝ) + 1) ^ Fintype.card Empty ∧
      ¬ ∃ ξ : Empty → ℤ, ξ ≠ 0 := by
  refine ⟨by simp, ?_⟩
  rintro ⟨ξ, hξ0⟩
  exact hξ0 (Subsingleton.elim ξ 0)

/-- Boundary equality instance of `exists_ne_zero_int_vec_norm_le_of_pow_le`: for two variables,
one complex form with `∑ i, ‖u i 0‖ ≤ 1`, `X = 3`, `U = 0`, and `V = -log √2` so that
`√2 · X · exp (U + V) = 3` is an integer and `(√2 · X · exp (U + V) + 1) ^ 2 = (X + 1) ^ 2 = 16`
holds with equality, a nonzero `ξ : Fin 2 → ℤ` with `|ξ i| ≤ 3` and
`‖u 0 0 * ξ 0 + u 1 0 * ξ 1‖ ≤ √2` still exists. -/
theorem exists_ne_zero_int_vec_norm_le_at_integer_boundary (u : Fin 2 → Fin 1 → ℂ)
    (hu : ‖u 0 0‖ + ‖u 1 0‖ ≤ 1) :
    ∃ ξ : Fin 2 → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ 3) ∧
      ‖u 0 0 * (ξ 0 : ℂ) + u 1 0 * (ξ 1 : ℂ)‖ ≤ Real.sqrt 2 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  obtain ⟨ξ, hξ0, hξX, hξu⟩ := exists_ne_zero_int_vec_norm_le_of_pow_le u
    (U := 0) (V := -Real.log (Real.sqrt 2)) (X := 3)
    (fun j ↦ by simpa [Fin.sum_univ_two, Subsingleton.elim j 0] using hu)
    (by decide)
    (by
      rw [zero_add, Real.exp_neg, Real.exp_log hsqrt]
      have hmul : Real.sqrt 2 * ((3 : ℕ) : ℝ) * (Real.sqrt 2)⁻¹ = 3 := by
        push_cast
        field_simp [hsqrt.ne']
      rw [hmul]
      norm_num)
  refine ⟨ξ, hξ0, hξX, ?_⟩
  simpa [Fin.sum_univ_two, Real.exp_log hsqrt] using hξu 0

end TauCeti.ThueSiegelExample
