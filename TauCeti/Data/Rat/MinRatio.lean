/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.PNat.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order

/-!
# Minimum-ratio bounds for integer pairs

Given a nonempty finite set `S` and integer-valued functions `num` and `den` with `0 < den i` on
`S`, minimizing the rational ratio `num i / den i` yields a coprime fraction `s / r` (`r > 0`) that
attains `s * den i₀ = r * num i₀` at a minimizer `i₀ ∈ S` and satisfies `s * den i ≤ r * num i` on
all of `S` (`Rat.exists_min_div_coprime`).
-/

public section

namespace Rat

/-- A nonempty finite family of rational ratios `num i / den i` with positive integer denominators
`den i` attains a minimum at some `i₀ ∈ S`, written in lowest terms as `s / r` (`s : ℤ`, `r : ℕ+`,
`s.natAbs.Coprime r`), so `s * den i₀ = r * num i₀` and `s * den i ≤ r * num i` for all `i ∈ S`. -/
theorem exists_min_div_coprime {α : Type*} {S : Finset α} (hS : S.Nonempty)
    (num : α → ℤ) (den : α → ℤ) (hden : ∀ i ∈ S, 0 < den i) :
    ∃ i₀ ∈ S, ∃ (s : ℤ) (r : ℕ+), s.natAbs.Coprime r ∧
      s * den i₀ = (r : ℤ) * num i₀ ∧
      ∀ i ∈ S, s * den i ≤ (r : ℤ) * num i := by
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S (fun i ↦ (num i : ℚ) / den i) hS
  set q₀ : ℚ := (num i₀ : ℚ) / den i₀
  set s : ℤ := q₀.num
  set r : ℕ+ := ⟨q₀.den, q₀.den_pos⟩
  have hq : (s : ℚ) / (r : ℕ) = q₀ := Rat.num_div_den q₀
  have hr_pos : (0 : ℚ) < r := by exact_mod_cast r.pos
  refine ⟨i₀, hi₀, s, r, q₀.reduced, ?_, fun i hi ↦ ?_⟩
  · have hi₀_pos : (den i₀ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (hden i₀ hi₀).ne'
    have h := hq
    rw [div_eq_div_iff hr_pos.ne' hi₀_pos] at h
    rw [mul_comm (r : ℤ)]
    exact_mod_cast h
  · have hle := hmin i hi
    have hi_pos : (0 : ℚ) < den i := Int.cast_pos.mpr (hden i hi)
    rw [← hq, div_le_div_iff₀ hr_pos hi_pos] at hle
    rw [mul_comm (r : ℤ)]
    exact_mod_cast hle

end Rat
