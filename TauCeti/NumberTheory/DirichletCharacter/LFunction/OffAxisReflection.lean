/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection

/-!
# Off-axis zero reflection for every Dirichlet character

For any Dirichlet character `χ` modulo `N ≥ 1`, primitive or imprimitive, and any `s ∈ ℂ` off the
imaginary axis `Re s = 0` with `s ≠ 1`, a zero of `χ.LFunction` at `s` is either a trivial zero
(where Mathlib's `χ.gammaFactor s = 0`, i.e., `s + j ∈ {0, -2, -4, …}` for the parity `j` of `χ`)
or reflects across the critical line to a zero `χ⁻¹.LFunction (1 - s) = 0`.

This unifies the open-left-half-plane classification of trivial zeros for imprimitive characters
(`DirichletCharacter.LFunction_eq_zero_iff_of_re_neg`), the open-strip reflection
(`DirichletCharacter.LFunction_one_sub_eq_zero_iff`), and nonvanishing on `Re s ≥ 1`.

## Main results

* `DirichletCharacter.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`: off `Re s = 0` and
  away from `s = 1`, `χ.LFunction s = 0` implies `χ.gammaFactor s = 0 ∨ χ⁻¹.LFunction (1 - s) = 0`.
* `DirichletCharacter.exists_add_parity_eq_neg_two_mul_or_LFunction_one_sub_eq_zero`: the explicit
  parity form with `s + j = -2 * n` (`j = 0` if `χ` is even, `j = 1` if `χ` is odd).
* `DirichletCharacter.LFunction_one_sub_eq_zero_of_re_ne_zero`: if `χ.gammaFactor s ≠ 0`, then
  `s` lies in the open critical strip `0 < Re s < 1` and `χ⁻¹.LFunction (1 - s) = 0`.

## Provenance

Adapted from `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` in
`grh/src/Lib/Analytic/ZeroSymmetry.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Complex

namespace DirichletCharacter

/-- Off the imaginary axis `Re s = 0` and away from `s = 1`, every zero of `χ.LFunction` for an
arbitrary (possibly imprimitive) Dirichlet character `χ` is either a pole of its gamma factor
(represented by `χ.gammaFactor s = 0`) or reflects to a zero of `χ⁻¹.LFunction` at `1 - s`. -/
theorem gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hre : s.re ≠ 0) (hs1 : s ≠ 1) (hz : χ.LFunction s = 0) :
    χ.gammaFactor s = 0 ∨ χ⁻¹.LFunction (1 - s) = 0 := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · exact .inl ((χ.LFunction_eq_zero_iff_of_re_neg hneg).mp hz)
  · rcases lt_or_ge s.re 1 with hlt | hge
    · exact .inr ((χ⁻¹.LFunction_one_sub_eq_zero_iff hpos hlt).mpr (by simpa using hz))
    · exact absurd hz (χ.LFunction_ne_zero_of_one_le_re (.inr hs1) hge)

/-- Explicit parity form of off-axis zero reflection: for `Re s ≠ 0` and `s ≠ 1`, a zero of
`χ.LFunction` at `s` satisfies either `s + j = -2 * n` for some `n : ℕ` (where `j = 0` if `χ` is
even and `j = 1` if `χ` is odd) or `χ⁻¹.LFunction (1 - s) = 0`. -/
theorem exists_add_parity_eq_neg_two_mul_or_LFunction_one_sub_eq_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [Decidable χ.Even] {s : ℂ} (hre : s.re ≠ 0) (hs1 : s ≠ 1)
    (hz : χ.LFunction s = 0) :
    (∃ n : ℕ, s + (if χ.Even then (0 : ℂ) else 1) = -2 * (n : ℂ)) ∨
      χ⁻¹.LFunction (1 - s) = 0 := by
  refine (χ.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero hre hs1 hz).imp_left fun hγ ↦ ?_
  rcases χ.even_or_odd with he | ho
  · obtain ⟨n, hn⟩ := (χ.gammaFactor_eq_zero_iff_of_even he).mp hγ
    exact ⟨n, by simp only [he, ↓reduceIte, add_zero]; rw [hn]; ring⟩
  · have hne : ¬ χ.Even := fun he ↦ by
      have h1 : χ (-1) = 1 := he
      have h2 : χ (-1) = -1 := ho
      norm_num [h1] at h2
    obtain ⟨n, hn⟩ := (χ.gammaFactor_eq_zero_iff_of_odd ho).mp hγ
    exact ⟨n, by simp only [hne, ↓reduceIte]; rw [hn]; ring⟩

/-- A non-trivial zero of `χ.LFunction` off the imaginary axis `Re s = 0` (with `s ≠ 1` and
`χ.gammaFactor s ≠ 0`) lies in the open critical strip `0 < Re s < 1` and reflects to a zero of
`χ⁻¹.LFunction` at `1 - s`. -/
theorem LFunction_one_sub_eq_zero_of_re_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hre : s.re ≠ 0) (hs1 : s ≠ 1) (hz : χ.LFunction s = 0) (hγ : χ.gammaFactor s ≠ 0) :
    0 < s.re ∧ s.re < 1 ∧ χ⁻¹.LFunction (1 - s) = 0 := by
  have hpos : 0 < s.re := lt_of_not_ge fun hle ↦
    hγ ((χ.LFunction_eq_zero_iff_of_re_neg (lt_of_le_of_ne hle hre)).mp hz)
  have hlt : s.re < 1 := lt_of_not_ge fun hge ↦
    χ.LFunction_ne_zero_of_one_le_re (.inr hs1) hge hz
  exact ⟨hpos, hlt, (χ⁻¹.LFunction_one_sub_eq_zero_iff hpos hlt).mpr (by simpa using hz)⟩

end DirichletCharacter
