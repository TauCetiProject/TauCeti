/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A pigeonhole on scales

Let `B` be a scale factor with `2 B ≥ 1`. A point `a` *forbids* the scales `y` with
`a / 2 ≤ y < B a`, a window of ratio `2 B`. A finite set `T` of at most `R` points cannot forbid
every scale of the range `[U / (2 ^ (R + 2) B ^ R), U / 2]`, whose ratio is `2 (2 B) ^ R`: for
`U ≥ 0` some `y` in that range has `2 y < a` or `B a ≤ y` for every `a ∈ T`
(`Finset.exists_mem_Icc_forall_two_mul_lt_or_mul_le`).

The proof is an induction on `T` adding a largest point `a`. If `B a ≤ U / 2`, the larger of
`B a` and the lower end of the range is a scale lying above `B b` for every `b ≤ a`. Otherwise
`a` is larger than `U / (2 B)`, and the induction hypothesis applied with `U / (2 B)` in place of
`U` gives a scale below `a / 2`. No logarithms are used, so the statement holds in any linearly
ordered semifield.

With `U = log X` and `T` a set of logarithms, this chooses a window of scales
`x ∈ [Y, Y ^ 2]` that avoids finitely many exceptional values.

## Main results

* `Finset.exists_mem_Icc_forall_two_mul_lt_or_mul_le`: the pigeonhole on scales.

## References

* The statement follows, for `B > 1`, `UpperTheory.V.Win.window1`
  (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Window1.lean`)
  of L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet L-functions,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005>.
-/

public section

open Set

namespace Finset

variable {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {B : 𝕜}

/-- The pigeonhole on scales with `R = #T`, for every `U ≥ 0` at once. -/
private theorem exists_mem_Icc_card (T : Finset 𝕜) (hB : 1 ≤ 2 * B) :
    ∀ U : 𝕜, 0 ≤ U → ∃ y ∈ Icc (U / (2 ^ (#T + 2) * B ^ #T)) (U / 2),
      ∀ a ∈ T, 2 * y < a ∨ B * a ≤ y := by
  have hB0 : 0 < B := pos_of_mul_pos_right (one_pos.trans_le hB) zero_le_two
  induction T using Finset.induction_on_max with
  | empty =>
    refine fun U hU ↦ ⟨U / 2, ⟨?_, le_rfl⟩, by simp⟩
    simpa using div_le_div_of_nonneg_left hU two_pos (by norm_num : (2 : 𝕜) ≤ 2 ^ 2)
  | insert a s has ih =>
    intro U hU
    rw [card_insert_of_notMem fun h ↦ (has a h).false]
    by_cases haU : B * a ≤ U / 2
    · -- the larger of `B a` and the lower end lies above `B b` for every `b ≤ a`
      have hden : 2 ≤ 2 ^ (#s + 1 + 2) * B ^ (#s + 1) := by
        have h1 : (1 : 𝕜) ≤ (2 * B) ^ (#s + 1) := one_le_pow₀ hB
        calc (2 : 𝕜) ≤ 4 * (2 * B) ^ (#s + 1) :=
            (by norm_num : (2 : 𝕜) ≤ 4).trans (le_mul_of_one_le_right (by norm_num) h1)
          _ = 2 ^ (#s + 1 + 2) * B ^ (#s + 1) := by ring
      refine ⟨max (B * a) (U / (2 ^ (#s + 1 + 2) * B ^ (#s + 1))),
        ⟨le_max_right _ _, max_le haU (div_le_div_of_nonneg_left hU two_pos hden)⟩, ?_⟩
      intro b hb
      have hba : b ≤ a := (mem_insert.1 hb).elim le_of_eq fun h ↦ (has b h).le
      exact Or.inr ((mul_le_mul_of_nonneg_left hba hB0.le).trans (le_max_left _ _))
    · -- `a > U / (2 B)`, so a scale of the range for `U / (2 B)` lies below `a / 2`
      obtain ⟨y, ⟨hy₁, hy₂⟩, hy⟩ := ih (U / (2 * B)) (by positivity)
      have hU2 : U / (2 * B) < a := by
        rw [div_lt_iff₀ (by positivity)]
        exact ((div_lt_iff₀' two_pos).1 (not_le.1 haU)).trans_eq (by ring)
      refine ⟨y, ⟨?_, ?_⟩, ?_⟩
      · calc U / (2 ^ (#s + 1 + 2) * B ^ (#s + 1))
              = U / (2 * B) / (2 ^ (#s + 2) * B ^ #s) := by rw [div_div]; ring
          _ ≤ y := hy₁
      · calc y ≤ U / (2 * B) / 2 := hy₂
          _ ≤ U / 2 := by gcongr; exact div_le_self hU hB
      · intro b hb
        rcases mem_insert.1 hb with rfl | hb
        · exact Or.inl (((le_div_iff₀' two_pos).1 hy₂).trans_lt hU2)
        · exact hy b hb

/-- **A pigeonhole on scales.** Let `2 B ≥ 1`, `U ≥ 0` and let `T` be a finite set of at most `R`
elements of a linearly ordered semifield. Then some `y ∈ [U / (2 ^ (R + 2) B ^ R), U / 2]` has
`2 y < a` or `B a ≤ y` for every `a ∈ T`, that is, no point of `T` lies in `(y / B, 2 y]`. -/
theorem exists_mem_Icc_forall_two_mul_lt_or_mul_le (T : Finset 𝕜) (hB : 1 ≤ 2 * B) {U : 𝕜}
    (hU : 0 ≤ U) {R : ℕ} (hT : #T ≤ R) :
    ∃ y ∈ Icc (U / (2 ^ (R + 2) * B ^ R)) (U / 2), ∀ a ∈ T, 2 * y < a ∨ B * a ≤ y := by
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy⟩ := exists_mem_Icc_card T hB U hU
  refine ⟨y, ⟨le_trans ?_ hy₁, hy₂⟩, hy⟩
  -- the lower end decreases in `R`, as `2 ^ (n + 2) B ^ n = 4 (2 B) ^ n` and `2 B ≥ 1`
  have hpow (n : ℕ) : (2 : 𝕜) ^ (n + 2) * B ^ n = 4 * (2 * B) ^ n := by ring
  rw [hpow, hpow]
  gcongr

end Finset
