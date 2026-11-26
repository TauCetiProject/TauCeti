/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A point of an interval far from a finite set

For a finite set `S` of reals and `a ≤ b`, some `x ∈ [a, b]` is at distance at least
`(b - a) / (2 (#S + 1))` from every point of `S`
(`TauCeti.exists_mem_Icc_forall_le_abs_sub`). Among the `#S + 1` points
`a + (2k + 1) δ`, `k = 0, …, #S`, with `δ = (b - a) / (2 (#S + 1))`, each point of `S` is within
less than `δ` of at most one, so one of them is within less than `δ` of none.
-/

public section

open Set

namespace TauCeti

/-- **Pigeonhole for a finite set of reals.** For a finite set `S` of reals and `a ≤ b`, some
`x ∈ [a, b]` satisfies `(b - a) / (2 (#S + 1)) ≤ |x - γ|` for every `γ ∈ S`. -/
theorem exists_mem_Icc_forall_le_abs_sub (S : Finset ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Icc a b, ∀ γ ∈ S, (b - a) / (2 * (S.card + 1)) ≤ |x - γ| := by
  set δ := (b - a) / (2 * (S.card + 1)) with hδdef
  have hbδ : b - a = 2 * (S.card + 1) * δ := by rw [hδdef]; field_simp
  by_contra! h
  obtain ⟨γ₀, -, hγ₀⟩ := h a ⟨le_rfl, hab⟩
  have hδ : 0 < δ := (abs_nonneg _).trans_lt hγ₀
  -- the points `a + (2k + 1) δ` for `k ≤ #S` lie in `[a, b]`
  have hm (k : ℕ) (hk : k ∈ Finset.range (S.card + 1)) : a + (2 * k + 1) * δ ∈ Icc a b := by
    have hk' : (k : ℝ) ≤ S.card := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    constructor <;> nlinarith
  choose! g hgS hg using fun k hk ↦ h _ (hm k hk)
  -- two of these points are `2δ` apart, so no `γ` is within `δ` of both
  have hinj : InjOn g (Finset.range (S.card + 1)) := fun k hk j hj hkj ↦ by
    have h1 := abs_lt.1 (hg k hk)
    have h2 := abs_lt.1 (hg j hj)
    rw [hkj] at h1
    have hlt : (k : ℝ) < j + 1 := by nlinarith
    have hgt : (j : ℝ) < k + 1 := by nlinarith
    exact_mod_cast le_antisymm (Nat.lt_succ_iff.1 (by exact_mod_cast hlt))
      (Nat.lt_succ_iff.1 (by exact_mod_cast hgt))
  have := Finset.card_le_card_of_injOn g hgS hinj
  rw [Finset.card_range] at this
  omega

end TauCeti
