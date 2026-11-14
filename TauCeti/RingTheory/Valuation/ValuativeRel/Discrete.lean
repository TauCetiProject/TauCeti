/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Divisibility rigidity in discrete rank-at-most-one value groups

In a discrete valuative relation (`ValuativeRel.IsDiscrete`), every value strictly below `1` lies
at or below `ValuativeRel.uniformizer R < 1`. When the valuative relation also has rank at most one
(`ValuativeRel.IsRankLeOne`), its value group is archimedean, so high powers of `uniformizer R`
eventually drop below any given nonzero value. Consequently no nonzero value other than `1` can be
an `m ^ k`-th power for an integer `m ≥ 2` and every `k : ℕ`.

In local field theory this rules out nontrivial discrete rank-one valuations on groups of units:
raising a unit of `𝒪[K]` to the `(q - 1)`-st power lands in the principal units `U(K, 1)`, where
Hensel's lemma extracts `ℓ ^ k`-th roots for any prime `ℓ` away from the residue characteristic.

## Main results

* `ValuativeRel.ValueGroupWithZero.eq_one_of_forall_exists_pow_pow_eq`: in `ValueGroupWithZero R`
  with `[IsDiscrete R] [IsRankLeOne R]`, a nonzero element that is an `m ^ k`-th power for some
  `m ≥ 2` and all `k : ℕ` equals `1`.
* `ValuativeRel.ValueGroupWithZero.eq_one_of_pow_forall_exists_pow_pow_eq`: the same conclusion
  when a positive power `γ ^ n` is `m ^ k`-divisible.
* `ValuativeRel.valuation_eq_one_of_forall_exists_pow_pow_eq` and
  `ValuativeRel.valuation_eq_one_of_pow_forall_exists_pow_pow_eq`: the corresponding statements for
  ring elements of nonzero valuation.
-/

public section

namespace ValuativeRel

namespace ValueGroupWithZero

variable {R : Type*} [Semiring R] [ValuativeRel R] [IsDiscrete R] [IsRankLeOne R]

/-- A nonzero element of a discrete archimedean value group that admits `m ^ k`-th roots for some
`m ≥ 2` and all `k` cannot lie strictly below `1`: each root would be at most `uniformizer R`,
forcing the element below every `(uniformizer R) ^ (m ^ k)`. -/
private theorem one_le_of_forall_exists_pow_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) (h : ∀ k : ℕ, ∃ δ : ValueGroupWithZero R, δ ^ m ^ k = γ) :
    1 ≤ γ := by
  by_contra! hlt
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := R)) (Units.mk0 γ hγ)
  obtain ⟨δ, hδ⟩ := h n
  have hδ1 : δ < 1 := by
    by_contra! h1
    exact hlt.not_ge ((one_le_pow₀ h1).trans_eq hδ)
  have hpow : δ ^ m ^ n ≤ uniformizer R ^ n :=
    (pow_le_pow_left' (le_uniformizer_iff.mpr hδ1) (m ^ n)).trans
      (pow_le_pow_of_le_one zero_le (uniformizer_lt_one (R := R)).le
        (n.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hm n)))
  exact hn.not_ge (hδ ▸ hpow)

/-- **No nontrivial `m ^ ∞`-divisible values in a discrete rank-at-most-one value group.** If a
nonzero `γ : ValueGroupWithZero R` is an `m ^ k`-th power for some `m ≥ 2` and every `k : ℕ`, then
`γ = 1`. -/
theorem eq_one_of_forall_exists_pow_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (h : ∀ k : ℕ, ∃ δ : ValueGroupWithZero R, δ ^ m ^ k = γ) :
    γ = 1 := by
  have hge := one_le_of_forall_exists_pow_pow_eq hγ hm h
  have hge_inv : 1 ≤ γ⁻¹ :=
    one_le_of_forall_exists_pow_pow_eq (inv_ne_zero hγ) hm fun k ↦ by
      obtain ⟨δ, hδ⟩ := h k
      exact ⟨δ⁻¹, by rw [inv_pow, hδ]⟩
  exact le_antisymm ((one_le_inv₀ (zero_lt_iff.mpr hγ)).mp hge_inv) hge

/-- If a positive power `γ ^ n` of a nonzero `γ : ValueGroupWithZero R` is an `m ^ k`-th power for
some `m ≥ 2` and every `k : ℕ`, then `γ = 1`. -/
theorem eq_one_of_pow_forall_exists_pow_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0) {n m : ℕ}
    (hn : n ≠ 0) (hm : 2 ≤ m)
    (h : ∀ k : ℕ, ∃ δ : ValueGroupWithZero R, δ ^ m ^ k = γ ^ n) :
    γ = 1 :=
  (pow_eq_one_iff_of_nonneg zero_le hn).mp
    (eq_one_of_forall_exists_pow_pow_eq (pow_ne_zero n hγ) hm h)

end ValueGroupWithZero

section Ring

variable {R : Type*} [Ring R] [ValuativeRel R] [IsDiscrete R] [IsRankLeOne R]

/-- If `x : R` has nonzero valuation and is an `m ^ k`-th power in `R` for some `m ≥ 2` and every
`k : ℕ`, then `valuation R x = 1`. -/
theorem valuation_eq_one_of_forall_exists_pow_pow_eq {x : R} (hx : valuation R x ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (h : ∀ k : ℕ, ∃ y : R, y ^ m ^ k = x) :
    valuation R x = 1 :=
  ValueGroupWithZero.eq_one_of_forall_exists_pow_pow_eq hx hm fun k ↦ by
    obtain ⟨y, hy⟩ := h k
    exact ⟨valuation R y, by rw [← map_pow, hy]⟩

/-- If `x : R` has nonzero valuation and a positive power `x ^ n` is an `m ^ k`-th power in `R` for
some `m ≥ 2` and every `k : ℕ`, then `valuation R x = 1`. -/
theorem valuation_eq_one_of_pow_forall_exists_pow_pow_eq {x : R} (hx : valuation R x ≠ 0)
    {n m : ℕ} (hn : n ≠ 0) (hm : 2 ≤ m) (h : ∀ k : ℕ, ∃ y : R, y ^ m ^ k = x ^ n) :
    valuation R x = 1 :=
  ValueGroupWithZero.eq_one_of_pow_forall_exists_pow_pow_eq hx hn hm fun k ↦ by
    obtain ⟨y, hy⟩ := h k
    exact ⟨valuation R y, by rw [← map_pow, hy, map_pow]⟩

end Ring

end ValuativeRel
