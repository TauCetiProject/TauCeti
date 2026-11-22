/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Divisibility rigidity in discrete archimedean value groups

In a discrete valuative relation (`ValuativeRel.IsDiscrete`), every value strictly below `1` lies
at or below `ValuativeRel.uniformizer R < 1`. When the value group is also archimedean
(`MulArchimedean (ValueGroupWithZero R)`, in particular when `ValuativeRel.IsRankLeOne R` holds),
high powers of `uniformizer R` eventually drop below any given nonzero value. Consequently no
nonzero value other than `1` can be a `k`-th power for arbitrarily large `k : ℕ`.

In valuation theory this rules out nontrivial discrete archimedean valuations on elements admitting
roots of arbitrarily large degree: over a Henselian valued field `K`, every element `1 + m` with
`m ∈ 𝓂[K]` admits `k`-th roots for all `k` invertible in `𝒪[K]`, in particular for arbitrarily
large primes `k`.

## Main results

* `ValuativeRel.ValueGroupWithZero.eq_one_of_forall_exists_le_pow_eq`: in `ValueGroupWithZero R`
  with `[IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, a nonzero element that is a
  `k`-th power for arbitrarily large `k : ℕ` equals `1`.
* `ValuativeRel.valuation_eq_one_of_forall_exists_le_pow_eq`: the corresponding statement for ring
  elements of nonzero valuation.
-/

public section

namespace ValuativeRel

namespace ValueGroupWithZero

variable {R : Type*} [Semiring R] [ValuativeRel R] [IsDiscrete R]
  [MulArchimedean (ValueGroupWithZero R)]

/-- A nonzero element of a discrete archimedean value group that admits `k`-th roots for
arbitrarily large `k : ℕ` is at least `1`. -/
private theorem one_le_of_forall_exists_le_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ δ : ValueGroupWithZero R, δ ^ k = γ) :
    1 ≤ γ := by
  by_contra! hlt
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := R)) (Units.mk0 γ hγ)
  obtain ⟨k, hkn, δ, hδ⟩ := h n
  have hδ1 : δ < 1 := by
    by_contra! h1
    exact hlt.not_ge ((one_le_pow₀ h1).trans_eq hδ)
  have hpow : δ ^ k ≤ uniformizer R ^ n :=
    (pow_le_pow_left' (le_uniformizer_iff.mpr hδ1) k).trans
      (pow_le_pow_of_le_one zero_le (uniformizer_lt_one (R := R)).le hkn)
  exact hn.not_ge (hδ ▸ hpow)

/-- **No nontrivial arbitrarily divisible values in a discrete archimedean value group.** In a
semiring `R` with `[IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, if a nonzero
`γ : ValueGroupWithZero R` is a `k`-th power for arbitrarily large `k : ℕ`, then `γ = 1`. -/
theorem eq_one_of_forall_exists_le_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ δ : ValueGroupWithZero R, δ ^ k = γ) :
    γ = 1 := by
  have hge := one_le_of_forall_exists_le_pow_eq hγ h
  have hge_inv : 1 ≤ γ⁻¹ :=
    one_le_of_forall_exists_le_pow_eq (inv_ne_zero hγ) fun n ↦ by
      obtain ⟨k, hkn, δ, hδ⟩ := h n
      exact ⟨k, hkn, δ⁻¹, by rw [inv_pow, hδ]⟩
  exact le_antisymm ((one_le_inv₀ (pos_iff_ne_zero.mpr hγ)).mp hge_inv) hge

end ValueGroupWithZero

section Ring

variable {R : Type*} [Ring R] [ValuativeRel R] [IsDiscrete R]
  [MulArchimedean (ValueGroupWithZero R)]

/-- In a ring `R` with `[IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, if `x : R` has
nonzero valuation and is a `k`-th power in `R` for arbitrarily large `k : ℕ`, then
`valuation R x = 1`. -/
theorem valuation_eq_one_of_forall_exists_le_pow_eq {x : R} (hx : valuation R x ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ y : R, y ^ k = x) :
    valuation R x = 1 :=
  ValueGroupWithZero.eq_one_of_forall_exists_le_pow_eq hx fun n ↦ by
    obtain ⟨k, hkn, y, hy⟩ := h n
    exact ⟨k, hkn, valuation R y, by rw [← map_pow, hy]⟩

end Ring

end ValuativeRel
