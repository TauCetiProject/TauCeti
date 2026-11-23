/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.Algebra.Order.GroupWithZero.Pow

/-!
# Divisibility rigidity in discrete archimedean value groups

In a discrete valuative relation (`ValuativeRel.IsDiscrete`), every value strictly below `1` lies
at or below `ValuativeRel.uniformizer R < 1`. When the value group is also archimedean
(`MulArchimedean (ValueGroupWithZero R)`, in particular when `ValuativeRel.IsRankLeOne R` holds),
high powers of `uniformizer R` eventually drop below any given nonzero value. Consequently, by
`TauCeti.eq_one_of_forall_exists_le_pow_eq`, no nonzero value other than `1` can be a `k`-th power
for arbitrarily large `k : ℕ`.

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

/-- **No nontrivial arbitrarily divisible values in a discrete archimedean value group.** In a
semiring `R` with `[IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, if a nonzero
`γ : ValueGroupWithZero R` is a `k`-th power for arbitrarily large `k : ℕ`, then `γ = 1`. -/
theorem eq_one_of_forall_exists_le_pow_eq {γ : ValueGroupWithZero R} (hγ : γ ≠ 0)
    (h : ∀ n : ℕ, ∃ k ≥ n, ∃ δ : ValueGroupWithZero R, δ ^ k = γ) :
    γ = 1 :=
  TauCeti.eq_one_of_forall_exists_le_pow_eq
    ⟨uniformizer R, uniformizer_lt_one, fun _ ↦ le_uniformizer_iff.mpr⟩ hγ h

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
