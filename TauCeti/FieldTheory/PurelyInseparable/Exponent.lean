/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# The exponent of a finite purely inseparable extension is bounded by its degree

Let `L / K` be a finite purely inseparable extension in exponential characteristic `p`. If
`[L : K] ≤ p ^ n`, then every `p ^ n`-th power of `L` lies in `K`, and so the exponent of `L / K`
is at most `n`. In particular a purely inseparable extension of degree `p ^ n` is cut out by
`p ^ n`-th powers.

Mathlib's `IsPurelyInseparable.hasExponent_of_finiteDimensional` shows that a finite purely
inseparable extension *has* an exponent, but keeps the bound inside the instance proof. This file
states the bound, in the pointwise form a caller holding a degree uses and as a bound on
`IsPurelyInseparable.exponent`.

## Main results

* `TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, every `p ^ n`-th
  power of `L` lies in `K`.
* `TauCeti.IsPurelyInseparable.exponent_le_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, the exponent
  of `L / K` is at most `n`.
-/

public section

namespace TauCeti.IsPurelyInseparable

open _root_.IsPurelyInseparable

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
  [FiniteDimensional K L] (p : ℕ) [ExpChar K p]

/-- **A purely inseparable extension of degree at most `p ^ n` is cut out by `p ^ n`-th powers**:
every `a ^ p ^ n` lies in the base field. -/
theorem pow_mem_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) (a : L) :
    a ^ p ^ n ∈ (algebraMap K L).range := by
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · -- in characteristic zero a purely inseparable extension is trivial
    obtain ⟨k, hk⟩ := IsPurelyInseparable.pow_mem K 1 a
    simpa using hk
  · -- the minimal polynomial of `a` is `X ^ p ^ e - c` with `e` its exponent, of degree at most
    -- `[L : K] ≤ p ^ n`, so `e ≤ n`
    have he : elemExponent K a ≤ n := by
      have h1 := minpoly.natDegree_le (A := K) a
      rw [minpoly_natDegree_eq' K p a] at h1
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h)
    obtain ⟨b, hb⟩ := elemExponent_def' K p a
    exact ⟨b ^ p ^ (n - elemExponent K a), by
      rw [map_pow, hb, ← pow_mul, ← pow_add, Nat.add_sub_cancel' he]⟩

/-- **The exponent of a purely inseparable extension of degree at most `p ^ n` is at most `n`.** -/
theorem exponent_le_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) :
    exponent K L ≤ n := by
  by_contra hn
  obtain ⟨a, ha⟩ := exponent_min' p (not_le.1 hn)
  exact ha (pow_mem_of_finrank_le_pow K L p h a)

end TauCeti.IsPurelyInseparable

end
