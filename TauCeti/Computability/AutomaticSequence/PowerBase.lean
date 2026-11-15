/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.Kernel
import Mathlib.Data.Set.Finite.Range
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma

/-!
# Automaticity in a power of the base

For `k ≥ 2` and `m > 0`, a sequence is `k ^ m`-automatic if and only if it is
`k`-automatic. This allows automaticity over a finite field to be expressed either in
its characteristic or in its cardinality.

The comparison is made at the level of kernels. The `k ^ m`-kernel is contained in
the `k`-kernel. In the other direction, every element of the `k`-kernel is obtained
from an element of the `k ^ m`-kernel by taking a subsequence with exponent less
than `m`. There are only finitely many such subsequence operations.

## References

* Andrew Bridy, *Automatic sequences and curves over finite fields*,
  Algebra & Number Theory 11 (2017), Section 2.3, before Proposition 2.16.
-/

public section

namespace TauCeti

variable {k m : ℕ} {Δ : Type*} {a b : ℕ → Δ}

/-- The kernel in a power of the base is contained in the original kernel. -/
theorem kernel_pow_subset (k m : ℕ) (a : ℕ → Δ) : kernel (k ^ m) a ⊆ kernel k a := by
  intro b hb
  obtain ⟨e, r, hr, rfl⟩ := mem_kernel.1 hb
  exact mem_kernel.2 ⟨m * e, r, by simpa [pow_mul] using hr, by simp [pow_mul]⟩

/-- Every element of the `k`-kernel is a subsequence of an element of the
`k ^ m`-kernel, with the remaining exponent strictly less than `m`. -/
theorem mem_kernel_iff_exists_mem_kernel_pow [NeZero k] (hm : 0 < m) :
    b ∈ kernel k a ↔ ∃ c ∈ kernel (k ^ m) a, ∃ j < m, ∃ r < k ^ j,
      b = fun n ↦ c (k ^ j * n + r) := by
  constructor
  · intro hb
    obtain ⟨e, r, hr, rfl⟩ := mem_kernel.1 hb
    let d := (k ^ m) ^ (e / m)
    have hd : 0 < d := pow_pos (pow_pos (NeZero.pos k) _) _
    have he : k ^ e = d * k ^ (e % m) := by
      dsimp only [d]
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hrdiv : r / d < k ^ (e % m) := by
      apply (Nat.div_lt_iff_lt_mul hd).2
      simpa [he, mul_comm] using hr
    refine ⟨(fun n ↦ a (d * n + r % d)),
      mem_kernel.2 ⟨e / m, r % d, Nat.mod_lt _ hd, rfl⟩,
      e % m, Nat.mod_lt _ hm, r / d, hrdiv, ?_⟩
    funext n
    apply congrArg a
    calc
      k ^ e * n + r = d * k ^ (e % m) * n + (r % d + d * (r / d)) := by
        rw [he, Nat.mod_add_div]
      _ = d * (k ^ (e % m) * n + r / d) + r % d := by ring
  · rintro ⟨c, hc, j, _, r, hr, rfl⟩
    exact kernel_subset (kernel_pow_subset k m a hc) (mem_kernel.2 ⟨j, r, hr, rfl⟩)

/-- Finiteness of the kernel is unchanged by replacing a nonzero base with a
positive power of itself. This comparison also holds in base one. -/
theorem finite_kernel_pow_iff [NeZero k] (hm : 0 < m) :
    (kernel (k ^ m) a).Finite ↔ (kernel k a).Finite := by
  constructor
  · intro h
    classical
    have := h.to_subtype
    let F : (kernel (k ^ m) a) × (Σ j : Fin m, Fin (k ^ j.val)) → ℕ → Δ :=
      fun p n ↦ p.1.val (k ^ p.2.1.val * n + p.2.2.val)
    refine (Set.finite_range F).subset ?_
    intro b hb
    obtain ⟨c, hc, j, hj, r, hr, rfl⟩ :=
      (mem_kernel_iff_exists_mem_kernel_pow hm).1 hb
    exact ⟨(⟨c, hc⟩, ⟨⟨j, hj⟩, ⟨r, hr⟩⟩), rfl⟩
  · intro h
    exact h.subset (kernel_pow_subset k m a)

/-- A sequence is automatic in a positive power of a base `k ≥ 2` if and only if
it is automatic in base `k`. The output alphabet is arbitrary. -/
theorem isAutomatic_pow_iff [NeZero k] (hk : 2 ≤ k) (hm : 0 < m) :
    IsAutomatic (k ^ m) a ↔ IsAutomatic k a := by
  have hkm : 2 ≤ k ^ m := hk.trans (Nat.le_self_pow (by omega) k)
  rw [isAutomatic_iff_finite_kernel hkm, isAutomatic_iff_finite_kernel hk,
    finite_kernel_pow_iff hm]

end TauCeti
