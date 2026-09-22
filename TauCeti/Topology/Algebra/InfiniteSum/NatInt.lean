/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Reindexing infinite sums between the integers and natural numbers

This file supplements Mathlib's results on infinite sums over `ℕ` and `ℤ` with a reindexing
lemma for an integer-indexed family whose support is bounded below.

## Main results

* `TauCeti.hasSum_int_iff_natCast_sub`: reindex a family supported in `[-k, ∞)` by `n ↦ n - k`.
-/

public section

namespace TauCeti

/-- A sum over the integers whose terms vanish below `-k` can be reindexed over the natural
numbers by `n ↦ n - k`. -/
theorem hasSum_int_iff_natCast_sub {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {k : ℤ} {f : ℤ → E} (hf : ∀ j < -k, f j = 0) {s : E} :
    HasSum f s ↔ HasSum (fun n : ℕ ↦ f ((n : ℤ) - k)) s := by
  let g : ℕ → ℤ := fun n ↦ (n : ℤ) - k
  have hg : Function.Injective g := by
    intro m n hmn
    simp only [g] at hmn
    omega
  have hoff : ∀ j ∉ Set.range g, f j = 0 := by
    intro j hj
    apply hf j
    by_contra hjlt
    apply hj
    use (j + k).toNat
    simp only [g]
    omega
  simpa only [Function.comp_def, g] using (hg.hasSum_iff hoff).symm

end TauCeti
