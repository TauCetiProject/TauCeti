/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Reindexing infinite sums between the integers and natural numbers

This file supplements Mathlib's results on infinite sums over `ℕ` and `ℤ` with a reindexing
lemma for an integer-indexed family whose support is bounded below, and with the splitting of a
summable integer-indexed family into its residue classes modulo `M`.

## Main results

* `TauCeti.hasSum_int_iff_natCast_sub`: reindex a family supported in `[-k, ∞)` by `n ↦ n - k`.
* `TauCeti.hasSum_mul_zpow_natCast_sub_iff`: move an integer-power shift between the summands and
  their sum.
* `TauCeti.tsum_int_eq_sum_fin_tsum`: a summable family on `ℤ` sums to the sum over the residues
  `r < M` of its sums over the classes `qM + r`.
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

/-- Multiplication by `q ^ k` converts a sum with powers `q ^ (n - k)` into one with powers
`q ^ n`. -/
theorem hasSum_mul_zpow_natCast_sub_iff {K : Type*} [Semifield K] [TopologicalSpace K]
    [IsTopologicalSemiring K] {a : ℕ → K} {q s : K}
    (hq : q ≠ 0) (k : ℤ) :
    HasSum (fun n : ℕ ↦ a n * q ^ ((n : ℤ) - k)) s ↔
      HasSum (fun n : ℕ ↦ a n * q ^ n) (q ^ k * s) := by
  have hpow (n : ℕ) : q ^ k * (a n * q ^ ((n : ℤ) - k)) = a n * q ^ n := by
    rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ hq, add_sub_cancel]
  exact (hasSum_mul_left_iff (zpow_ne_zero k hq)).symm.trans (by simp only [hpow])

/-- **A sum over the integers splits into its residue classes modulo `M`**: for a summable family,
`∑ n, f n = ∑_{r < M} ∑ q, f (q * M + r)`. -/
theorem tsum_int_eq_sum_fin_tsum {E : Type*} [AddCommGroup E] [UniformSpace E]
    [IsUniformAddGroup E] [CompleteSpace E] [T0Space E] {f : ℤ → E} (hf : Summable f) (M : ℕ)
    [NeZero M] :
    ∑' n, f n = ∑ r : Fin M, ∑' q : ℤ, f (q * M + r) := by
  have hs : Summable (f ∘ (Int.divModEquiv M).symm) := (Equiv.summable_iff _).2 hf
  have h := hs.tsum_prod' fun _ ↦ .of_finite
  simp only [Function.comp_apply, tsum_fintype, Int.divModEquiv_symm_apply] at h
  rw [← (Int.divModEquiv M).symm.tsum_eq f]
  simp only [Int.divModEquiv_symm_apply]
  rw [h]
  refine Summable.tsum_finsetSum fun r _ ↦ hf.comp_injective fun a b h ↦ ?_
  simpa [NeZero.ne M] using h

end TauCeti
