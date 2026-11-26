/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.House
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Span

/-!
# Few integral vectors have bounded conjugates

Let `K` be a number field with `f′` infinite places and `ι` a finite set. A set of vectors in
`(𝓞 K) ^ ι` all of whose entries have absolute value at most `r` at every infinite place of `K` has
at most `(1 + 2r) ^ (2 · #ι · f′)` elements.

The proof is a pigeonhole argument. Put `m = ⌊2r⌋₊ + 1`. Two such vectors that are congruent
modulo `m` are equal: an entry of their difference is `m y` with `y ∈ 𝓞 K`, it has absolute value at
most `2r < m` at every place, while a nonzero `y` has a conjugate of absolute value at least `1`
(`NumberField.exists_conjugate_one_le_norm`). So the set injects into `(𝓞 K / m) ^ ι`, which has
`m ^ (#ι · [K : ℚ])` elements (`NumberField.RingOfIntegers.natCard_quotient_span_natCast`), and
`[K : ℚ] ≤ 2 f′`.

## Main results

* `NumberField.RingOfIntegers.finite_of_forall_infinitePlace_le`: such a set is finite.
* `NumberField.RingOfIntegers.ncard_le_floor_add_one_pow`: such a set has at most
  `(⌊2r⌋₊ + 1) ^ (#ι · [K : ℚ])` elements.
* `NumberField.RingOfIntegers.ncard_le_one_add_two_mul_pow`: such a set has at most
  `(1 + 2r) ^ (2 · #ι · f′)` elements.

## References

* The statement is the count of integral vectors with bounded conjugates used in the folder `grh`
  of https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New/Spanning/RemainingTerms/Box.lean`, `New.Filling.encard_le_of_isIntegral_norm_le`).
-/

public section

open Module
open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

variable {ι : Type*} {S : Set (ι → 𝓞 K)} {r : ℝ}

/-- Two vectors over `𝓞 K` whose entries have absolute value at most `r` at every infinite place
and which are congruent modulo `⌊2r⌋₊ + 1` are equal. -/
private theorem eq_of_forall_sub_mem_span {v v' : ι → 𝓞 K}
    (hv : ∀ i (w : InfinitePlace K), w (v i) ≤ r) (hv' : ∀ i (w : InfinitePlace K), w (v' i) ≤ r)
    (h : ∀ i, v i - v' i ∈ Ideal.span {((⌊2 * r⌋₊ + 1 : ℕ) : 𝓞 K)}) : v = v' := by
  funext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (h i)
  by_contra hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hne (sub_eq_zero.mp (by rw [← hy, zero_mul]))
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hy0
  have hsub : ‖σ (v i : K)‖ + ‖σ (v' i : K)‖ ≤ 2 * r := by
    linarith [hv i (.mk σ), hv' i (.mk σ), InfinitePlace.apply σ (v i : K),
      InfinitePlace.apply σ (v' i : K)]
  have hm : ((⌊2 * r⌋₊ + 1 : ℕ) : ℝ) ≤ ‖σ (v i : K) - σ (v' i : K)‖ := by
    have hyK : (v i : K) - v' i = y * ((⌊2 * r⌋₊ + 1 : ℕ) : K) := by
      simpa using congrArg (algebraMap (𝓞 K) K) hy.symm
    rw [← map_sub, hyK, map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hσ
  push_cast at hm
  linarith [Nat.lt_floor_add_one (2 * r), norm_sub_le (σ (v i : K)) (σ (v' i : K))]

/-- Reduction modulo `⌊2r⌋₊ + 1` is injective on vectors over `𝓞 K` whose entries have absolute
value at most `r` at every infinite place. -/
private theorem injOn_quotient (hS : ∀ v ∈ S, ∀ i (w : InfinitePlace K), w (v i) ≤ r) :
    S.InjOn fun v i ↦ Ideal.Quotient.mk (Ideal.span {((⌊2 * r⌋₊ + 1 : ℕ) : 𝓞 K)}) (v i) :=
  fun _ hv _ hv' h ↦ eq_of_forall_sub_mem_span (hS _ hv) (hS _ hv') fun i ↦
    Ideal.Quotient.eq.mp (congr_fun h i)

variable [Finite ι]

/-- A set of vectors over `𝓞 K` whose entries have absolute value at most `r` at every infinite
place of `K` is finite. -/
theorem finite_of_forall_infinitePlace_le
    (hS : ∀ v ∈ S, ∀ i (w : InfinitePlace K), w (v i) ≤ r) : S.Finite :=
  Set.Finite.of_injOn (fun _ _ ↦ Set.mem_univ _) (injOn_quotient hS) Set.finite_univ

/-- A set of vectors in `(𝓞 K) ^ ι` whose entries have absolute value at most `r` at every
infinite place of `K` has at most `(⌊2r⌋₊ + 1) ^ (#ι · [K : ℚ])` elements. -/
theorem ncard_le_floor_add_one_pow (hS : ∀ v ∈ S, ∀ i (w : InfinitePlace K), w (v i) ≤ r) :
    S.ncard ≤ (⌊2 * r⌋₊ + 1) ^ (Nat.card ι * finrank ℚ K) := by
  calc S.ncard ≤ (Set.univ : Set (ι → 𝓞 K ⧸ Ideal.span {((⌊2 * r⌋₊ + 1 : ℕ) : 𝓞 K)})).ncard :=
        Set.ncard_le_ncard_of_injOn _ (fun _ _ ↦ Set.mem_univ _) (injOn_quotient hS)
    _ = (⌊2 * r⌋₊ + 1) ^ (Nat.card ι * finrank ℚ K) := by
        rw [Set.ncard_univ, Nat.card_fun, natCard_quotient_span_natCast, ← pow_mul']

/-- **Few integral vectors have bounded conjugates.** If `K` has `f′` infinite places, a set of
vectors in `(𝓞 K) ^ ι` whose entries have absolute value at most `r` at every infinite place of `K`
has at most `(1 + 2r) ^ (2 · #ι · f′)` elements. -/
theorem ncard_le_one_add_two_mul_pow (hS : ∀ v ∈ S, ∀ i (w : InfinitePlace K), w (v i) ≤ r) :
    (S.ncard : ℝ) ≤ (1 + 2 * r) ^ (2 * Nat.card ι * Fintype.card (InfinitePlace K)) := by
  rcases lt_or_ge r 0 with hr | hr
  · rcases isEmpty_or_nonempty ι with hι | hι
    · have := ncard_le_floor_add_one_pow hS
      simp only [Nat.card_of_isEmpty, mul_zero, zero_mul, pow_zero] at this ⊢
      exact_mod_cast this
    · -- for `r < 0` no vector satisfies the bound, since absolute values are nonnegative
      have hS0 : S = ∅ := Set.eq_empty_of_forall_notMem fun v hv ↦
        (hr.trans_le (apply_nonneg (Classical.arbitrary (InfinitePlace K)) _)).not_ge
          (hS v hv hι.some _)
      rw [hS0, Set.ncard_empty, Nat.cast_zero]
      exact ((even_two_mul _).mul_right _).pow_nonneg _
  have hdeg : Nat.card ι * finrank ℚ K ≤ 2 * Nat.card ι * Fintype.card (InfinitePlace K) := by
    rw [mul_comm 2, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    have := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    omega
  calc (S.ncard : ℝ) ≤ ((⌊2 * r⌋₊ + 1 : ℕ) : ℝ) ^ (Nat.card ι * finrank ℚ K) := by
        exact_mod_cast ncard_le_floor_add_one_pow hS
    _ ≤ (1 + 2 * r) ^ (Nat.card ι * finrank ℚ K) := by
        gcongr
        push_cast
        linarith [Nat.floor_le (by positivity : 0 ≤ 2 * r)]
    _ ≤ (1 + 2 * r) ^ (2 * Nat.card ι * Fintype.card (InfinitePlace K)) :=
        pow_le_pow_right₀ (by linarith) hdeg

end NumberField.RingOfIntegers
