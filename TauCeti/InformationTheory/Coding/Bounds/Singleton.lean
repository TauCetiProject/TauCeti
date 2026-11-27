/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import TauCeti.InformationTheory.Coding.Puncture.Basic

/-!
# The Singleton bound

A code `C` of length `n` with minimum distance `d` over an alphabet of `q` letters has at most
`q ^ (n - d + 1)` words, and a linear code of dimension `k` over a field has `k + d ≤ n + 1`.
Both follow from one observation: if fewer than `d` coordinates lie outside a set `s` of
coordinates, then two distinct words of `C` differ somewhere in `s`, so restriction to `s` is
injective on `C`.

## Main results

* `Set.injOn_restrict_of_card_compl_lt`: restriction to `s` (`Finset.restrict`) is injective on
  `C` when `#sᶜ < d(C)`.
* `Set.exists_finset_card_eq_card_compl_lt`: for a code with at least two words, some `s` with
  `n - d + 1` coordinates has `#sᶜ < d(C)`.
* `Set.natCard_le_prod_of_card_compl_lt`: then `|C| ≤ ∏_{i ∈ s} |β i|`, for alphabets `β i` that
  may depend on the coordinate.
* `Set.natCard_le_pow_of_nontrivial`: **the Singleton bound** `|C| ≤ q ^ (n - d + 1)` for a code
  with at least two words.
* `TauCeti.finrank_add_hammingMinDist_le`: **the Singleton bound for linear codes**,
  `k + d ≤ n + 1`, over any field.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, Theorem 4.3.1.
* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Theorem 2.4.1.
-/

public section

open Finset

namespace Set

variable {ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)] {C : Set (∀ i, β i)}

/-- If fewer than `d(C)` coordinates lie outside `s`, then two distinct words of `C` differ
somewhere in `s`: restriction to `s` is injective on `C`. -/
theorem injOn_restrict_of_card_compl_lt [DecidableEq ι] (s : Finset ι)
    (hs : #sᶜ < C.hammingMinDist) : C.InjOn s.restrict := by
  intro x hx y hy hxy
  by_contra hne
  have hle : hammingDist x y ≤ #sᶜ := by
    rw [hammingDist]
    refine Finset.card_le_card fun i hi ↦ Finset.mem_compl.2 fun his ↦ (Finset.mem_filter.1 hi).2 ?_
    simpa using congr_fun hxy ⟨i, his⟩
  exact absurd hs (not_lt.2 ((hammingMinDist_le hx hy hne).trans hle))

/-- If fewer than `d(C)` coordinates lie outside `s`, then `|C| ≤ ∏_{i ∈ s} |β i|`. -/
theorem natCard_le_prod_of_card_compl_lt [DecidableEq ι] [∀ i, Fintype (β i)] (s : Finset ι)
    (hs : #sᶜ < C.hammingMinDist) : Nat.card C ≤ ∏ i ∈ s, Fintype.card (β i) :=
  calc Nat.card C ≤ Nat.card (∀ i : s, β i) := Nat.card_le_card_of_injective _
        (injOn_iff_injective.1 (injOn_restrict_of_card_compl_lt s hs))
    _ = ∏ i ∈ s, Fintype.card (β i) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_pi, prod_coe_sort s fun i ↦ Fintype.card (β i)]

/-- If `C` has at least two words, some set `s` of `n - d(C) + 1` coordinates leaves fewer than
`d(C)` coordinates outside. -/
theorem exists_finset_card_eq_card_compl_lt [DecidableEq ι] (hC : C.Nontrivial) :
    ∃ s : Finset ι, #s = Fintype.card ι - C.hammingMinDist + 1 ∧ #sᶜ < C.hammingMinDist := by
  have hd := hammingMinDist_pos_iff.2 hC
  have hdn : C.hammingMinDist ≤ Fintype.card ι := hammingMinDist_le_card
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := Fintype.card ι - C.hammingMinDist + 1) (by rw [Finset.card_univ]; omega)
  exact ⟨s, hs, by rw [Finset.card_compl, hs]; omega⟩

/-- **The Singleton bound.** A code `C` of length `n` with at least two words and minimum
distance `d` over an alphabet of `q` letters has `|C| ≤ q ^ (n - d + 1)`. -/
theorem natCard_le_pow_of_nontrivial {α : Type*} [Fintype α] [DecidableEq α] {C : Set (ι → α)}
    (hC : C.Nontrivial) :
    Nat.card C ≤ Fintype.card α ^ (Fintype.card ι - C.hammingMinDist + 1) := by
  classical
  obtain ⟨s, hs, hsc⟩ := exists_finset_card_eq_card_compl_lt hC
  simpa [hs] using natCard_le_prod_of_card_compl_lt s hsc

end Set

namespace TauCeti

open Set

/-- **The Singleton bound for linear codes.** A linear code of length `n`, dimension `k` and
minimum distance `d` over a field has `k + d ≤ n + 1`. The zero code has `k = d = 0`. -/
theorem finrank_add_hammingMinDist_le {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    (C : LinearCode F ι) :
    Module.finrank F C + (C : Set (ι → F)).hammingMinDist ≤ Fintype.card ι + 1 := by
  classical
  rcases eq_or_ne C ⊥ with rfl | hC
  · simp [Submodule.bot_coe, hammingMinDist_singleton]
  -- Keep `n - d + 1` coordinates; a codeword vanishing on them has weight below `d`.
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
  have hdn : (C : Set (ι → F)).hammingMinDist ≤ Fintype.card ι := hammingMinDist_le_card
  obtain ⟨s, hs, hsc⟩ := exists_finset_card_eq_card_compl_lt (C := (C : Set (ι → F)))
    ⟨x, hx, 0, C.zero_mem, hx0⟩
  have hinj := injOn_restrict_of_card_compl_lt s hsc
  have hk := finrank_puncture_eq C (s : Set ι) fun y hy hy0 ↦
    hinj hy C.zero_mem (funext fun i ↦ by simpa using hy0 ⟨i, i.property⟩)
  have hle : Module.finrank F (puncture C (s : Set ι)) ≤ #s :=
    (Submodule.finrank_le _).trans (by simp)
  omega

end TauCeti
