/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic

/-!
# The Singleton bound

A code `C` of length `n` with at least two words and minimum distance `d` over an alphabet of
`q` letters has at most `q ^ (n - d + 1)` words. A linear code of rank `k` over a semiring with
the strong rank condition, for instance a field, has `k + d ≤ n + 1`. Both follow from one
observation: if fewer than `d` coordinates lie outside a set `s` of coordinates, then two distinct
words of `C` differ somewhere in `s`, so restriction to `s` is injective on `C`.

## Main results

* `Set.injOn_restrict_of_card_compl_lt_hammingMinDist`: restriction to `s` (`Finset.restrict`)
  is injective on `C` when `#sᶜ < d(C)`.
* `Set.exists_finset_card_eq_card_compl_lt_hammingMinDist`: for a code with at least two words,
  some `s` with `n - d + 1` coordinates has `#sᶜ < d(C)`.
* `Set.natCard_le_prod_of_card_compl_lt_hammingMinDist`: then `|C| ≤ ∏_{i ∈ s} |β i|`, for
  alphabets `β i` that may depend on the coordinate.
* `Set.natCard_le_pow_card_sub_hammingMinDist_add_one`: **the Singleton bound**
  `|C| ≤ q ^ (n - d + 1)` for a code with at least two words.
* `TauCeti.finrank_add_hammingMinDist_le`: **the Singleton bound for linear codes**,
  `k + d ≤ n + 1`, over any semiring with the strong rank condition, in particular over any
  field.

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
theorem injOn_restrict_of_card_compl_lt_hammingMinDist [DecidableEq ι] (s : Finset ι)
    (hs : #sᶜ < C.hammingMinDist) : C.InjOn s.restrict := by
  intro x hx y hy hxy
  by_contra hne
  have hle : hammingDist x y ≤ #sᶜ := by
    rw [hammingDist]
    refine Finset.card_le_card fun i hi ↦ Finset.mem_compl.2 fun his ↦ (Finset.mem_filter.1 hi).2 ?_
    simpa using congr_fun hxy ⟨i, his⟩
  exact absurd hs (not_lt.2 ((hammingMinDist_le hx hy hne).trans hle))

/-- If fewer than `d(C)` coordinates lie outside `s`, then `|C| ≤ ∏_{i ∈ s} |β i|`. -/
theorem natCard_le_prod_of_card_compl_lt_hammingMinDist [DecidableEq ι] [∀ i, Fintype (β i)]
    (s : Finset ι) (hs : #sᶜ < C.hammingMinDist) : Nat.card C ≤ ∏ i ∈ s, Fintype.card (β i) :=
  calc Nat.card C ≤ Nat.card (∀ i : s, β i) := Nat.card_le_card_of_injective _
        (injOn_iff_injective.1 (injOn_restrict_of_card_compl_lt_hammingMinDist s hs))
    _ = ∏ i ∈ s, Fintype.card (β i) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_pi, prod_coe_sort s fun i ↦ Fintype.card (β i)]

/-- If `C` has at least two words, some set `s` of `n - d(C) + 1` coordinates leaves fewer than
`d(C)` coordinates outside. -/
theorem exists_finset_card_eq_card_compl_lt_hammingMinDist [DecidableEq ι] (hC : C.Nontrivial) :
    ∃ s : Finset ι, #s = Fintype.card ι - C.hammingMinDist + 1 ∧ #sᶜ < C.hammingMinDist := by
  have hd := hammingMinDist_pos_iff.2 hC
  have hdn : C.hammingMinDist ≤ Fintype.card ι := hammingMinDist_le_card
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := Fintype.card ι - C.hammingMinDist + 1) (by rw [Finset.card_univ]; omega)
  exact ⟨s, hs, by rw [Finset.card_compl, hs]; omega⟩

/-- **The Singleton bound.** A code `C` of length `n` with at least two words and minimum
distance `d` over an alphabet of `q` letters has `|C| ≤ q ^ (n - d + 1)`. -/
theorem natCard_le_pow_card_sub_hammingMinDist_add_one {α : Type*} [Fintype α] [DecidableEq α]
    {C : Set (ι → α)} (hC : C.Nontrivial) :
    Nat.card C ≤ Fintype.card α ^ (Fintype.card ι - C.hammingMinDist + 1) := by
  classical
  obtain ⟨s, hs, hsc⟩ := exists_finset_card_eq_card_compl_lt_hammingMinDist hC
  simpa [hs] using natCard_le_prod_of_card_compl_lt_hammingMinDist s hsc

end Set

namespace TauCeti

open Set

/-- **The Singleton bound for linear codes.** A linear code of length `n`, rank `k` and minimum
distance `d` has `k + d ≤ n + 1`. The scalars form a semiring with the strong rank condition, for
instance a field, and `k` is `Module.finrank R C`. The zero code has `k = d = 0`. -/
theorem finrank_add_hammingMinDist_le {R ι : Type*} [Semiring R] [StrongRankCondition R]
    [Fintype ι] [DecidableEq R] (C : LinearCode R ι) :
    Module.finrank R C + (C : Set (ι → R)).hammingMinDist ≤ Fintype.card ι + 1 := by
  classical
  rcases (C : Set (ι → R)).subsingleton_or_nontrivial with hC | hC
  · -- The zero code has `d = 0`, and `k ≤ n` holds for each code.
    have hk : Module.finrank R C ≤ Fintype.card ι := by simpa using Submodule.finrank_le C
    rw [hammingMinDist_eq_zero_of_subsingleton hC]
    omega
  -- Restriction to `n - d + 1` retained coordinates is an injective linear map on `C`.
  have hdn : (C : Set (ι → R)).hammingMinDist ≤ Fintype.card ι := hammingMinDist_le_card
  obtain ⟨s, hs, hsc⟩ := exists_finset_card_eq_card_compl_lt_hammingMinDist hC
  have hinj := injOn_restrict_of_card_compl_lt_hammingMinDist s hsc
  have hk : Module.finrank R C ≤ #s :=
    (LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.funLeft R R ((↑) : s → ι)).domRestrict C) fun x y hxy ↦
        Subtype.ext (hinj x.property y.property
          (funext fun i ↦ by simpa using congrFun hxy i))).trans_eq (by simp)
  omega

end TauCeti
