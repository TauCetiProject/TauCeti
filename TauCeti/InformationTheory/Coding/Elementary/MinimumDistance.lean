/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import TauCeti.InformationTheory.Coding.Puncture

/-!
# Minimum distance of repetition codes

Two distinct constant words differ in every coordinate, so over a nontrivial alphabet the
repetition code of length `n` has minimum distance `n`. Puncturing a repetition code is again a
repetition code, on the retained coordinates. Shortening it at any proper retained set
collapses it to the zero code: a constant word vanishing at one deleted coordinate is zero.

These computations test the hypotheses of the general minimum-distance bounds for coordinate
operations. The repetition code attains the deleted-coordinate bound for puncturing
(`TauCeti.hammingMinDist_le_hammingMinDist_puncture_add_card_compl`) with equality, and it shows
that the nonvanishing hypothesis in the shortening bound
(`TauCeti.hammingMinDist_le_hammingMinDist_shorten`) cannot be dropped. Already the binary
repetition code `{00, 11}` has minimum distance two, while retaining only its first coordinate
leaves the zero code, of minimum distance zero.

## Main declarations

* `TauCeti.hammingMinDist_repetitionCode`: the repetition code has minimum distance equal to its
  length.
* `TauCeti.puncture_repetitionCode` and `TauCeti.shorten_repetitionCode_eq_bot_iff`: puncturing
  and shortening a repetition code.
* `TauCeti.hammingMinDist_puncture_repetitionCode_add_card_compl`: sharpness of the puncturing
  bound.
* `TauCeti.hammingMinDist_shorten_repetitionCode_lt`: shortening can decrease minimum distance
  once the shortened code collapses.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.4–1.5.
-/

public section

namespace TauCeti

variable {R ι : Type*}

/-- Over a nontrivial alphabet, the repetition code has minimum distance equal to its length.
At length zero both sides vanish. -/
@[simp]
theorem hammingMinDist_repetitionCode [Semiring R] [Nontrivial R] [DecidableEq R] [Fintype ι] :
    Set.hammingMinDist (repetitionCode R ι : Set (ι → R)) = Fintype.card ι := by
  refine le_antisymm Set.hammingMinDist_le_card ?_
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Fintype.card_eq_zero]
  | inr hι =>
    obtain ⟨a, b, hab⟩ := exists_pair_ne R
    have hC : (repetitionCode R ι : Set (ι → R)).Nontrivial :=
      ⟨Function.const ι a, (mem_repetitionCode R ι).2 ⟨a, rfl⟩,
        Function.const ι b, (mem_repetitionCode R ι).2 ⟨b, rfl⟩,
        (Function.const_injective (α := ι)).ne hab⟩
    refine (Set.le_hammingMinDist_iff hC).2 ?_
    intro x hx y hy hxy
    obtain ⟨c, rfl⟩ := (mem_repetitionCode R ι).1 hx
    obtain ⟨d, rfl⟩ := (mem_repetitionCode R ι).1 hy
    have hcd : c ≠ d := fun h ↦ hxy (h ▸ rfl)
    simp [hammingDist, hcd]

variable [Field R]

/-- Puncturing a repetition code gives the repetition code on the retained coordinates. -/
@[simp]
theorem puncture_repetitionCode (s : Set ι) :
    puncture (repetitionCode R ι) s = repetitionCode R s := by
  ext y
  rw [mem_puncture, mem_repetitionCode]
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨a, rfl⟩ := (mem_repetitionCode R ι).1 hx
    exact ⟨a, funext hxy⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Function.const ι a, (mem_repetitionCode R ι).2 ⟨a, rfl⟩, fun _ ↦ rfl⟩

/-- Shortening a repetition code at a proper retained set gives the zero code. -/
theorem shorten_repetitionCode_eq_bot {s : Set ι} (hs : s ≠ Set.univ) :
    shorten (repetitionCode R ι) s = ⊥ := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem s).1 hs
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ ?_
  obtain ⟨x, hx, hzero, hxy⟩ := mem_shorten.1 hy
  obtain ⟨a, rfl⟩ := (mem_repetitionCode R ι).1 hx
  have ha : a = 0 := hzero i hi
  funext j
  simp [← hxy j, ha]

/-- A positive-length repetition code collapses under shortening exactly when some coordinate is
deleted. -/
@[simp]
theorem shorten_repetitionCode_eq_bot_iff [Nonempty ι] {s : Set ι} :
    shorten (repetitionCode R ι) s = ⊥ ↔ s ≠ Set.univ := by
  refine ⟨?_, shorten_repetitionCode_eq_bot⟩
  intro h hs
  subst hs
  have hone : (fun _ ↦ 1 : ↥(Set.univ : Set ι) → R) ∈ shorten (repetitionCode R ι) Set.univ :=
    mem_shorten.2 ⟨Function.const ι 1, (mem_repetitionCode R ι).2 ⟨1, rfl⟩,
      fun i hi ↦ absurd (Set.mem_univ i) hi, fun _ ↦ rfl⟩
  rw [h, Submodule.mem_bot] at hone
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact one_ne_zero (congrFun hone ⟨i, Set.mem_univ i⟩)

variable [DecidableEq R] [Fintype ι]

/-- The repetition code attains the deleted-coordinate bound for puncturing with equality:
each deleted coordinate lowers its minimum distance by exactly one. -/
theorem hammingMinDist_puncture_repetitionCode_add_card_compl (s : Set ι)
    [DecidablePred (· ∈ s)] :
    Set.hammingMinDist (puncture (repetitionCode R ι) s : Set (s → R)) + Fintype.card ↥sᶜ =
      Set.hammingMinDist (repetitionCode R ι : Set (ι → R)) := by
  rw [puncture_repetitionCode, hammingMinDist_repetitionCode, hammingMinDist_repetitionCode,
    Fintype.card_compl_set]
  have := set_fintype_card_le_univ s
  omega

/-- Shortening a positive-length repetition code at a proper retained set strictly decreases its
minimum distance, since the shortened code is zero. Hence the bound
`TauCeti.hammingMinDist_le_hammingMinDist_shorten` needs its hypothesis that the shortened code is
nonzero. -/
theorem hammingMinDist_shorten_repetitionCode_lt [Nonempty ι] {s : Set ι}
    [DecidablePred (· ∈ s)] (hs : s ≠ Set.univ) :
    Set.hammingMinDist (shorten (repetitionCode R ι) s : Set (s → R)) <
      Set.hammingMinDist (repetitionCode R ι : Set (ι → R)) := by
  rw [shorten_repetitionCode_eq_bot hs, Submodule.bot_coe, Set.hammingMinDist_singleton,
    hammingMinDist_repetitionCode]
  exact Fintype.card_pos

end TauCeti
