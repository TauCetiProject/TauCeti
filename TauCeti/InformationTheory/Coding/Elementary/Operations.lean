/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.InformationTheory.Coding.Puncture

/-!
# Coordinate operations on repetition codes

Puncturing a repetition code gives the repetition code on the retained coordinates. Shortening it
at any proper retained set gives the zero code, since a constant word vanishing at one deleted
coordinate vanishes everywhere.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §§1.4–1.5.
-/

public section

namespace TauCeti

variable {R ι : Type*} [Field R]

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

end TauCeti
