/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic

/-!
# Braid words

A braid word on `n` strands is a finite list of letters `σ i ^ ε`, an elementary braid together
with a sign `ε = ±1`. Unlike an element of `TauCeti.BraidGroup n`, a word remembers its
individual crossings, which is what the closure of a braid into a link diagram consumes. This file
defines the words and the braid each word represents.

## Main definitions

* `TauCeti.BraidWord`: the braid words on `n` strands.
* `TauCeti.BraidWord.toBraid`: the braid represented by a word, the product of its letters.
* `TauCeti.BraidWord.strandIncl`: the same word on one strand more, the new strand uncrossed.
* `TauCeti.BraidWord.stabilize`: the Markov stabilization of a word, which adds a strand and
  crosses it once with the previous last strand.

## Main results

* `TauCeti.BraidWord.toBraid_surjective`: every braid is represented by a word.
* `TauCeti.BraidWord.exponentSum_toBraid`: the exponent sum of the represented braid is the sum
  of the signs of the letters.
* `TauCeti.BraidWord.toBraid_strandIncl` and `TauCeti.BraidWord.toBraid_stabilize`: these word
  operations represent `TauCeti.BraidGroup.strandIncl` and the stabilization of
  `TauCeti.IsMarkovMove`.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 1.
-/

public section

namespace TauCeti

open BraidGroup

/-- A braid word on `n` strands. The letter `(i, ε)` stands for the elementary braid
`σ i ^ ε`, the crossing of strands `i` and `i + 1` with sign `ε = ±1`; the letters are read
from the bottom of the braid to its top. -/
abbrev BraidWord (n : ℕ) : Type := List (Fin (n - 1) × ℤˣ)

namespace BraidWord

variable {n : ℕ}

/-- The braid represented by a word: the product of the signed elementary braids it lists. -/
def toBraid (w : BraidWord n) : BraidGroup n :=
  (w.map fun x ↦ sigma x.1 ^ (x.2 : ℤ)).prod

/-- The empty word represents the trivial braid. -/
@[simp]
theorem toBraid_nil : toBraid ([] : BraidWord n) = 1 := (rfl)

/-- Prepending a letter multiplies the represented braid on the left by that letter. -/
@[simp]
theorem toBraid_cons (x : Fin (n - 1) × ℤˣ) (w : BraidWord n) :
    toBraid (x :: w) = sigma x.1 ^ (x.2 : ℤ) * toBraid w := by
  simp [toBraid]

/-- Concatenating words multiplies the represented braids. -/
@[simp]
theorem toBraid_append (w w' : BraidWord n) : toBraid (w ++ w') = toBraid w * toBraid w' := by
  simp [toBraid]

/-- Reversing a word and negating all its signs represents the inverse braid. -/
theorem toBraid_reverse_map_neg (w : BraidWord n) :
    toBraid (w.reverse.map fun x ↦ (x.1, -x.2)) = (toBraid w)⁻¹ := by
  simp only [toBraid, List.prod_inv_reverse, List.map_reverse, List.map_map, Function.comp_def,
    Units.val_neg, zpow_neg]

/-- Every braid is represented by a braid word. -/
theorem toBraid_surjective : Function.Surjective (toBraid (n := n)) := by
  intro b
  induction b using sigma_induction_on with
  | sigma i => exact ⟨[(i, 1)], by simp⟩
  | one => exact ⟨[], toBraid_nil⟩
  | mul b b' hb hb' =>
    obtain ⟨w, rfl⟩ := hb
    obtain ⟨w', rfl⟩ := hb'
    exact ⟨w ++ w', toBraid_append w w'⟩
  | inv b hb =>
    obtain ⟨w, rfl⟩ := hb
    exact ⟨_, toBraid_reverse_map_neg w⟩

/-- The exponent sum of the braid represented by a word is the sum of the signs of its
letters. -/
@[simp]
theorem exponentSum_toBraid (w : BraidWord n) :
    ArtinGroup.exponentSum _ (toBraid w) = Multiplicative.ofAdd (w.map fun x ↦ (x.2 : ℤ)).sum := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [toBraid_cons, map_mul, map_zpow, exponentSum_sigma, ih, List.map_cons,
      List.sum_cons, ofAdd_add, ← ofAdd_zsmul, smul_eq_mul, mul_one]

/-! ### Adding a strand -/

/-- The same braid word on one strand more: every letter keeps its index, so the new top strand
is never crossed. It represents `TauCeti.BraidGroup.strandIncl` of the braid of the word. -/
def strandIncl (w : BraidWord (n + 1)) : BraidWord (n + 2) :=
  w.map fun x ↦ ((x.1.castSucc : Fin (n + 1)), x.2)

/-- The defining equation of `TauCeti.BraidWord.strandIncl`: each letter keeps its index. -/
theorem strandIncl_def (w : BraidWord (n + 1)) :
    w.strandIncl = w.map fun x ↦ ((x.1.castSucc : Fin (n + 1)), x.2) :=
  (rfl)

-- The list type is written `Fin (n + 1) × ℤˣ` rather than `BraidWord (n + 2)`: `simp` rewrites the
-- `n + 2 - 1` hidden in the latter, after which a left-hand side stated with it no longer matches.
/-- Adding a strand keeps the number of letters. -/
@[simp]
theorem length_strandIncl (w : BraidWord (n + 1)) :
    List.length (α := Fin (n + 1) × ℤˣ) w.strandIncl = w.length :=
  List.length_map _

/-- Adding a strand to a word adds an uncrossed strand to the braid it represents. -/
@[simp]
theorem toBraid_strandIncl (w : BraidWord (n + 1)) :
    w.strandIncl.toBraid = BraidGroup.strandIncl w.toBraid := by
  induction w with
  | nil => rw [strandIncl_def, List.map_nil, toBraid_nil, toBraid_nil, map_one]
  | cons x w ih =>
    rw [strandIncl_def, List.map_cons, toBraid_cons, ← strandIncl_def, ih, toBraid_cons, map_mul,
      map_zpow, strandIncl_sigma]

/-- The **Markov stabilization** of a braid word with sign `ε`: add a strand and cross it once
with the previous last strand, by the letter `σ (Fin.last n) ^ ε` placed at the top. -/
def stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) : BraidWord (n + 2) :=
  w.strandIncl ++ ([(Fin.last n, ε)] : BraidWord (n + 2))

/-- The defining equation of `TauCeti.BraidWord.stabilize`: the new letter is placed at the top. -/
theorem stabilize_def (w : BraidWord (n + 1)) (ε : ℤˣ) :
    w.stabilize ε = w.strandIncl ++ ([(Fin.last n, ε)] : BraidWord (n + 2)) :=
  (rfl)

-- The list type is written `Fin (n + 1) × ℤˣ` for the reason given at `length_strandIncl`.
/-- Stabilization adds one letter. -/
@[simp]
theorem length_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    List.length (α := Fin (n + 1) × ℤˣ) (w.stabilize ε) = w.length + 1 := by
  rw [stabilize_def, List.length_append, length_strandIncl, List.length_singleton]

/-- A stabilized word represents the braid `strandIncl b * σ (Fin.last n) ^ ε`, the stabilization
of the braid `b` of the word, as in `TauCeti.IsMarkovMove.stabilize` and
`TauCeti.IsMarkovMove.stabilizeInv`. -/
@[simp]
theorem toBraid_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    (w.stabilize ε).toBraid = BraidGroup.strandIncl w.toBraid * sigma (Fin.last n) ^ (ε : ℤ) := by
  rw [stabilize_def, toBraid_append, toBraid_strandIncl, toBraid_cons, toBraid_nil, mul_one]

end BraidWord

end TauCeti
