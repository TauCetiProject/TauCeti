/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.PiNat.WordCylinder

/-!
# Coordinate flips in Cantor space

The coordinate flip `PiNat.flipAt n` negates the `n`-th coordinate of a point of Cantor space
`ℕ → Bool`. It is an involutive homeomorphism, and it maps the word cylinder `PiNat.wordCylinder w`
onto the cylinder of the word obtained by negating the `n`-th letter of `w`
(`PiNat.image_flipAt_wordCylinder`). In particular it exchanges the two halves
`wordCylinder (s ++ [false])` and `wordCylinder (s ++ [true])` of `wordCylinder s` when `s` has
length `n`: this is the symmetry used in Miller's proof that the graphs `G_S` have no countable
Baire-measurable coloring, and in the proof that eventual equality `E₀` is generically ergodic.

For the alphabet-generic word-cylinder API (`PiNat.prependWord`, `PiNat.wordCylinder`), see
`TauCeti.Topology.MetricSpace.PiNat.WordCylinder`.

## Main definitions

* `PiNat.flipAt n`: the homeomorphism of `ℕ → Bool` negating the `n`-th coordinate.

## Main results

* `PiNat.image_flipAt_wordCylinder`: `flipAt n` maps `wordCylinder w` onto the cylinder of `w`
  with its `n`-th letter negated.
* `PiNat.image_flipAt_wordCylinder_append_singleton`: `flipAt s.length` exchanges
  `wordCylinder (s ++ [false])` and `wordCylinder (s ++ [true])`.

## References

* B. D. Miller, "The graph-theoretic approach to descriptive set theory", *Bulletin of Symbolic
  Logic* 18 (2012), 554–575, for the graphs `G_S` and the coordinate flip.
-/

public section

open Set Function

namespace PiNat

/-! ### The coordinate flip of Cantor space -/

/-- The homeomorphism of Cantor space `ℕ → Bool` negating the `n`-th coordinate. -/
def flipAt (n : ℕ) : (ℕ → Bool) ≃ₜ (ℕ → Bool) where
  toFun x := update x n (!x n)
  invFun x := update x n (!x n)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_id.update n (continuous_of_discreteTopology.comp
    (continuous_apply n))
  continuous_invFun := continuous_id.update n (continuous_of_discreteTopology.comp
    (continuous_apply n))

theorem flipAt_apply (n : ℕ) (x : ℕ → Bool) : flipAt n x = update x n (!x n) := (rfl)

@[simp]
theorem flipAt_apply_self (n : ℕ) (x : ℕ → Bool) : flipAt n x n = !x n := by
  simp [flipAt_apply]

@[simp]
theorem flipAt_apply_of_ne {m n : ℕ} (h : m ≠ n) (x : ℕ → Bool) : flipAt n x m = x m := by
  simp [flipAt_apply, h]

@[simp]
theorem symm_flipAt (n : ℕ) : (flipAt n).symm = flipAt n := (rfl)

@[simp]
theorem flipAt_flipAt (n : ℕ) (x : ℕ → Bool) : flipAt n (flipAt n x) = x :=
  (flipAt n).symm_apply_apply x

/-- The coordinate flip is an involution. -/
theorem flipAt_involutive (n : ℕ) : Involutive (flipAt n) :=
  flipAt_flipAt n

/-- The coordinate flip at `n` pulls the cylinder of `w` back to the cylinder of `w` with its
`n`-th letter negated; when `w.length ≤ n` the cylinder is unchanged. -/
theorem preimage_flipAt_wordCylinder (n : ℕ) (w : List Bool) :
    flipAt n ⁻¹' wordCylinder w = wordCylinder (w.modify n not) := by
  ext y
  simp only [mem_preimage, mem_wordCylinder_iff, List.length_modify, List.getElem_modify]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rcases eq_or_ne n i with rfl | h
  · simp [Bool.not_eq_eq_eq_not]
  · simp [h, Ne.symm h]

/-- The coordinate flip at `n` maps the cylinder of `w` onto the cylinder of `w` with its `n`-th
letter negated; when `w.length ≤ n` the cylinder is unchanged. -/
theorem image_flipAt_wordCylinder (n : ℕ) (w : List Bool) :
    flipAt n '' wordCylinder w = wordCylinder (w.modify n not) := by
  rw [Homeomorph.image_eq_preimage_symm, symm_flipAt, preimage_flipAt_wordCylinder]

/-- The coordinate flip at `s.length` exchanges `prependWord (s ++ [b]) x` and
`prependWord (s ++ [!b]) x`. -/
theorem flipAt_prependWord_append_singleton (s : List Bool) (b : Bool) (x : ℕ → Bool) :
    flipAt s.length (prependWord (s ++ [b]) x) = prependWord (s ++ [!b]) x := by
  ext m
  rcases eq_or_ne m s.length with rfl | h
  · simp [prependWord_apply_of_lt]
  · rw [flipAt_apply_of_ne h, prependWord_append, prependWord_append]
    rcases lt_or_ge m s.length with hm | hm
    · simp [prependWord_apply_of_lt hm]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_add_one.2 (by omega)
      simp [prependWord_apply_of_le]

/-- The coordinate flip at `s.length` maps the cylinder of `s ++ [b]` onto the cylinder of
`s ++ [!b]`, exchanging the two halves of the cylinder of `s`. -/
theorem image_flipAt_wordCylinder_append_singleton (s : List Bool) (b : Bool) :
    flipAt s.length '' wordCylinder (s ++ [b]) = wordCylinder (s ++ [!b]) := by
  rw [← range_prependWord, ← range_prependWord, ← range_comp]
  exact congrArg range (funext (flipAt_prependWord_append_singleton s b))

end PiNat
