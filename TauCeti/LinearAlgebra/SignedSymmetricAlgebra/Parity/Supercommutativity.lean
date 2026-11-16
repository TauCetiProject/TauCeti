/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Grading
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.CharP.Invertible
import TauCeti.RingTheory.GradedAlgebra.Supercommutativity

/-!
# Supercommutativity of the parity-presented signed symmetric algebra

Homogeneous elements of `TauCeti.ParitySignedSym G`, not just its generators, satisfy the parity
Koszul commutation rule `a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)` for `a` of parity `i` and `b`
of parity `j`. Even homogeneous elements commute with the entire algebra, hence lie in its center,
while every odd homogeneous element squares to its own negative, so its square vanishes when `2` is
invertible in the coefficient ring.

The results parallel `TauCeti.SignedSym.mul_eq_negOnePow_smul_mul` in
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity`, sharing the general
graded-algebra supercommutativity theorem `TauCeti.mul_eq_smul_mul_of_adjoin_range_eq_top`
without requiring an integer lift of `G`.

## Main results

* `TauCeti.ParitySignedSym.mul_eq_uzpow_smul_mul`: parity-homogeneous elements supercommute.
* `TauCeti.ParitySignedSym.commute_of_mem_zero_left`,
  `TauCeti.ParitySignedSym.commute_of_mem_zero_right`, and
  `TauCeti.ParitySignedSym.mem_center_of_mem_zero`: even homogeneous elements are central.
* `TauCeti.ParitySignedSym.sq_eq_neg` and `TauCeti.ParitySignedSym.sq_eq_zero`: odd homogeneous
  elements square to their negatives, and to zero when `2` is invertible.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*, Section 1.9.
-/

public section

namespace TauCeti.ParitySignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V (ZMod 2))

/-- Parity-homogeneous elements supercommute with the sign `(-1) ^ (i * j)` determined by their
parities, over any commutative ring. -/
theorem mul_eq_uzpow_smul_mul {i j : ZMod 2} {a b : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) :=
  mul_eq_smul_mul_of_adjoin_range_eq_top (𝒜 := paritySignedSymPiece G)
    (s := fun i j => (-1 : ℤˣ) ^ (i * j))
    (fun _ => by simp)
    (fun _ _ _ => by rw [mul_add, uzpow_add])
    (fun _ => by simp)
    (fun i₁ _ j => by rw [add_mul, add_comm (i₁ * j), uzpow_add])
    (adjoin_range_generator G) G.isInternal.submodule_iSup_eq_top
    (isHomogeneous_paritySignedSymGenerator G)
    (fun hx hy => generator_mul_generator G hx hy) ha hb

/-- An even homogeneous element commutes with every element of `ParitySignedSym G`. -/
theorem commute_of_mem_zero_left {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 0)
    (b : ParitySignedSym G) : Commute a b :=
  TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero (mul_eq_uzpow_smul_mul G) ha b

/-- Every element of `ParitySignedSym G` commutes with an even homogeneous element. -/
theorem commute_of_mem_zero_right {b : ParitySignedSym G} (hb : b ∈ paritySignedSymPiece G 0)
    (a : ParitySignedSym G) : Commute a b :=
  (commute_of_mem_zero_left G hb a).symm

/-- Every even homogeneous element lies in the center of `ParitySignedSym G`. -/
theorem mem_center_of_mem_zero {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 0) :
    a ∈ Subalgebra.center R (ParitySignedSym G) :=
  Subalgebra.mem_center_iff.2 fun b => (commute_of_mem_zero_left G ha b).symm

/-- An odd homogeneous element squares to its own negative, over any commutative ring. -/
theorem sq_eq_neg {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 1) :
    a ^ 2 = -(a ^ 2) := by
  rw [pow_two]
  exact TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one (mul_eq_uzpow_smul_mul G) ha

/-- Every odd homogeneous element has square zero when `2` is invertible, in particular over `ℚ`. -/
theorem sq_eq_zero [Invertible (2 : R)] {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg G ha)

end TauCeti.ParitySignedSym
