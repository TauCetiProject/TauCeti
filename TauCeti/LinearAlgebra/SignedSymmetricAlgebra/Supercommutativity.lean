/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.Coarsen
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.RingTheory.GradedAlgebra.Supercommutativity.Basic
import TauCeti.RingTheory.GradedAlgebra.Supercommutativity.Generators

/-!
# Supercommutativity of the signed symmetric algebra

Homogeneous elements of `TauCeti.SignedSym G`, not just its generators, obey the Koszul
commutation rule `a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a)`. In particular, over any Koszul-signed
degree semiring `ι`, every homogeneous element whose degree has Koszul sign `1` (including degree
`0`) lies in the center of `SignedSym G` over any commutative ring, and every homogeneous element
whose degree has sign `-1` (including degree `1`) has square zero when `2` is invertible in the
coefficient ring. For integer-graded modules, passing to `TauCeti.parityGrading` extends these
identities to elements of pure parity across multiple integer degrees: even-parity elements lie in
the center of `SignedSym G` over any commutative ring, and every element of odd parity has square
zero when `2` is invertible in the coefficient ring. These identities allow the signed symmetric
algebra to serve as a receiving supercommutative algebra in universal properties and tensor
comparisons, for both integer and parity (`ZMod 2`) gradings.

The proof instantiates `TauCeti.mul_eq_smul_mul_of_adjoin_range_eq_top_of_isHomogeneous` from
`TauCeti.RingTheory.GradedAlgebra.Supercommutativity.Generators`.
The construction follows the supercommutative algebra of J. Pardon,
*Contact homology and virtual fundamental cycles*, equation (1.1).
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

section General

variable {ι : Type*} [DecidableEq ι] [CommSemiring ι] [Module ι (Additive ℤˣ)]
variable (G : InternalGrading R V ι)

/-- Homogeneous elements supercommute with the sign determined by their total input degrees.
No assumption on the characteristic of the coefficient ring is needed. -/
theorem mul_eq_uzpow_smul_mul {p q : ι} {a b : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q) :
    a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a) :=
  mul_eq_smul_mul_of_adjoin_range_eq_top_of_isHomogeneous (𝒜 := signedSymPiece G)
    (s := fun p q => (-1 : ℤˣ) ^ (p * q))
    (fun _ => by simp)
    (fun _ _ _ => by rw [mul_add, uzpow_add])
    (fun _ => by simp)
    (fun i₁ _ j => by rw [add_mul, add_comm (i₁ * j), uzpow_add])
    (adjoin_range_generator G) G.isInternal.submodule_iSup_eq_top
    (isHomogeneous_signedSymGenerator G)
    (fun hx hy => generator_mul_generator G hx hy) ha hb

/-- Every homogeneous element whose degree has Koszul sign `1` commutes with all of
`SignedSym G`. -/
theorem commute_of_uzpow_eq_one {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hp : (-1 : ℤˣ) ^ p = 1) (b : SignedSym G) : Commute a b :=
  TauCeti.commute_of_mul_eq_uzpow_smul_mul (mul_eq_uzpow_smul_mul G) ha hp b

/-- Every homogeneous element whose degree has Koszul sign `1` lies in the center of
`SignedSym G`. -/
theorem mem_center_of_uzpow_eq_one {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hp : (-1 : ℤˣ) ^ p = 1) : a ∈ Subalgebra.center R (SignedSym G) :=
  Subalgebra.mem_center_iff.mpr fun b => (commute_of_uzpow_eq_one G ha hp b).symm

/-- Every element of degree `0` (in particular, any even-parity element when `ι = ZMod 2`)
commutes with all of `SignedSym G`. -/
theorem commute_of_mem_zero {a : SignedSym G} (ha : a ∈ signedSymPiece G 0) (b : SignedSym G) :
    Commute a b :=
  TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero (mul_eq_uzpow_smul_mul G) ha b

/-- Every element of degree `0` (in particular, any even-parity element when `ι = ZMod 2`) lies
in the center of `SignedSym G`. -/
theorem mem_center_of_mem_zero {a : SignedSym G} (ha : a ∈ signedSymPiece G 0) :
    a ∈ Subalgebra.center R (SignedSym G) :=
  Subalgebra.mem_center_iff.mpr fun b => (commute_of_mem_zero G ha b).symm

/-- Generators whose degree has Koszul sign `1` are central in `SignedSym G`. -/
theorem generator_mem_center_of_uzpow_eq_one {p : ι} {x : V} (hx : x ∈ G.piece p)
    (hp : (-1 : ℤˣ) ^ p = 1) : generator G x ∈ Subalgebra.center R (SignedSym G) :=
  mem_center_of_uzpow_eq_one G (generator_mem_signedSymPiece G hx) hp

/-- Generators of degree `0` (in particular, even-parity generators when `ι = ZMod 2`) are
central in `SignedSym G`. -/
theorem generator_mem_center_of_mem_zero {x : V} (hx : x ∈ G.piece 0) :
    generator G x ∈ Subalgebra.center R (SignedSym G) :=
  mem_center_of_mem_zero G (generator_mem_signedSymPiece G hx)

/-- A homogeneous element whose degree has Koszul sign `-1` squares to its own negative, over any
commutative ring. -/
theorem sq_eq_neg {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hp : (-1 : ℤˣ) ^ p = -1) : a ^ 2 = -(a ^ 2) := by
  rw [pow_two]
  exact TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul (mul_eq_uzpow_smul_mul G) ha hp

/-- Every homogeneous element whose degree has Koszul sign `-1` has square zero when `2` is
invertible, in particular over `ℚ`. -/
theorem sq_eq_zero [Invertible (2 : R)] {p : ι} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hp : (-1 : ℤˣ) ^ p = -1) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg G ha hp)

/-- An element of degree `1` (in particular, any odd-parity element when `ι = ZMod 2`) squares to
its own negative. -/
theorem sq_eq_neg_of_mem_one {a : SignedSym G} (ha : a ∈ signedSymPiece G 1) :
    a ^ 2 = -(a ^ 2) :=
  sq_eq_neg G ha (uzpow_one (-1))

/-- An element of degree `1` (in particular, any odd-parity element when `ι = ZMod 2`) has square
zero when `2` is invertible. -/
theorem sq_eq_zero_of_mem_one [Invertible (2 : R)] {a : SignedSym G}
    (ha : a ∈ signedSymPiece G 1) : a ^ 2 = 0 :=
  sq_eq_zero G ha (uzpow_one (-1))

end General

section Int

variable (G : InternalGrading R V ℤ)

/-- Elements of pure parity supercommute with the sign determined by their parities, even when
they combine multiple integer degrees. -/
theorem mul_eq_uzpow_smul_mul_of_mem_parityGrading {i j : ZMod 2} {a b : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) i) (hb : b ∈ parityGrading (signedSymPiece G) j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) :=
  TauCeti.mul_eq_uzpow_smul_mul_of_mem_parityGrading (mul_eq_uzpow_smul_mul G) ha hb

/-- Every element of even parity commutes with all of `SignedSym G`. -/
theorem commute_of_mem_parityGrading_zero {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 0) (b : SignedSym G) : Commute a b :=
  TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero
    (mul_eq_uzpow_smul_mul_of_mem_parityGrading G) ha b

/-- Every element of even parity lies in the center of `SignedSym G`. -/
theorem mem_center_of_mem_parityGrading_zero {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 0) : a ∈ Subalgebra.center R (SignedSym G) :=
  Subalgebra.mem_center_iff.mpr fun b => (commute_of_mem_parityGrading_zero G ha b).symm

/-- Every element of odd parity squares to its own negative, over any commutative ring. -/
theorem sq_eq_neg_of_mem_parityGrading_one {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 1) : a ^ 2 = -(a ^ 2) := by
  rw [pow_two]
  exact TauCeti.mul_self_eq_neg_of_mul_eq_uzpow_smul_mul_of_mem_one
    (mul_eq_uzpow_smul_mul_of_mem_parityGrading G) ha

/-- Every element of odd parity has square zero when `2` is invertible in the coefficient ring,
even if it sums terms of distinct odd integer degrees. -/
theorem sq_eq_zero_of_mem_parityGrading_one [Invertible (2 : R)] {a : SignedSym G}
    (ha : a ∈ parityGrading (signedSymPiece G) 1) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg_of_mem_parityGrading_one G ha)

/-- Generators of even parity are central in `SignedSym G`. -/
theorem generator_mem_center_of_mem_parityGrading_zero {x : V}
    (hx : x ∈ parityGrading G.piece 0) : generator G x ∈ Subalgebra.center R (SignedSym G) :=
  mem_center_of_mem_parityGrading_zero G (generator_mem_parityGrading G hx)

/-- Generators of odd parity square to zero when `2` is invertible. -/
theorem generator_sq_eq_zero_of_mem_parityGrading_one [Invertible (2 : R)] {x : V}
    (hx : x ∈ parityGrading G.piece 1) : generator G x ^ 2 = 0 :=
  sq_eq_zero_of_mem_parityGrading_one G (generator_mem_parityGrading G hx)

end Int

end TauCeti.SignedSym
