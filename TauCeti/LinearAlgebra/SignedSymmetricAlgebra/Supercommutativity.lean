/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.CharP.Invertible

/-!
# Supercommutativity of the signed symmetric algebra

Homogeneous elements of `TauCeti.SignedSym G`, not just its generators, obey the Koszul
commutation rule `a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a)`. In particular every homogeneous
element whose degree has sign `-1` has square zero when `2` is invertible in the coefficient ring.
These identities allow the signed symmetric algebra to serve as a receiving supercommutative
algebra in universal properties and tensor comparisons, for both integer and parity (`ZMod 2`)
gradings.

The proof uses `TauCeti.SignedSym.homogeneous_induction` from the grading API.
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

private theorem generator_mul_eq_uzpow_smul_mul {p q : ι} {x : V} (hx : x ∈ G.piece p)
    {b : SignedSym G} (hb : b ∈ signedSymPiece G q) :
    generator G x * b = ((-1 : ℤˣ) ^ (p * q)) • (b * generator G x) := by
  refine homogeneous_induction G (P := fun q b =>
    generator G x * b = ((-1 : ℤˣ) ^ (p * q)) • (b * generator G x))
    (by simp)
    (fun _ _ hy => generator_mul_generator G hx hy)
    (fun _ _ _ _ hb hc => by
      rw [← mul_assoc, hb, smul_mul_assoc, mul_assoc, hc, mul_smul_comm, smul_smul,
        ← mul_assoc, ← uzpow_add, ← mul_add])
    (by simp [Units.smul_def])
    (fun _ _ _ hb hc => by simp only [mul_add, add_mul, hb, hc, Units.smul_def, zsmul_add])
    (fun _ r _ hb => by rw [mul_smul_comm, hb, smul_mul_assoc, smul_comm r])
    hb

/-- Homogeneous elements supercommute with the sign determined by their total input degrees.
No assumption on the characteristic of the coefficient ring is needed. -/
theorem mul_eq_uzpow_smul_mul {p q : ι} {a b : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q) :
    a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a) := by
  refine homogeneous_induction G (P := fun p a =>
    a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    (by simp)
    (fun _ _ hx => generator_mul_eq_uzpow_smul_mul G hx hb)
    (fun p r _ _ ha hc => by
      rw [mul_assoc, hc, mul_smul_comm, ← mul_assoc, ha, smul_mul_assoc, smul_smul,
        mul_comm ((-1 : ℤˣ) ^ (r * q)), ← uzpow_add, ← add_mul, mul_assoc])
    (by simp [Units.smul_def])
    (fun _ _ _ ha hc => by simp only [add_mul, mul_add, ha, hc, Units.smul_def, zsmul_add])
    (fun _ r _ ha => by rw [smul_mul_assoc, ha, mul_smul_comm, smul_comm r])
    ha

/-- A homogeneous element whose degree has Koszul sign `-1` squares to its own negative, over any
commutative ring. -/
theorem sq_eq_neg {p : ι} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (hp : (-1 : ℤˣ) ^ p = -1) : a ^ 2 = -(a ^ 2) := by
  have hpp : (-1 : ℤˣ) ^ (p * p) = -1 := by rw [uzpow_mul, hp, hp]
  simpa only [pow_two, hpp, Units.neg_smul, one_smul] using mul_eq_uzpow_smul_mul G ha ha

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

/-- An odd integer-degree homogeneous element squares to its own negative, over any commutative
ring. -/
theorem sq_eq_neg_of_odd {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) (hp : Odd p) :
    a ^ 2 = -(a ^ 2) :=
  sq_eq_neg G ha (Int.negOnePow_odd p hp)

/-- Every odd integer-degree homogeneous element has square zero when `2` is invertible. -/
theorem sq_eq_zero_of_odd [Invertible (2 : R)] {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hp : Odd p) : a ^ 2 = 0 :=
  sq_eq_zero G ha (Int.negOnePow_odd p hp)

end Int

end TauCeti.SignedSym
