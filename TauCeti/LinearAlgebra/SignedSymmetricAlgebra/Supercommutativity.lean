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

/-- Homogeneous elements supercommute with the sign determined by their total input degrees.
No assumption on the characteristic of the coefficient ring is needed. -/
theorem mul_eq_uzpow_smul_mul {p q : ι} {a b : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q) :
    a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a) := by
  -- Share the product step between the ring and its opposite via integer-unit scalars.
  have hmul {A : Type (max u v)} [Ring A] {x b c : A} {s t : ℤˣ}
      (hb : x * b = s • (b * x)) (hc : x * c = t • (c * x)) :
      x * (b * c) = (s * t) • ((b * c) * x) := by
    simp only [Units.smul_def, Units.val_mul] at hb hc ⊢
    calc
      x * (b * c) = (x * b) * c := (mul_assoc _ _ _).symm
      _ = (s : ℤ) • (b * (x * c)) := by rw [hb, smul_mul_assoc, mul_assoc]
      _ = ((s : ℤ) * (t : ℤ)) • ((b * c) * x) := by
        rw [hc, mul_smul_comm, smul_smul, mul_assoc]
  -- First commute a generator past a homogeneous expression, then induct on the other factor.
  have hgen : ∀ (p : ι) (x : V), x ∈ G.piece p →
      ∀ (q : ι) (b : SignedSym G), b ∈ signedSymPiece G q →
        generator G x * b = ((-1 : ℤˣ) ^ (p * q)) • (b * generator G x) := by
    intro p x hx q b hb
    refine homogeneous_induction G (P := fun q b =>
      generator G x * b = ((-1 : ℤˣ) ^ (p * q)) • (b * generator G x))
      ?_ ?_ ?_ ?_ ?_ ?_ hb
    · simp
    · exact fun q y hy => generator_mul_generator G hx hy
    · intro q r b c hb hc
      simpa only [mul_add, uzpow_add] using hmul hb hc
    · simp [Units.smul_def]
    · intro q b c hb hc
      simp only [mul_add, add_mul, hb, hc, Units.smul_def, zsmul_add]
    · intro q r b hb
      rw [mul_smul_comm, hb, smul_mul_assoc, smul_comm r]
  refine homogeneous_induction G (P := fun p a =>
    a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a)) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · simp
  · exact fun p x hx => hgen p x hx q b hb
  · intro p r a c ha hc
    -- The same product rule in the opposite ring handles multiplication on the left.
    have hc' : MulOpposite.op b * MulOpposite.op c =
        ((-1 : ℤˣ) ^ (r * q)) • (MulOpposite.op c * MulOpposite.op b) := by
      simpa only [MulOpposite.op_mul, Units.smul_def, MulOpposite.op_smul] using
        congrArg MulOpposite.op hc
    have ha' : MulOpposite.op b * MulOpposite.op a =
        ((-1 : ℤˣ) ^ (p * q)) • (MulOpposite.op a * MulOpposite.op b) := by
      simpa only [MulOpposite.op_mul, Units.smul_def, MulOpposite.op_smul] using
        congrArg MulOpposite.op ha
    rw [add_mul, uzpow_add, mul_comm ((-1 : ℤˣ) ^ (p * q))]
    simpa only [MulOpposite.unop_mul, Units.smul_def, MulOpposite.unop_smul, MulOpposite.unop_op]
      using congrArg MulOpposite.unop (hmul hc' ha')
  · simp [Units.smul_def]
  · intro p a c ha hc
    simp only [add_mul, mul_add, ha, hc, Units.smul_def, zsmul_add]
  · intro p r a ha
    rw [smul_mul_assoc, ha, mul_smul_comm, smul_comm r]

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
