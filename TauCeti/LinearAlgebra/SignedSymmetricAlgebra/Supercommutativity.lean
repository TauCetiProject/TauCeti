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
commutation rule. In particular every odd homogeneous element has square zero when 2 is
invertible in the coefficient ring. These identities allow the signed symmetric algebra to
serve as a receiving supercommutative algebra in universal properties and tensor comparisons.

The proof uses `TauCeti.SignedSym.homogeneous_induction` from the grading API.
The construction follows the supercommutative algebra of J. Pardon,
*Contact homology and virtual fundamental cycles*, equation (1.1).
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V)

/-- Homogeneous elements supercommute with the sign determined by their total input degrees.
No assumption on the characteristic of the coefficient ring is needed. -/
theorem mul_eq_negOnePow_smul_mul {p q : ℤ} {a b : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q) :
    a * b = ((p * q).negOnePow : ℤ) • (b * a) := by
  -- Share the product step between the ring and its opposite.
  have hmul {A : Type (max u v)} [Ring A] {x b c : A} {s t : ℤ}
      (hb : x * b = s • (b * x)) (hc : x * c = t • (c * x)) :
      x * (b * c) = (s * t) • ((b * c) * x) := by
    calc
      x * (b * c) = (x * b) * c := (mul_assoc _ _ _).symm
      _ = s • (b * (x * c)) := by rw [hb]; simp only [smul_mul_assoc, mul_assoc]
      _ = (s * t) • ((b * c) * x) := by
        rw [hc]
        simp only [mul_smul_comm, smul_smul, mul_assoc]
  -- First commute a generator past a homogeneous expression, then induct on the other factor.
  have hgen : ∀ (p : ℤ) (x : V), x ∈ G.piece p →
      ∀ (q : ℤ) (b : SignedSym G), b ∈ signedSymPiece G q →
        generator G x * b = ((p * q).negOnePow : ℤ) • (b * generator G x) := by
    intro p x hx q b hb
    refine homogeneous_induction G (P := fun q b =>
      generator G x * b = ((p * q).negOnePow : ℤ) • (b * generator G x))
      ?_ ?_ ?_ ?_ ?_ ?_ hb
    · simp
    · exact fun q y hy => generator_mul_generator G hx hy
    · intro q r b c hb hc
      simpa [Int.mul_add, Int.negOnePow_add] using hmul hb hc
    · simp
    · intro q b c hb hc
      simp only [mul_add, add_mul, zsmul_add, hb, hc]
    · intro q r b hb
      rw [mul_smul_comm, hb, smul_mul_assoc, smul_comm r]
  refine homogeneous_induction G (P := fun p a =>
    a * b = ((p * q).negOnePow : ℤ) • (b * a)) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · simp
  · exact fun p x hx => hgen p x hx q b hb
  · intro p r a c ha hc
    -- The same product rule in the opposite ring handles multiplication on the left.
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op,
      Int.add_mul, Int.mul_add, Int.negOnePow_add, Units.val_mul, mul_comm] using
      congrArg MulOpposite.unop
      (hmul (x := MulOpposite.op b)
        (b := MulOpposite.op c) (c := MulOpposite.op a)
        (s := ((r * q).negOnePow : ℤ)) (t := ((p * q).negOnePow : ℤ))
        (by simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
          congrArg MulOpposite.op hc)
        (by simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
          congrArg MulOpposite.op ha))
  · simp
  · intro p a c ha hc
    simp only [add_mul, mul_add, zsmul_add, ha, hc]
  · intro p r a ha
    rw [smul_mul_assoc, ha, mul_smul_comm, smul_comm r]

/-- An odd homogeneous element squares to its own negative, over any commutative ring. -/
theorem sq_eq_neg {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) (hp : Odd p) :
    a ^ 2 = -(a ^ 2) := by
  simpa only [pow_two, Int.negOnePow_mul_self, Int.negOnePow_odd _ hp,
    Units.val_neg, Units.val_one, neg_smul, one_smul] using
    mul_eq_negOnePow_smul_mul G ha ha

/-- Every odd homogeneous element has square zero when 2 is invertible, in particular over ℚ. -/
theorem sq_eq_zero [Invertible (2 : R)] {p : ℤ} {a : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hp : Odd p) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg G ha hp)

end TauCeti.SignedSym
