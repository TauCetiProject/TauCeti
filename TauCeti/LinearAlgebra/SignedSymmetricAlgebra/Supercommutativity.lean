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

We also provide induction within the homogeneous pieces: expressions are built from homogeneous
generators and the unit by multiplication, addition and scalar multiplication, retaining their
total input degree. The construction follows the supercommutative algebra of J. Pardon,
*Contact homology and virtual fundamental cycles*, equation (1.1).
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (G : InternalGrading R V)

/-- Induction on homogeneous expressions in the signed symmetric algebra, keeping track of
input degree. The zero and addition steps take place in each fixed degree. -/
@[elab_as_elim]
theorem homogeneous_induction {P : ℤ → SignedSym G → Prop}
    (one : P 0 1)
    (generator : ∀ (p : ℤ) (x : V), x ∈ G.piece p → P p (SignedSym.generator G x))
    (mul : ∀ (p q : ℤ) (a b : SignedSym G), P p a → P q b → P (p + q) (a * b))
    (zero : ∀ p, P p 0)
    (add : ∀ (p : ℤ) (a b : SignedSym G), P p a → P p b → P p (a + b))
    (smul : ∀ (p : ℤ) (r : R) (a : SignedSym G), P p a → P p (r • a))
    {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) : P p a := by
  rw [signedSymPiece_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, d, x, hx, rfl, rfl⟩ := ha
    induction n with
    | zero => simpa using one
    | succ n ih =>
      simpa only [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons] using
        mul (d 0) (∑ i : Fin n, d i.succ) _ _ (generator _ _ (hx 0))
          (ih (fun i => d i.succ) (fun i => x i.succ) (fun i => hx i.succ))
  | zero => exact zero p
  | add a b _ _ ha hb => exact add p a b ha hb
  | smul r a _ ha => exact smul p r a ha

/-- Homogeneous elements supercommute with the sign determined by their total input degrees.
No assumption on the characteristic of the coefficient ring is needed. -/
theorem mul_eq_negOnePow_smul_mul {p q : ℤ} {a b : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q) :
    a * b = ((p * q).negOnePow : ℤ) • (b * a) := by
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
      rw [← mul_assoc, hb, smul_mul_assoc, mul_assoc, hc, mul_smul_comm, smul_smul]
      simp only [Int.mul_add, Int.negOnePow_add, Units.val_mul, mul_assoc]
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
    rw [mul_assoc, hc, mul_smul_comm, ← mul_assoc, ha, smul_mul_assoc, smul_smul]
    simp only [Int.add_mul, Int.negOnePow_add, Units.val_mul, mul_assoc]
    rw [mul_comm (↑(r * q).negOnePow : ℤ)]
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
