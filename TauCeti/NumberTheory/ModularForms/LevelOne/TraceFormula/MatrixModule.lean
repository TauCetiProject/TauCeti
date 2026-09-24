/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular

/-!
# Determinant-indexed projective matrix modules

For a positive integer `n`, the Eichler--Selberg trace formula uses integral two-by-two matrices
of determinant `n`, modulo simultaneous sign.  This file supplies that carrier together with
the left action and the right and conjugation maps of `SL(2, ℤ)`.  They are the input for the
group-ring calculations in the Popa--Zagier construction of the trace formula.

The right action is written as an ordinary left action by composing with inversion.  Thus its
formula is `A ↦ A * g⁻¹`, which makes the action laws use the standard multiplication order.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), Section 2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-! ### The projective determinant fibre -/

/-- Integral two-by-two matrices of determinant `n`. -/
abbrev TraceFormulaMatrix (n : ℤ) := { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = n }

theorem det_neg_traceFormulaMatrix (n : ℤ) (A : TraceFormulaMatrix n) :
    (-A.1).det = n := by
  simpa only [Matrix.det_fin_two, Matrix.neg_apply, neg_mul_neg] using A.2

instance (n : ℤ) : Neg (TraceFormulaMatrix n) where
  neg A := ⟨-A.1, det_neg_traceFormulaMatrix n A⟩

/-- Two determinant-`n` matrices define the same projective matrix when they differ by sign. -/
protected def TraceFormulaMatrix.Rel (A B : TraceFormulaMatrix n) : Prop := A = B ∨ A = -B

instance (n : ℤ) : Setoid (TraceFormulaMatrix n) where
  r := TraceFormulaMatrix.Rel
  iseqv := by
    have neg_neg (A : TraceFormulaMatrix n) : - -A = A := by
      apply Subtype.ext
      -- Negation of the determinant fibre is defined on its underlying matrix.
      change - -A.1 = A.1
      simp
    refine ⟨?_, ?_, ?_⟩
    · intro A
      exact Or.inl rfl
    · intro A B h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (neg_neg B).symm)
    · intro A B C hAB hBC
      rcases hAB with hAB | hAB
      · exact hAB ▸ hBC
      · rcases hBC with hBC | hBC
        · exact Or.inr (hBC ▸ hAB)
        · exact Or.inl (by rw [hAB, hBC]; exact neg_neg C)

/-- The projective determinant-`n` matrix module `ℳₙ`: matrices modulo simultaneous sign. -/
abbrev TraceFormulaMatrixModule (n : ℤ) :=
  Quotient (inferInstance : Setoid (TraceFormulaMatrix n))

/-- The projective class of a determinant-`n` matrix. -/
def TraceFormulaMatrixModule.mk (A : TraceFormulaMatrix n) : TraceFormulaMatrixModule n :=
  Quotient.mk'' A

/-- Passing to the projective matrix module identifies a matrix with its negative. -/
@[simp]
theorem TraceFormulaMatrixModule.mk_neg (A : TraceFormulaMatrix n) :
    TraceFormulaMatrixModule.mk (-A) = TraceFormulaMatrixModule.mk A :=
  Quotient.sound (Or.inr rfl)

/-- Two representatives of `ℳₙ` agree exactly when they are equal up to simultaneous sign. -/
theorem TraceFormulaMatrixModule.mk_eq_iff {A B : TraceFormulaMatrix n} :
    TraceFormulaMatrixModule.mk A = TraceFormulaMatrixModule.mk B ↔ A = B ∨ A = -B := by
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

/-! ### The three modular-group actions -/

/-- Left multiplication by an integral determinant-one matrix on the determinant fibre. -/
def traceFormulaMatrixLeft (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    TraceFormulaMatrix n :=
  ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) * A.1, by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, A.2]⟩

/-- Right multiplication by the inverse of an integral determinant-one matrix. -/
def traceFormulaMatrixRight (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    TraceFormulaMatrix n :=
  ⟨A.1 * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, A.2, mul_one]⟩

/-- Conjugation by an integral determinant-one matrix on the determinant fibre. -/
def traceFormulaMatrixConj (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    TraceFormulaMatrix n := traceFormulaMatrixLeft g (traceFormulaMatrixRight g A)

/-- Left multiplication makes `ℳₙ` an `SL(2, ℤ)`-set. -/
instance (n : ℤ) : SMul SL(2, ℤ) (TraceFormulaMatrixModule n) where
  smul g := Quotient.map' (traceFormulaMatrixLeft g) fun A B h ↦ by
    rcases h with h | h
    · exact Or.inl (h ▸ rfl)
    · right
      apply Subtype.ext
      have hval : A.1 = -B.1 := congrArg Subtype.val h
      -- Subtype equality reduces to equality of the underlying matrices.
      change (g : Matrix (Fin 2) (Fin 2) ℤ) * A.1 =
        -((g : Matrix (Fin 2) (Fin 2) ℤ) * B.1)
      rw [hval, Matrix.mul_neg]

instance (n : ℤ) : MulAction SL(2, ℤ) (TraceFormulaMatrixModule n) where
  one_smul x := by
    refine Quotient.inductionOn' x fun A ↦ ?_
    apply Quotient.sound
    left
    apply Subtype.ext
    -- The quotient and subtype constructors expose the matrix action definitionally.
    change (1 : Matrix (Fin 2) (Fin 2) ℤ) * A.1 = A.1
    simp
  mul_smul g h x := by
    refine Quotient.inductionOn' x fun A ↦ ?_
    apply Quotient.sound
    left
    apply Subtype.ext
    -- The quotient and subtype constructors expose the matrix action definitionally.
    change ((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A.1 =
      (g : Matrix (Fin 2) (Fin 2) ℤ) * ((h : Matrix (Fin 2) (Fin 2) ℤ) * A.1)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

@[simp]
theorem TraceFormulaMatrixModule.smul_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    g • TraceFormulaMatrixModule.mk A = TraceFormulaMatrixModule.mk (traceFormulaMatrixLeft g A) :=
  (rfl)

/-- The right multiplication action on `ℳₙ`, expressed as a left action through inversion. -/
public def TraceFormulaMatrixModule.right (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    TraceFormulaMatrixModule n :=
  Quotient.map' (traceFormulaMatrixRight g) (fun A B h ↦ by
    rcases h with h | h
    · exact Or.inl (h ▸ rfl)
    · right
      apply Subtype.ext
      have hval : A.1 = -B.1 := congrArg Subtype.val h
      -- Subtype equality reduces to equality of the underlying matrices.
      change A.1 * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        -(B.1 * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      rw [hval, Matrix.neg_mul]) x

@[simp]
theorem TraceFormulaMatrixModule.right_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    (TraceFormulaMatrixModule.mk A).right g =
      TraceFormulaMatrixModule.mk (traceFormulaMatrixRight g A) := (rfl)

/-- The conjugation action on `ℳₙ`, expressed as a left action by `A ↦ g A g⁻¹`. -/
public def TraceFormulaMatrixModule.conj (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    TraceFormulaMatrixModule n := g • x.right g

/-- Conjugation is left multiplication followed by inverse right multiplication. -/
theorem TraceFormulaMatrixModule.conj_eq_smul_right (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : x.conj g = g • x.right g := by
  unfold TraceFormulaMatrixModule.conj
  rfl

@[simp]
theorem TraceFormulaMatrixModule.conj_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    (TraceFormulaMatrixModule.mk A).conj g =
      TraceFormulaMatrixModule.mk (traceFormulaMatrixConj g A) := (rfl)

/-- Inverse right multiplication fixes `ℳₙ` at the identity. -/
@[simp]
theorem TraceFormulaMatrixModule.right_one (x : TraceFormulaMatrixModule n) : x.right 1 = x := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  apply Quotient.sound
  left
  apply Subtype.ext
  -- The quotient and subtype constructors expose the right matrix action definitionally.
  change A.1 * ((1⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = A.1
  simp

/-- Inverse right multiplication defines a left action, so successive arguments reverse. -/
@[simp]
theorem TraceFormulaMatrixModule.right_mul_rev (g h : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    x.right (g * h) = (x.right h).right g := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  apply Quotient.sound
  left
  apply Subtype.ext
  -- The quotient and subtype constructors expose the right matrix action definitionally.
  change A.1 * (((g * h)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    (A.1 * ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
      ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

/-- Left multiplication commutes with the right modular-group action on `ℳₙ`. -/
theorem TraceFormulaMatrixModule.smul_right (g h : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    (g • x).right h = g • x.right h := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  apply Quotient.sound
  left
  apply Subtype.ext
  -- Both quotient actions reduce to matrix multiplication on representatives.
  change ((g : Matrix (Fin 2) (Fin 2) ℤ) * A.1) *
      ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    (g : Matrix (Fin 2) (Fin 2) ℤ) *
      (A.1 * ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
  rw [Matrix.mul_assoc]

/-- Conjugation fixes `ℳₙ` at the identity. -/
@[simp]
theorem TraceFormulaMatrixModule.conj_one (x : TraceFormulaMatrixModule n) : x.conj 1 = x := by
  simp [TraceFormulaMatrixModule.conj]

/-- Conjugation by a product composes in the usual left-action order. -/
theorem TraceFormulaMatrixModule.conj_mul (g h : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : x.conj (g * h) = (x.conj h).conj g := by
  simp only [TraceFormulaMatrixModule.conj, right_mul_rev, mul_smul, smul_right]

end TauCeti
