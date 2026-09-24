/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Determinant-indexed projective matrix modules

For a positive integer `n`, the Eichler--Selberg trace formula uses integral two-by-two matrices
of determinant `n`, modulo simultaneous sign. This file supplies that carrier and its left,
inverse right, and conjugation actions of `PSL(2, ℤ)`. The corresponding `SL(2, ℤ)` maps
on representatives provide the descent to the projective group. These are the input for the
group-ring calculations in the Popa--Zagier construction of the trace formula.

Inverse right multiplication is written as a left action. Its representative formula is
`A ↦ A * g⁻¹`, so applying `h` and then `g` gives the action of `g * h`.

## References

* A. Popa and D. Zagier, *A simple proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Section 2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-! ### The projective determinant fibre -/

/-- Integral two-by-two matrices of determinant `n`. -/
abbrev TraceFormulaMatrix (n : ℤ) := FixedDetMatrix (Fin 2) ℤ n

instance (n : ℤ) : Neg (TraceFormulaMatrix n) where
  neg A := ⟨-A.1, by simpa [Matrix.det_neg] using A.2⟩

/-- Negation of a determinant fibre is computed on its underlying matrix. -/
@[simp]
theorem TraceFormulaMatrix.val_neg (A : TraceFormulaMatrix n) : (-A).1 = -A.1 := rfl

instance (n : ℤ) : InvolutiveNeg (TraceFormulaMatrix n) where
  neg_neg A := by
    apply FixedDetMatrices.ext'
    simp

/-- Two determinant-`n` matrices define the same projective matrix when they differ by sign. -/
protected def TraceFormulaMatrix.Rel (A B : TraceFormulaMatrix n) : Prop := A = B ∨ A = -B

instance (n : ℤ) : Setoid (TraceFormulaMatrix n) where
  r := TraceFormulaMatrix.Rel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      exact Or.inl rfl
    · intro A B h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    · intro A B C hAB hBC
      rcases hAB with hAB | hAB
      · exact hAB ▸ hBC
      · rcases hBC with hBC | hBC
        · exact Or.inr (hBC ▸ hAB)
        · exact Or.inl (by rw [hAB, hBC]; simp)

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
@[simp]
theorem TraceFormulaMatrixModule.mk_eq_iff {A B : TraceFormulaMatrix n} :
    TraceFormulaMatrixModule.mk A = TraceFormulaMatrixModule.mk B ↔ A = B ∨ A = -B := by
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

/-- To prove a property of every projective determinant matrix, it suffices to prove it on
representatives. -/
@[elab_as_elim]
theorem TraceFormulaMatrixModule.ind {p : TraceFormulaMatrixModule n → Prop}
    (h : ∀ A, p (TraceFormulaMatrixModule.mk A)) (x) : p x := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  exact h A

/-- Every projective determinant matrix has a determinant-fibre representative. -/
theorem TraceFormulaMatrixModule.mk_surjective :
    Function.Surjective (TraceFormulaMatrixModule.mk : TraceFormulaMatrix n →
      TraceFormulaMatrixModule n) :=
  fun x ↦ TraceFormulaMatrixModule.ind (fun A ↦ ⟨A, rfl⟩) x

/-! ### The three modular-group actions -/

/-- Right multiplication by the inverse of an integral determinant-one matrix. -/
@[expose] public def traceFormulaMatrixRight (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    TraceFormulaMatrix n :=
  ⟨A.1 * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, A.2, mul_one]⟩

/-- Inverse right multiplication is computed on the underlying matrix. -/
@[simp]
theorem val_traceFormulaMatrixRight (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    (traceFormulaMatrixRight g A).1 =
      A.1 * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl

/-- Left multiplication makes `ℳₙ` an `SL(2, ℤ)`-set. -/
instance (n : ℤ) : SMul SL(2, ℤ) (TraceFormulaMatrixModule n) where
  smul g := Quotient.map' (g • ·) fun A B h ↦ by
    rcases h with h | h
    · exact Or.inl (h ▸ rfl)
    · right
      apply FixedDetMatrices.ext'
      subst A
      simp [FixedDetMatrices.smul_coe]

instance (n : ℤ) : MulAction SL(2, ℤ) (TraceFormulaMatrixModule n) where
  one_smul x := by
    refine Quotient.inductionOn' x fun A ↦ ?_
    exact congrArg TraceFormulaMatrixModule.mk (one_smul _ A)
  mul_smul g h x := by
    refine Quotient.inductionOn' x fun A ↦ ?_
    exact congrArg TraceFormulaMatrixModule.mk (mul_smul g h A)

/-- Left multiplication on a projective class is computed on any representative. -/
@[simp]
theorem TraceFormulaMatrixModule.smul_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    g • TraceFormulaMatrixModule.mk A = TraceFormulaMatrixModule.mk (g • A) :=
  (rfl)

/-- The central sign acts trivially on the projective determinant fibre. -/
@[simp]
theorem TraceFormulaMatrixModule.neg_one_smul (x : TraceFormulaMatrixModule n) :
    (-1 : SL(2, ℤ)) • x = x := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  -- Quotient induction produces a raw constructor; `mk` exposes the representative lemma.
  change (-1 : SL(2, ℤ)) • TraceFormulaMatrixModule.mk A = TraceFormulaMatrixModule.mk A
  rw [TraceFormulaMatrixModule.smul_mk]
  calc
    TraceFormulaMatrixModule.mk ((-1 : SL(2, ℤ)) • A) =
        TraceFormulaMatrixModule.mk (-A) := by
          congr 1
          apply FixedDetMatrices.ext'
          simp [FixedDetMatrices.smul_coe]
    _ = TraceFormulaMatrixModule.mk A := TraceFormulaMatrixModule.mk_neg A

/-- The left action of `PSL(2, ℤ)` on projective determinant-`n` matrices. -/
instance (n : ℤ) : MulAction PSL(2, ℤ) (TraceFormulaMatrixModule n) :=
  MulAction.compHom _ <| QuotientGroup.lift (Subgroup.center SL(2, ℤ))
    (MulAction.toPermHom SL(2, ℤ) (TraceFormulaMatrixModule n)) fun c hc ↦
      Equiv.ext fun x ↦ by
        rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with
          rfl | rfl
        · simp
        · simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
            Equiv.Perm.one_apply] using TraceFormulaMatrixModule.neg_one_smul x

/-- A projective modular-group element represented by `g` acts as `g`. -/
@[simp]
theorem TraceFormulaMatrixModule.coe_smul (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : (g : PSL(2, ℤ)) • x = g • x := (rfl)

/-- The right multiplication action on `ℳₙ`, expressed as a left action through inversion. -/
public def TraceFormulaMatrixModule.right (x : TraceFormulaMatrixModule n) (g : SL(2, ℤ)) :
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

/-- Inverse right multiplication on a projective class is computed on any representative. -/
@[simp]
theorem TraceFormulaMatrixModule.right_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    (TraceFormulaMatrixModule.mk A).right g =
      TraceFormulaMatrixModule.mk (traceFormulaMatrixRight g A) := (rfl)

/-- The conjugation action on `ℳₙ`, expressed as a left action by `A ↦ g A g⁻¹`. -/
public def TraceFormulaMatrixModule.conj (x : TraceFormulaMatrixModule n) (g : SL(2, ℤ)) :
    TraceFormulaMatrixModule n := g • x.right g

/-- Conjugation on a projective class is computed on any representative. -/
@[simp]
theorem TraceFormulaMatrixModule.conj_mk (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    (TraceFormulaMatrixModule.mk A).conj g =
      TraceFormulaMatrixModule.mk (g • traceFormulaMatrixRight g A) := (rfl)

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

/-- Inverse right multiplication defines a left action. -/
@[simp]
theorem TraceFormulaMatrixModule.right_mul (g h : SL(2, ℤ))
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

/-- Inverse right multiplication by `g` is cancelled by its inverse. -/
@[simp]
theorem TraceFormulaMatrixModule.right_inv_right (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    (x.right g).right g⁻¹ = x := by
  rw [← TraceFormulaMatrixModule.right_mul]
  simp

/-- Inverse right multiplication by the inverse of `g` is cancelled by `g`. -/
@[simp]
theorem TraceFormulaMatrixModule.right_right_inv (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    (x.right g⁻¹).right g = x := by
  rw [← TraceFormulaMatrixModule.right_mul]
  simp

/-- The central sign also acts trivially by inverse right multiplication. -/
@[simp]
theorem TraceFormulaMatrixModule.right_neg_one (x : TraceFormulaMatrixModule n) :
    x.right (-1 : SL(2, ℤ)) = x := by
  refine Quotient.inductionOn' x fun A ↦ ?_
  -- Quotient induction produces a raw constructor; `mk` exposes the representative lemma.
  change (TraceFormulaMatrixModule.mk A).right (-1 : SL(2, ℤ)) =
    TraceFormulaMatrixModule.mk A
  rw [TraceFormulaMatrixModule.right_mk]
  calc
    TraceFormulaMatrixModule.mk (traceFormulaMatrixRight (-1) A) =
        TraceFormulaMatrixModule.mk (-A) := by
          congr 1
          apply Subtype.ext
          -- The scalar matrix `-1` acts on the underlying matrix by negation.
          change A.1 * (((-1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
            -A.1
          simp
    _ = TraceFormulaMatrixModule.mk A := TraceFormulaMatrixModule.mk_neg A

/-- Inverse right multiplication, packaged as permutations for descent to `PSL(2, ℤ)`. -/
private def traceFormulaMatrixRightHom (n : ℤ) :
    SL(2, ℤ) →* Equiv.Perm (TraceFormulaMatrixModule n) where
  toFun g := {
    toFun := fun x ↦ x.right g
    invFun := fun x ↦ x.right g⁻¹
    left_inv := TraceFormulaMatrixModule.right_inv_right g
    right_inv := TraceFormulaMatrixModule.right_right_inv g
  }
  map_one' := Equiv.ext fun x ↦ TraceFormulaMatrixModule.right_one x
  map_mul' g h := Equiv.ext fun x ↦ TraceFormulaMatrixModule.right_mul g h x

/-- Inverse right multiplication descends through the central quotient. -/
public def TraceFormulaMatrixModule.rightPSLHom (n : ℤ) :
    PSL(2, ℤ) →* Equiv.Perm (TraceFormulaMatrixModule n) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) (traceFormulaMatrixRightHom n)
    fun c hc ↦ by
      rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with
        rfl | rfl
      · simp
      · exact Equiv.ext fun x ↦ TraceFormulaMatrixModule.right_neg_one x

/-- Inverse right multiplication by a projective modular-group element. -/
public def TraceFormulaMatrixModule.rightPSL (x : TraceFormulaMatrixModule n) (g : PSL(2, ℤ)) :
    TraceFormulaMatrixModule n := TraceFormulaMatrixModule.rightPSLHom n g x

/-- The packaged permutation action agrees with inverse right multiplication. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSLHom_apply (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    TraceFormulaMatrixModule.rightPSLHom n g x = x.rightPSL g := by
  unfold TraceFormulaMatrixModule.rightPSL
  rfl

/-- A representative acts by inverse right multiplication. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_coe (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : x.rightPSL (g : PSL(2, ℤ)) = x.right g := (rfl)

/-- The identity acts trivially by inverse right multiplication. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_one (x : TraceFormulaMatrixModule n) :
    x.rightPSL 1 = x := by
  unfold TraceFormulaMatrixModule.rightPSL
  rw [map_one]
  rfl

/-- Inverse right multiplication gives a left action of `PSL(2, ℤ)`. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_mul (g h : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    x.rightPSL (g * h) = (x.rightPSL h).rightPSL g := by
  unfold TraceFormulaMatrixModule.rightPSL
  rw [map_mul]
  rfl

/-- Projective inverse right multiplication by `g` is cancelled by its inverse. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_inv_rightPSL (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    (x.rightPSL g).rightPSL g⁻¹ = x := by
  rw [← TraceFormulaMatrixModule.rightPSL_mul]
  simp

/-- Projective inverse right multiplication by the inverse of `g` is cancelled by `g`. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_rightPSL_inv (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    (x.rightPSL g⁻¹).rightPSL g = x := by
  rw [← TraceFormulaMatrixModule.rightPSL_mul]
  simp

/-- Left multiplication commutes with the right modular-group action on `ℳₙ`. -/
@[simp]
theorem TraceFormulaMatrixModule.right_smul (g h : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
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
@[simp]
theorem TraceFormulaMatrixModule.conj_mul (g h : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : x.conj (g * h) = (x.conj h).conj g := by
  simp only [TraceFormulaMatrixModule.conj, right_mul, mul_smul, right_smul]

/-- Conjugation by `g` is cancelled by conjugation by its inverse. -/
@[simp]
theorem TraceFormulaMatrixModule.conj_inv_conj (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    (x.conj g).conj g⁻¹ = x := by
  rw [← TraceFormulaMatrixModule.conj_mul]
  simp

/-- Conjugation by the inverse of `g` is cancelled by conjugation by `g`. -/
@[simp]
theorem TraceFormulaMatrixModule.conj_conj_inv (g : SL(2, ℤ)) (x : TraceFormulaMatrixModule n) :
    (x.conj g⁻¹).conj g = x := by
  rw [← TraceFormulaMatrixModule.conj_mul]
  simp

/-- Left multiplication commutes with inverse right multiplication on projective classes. -/
@[simp]
theorem TraceFormulaMatrixModule.rightPSL_smul (g h : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    (g • x).rightPSL h = g • x.rightPSL h := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  induction h using QuotientGroup.induction_on with | H b => ?_
  simpa only [coe_smul, rightPSL_coe] using TraceFormulaMatrixModule.right_smul a b x

/-- Conjugation of projective determinant-`n` matrices by `PSL(2, ℤ)`. -/
public def TraceFormulaMatrixModule.conjPSL (x : TraceFormulaMatrixModule n) (g : PSL(2, ℤ)) :
    TraceFormulaMatrixModule n := g • x.rightPSL g

/-- A representative conjugates by `A ↦ g A g⁻¹`. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSL_coe (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) : x.conjPSL (g : PSL(2, ℤ)) = x.conj g := (rfl)

/-- Conjugation fixes every class at the identity. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSL_one (x : TraceFormulaMatrixModule n) :
    x.conjPSL 1 = x := by
  simp [TraceFormulaMatrixModule.conjPSL]

/-- Conjugation by a product composes in left-action order. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSL_mul (g h : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    x.conjPSL (g * h) = (x.conjPSL h).conjPSL g := by
  simp only [TraceFormulaMatrixModule.conjPSL, rightPSL_mul, mul_smul,
    rightPSL_smul]

/-- Projective conjugation by `g` is cancelled by conjugation by its inverse. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSL_inv_conjPSL (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    (x.conjPSL g).conjPSL g⁻¹ = x := by
  rw [← TraceFormulaMatrixModule.conjPSL_mul]
  simp

/-- Projective conjugation by the inverse of `g` is cancelled by conjugation by `g`. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSL_conjPSL_inv (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    (x.conjPSL g⁻¹).conjPSL g = x := by
  rw [← TraceFormulaMatrixModule.conjPSL_mul]
  simp

/-- Conjugation of `ℳₙ` by projective modular-group elements, packaged as permutations. -/
public def TraceFormulaMatrixModule.conjPSLHom (n : ℤ) :
    PSL(2, ℤ) →* Equiv.Perm (TraceFormulaMatrixModule n) where
  toFun g := {
    toFun := fun x ↦ x.conjPSL g
    invFun := fun x ↦ x.conjPSL g⁻¹
    left_inv := TraceFormulaMatrixModule.conjPSL_inv_conjPSL g
    right_inv := TraceFormulaMatrixModule.conjPSL_conjPSL_inv g
  }
  map_one' := Equiv.ext fun x ↦ TraceFormulaMatrixModule.conjPSL_one x
  map_mul' g h := Equiv.ext fun x ↦ TraceFormulaMatrixModule.conjPSL_mul g h x

/-- The packaged conjugation permutation acts by `conjPSL`. -/
@[simp]
theorem TraceFormulaMatrixModule.conjPSLHom_apply (g : PSL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    TraceFormulaMatrixModule.conjPSLHom n g x = x.conjPSL g := by
  unfold TraceFormulaMatrixModule.conjPSLHom
  rfl

end TauCeti
