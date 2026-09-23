/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.LinearCombination
public import TauCeti.Combinatorics.Young.OfRowLens
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Branching

/-!
# Jacobi's bialternant formula

For a Young diagram `μ` with at most `N` rows, write `λ_j = μ.rowLen j` for its row lengths and
`δ_j = N - 1 - j` for the staircase exponents on the alphabet `Fin N`.  **Jacobi's bialternant
formula** says that the Schur polynomial `s_μ`, defined combinatorially as the generating function
of the semistandard tableaux of shape `μ`, is the quotient of two alternants,
`s_μ = a_{λ+δ} / a_δ`.  The quotient is not itself an operation on `MvPolynomial`, so the formula
is stated here in the division-free form

`s_μ · a_δ = a_{λ+δ}`,

`TauCeti.diagramSchurPoly_mul_alternant`.  It is the symmetric-polynomial form of the Weyl character
formula for `GL_N`, with `a_δ` the Weyl denominator and `a_{λ+δ}` the Weyl numerator; identifying
`s_μ` with the character of the irreducible representation of highest weight `λ` is a separate
statement, not made here.

## Both sides branch in the same way

The tableau side has a branching rule in the last variable,
`TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`:
`s_μ(x₀, …, x_n) = ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · s_ν(x₀, …, x_{n-1})`, the sum running over the
shapes `ν` with at most `n` rows interlacing `μ`.  The alternant side satisfies the same rule up to
the Vandermonde factor `∏_{i < n} (x_i - x_n)`: this is
`TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`,

`a_{λ+δ}(x₀, …, x_n) = ∏_{i < n} (x_i - x_n) · ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · a_{ν+δ'}(x')`,

with `x' = (x₀, …, x_{n-1})` and `δ'` the staircase on those `n` letters.  For the empty shape it
is the recursion `a_δ = ∏_{i < n} (x_i - x_n) · a_{δ'}` of the Vandermonde determinant, and the
bialternant formula follows from the two branching rules by induction on the number of variables.

## Main statements

* `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`: the branching rule for the alternants
  `a_{λ+δ}`.
* `TauCeti.diagramSchurPoly_mul_alternant`: **Jacobi's bialternant formula** `s_μ · a_δ = a_{λ+δ}`.

## Implementation notes

The branching rule for alternants is a determinant computation.  Writing `y = x_n` and
`e_j = λ_j + n - j` for the exponents, subtracting `y ^ (e_j - e_{j+1})` times column `j + 1` from
column `j` for every `j < n` at once (right multiplication by a unitriangular matrix) empties the
last row except for its final entry `y ^ λ_n`.  In the remaining `n × n` block the entry in row `i`
and column `j` is `x_i - y` times the geometric sum
`∑_{λ_{j+1} ≤ m ≤ λ_j} x_i ^ (m + n - 1 - j) · y ^ (λ_j - m)`.  Pulling the factor `x_i - y` out of
each row and expanding the determinant multilinearly in its columns
(`Matrix.det_of_sum_column`) gives a sum over the families `m_j ∈ [λ_{j+1}, λ_j]`, which are the
row lengths of the shapes interlacing `μ` (`YoungDiagram.sum_interlacingShapes_eq_sum_piFinset`).

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3 (the Schur functions as quotients of alternants) and Section 5 (their tableau
  expansion).
* [W. Fulton, *Young Tableaux*][fulton1997], Chapter 6.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Column reduction of an alternant.**  For weakly decreasing exponents `e` on `n + 1` letters,
subtracting `x_n ^ (e_j - e_{j+1})` times column `j + 1` from column `j`, for every `j < n` at
once, empties the last row of `(x_i ^ e_j)` except for its final entry `x_n ^ e_n`, so the
alternant is that entry times the determinant of the remaining `n × n` block. -/
private theorem alternant_eq_X_last_pow_mul_det {n : ℕ} (e : Fin (n + 1) → ℕ)
    (he : ∀ j : Fin n, e j.succ ≤ e j.castSucc) :
    alternant (Fin (n + 1)) R e = X (Fin.last n) ^ e (Fin.last n) *
      (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ e j.castSucc -
        X i.castSucc ^ e j.succ * X (Fin.last n) ^ (e j.castSucc - e j.succ)).det := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy
  -- The column operation, as right multiplication by a unitriangular matrix `U`.
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun k j =>
      (if k = j then 1 else 0) - if (k : ℕ) = j + 1 then y ^ (e j - e k) else 0 with hU
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U fun k j hkj => ?_]
    · simp [hU]
    · have hkj' : k < j := OrderDual.toDual_lt_toDual.mp hkj
      have h2 : (k : ℕ) ≠ j + 1 := by omega
      simp [hU, hkj'.ne, h2]
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun i j => X i ^ e j with hA
  have hAU_last : ∀ i, (A * U) i (Fin.last n) = X i ^ e (Fin.last n) := by
    intro i
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    rw [sum_eq_zero fun k _ => ite_eq_right (by simp only [Fin.val_last]; omega), sub_zero]
  have hAU_cs : ∀ i (j : Fin n), (A * U) i j.castSucc =
      X i ^ e j.castSucc - X i ^ e j.succ * y ^ (e j.castSucc - e j.succ) := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    congr 1
    rw [sum_eq_single j.succ (fun k _ hk => ite_eq_right fun h => hk (Fin.ext (by
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢; omega))) (fun h => absurd (mem_univ _) h)]
    simp
  have hrow : ∀ j : Fin n, (A * U) (Fin.last n) j.castSucc = 0 := by
    intro j
    rw [hAU_cs, ← pow_add, Nat.add_sub_cancel' (he j), sub_self]
  -- Laplace expansion along the last row of `A * U`.
  rw [alternant_def, ← hA, ← mul_one (Matrix.det _), ← hdetU, ← Matrix.det_mul,
    Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, sum_const_zero, zero_add, Fin.succAbove_last,
    hAU_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, ← hy]
  exact congrArg (y ^ e (Fin.last n) * Matrix.det ·)
    (Matrix.ext fun i j => by rw [Matrix.submatrix_apply, hAU_cs, Matrix.of_apply])

/-- **The branching rule for alternants.**  For a shape `μ` with at most `n + 1` rows, the
alternant `a_{λ+δ}` of its row lengths `λ` shifted by the staircase `δ_j = n - j` on `n + 1`
letters is the Vandermonde factor `∏_{i < n} (x_i - x_n)` times the sum, over the shapes `ν` with
at most `n` rows interlacing `μ`, of `x_n ^ (|μ| - |ν|)` times the alternant `a_{ν+δ'}` in the
first `n` letters, `δ'_j = n - 1 - j`.

This is the alternant counterpart of the branching rule
`TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` for Schur polynomials. -/
theorem alternant_eq_prod_mul_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram)
    (hμ : μ.colLen 0 ≤ n + 1) :
    alternant (Fin (n + 1)) R (fun j => μ.rowLen j + (n - j)) =
      (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
        ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) *
            rename Fin.castSucc (alternant (Fin n) R fun j => ν.rowLen j + (n - 1 - j)) := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy
  set e : Fin (n + 1) → ℕ := fun j => μ.rowLen j + (n - j) with he
  have he_anti : ∀ j : Fin n, e j.succ ≤ e j.castSucc := by
    intro j
    have := μ.rowLen_anti j (j + 1) (Nat.le_succ _)
    simp only [he, Fin.val_succ, Fin.val_castSucc]
    omega
  -- After column reduction, each entry of the block is `x_i - y` times a geometric sum.
  set N : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1)) R) := Matrix.of fun i j =>
    ∑ m ∈ Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
      X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m) with hN
  have hblock : (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^
      e j.castSucc - X i.castSucc ^ e j.succ * y ^ (e j.castSucc - e j.succ)) =
      Matrix.of fun i j : Fin n => (X i.castSucc - y) * N i j := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply, hN, Matrix.of_apply]
    set a := μ.rowLen ((j : ℕ) + 1)
    set b := μ.rowLen j
    set c := n - 1 - j
    have hab : a ≤ b := μ.rowLen_anti _ _ (Nat.le_succ _)
    have h1 : e j.castSucc = b + 1 + c := by simp only [he, Fin.val_castSucc]; omega
    have h2 : e j.succ = a + c := by simp only [he, Fin.val_succ]; omega
    have h3 : e j.castSucc - e j.succ = b + 1 - a := by rw [h1, h2]; omega
    have hgeom := (Commute.all (X i.castSucc : MvPolynomial (Fin (n + 1)) R) y).geom_sum₂_Ico_mul
      (show a ≤ b + 1 by omega)
    have hsum : ∑ m ∈ Icc a b, (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (m + c) *
        y ^ (b - m) = X i.castSucc ^ c *
          ∑ m ∈ Ico a (b + 1), X i.castSucc ^ m * y ^ (b + 1 - 1 - m) := by
      rw [Finset.Ico_add_one_right_eq_Icc, Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [pow_add, Nat.add_sub_cancel]
      ring
    rw [hsum, h3, h1, h2]
    linear_combination (-(X i.castSucc ^ c : MvPolynomial (Fin (n + 1)) R)) * hgeom
  -- The right-hand side, as a sum over the families of row lengths of the interlacing shapes.
  have hsum : ∑ ν ∈ YoungDiagram.interlacingShapes n μ, y ^ (μ.card - ν.card) *
      rename Fin.castSucc (alternant (Fin n) R fun j => ν.rowLen j + (n - 1 - j)) =
      ∑ r ∈ Fintype.piFinset fun j : Fin n => Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        y ^ (μ.card - ∑ j, r j) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    rw [← YoungDiagram.sum_interlacingShapes_eq_sum_piFinset hμ]
    refine sum_congr rfl fun ν hν => ?_
    rw [YoungDiagram.card_eq_sum_range_rowLen ν (YoungDiagram.mem_interlacingShapes.mp hν).2,
      ← Fin.sum_univ_eq_sum_range]
  -- Pull the factor `x_i - y` out of each row and expand the block multilinearly in its columns.
  have hel : e (Fin.last n) = μ.rowLen n := by simp [he]
  rw [alternant_eq_X_last_pow_mul_det e he_anti, ← hy, hel, hblock, Matrix.det_mul_column, hN,
    Matrix.det_of_sum_column, hsum, mul_left_comm, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have hr' : ∀ j ∈ univ, r j ≤ μ.rowLen j := fun j _ =>
    (mem_Icc.mp (Fintype.mem_piFinset.mp hr j)).2
  have hdet : (Matrix.of fun i j : Fin n =>
      (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (r j + (n - 1 - j)) *
        y ^ (μ.rowLen j - r j)).det = (∏ j : Fin n, y ^ (μ.rowLen j - r j)) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    rw [alternant_def, AlgHom.map_det, ← Matrix.det_mul_row]
    congr 1
    ext i j : 1
    simp [mul_comm]
  have hcard : μ.card = ∑ j : Fin n, μ.rowLen j + μ.rowLen n := by
    rw [YoungDiagram.card_eq_sum_range_rowLen μ hμ, sum_range_succ, Fin.sum_univ_eq_sum_range]
  have hle : ∑ j : Fin n, r j ≤ ∑ j : Fin n, μ.rowLen j := sum_le_sum hr'
  rw [hdet, ← mul_assoc, prod_pow_eq_pow_sum, ← pow_add, sum_tsub_distrib _ hr', hcard]
  congr 2
  omega

/-- **Jacobi's bialternant formula.**  For a Young diagram `μ` with at most `N` rows, the Schur
polynomial `s_μ` in the alphabet `Fin N` times the Vandermonde alternant `a_δ`, `δ_j = N - 1 - j`,
is the alternant `a_{λ+δ}` of the row lengths `λ_j = μ.rowLen j` shifted by the staircase:
`s_μ · a_δ = a_{λ+δ}`.  This is the division-free form of `s_μ = a_{λ+δ} / a_δ`.

The row bound is necessary: for a taller shape `s_μ` vanishes, while the right-hand side, which
only sees the first `N` rows, need not. -/
theorem diagramSchurPoly_mul_alternant (N : ℕ) (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ * alternant (Fin N) R (fun j => N - 1 - j) =
      alternant (Fin N) R fun j => μ.rowLen j + (N - 1 - j) := by
  have hbot : ∀ i, (⊥ : _root_.YoungDiagram).rowLen i = 0 := fun i =>
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr h)
  have hbotc : (⊥ : _root_.YoungDiagram).colLen 0 = 0 :=
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)
  induction N generalizing μ with
  | zero =>
    have hμ0 : μ = ⊥ := YoungDiagram.rowLen_injective (funext fun i => by
      rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.zero_le i)), hbot])
    subst hμ0
    simp [diagramSchurPoly_bot, alternant_def]
  | succ n ih =>
    -- The Vandermonde recursion: the branching rule for the alternant of the empty shape.
    have hvan : alternant (Fin (n + 1)) R (fun j => n - j) =
        (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
          rename Fin.castSucc (alternant (Fin n) R fun j => n - 1 - j) := by
      have hshapes : YoungDiagram.interlacingShapes n ⊥ = {⊥} := by
        ext ν
        simp only [YoungDiagram.mem_interlacingShapes, mem_singleton]
        refine ⟨fun h => le_bot_iff.mp h.1.le, ?_⟩
        rintro rfl
        exact ⟨YoungDiagram.interlacedBy_iff.mpr fun i => by simp [hbot], by simp [hbotc]⟩
      simpa [hshapes, hbot] using
        alternant_eq_prod_mul_sum_interlacingShapes (R := R) n ⊥ (by simp [hbotc])
    simp only [Nat.add_sub_cancel]
    rw [diagramSchurPoly_eq_sum_interlacingShapes, hvan,
      alternant_eq_prod_mul_sum_interlacingShapes n μ hμ, sum_mul, mul_sum]
    refine sum_congr rfl fun ν hν => ?_
    rw [← ih ν (YoungDiagram.mem_interlacingShapes.mp hν).2, map_mul]
    ring

end TauCeti
