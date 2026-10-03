/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.ColumnShift

/-!
# The rational character of `GL n` is a Laurent Schur polynomial: extreme shapes and rank two

The rational Weyl module `TauCeti.rationalWeylRep k n λ` of a dominant weight `λ` is `det ^ λₙ`
tensored with the Weyl module of the polynomial part `μ = λ.detShiftShape`, so its character is
`det ^ λₙ` times the character of that Weyl module (`TauCeti.char_rationalWeylRep`).  Read on the
diagonal torus `TauCeti.diagGL`, this says that the character is a **Laurent** symmetric
polynomial,

`char (rationalWeylRep k n λ) (diag t) = (t₀ ⋯ t_{n-1}) ^ λₙ · s_μ(t)`,

whose exponent `λₙ` may be negative: for a general dominant weight no honest `MvPolynomial`
expresses the character, and `TauCeti.diagramSchurPoly` is kept for shapes only.  That is what this
file proves, in the regime in which the polynomial factor `s_μ(t)` is known: when `μ` has at most
one row or at most one column, where the Weyl module degenerates to a symmetric, respectively an
exterior, power of the standard representation
(`TauCeti.char_weylRepOfShape_diagonal_of_colLen_le_one` and its one-column twin).

Twisting back, the Laurent form is the Schur polynomial of `λ` itself whenever `λ` is polynomial:
prepending `λₙ` full columns to the diagram of `μ` gives the diagram of `λ`, and that multiplies
the Schur polynomial by `(x₀ ⋯ x_{n-1}) ^ λₙ`
(`TauCeti.diagramSchurPoly_eq_prod_X_pow_mul`).  So

`char (rationalWeylRep k n λ) (diag t) = s_λ(t)`

holds for every polynomial weight whose polynomial part is an extreme shape, and those weights are
*not* the ones whose own diagram is extreme: the diagram of a weight `(c + a, c, …, c)` with
`0 < c` and `0 < a` is the `n`-row rectangle of width `c` with `a` further cells in its first row,
which is neither a single row nor a single column.  This extends the range of shapes for which the
character of a Weyl module is known to be a Schur polynomial.

For `GL 2` the polynomial part of a weight is always a single row
(`TauCeti.DominantWeight.colLen_zero_detShiftShape_le_one_of_le_two`), so over `GL 2` the Laurent
identity needs no hypothesis at all, and the identity against the weight's own diagram needs only
that the weight be polynomial, which is what makes `s_λ` an honest polynomial.  The weight
`λ = (2, 1)` of `GL 2` is the case
`s_{(2,1)}(t₀, t₁) = t₀² t₁ + t₀ t₁² = (t₀t₁)(t₀ + t₁)`, of dimension `2`, which the Weyl dimension
formula also gives.

Every statement below is about the constructed representation `TauCeti.rationalWeylRep k n λ`,
indexed by a dominant weight `λ`.  That this representation is the irreducible one of highest
weight `λ`, and that the construction exhausts the irreducible rational representations, belong to
the highest-weight classification, which is not available in the repository; nothing here
presupposes or claims either.

## Main results

* `TauCeti.diagramSchurPoly_shape_eq_prod_X_pow_mul`: the Schur polynomial of a polynomial weight
  is `(x₀ ⋯ x_{n-1}) ^ λₙ` times the Schur polynomial of its polynomial part.
* `TauCeti.char_rationalWeylRep_diagonal_of_colLen_le_one` and
  `TauCeti.char_rationalWeylRep_diagonal_of_rowLen_le_one`: **the rational character is Laurent**,
  for a weight whose polynomial part has at most one row, respectively at most one column, with
  `TauCeti.char_rationalWeylFDRep_diagonal_of_colLen_le_one` and
  `TauCeti.char_rationalWeylFDRep_diagonal_of_rowLen_le_one` their bundled forms.
* `TauCeti.char_rationalWeylRep_diagonal_eq_eval_shape_of_colLen_le_one` and
  `TauCeti.char_rationalWeylRep_diagonal_eq_eval_shape_of_rowLen_le_one`: for a polynomial such
  weight the character is the Schur polynomial of the weight's own diagram, with
  `TauCeti.char_rationalWeylFDRep_diagonal_eq_eval_shape_of_colLen_le_one` and
  `TauCeti.char_rationalWeylFDRep_diagonal_eq_eval_shape_of_rowLen_le_one` their bundled forms.
* `TauCeti.char_rationalWeylRep_diagonal_fin_two` and
  `TauCeti.char_rationalWeylRep_diagonal_eq_eval_shape_fin_two`, bundled as
  `TauCeti.char_rationalWeylFDRep_diagonal_fin_two` and
  `TauCeti.char_rationalWeylFDRep_diagonal_eq_eval_shape_fin_two`: for `GL 2`, the Laurent identity
  with no condition on the weight, and the identity against the weight's own diagram for a
  polynomial weight.
* `TauCeti.diagramSchurPoly_shape_of_eq_two_one`: `s_{(2,1)}(x₀, x₁) = x₀² x₁ + x₀ x₁²`, over any
  commutative semiring.
* `TauCeti.char_rationalWeylRep_diagonal_of_eq_two_one`, bundled as
  `TauCeti.char_rationalWeylFDRep_diagonal_of_eq_two_one`, and
  `TauCeti.finrank_weylModuleOfShape_detShiftShape_eq_weylDimension_of_eq_two_one`: the character
  and the dimension of the rational Weyl module of the weight `(2, 1)` of `GL 2`, the latter
  matching `TauCeti.weylDimension`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational irreducibles of `GL n` are the determinant twists of the polynomial ones, and
  Appendix A.1 for the Schur polynomials.
-/

public section

open Matrix MvPolynomial

universe u

namespace TauCeti

section Schur

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- **The Schur polynomial of a polynomial dominant weight is a determinant twist of the Schur
polynomial of its polynomial part**: the diagram of `λ` has `λₙ` full columns in front of the
diagram of `μ = λ.detShiftShape`, and each such column multiplies the Schur polynomial by
`x₀ ⋯ x_{n-1}`. -/
theorem diagramSchurPoly_shape_eq_prod_X_pow_mul {l : DominantWeight n} (hl : l.IsPolynomial) :
    diagramSchurPoly n R l.shape =
      (∏ i, (X i : MvPolynomial (Fin n) R)) ^ l.detShift.toNat *
        diagramSchurPoly n R l.detShiftShape :=
  diagramSchurPoly_eq_prod_X_pow_mul l.colLen_zero_detShiftShape_le l.colLen_zero_shape_le
    fun i => DominantWeight.rowLen_shape_eq_rowLen_detShiftShape_add hl i

end Schur

section Prefactor

variable (R : Type*) [CommSemiring R] {n : ℕ}

/-- The Laurent prefactor of a **polynomial** weight is an honest monomial: `λₙ` is nonnegative, so
`(t₀ ⋯ t_{n-1}) ^ λₙ` is the value at `t` of `(x₀ ⋯ x_{n-1}) ^ λₙ`. -/
theorem val_prod_zpow_detShift {l : DominantWeight n} (hl : l.IsPolynomial) (t : Fin n → Rˣ) :
    (↑((∏ i, t i) ^ l.detShift) : R) =
      eval (fun i => (t i : R)) ((∏ i, (X i : MvPolynomial (Fin n) R)) ^ l.detShift.toNat) := by
  set m := l.detShift.toNat
  have hdet : l.detShift = (m : ℤ) :=
    (Int.toNat_of_nonneg (l.isPolynomial_iff_zero_le_detShift.mp hl)).symm
  rw [hdet, zpow_natCast, map_pow, map_prod]
  simp

end Prefactor

/-! ### A polynomial part with at most one row -/

section OneRow

variable (k : Type) [Field k] [CharZero k] {n : ℕ}

/-- **The rational character is Laurent**, for a weight whose polynomial part has at most one row:
the character of the rational Weyl module of `λ` at `diag t` is `(t₀ ⋯ t_{n-1}) ^ λₙ` times the
Schur polynomial of the polynomial part, the exponent `λₙ` being an integer. -/
theorem char_rationalWeylRep_diagonal_of_colLen_le_one {l : DominantWeight n}
    (h : l.detShiftShape.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) := by
  rw [char_rationalWeylRep, det_diagGL,
    char_weylRepOfShape_diagonal_of_colLen_le_one k n l.detShiftShape h t]

/-- **The rational character is Laurent**, the same identity for the bundled rational Weyl module
of a weight whose polynomial part has at most one row. -/
theorem char_rationalWeylFDRep_diagonal_of_colLen_le_one {l : DominantWeight n}
    (h : l.detShiftShape.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n l).character (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) :=
  char_rationalWeylRep_diagonal_of_colLen_le_one k h t

/-- **The character of the rational Weyl module of a polynomial weight whose polynomial part has at
most one row is the Schur polynomial of the weight's own diagram.**  Twisting the one-row
polynomial character back by `det ^ λₙ` turns the Schur polynomial of the polynomial part into the
Schur polynomial of `λ`, whose diagram is a rectangle of width `λₙ` with one row on top — a shape
that need be neither a single row nor a single column. -/
theorem char_rationalWeylRep_diagonal_eq_eval_shape_of_colLen_le_one {l : DominantWeight n}
    (hl : l.IsPolynomial) (h : l.detShiftShape.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k l.shape) := by
  rw [diagramSchurPoly_shape_eq_prod_X_pow_mul hl, map_mul,
    char_rationalWeylRep_diagonal_of_colLen_le_one k h t, val_prod_zpow_detShift k hl t]

/-- **The character of the bundled rational Weyl module of a polynomial weight whose polynomial
part has at most one row is the Schur polynomial of the weight's own diagram.** -/
theorem char_rationalWeylFDRep_diagonal_eq_eval_shape_of_colLen_le_one {l : DominantWeight n}
    (hl : l.IsPolynomial) (h : l.detShiftShape.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n l).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k l.shape) :=
  char_rationalWeylRep_diagonal_eq_eval_shape_of_colLen_le_one k hl h t

end OneRow

/-! ### A polynomial part with at most one column -/

section OneColumn

variable (k : Type u) [Field k] [CharZero k] {n : ℕ}

/-- **The rational character is Laurent**, for a weight whose polynomial part has at most one
column. -/
theorem char_rationalWeylRep_diagonal_of_rowLen_le_one {l : DominantWeight n}
    (h : l.detShiftShape.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) := by
  rw [char_rationalWeylRep, det_diagGL,
    char_weylRepOfShape_diagonal_of_rowLen_le_one k n l.detShiftShape h t]

/-- **The rational character is Laurent**, the same identity for the bundled rational Weyl module
of a weight whose polynomial part has at most one column. -/
theorem char_rationalWeylFDRep_diagonal_of_rowLen_le_one {l : DominantWeight n}
    (h : l.detShiftShape.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n l).character (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) :=
  char_rationalWeylRep_diagonal_of_rowLen_le_one k h t

/-- **The character of the rational Weyl module of a polynomial weight whose polynomial part has at
most one column is the Schur polynomial of the weight's own diagram.** -/
theorem char_rationalWeylRep_diagonal_eq_eval_shape_of_rowLen_le_one {l : DominantWeight n}
    (hl : l.IsPolynomial) (h : l.detShiftShape.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k l.shape) := by
  rw [diagramSchurPoly_shape_eq_prod_X_pow_mul hl, map_mul,
    char_rationalWeylRep_diagonal_of_rowLen_le_one k h t, val_prod_zpow_detShift k hl t]

/-- **The character of the bundled rational Weyl module of a polynomial weight whose polynomial
part has at most one column is the Schur polynomial of the weight's own diagram.** -/
theorem char_rationalWeylFDRep_diagonal_eq_eval_shape_of_rowLen_le_one {l : DominantWeight n}
    (hl : l.IsPolynomial) (h : l.detShiftShape.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n l).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k l.shape) :=
  char_rationalWeylRep_diagonal_eq_eval_shape_of_rowLen_le_one k hl h t

end OneColumn

/-! ### The general linear group of rank two -/

section FinTwo

variable (k : Type) [Field k] [CharZero k]

/-- **For `GL 2` the rational character is Laurent for every dominant weight**: the polynomial part
of a weight of `GL 2` is always a single row, so the Laurent form holds with no hypothesis. -/
theorem char_rationalWeylRep_diagonal_fin_two (l : DominantWeight 2) (t : Fin 2 → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k 2 l.detShiftShape).toSubmodule)
        (rationalWeylRep k 2 l) (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly 2 k l.detShiftShape) :=
  char_rationalWeylRep_diagonal_of_colLen_le_one k
    (l.colLen_zero_detShiftShape_le_one_of_le_two le_rfl) t

/-- **For `GL 2` the rational character is Laurent for every dominant weight**, for the bundled
rational Weyl module. -/
theorem char_rationalWeylFDRep_diagonal_fin_two (l : DominantWeight 2) (t : Fin 2 → kˣ) :
    (rationalWeylFDRep k 2 l).character (diagGL t) =
      (↑((∏ i, t i) ^ l.detShift) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly 2 k l.detShiftShape) :=
  char_rationalWeylRep_diagonal_fin_two k l t

/-- **For `GL 2` the character of a polynomial weight is the Schur polynomial of its own
diagram**, with no condition on the shape: the polynomial part of a weight of `GL 2` is a single
row, so the determinant twist always turns the one-row character into the character of `λ`. -/
theorem char_rationalWeylRep_diagonal_eq_eval_shape_fin_two {l : DominantWeight 2}
    (hl : l.IsPolynomial) (t : Fin 2 → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k 2 l.detShiftShape).toSubmodule)
        (rationalWeylRep k 2 l) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly 2 k l.shape) :=
  char_rationalWeylRep_diagonal_eq_eval_shape_of_colLen_le_one k hl
    (l.colLen_zero_detShiftShape_le_one_of_le_two le_rfl) t

/-- **For `GL 2` the character of a polynomial weight is the Schur polynomial of its own
diagram**, for the bundled rational Weyl module. -/
theorem char_rationalWeylFDRep_diagonal_eq_eval_shape_fin_two {l : DominantWeight 2}
    (hl : l.IsPolynomial) (t : Fin 2 → kˣ) :
    (rationalWeylFDRep k 2 l).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly 2 k l.shape) :=
  char_rationalWeylRep_diagonal_eq_eval_shape_fin_two k hl t

end FinTwo

/-! ### The weight `(2, 1)` of `GL 2` -/

section TwoOne

variable {l : DominantWeight 2} (h0 : l.1 0 = 2) (h1 : l.1 1 = 1)

include h1 in
/-- The weight `(2, 1)` of `GL 2` carries the determinant-twist exponent `1`. -/
theorem detShift_eq_one_of_eq_two_one : l.detShift = 1 := by
  rw [DominantWeight.detShift_succ]
  simpa using h1

include h1 in
/-- The weight `(2, 1)` of `GL 2` is polynomial. -/
theorem isPolynomial_of_eq_two_one : l.IsPolynomial :=
  l.isPolynomial_iff_zero_le_detShift.mpr (by rw [detShift_eq_one_of_eq_two_one h1]; norm_num)

include h0 h1 in
/-- **The polynomial part of the weight `(2, 1)` of `GL 2` is a single cell**: subtracting the last
entry `1` leaves the weight `(1, 0)`.  So the rational Weyl module of `(2, 1)` is the determinant
twist of the standard representation. -/
theorem card_detShiftShape_eq_one_of_eq_two_one : l.detShiftShape.card = 1 := by
  have hr0 := DominantWeight.rowLen_detShiftShape l 0
  rw [h0, detShift_eq_one_of_eq_two_one h1] at hr0
  norm_num at hr0
  rw [YoungDiagram.card_eq_sum_range_rowLen _
      (l.colLen_zero_detShiftShape_le_one_of_le_two le_rfl),
    Finset.sum_range_one, hr0]

include h0 h1 in
/-- **The Schur polynomial of `(2, 1)` in two variables is `x₀² x₁ + x₀ x₁²`.**  It is the
determinant twist `x₀ x₁ · (x₀ + x₁)` of the Schur polynomial of a single cell, which is the sum of
the two variables. -/
theorem diagramSchurPoly_shape_of_eq_two_one (R : Type*) [CommSemiring R] :
    diagramSchurPoly 2 R l.shape = X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 := by
  rw [diagramSchurPoly_shape_eq_prod_X_pow_mul (isPolynomial_of_eq_two_one h1),
    diagramSchurPoly_eq_hsymm_of_colLen_le_one
      (l.colLen_zero_detShiftShape_le_one_of_le_two le_rfl),
    card_detShiftShape_eq_one_of_eq_two_one h0 h1, hsymm_one,
    detShift_eq_one_of_eq_two_one h1]
  simp only [Int.toNat_one, pow_one, Fin.prod_univ_two, Fin.sum_univ_two]
  ring

end TwoOne

section TwoOneCharacter

variable (k : Type) [Field k] [CharZero k] {l : DominantWeight 2}
  (h0 : l.1 0 = 2) (h1 : l.1 1 = 1)

include h0 h1 in
/-- **The weight `(2, 1)` of `GL 2`, on characters**: the character of the rational Weyl module of
`(2, 1)` at `diag (t₀, t₁)` is `s_{(2,1)}(t₀, t₁) = t₀² t₁ + t₀ t₁²`, equivalently
`(t₀ t₁)(t₀ + t₁)`. -/
theorem char_rationalWeylRep_diagonal_of_eq_two_one (t : Fin 2 → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k 2 l.detShiftShape).toSubmodule)
        (rationalWeylRep k 2 l) (diagGL t) =
      (t 0 : k) ^ 2 * (t 1 : k) + (t 0 : k) * (t 1 : k) ^ 2 := by
  rw [char_rationalWeylRep_diagonal_eq_eval_shape_fin_two k (isPolynomial_of_eq_two_one h1) t,
    diagramSchurPoly_shape_of_eq_two_one h0 h1]
  simp

include h0 h1 in
/-- **The weight `(2, 1)` of `GL 2`, on characters**, for the bundled rational Weyl module. -/
theorem char_rationalWeylFDRep_diagonal_of_eq_two_one (t : Fin 2 → kˣ) :
    (rationalWeylFDRep k 2 l).character (diagGL t) =
      (t 0 : k) ^ 2 * (t 1 : k) + (t 0 : k) * (t 1 : k) ^ 2 :=
  char_rationalWeylRep_diagonal_of_eq_two_one k h0 h1 t

include h0 h1 in
/-- **The weight `(2, 1)` of `GL 2`, on dimensions**: the rational Weyl module of `(2, 1)` is
two-dimensional, and that is what the Weyl dimension formula gives.  The dimension is the character
at the identity, the Schur polynomial of `(2, 1)` evaluated at one. -/
theorem finrank_weylModuleOfShape_detShiftShape_eq_weylDimension_of_eq_two_one :
    Module.finrank k (weylModuleOfShape k 2 l.detShiftShape).toSubmodule = weylDimension l := by
  have hdim : weylDimension l = 2 := by
    have h := weylDimension_fin_two l
    rw [h0, h1] at h
    omega
  have key := char_rationalWeylRep_diagonal_of_eq_two_one k h0 h1 1
  rw [map_one, Representation.char_one] at key
  have hcast :
      ((Module.finrank k ↥(weylModuleOfShape k 2 l.detShiftShape).toSubmodule : ℕ) : k)
        = ((2 : ℕ) : k) := by
    rw [key]
    norm_num
  rw [hdim]
  exact Nat.cast_injective hcast

end TwoOneCharacter

end TauCeti
