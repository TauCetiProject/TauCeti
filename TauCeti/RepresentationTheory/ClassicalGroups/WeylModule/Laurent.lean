/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.FullColumns

/-!
# The character of a rational Weyl module is a Laurent symmetric polynomial

A Young diagram has nonnegative row lengths, so Schur polynomials only reach the *polynomial*
representations of `GL n`.  The character of the rational Weyl module
`TauCeti.rationalWeylRep k n λ` of a general dominant weight `λ` is instead a **Laurent** symmetric
polynomial on the diagonal torus: with `m = λₙ` the determinant-twist exponent
(`TauCeti.DominantWeight.detShift`) and `μ` the polynomial part of `λ`
(`TauCeti.DominantWeight.detShiftShape`),

`χ_{V_λ}(diag t) = (∏ᵢ tᵢ)^m · s_μ(t)`,

the determinant character to a possibly negative power times a genuine Schur polynomial.  That is
`TauCeti.char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly`.

The presentation of `λ` as a shifted diagram is not unique unless the diagram is required to have
at most `n - 1` rows, and the formula does not care which presentation is used:
`TauCeti.char_rationalWeylRep_shift_weightOfShape_diagonal` evaluates the character of
`V_{ν + m·(1, …, 1)}` as `(∏ᵢ tᵢ)^m · s_ν(t)` for *every* Young diagram `ν` with at most `n` rows,
not only for the polynomial part.  Two facts combine to give it.  Shifting a weight multiplies the
torus character by a power of the determinant
(`TauCeti.char_rationalWeylRep_shift_diagonal`), the twist being invisible to the polynomial part.
And a weight that is already the weight of a diagram `ν` needs no twist at all: the rational Weyl
module of `TauCeti.weightOfShape n ν` has the same character as the Weyl module `𝕊^ν(kⁿ)`
(`TauCeti.char_rationalWeylRep_weightOfShape_diagonal`), even when `ν` has a nonzero `n`-th row
and the canonical presentation therefore carries a nontrivial determinant twist.  That last
identity is the representation-theoretic reading of
`TauCeti.diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add`: the full column block that the
canonical presentation strips off the diagram is exactly the determinant character it puts back.

Identifying `TauCeti.rationalWeylRep k n λ` as *the* irreducible of highest weight `λ` belongs to
the highest-weight classification and is not claimed here, so these are statements about the
construction, not yet about a classified irreducible.

## Main results

* `TauCeti.char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly` and its bundled form
  `TauCeti.char_rationalWeylFDRep_diagonal_eq_eval_diagramSchurPoly`: **the torus character of a
  rational Weyl module is a determinant twist of a Schur polynomial**.
* `TauCeti.char_rationalWeylRep_shift_diagonal` and its bundled form
  `TauCeti.char_rationalWeylFDRep_shift_diagonal`: shifting the weight by `m` multiplies the torus
  character by the `m`-th power of the determinant.
* `TauCeti.char_rationalWeylRep_weightOfShape_diagonal` and its bundled form
  `TauCeti.char_rationalWeylFDRep_weightOfShape_diagonal`: on the weight of a Young diagram the
  rational Weyl module has the character of the Weyl module of that diagram.
* `TauCeti.char_rationalWeylRep_shift_weightOfShape_diagonal` and its bundled form
  `TauCeti.char_rationalWeylFDRep_shift_weightOfShape_diagonal`: **the Laurent character read off
  an arbitrary presentation** `λ = ν + m·(1, …, 1)` of the weight.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones and their
  characters are the corresponding Laurent symmetric functions.
-/

public section

open Matrix MvPolynomial

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- **The torus character of a rational Weyl module is a Laurent symmetric polynomial**: it is the
determinant character to the power `λₙ` times the Schur polynomial of the polynomial part of `λ`.
Both factors are needed, the power being negative exactly when `λₙ` is. -/
theorem char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly (l : DominantWeight n)
    (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
        (rationalWeylRep k n l) (diagGL t) =
      (((∏ i, t i) ^ l.detShift : kˣ) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) := by
  rw [char_rationalWeylRep, det_diagGL, char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly]

/-- The Laurent character of the bundled rational Weyl module, the same identity read in
`FDRep`. -/
theorem char_rationalWeylFDRep_diagonal_eq_eval_diagramSchurPoly (l : DominantWeight n)
    (t : Fin n → kˣ) :
    (rationalWeylFDRep k n l).character (diagGL t) =
      (((∏ i, t i) ^ l.detShift : kˣ) : k) *
        eval (fun i => (t i : k)) (diagramSchurPoly n k l.detShiftShape) :=
  char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly k n l t

/-- **Shifting a dominant weight by `m` twists the torus character by `det ^ m`.**  The polynomial
part of a weight is unchanged by the shift, so the two characters differ by the determinant factor
alone. -/
theorem char_rationalWeylRep_shift_diagonal (l : DominantWeight n) (m : ℤ) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n (l.shift m).detShiftShape).toSubmodule)
        (rationalWeylRep k n (l.shift m)) (diagGL t) =
      (((∏ i, t i) ^ m : kˣ) : k) *
        Representation.character (V := ↥(weylModuleOfShape k n l.detShiftShape).toSubmodule)
          (rationalWeylRep k n l) (diagGL t) := by
  rw [char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly,
    char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly,
    DominantWeight.detShiftShape_shift]
  cases n with
  | zero => simp
  | succ n =>
    rw [DominantWeight.detShift_shift, zpow_add, Units.val_mul]
    ring

/-- The determinant twist along a shift of the weight, for the bundled rational Weyl module. -/
theorem char_rationalWeylFDRep_shift_diagonal (l : DominantWeight n) (m : ℤ) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n (l.shift m)).character (diagGL t) =
      (((∏ i, t i) ^ m : kˣ) : k) * (rationalWeylFDRep k n l).character (diagGL t) :=
  char_rationalWeylRep_shift_diagonal k n l m t

/-- **On the weight of a Young diagram the determinant twist is invisible**: the rational Weyl
module of `TauCeti.weightOfShape n ν` has the torus character of the Weyl module `𝕊^ν(kⁿ)`.  The
canonical presentation of that weight strips the full column block of height `n` off `ν` and
records it as a power of the determinant, and
`TauCeti.diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add` says that the two cancel. -/
theorem char_rationalWeylRep_weightOfShape_diagonal {ν : YoungDiagram} (hν : ν.colLen 0 ≤ n)
    (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n (weightOfShape n ν).detShiftShape).toSubmodule)
        (rationalWeylRep k n (weightOfShape n ν)) (diagGL t) =
      Representation.character (V := ↥(weylModuleOfShape k n ν).toSubmodule)
        (weylRepOfShape k n ν) (diagGL t) := by
  set l := weightOfShape n ν
  obtain ⟨c, hc⟩ : ∃ c : ℕ, l.detShift = (c : ℤ) :=
    ⟨l.detShift.toNat, (Int.toNat_of_nonneg
      ((DominantWeight.isPolynomial_iff_zero_le_detShift l).mp
        (isPolynomial_weightOfShape n ν))).symm⟩
  have hrow : ∀ j < n, ν.rowLen j = l.detShiftShape.rowLen j + c := by
    intro j hj
    have hshape := DominantWeight.rowLen_detShiftShape l ⟨j, hj⟩
    have hval : l.1 ⟨j, hj⟩ = (ν.rowLen j : ℤ) := weightOfShape_apply n ν ⟨j, hj⟩
    have hle := DominantWeight.detShift_le l ⟨j, hj⟩
    simp only [hval] at hshape hle
    omega
  rw [char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly,
    char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly,
    diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add k
      l.colLen_zero_detShiftShape_le hν hrow,
    hc, zpow_natCast, eval_mul, eval_pow, eval_prod]
  simp only [eval_X, Units.val_pow_eq_pow_val, Units.coe_prod]

/-- The absence of a determinant twist on the weight of a Young diagram, for the bundled rational
Weyl module. -/
theorem char_rationalWeylFDRep_weightOfShape_diagonal {ν : YoungDiagram} (hν : ν.colLen 0 ≤ n)
    (t : Fin n → kˣ) :
    (rationalWeylFDRep k n (weightOfShape n ν)).character (diagGL t) =
      (weylFDRepOfShape k n ν).character (diagGL t) :=
  char_rationalWeylRep_weightOfShape_diagonal k n hν t

/-- **The Laurent character of a rational Weyl module, read off an arbitrary presentation of its
weight**: for every Young diagram `ν` with at most `n` rows and every `m`, the torus character of
`V_{ν + m·(1, …, 1)}` is `(∏ᵢ tᵢ)^m · s_ν(t)`.  The canonical presentation
`TauCeti.char_rationalWeylRep_diagonal_eq_eval_diagramSchurPoly` is the case where `ν` has at most
`n - 1` rows; here the number of rows is only bounded by `n`, so the shift `m` need not be the
last entry of the weight. -/
theorem char_rationalWeylRep_shift_weightOfShape_diagonal {ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ n) (m : ℤ) (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n ((weightOfShape n ν).shift m).detShiftShape).toSubmodule)
        (rationalWeylRep k n ((weightOfShape n ν).shift m)) (diagGL t) =
      (((∏ i, t i) ^ m : kˣ) : k) * eval (fun i => (t i : k)) (diagramSchurPoly n k ν) := by
  rw [char_rationalWeylRep_shift_diagonal, char_rationalWeylRep_weightOfShape_diagonal k n hν,
    char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly]

/-- The Laurent character read off an arbitrary presentation, for the bundled rational Weyl
module. -/
theorem char_rationalWeylFDRep_shift_weightOfShape_diagonal {ν : YoungDiagram}
    (hν : ν.colLen 0 ≤ n) (m : ℤ) (t : Fin n → kˣ) :
    (rationalWeylFDRep k n ((weightOfShape n ν).shift m)).character (diagGL t) =
      (((∏ i, t i) ^ m : kˣ) : k) * eval (fun i => (t i : k)) (diagramSchurPoly n k ν) :=
  char_rationalWeylRep_shift_weightOfShape_diagonal k n hν m t

end TauCeti
