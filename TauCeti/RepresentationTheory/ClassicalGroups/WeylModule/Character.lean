/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.ExtremeShape
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.SchurWeyl
public import TauCeti.RepresentationTheory.Symmetric.FrobeniusCharacteristic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Elementary

/-!
# The character of a Weyl module is a Schur polynomial

The Weyl module `𝕊^μ(kⁿ) = TauCeti.weylModuleOfShape k n μ` is the subrepresentation of
`(kⁿ)^{⊗|μ|}` cut out by a Young symmetrizer of the shape `μ`, and the classical statement about
its character is that on the diagonal torus `TauCeti.diagGL` it is the Schur polynomial of `μ`:

`char (𝕊^μ(kⁿ)) (diag t) = s_μ(t₀, …, t_{n-1})`.

Over a field of characteristic zero this file proves that identity for **every partition** `μ`
(`TauCeti.char_weylRepOfShape_diagramOf_diagonal`). The character of `𝕊^μ(kⁿ)` on the torus is
`(1 / d!) · ∑_{σ ∈ S_d} χ^μ(σ) · p_{ρ(σ)}`, the Specht character `χ^μ` weighting the power sums
over the cycle types (`TauCeti.char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar`), and
the inverse of Frobenius's formula (`TauCeti.sum_spechtChar_smul_psumPart`) identifies that
average with `s_μ`. Read at the identity element, the identity is a dimension count: the Weyl
module of `μ` has dimension the number of semistandard tableaux of shape `μ` with entries below
`n`.

The two extreme shapes — a shape with at most one row, and a shape with at most one column — are
also treated directly, indexed by Young diagrams against `TauCeti.diagramSchurPoly`: there the
Weyl module is a symmetric, respectively an exterior, power of the standard representation, and
its character is a complete homogeneous, respectively an elementary, symmetric polynomial.

## Main results

* `TauCeti.char_weylRepOfShape_diagramOf_diagonal` and its bundled form
  `TauCeti.char_weylFDRepOfShape_diagramOf_diagonal`: **the character of the Weyl module of a
  partition `μ` is the Schur polynomial `s_μ`** on the diagonal torus.
* `TauCeti.finrank_weylModuleOfShape_diagramOf`: **the dimension of the Weyl module of a partition
  is the number of semistandard tableaux of its shape in the `n`-letter alphabet**, the value of
  its Schur polynomial at one.
* `TauCeti.char_weylRepOfShape_diagonal_of_colLen_le_one` and
  `TauCeti.char_weylRepOfShape_diagonal_of_rowLen_le_one`: the character of the Weyl module of a
  shape with at most one row, respectively at most one column, is the Schur polynomial of that
  shape, with `TauCeti.char_weylFDRepOfShape_diagonal_of_colLen_le_one` and
  `TauCeti.char_weylFDRepOfShape_diagonal_of_rowLen_le_one` their bundled forms.
* `TauCeti.finrank_weylModuleOfShape_of_colLen_le_one` and
  `TauCeti.finrank_weylModuleOfShape_of_rowLen_le_one`: the dimension of the Weyl module of an
  extreme shape is the number of semistandard tableaux of that shape in the `n`-letter alphabet.

The `k = ℂ` case of the bundled statements is the statement for `TauCeti.schurFunctor`, which is a
definitional re-export of `TauCeti.weylFDRepOfShape` over `ℂ`, so it needs no separate
declaration.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, §6.1, where
  the character of `𝕊_λ V` is shown to be the Schur polynomial through Frobenius's formula, and
  Appendix A.1 for the Schur polynomials of the extreme shapes, `s_{(d)} = h_d` and
  `s_{(1^d)} = e_d`.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
-/

public section

open Matrix MvPolynomial
open scoped TensorProduct

universe u

namespace TauCeti

/-! ### A shape with at most one row -/

section OneRow

variable (k : Type) [Field k] [CharZero k] (n : ℕ) (μ : YoungDiagram)

/-- **The character of the Weyl module of a shape with at most one row is the Schur polynomial of
that shape**, evaluated at the diagonal entries. Such a Weyl module is a symmetric power of the
standard representation, whose character is a complete homogeneous symmetric polynomial, and that
is the Schur polynomial of a one-row shape. -/
@[simp]
theorem char_weylRepOfShape_diagonal_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivSymPowerRep k n μ h),
    char_symPowerRep_diagonal, diagramSchurPoly_eq_hsymm_of_colLen_le_one h]

/-- **The character of the bundled Weyl module of a shape with at most one row is the Schur
polynomial of that shape**, evaluated at the diagonal entries. -/
@[simp]
theorem char_weylFDRepOfShape_diagonal_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    (weylFDRepOfShape k n μ).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) :=
  char_weylRepOfShape_diagonal_of_colLen_le_one k n μ h t

/-- **The dimension of the Weyl module of a shape with at most one row** is the number of
semistandard tableaux of that shape in the alphabet `{0, …, n - 1}`: the character at the identity
is the dimension, and a Schur polynomial at one counts the tableaux of its shape. -/
theorem finrank_weylModuleOfShape_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Module.finrank k (weylModuleOfShape k n μ).toSubmodule = Nat.card (BoundedSSYT n μ) := by
  have key := char_weylRepOfShape_diagonal_of_colLen_le_one k n μ h 1
  rw [map_one] at key
  simp only [Pi.one_apply, Units.val_one] at key
  rw [Representation.char_one, eval_one_diagramSchurPoly_eq_card_boundedSSYT] at key
  exact Nat.cast_injective key

end OneRow

/-! ### A shape with at most one column -/

section OneColumn

variable (k : Type u) [Field k] [CharZero k] (n : ℕ) (μ : YoungDiagram)

/-- **The character of the Weyl module of a shape with at most one column is the Schur polynomial
of that shape**, evaluated at the diagonal entries. Such a Weyl module is an exterior power of the
standard representation, whose character is an elementary symmetric polynomial, and that is the
Schur polynomial of a one-column shape. -/
@[simp]
theorem char_weylRepOfShape_diagonal_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivExtPowerRep k n μ h),
    char_extPowerRep_diagonal, diagramSchurPoly_eq_esymm_of_rowLen_le_one h]

/-- **The character of the bundled Weyl module of a shape with at most one column is the Schur
polynomial of that shape**, evaluated at the diagonal entries. -/
@[simp]
theorem char_weylFDRepOfShape_diagonal_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    (weylFDRepOfShape k n μ).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) :=
  char_weylRepOfShape_diagonal_of_rowLen_le_one k n μ h t

/-- **The dimension of the Weyl module of a shape with at most one column** is the number of
semistandard tableaux of that shape in the alphabet `{0, …, n - 1}`: the character at the identity
is the dimension, and a Schur polynomial at one counts the tableaux of its shape. -/
theorem finrank_weylModuleOfShape_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    Module.finrank k (weylModuleOfShape k n μ).toSubmodule = Nat.card (BoundedSSYT n μ) := by
  have key := char_weylRepOfShape_diagonal_of_rowLen_le_one k n μ h 1
  rw [map_one] at key
  simp only [Pi.one_apply, Units.val_one] at key
  rw [Representation.char_one, eval_one_diagramSchurPoly_eq_card_boundedSSYT] at key
  exact Nat.cast_injective key

end OneColumn

/-! ### Every partition -/

section Partition

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- **The character of the Weyl module of a partition is its Schur polynomial**: for a partition
`μ` of `d`, the character of `𝕊^μ(kⁿ)` at the diagonal matrix `diag t` is `s_μ(t₀, …, t_{n-1})`.
When `μ` has more than `n` parts both sides vanish. -/
@[simp]
theorem char_weylRepOfShape_diagramOf_diagonal {d : ℕ} (μ : d.Partition) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n (diagramOf μ)).toSubmodule)
        (weylRepOfShape k n (diagramOf μ)) (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k μ) := by
  have hd : (d.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  rw [char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar, sum_spechtChar_smul_psumPart,
    map_nsmul, nsmul_eq_mul, inv_mul_cancel_left₀ hd]

/-- **The character of the bundled Weyl module of a partition is its Schur polynomial**, evaluated
at the diagonal entries. -/
@[simp]
theorem char_weylFDRepOfShape_diagramOf_diagonal {d : ℕ} (μ : d.Partition) (t : Fin n → kˣ) :
    (weylFDRepOfShape k n (diagramOf μ)).character (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k μ) :=
  char_weylRepOfShape_diagramOf_diagonal k n μ t

/-- **The dimension of the Weyl module of a partition** is the number of semistandard tableaux of
its shape in the alphabet `{0, …, n - 1}`: the character at the identity is the dimension, and a
Schur polynomial at one counts the tableaux of its shape. -/
theorem finrank_weylModuleOfShape_diagramOf {d : ℕ} (μ : d.Partition) :
    Module.finrank k (weylModuleOfShape k n (diagramOf μ)).toSubmodule =
      Nat.card (BoundedSSYT n (diagramOf μ)) := by
  have key := char_weylRepOfShape_diagramOf_diagonal k n μ 1
  rw [map_one] at key
  simp only [Pi.one_apply, Units.val_one] at key
  rw [Representation.char_one, eval_one_schurPoly_eq_card_boundedSSYT, Fintype.card_fin] at key
  exact Nat.cast_injective key

end Partition

end TauCeti
