/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.ExtremeShape
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Elementary

/-!
# The character of a Weyl module of an extreme shape is a Schur polynomial

The Weyl module `𝕊^μ(kⁿ) = TauCeti.weylModuleOfShape k n μ` is the subrepresentation of
`(kⁿ)^{⊗|μ|}` cut out by a Young symmetrizer of the shape `μ`, and the classical statement about
its character is that on the diagonal torus `TauCeti.diagGL` it is the Schur polynomial of `μ`:

`char (𝕊^μ(kⁿ)) (diag t) = s_μ(t₀, …, t_{n-1})`,

where `TauCeti.diagramSchurPoly` is the generating function of the semistandard tableaux of `μ` in
the `n`-letter alphabet. Over a field of characteristic zero, this file proves that identity **for
the two extreme shapes** — a shape with at most one row, and a shape with at most one column —
where the Weyl module degenerates to a symmetric, respectively an exterior, power of the standard
representation.

The general shape is **not** proved here, and does not follow from anything below: for an
arbitrary `μ` one has to identify the weight multiplicities of `𝕊^μ(kⁿ)` with the Kostka numbers
that are the coefficients of `s_μ` (`TauCeti.coeff_diagramSchurPoly`), and that needs a
semistandard-tableau basis of the Weyl module.

Read at the identity element, the identity is a dimension count: the Weyl module of an extreme
shape has dimension the number of semistandard tableaux of that shape with entries below `n`.

## Main results

* `TauCeti.char_weylRepOfShape_diagonal_of_colLen_le_one` and
  `TauCeti.char_weylRepOfShape_diagonal_of_rowLen_le_one`: **the character of the Weyl module of a
  shape with at most one row, respectively at most one column, is the Schur polynomial of that
  shape** on the diagonal torus, with `TauCeti.char_weylFDRepOfShape_diagonal_of_colLen_le_one`
  and `TauCeti.char_weylFDRepOfShape_diagonal_of_rowLen_le_one` their bundled forms.
* `TauCeti.char_weylRepOfShape_diagramOf_indiscrete_diagonal` and
  `TauCeti.char_weylRepOfShape_diagramOf_ones_diagonal`, with the bundled
  `TauCeti.char_weylFDRepOfShape_diagramOf_indiscrete_diagonal` and
  `TauCeti.char_weylFDRepOfShape_diagramOf_ones_diagonal`: the same two identities indexed by the
  partitions `(d)` and `(1ᵈ)`, against the partition-indexed `TauCeti.schurPoly`.
* `TauCeti.finrank_weylModuleOfShape_of_colLen_le_one` and
  `TauCeti.finrank_weylModuleOfShape_of_rowLen_le_one`: **the dimension of the Weyl module of an
  extreme shape is the number of semistandard tableaux of that shape in the `n`-letter alphabet**,
  the value of its Schur polynomial at one.

The `k = ℂ` case of the bundled statements is the statement for `TauCeti.schurFunctor`, which is a
definitional re-export of `TauCeti.weylFDRepOfShape` over `ℂ`, so it needs no separate
declaration.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, where
  `𝕊^{(d)}V = Sym^d V` and `𝕊^{(1^d)}V = ⋀^d V`, and Appendix A.1 for the Schur polynomials of
  the extreme shapes, `s_{(d)} = h_d` and `s_{(1^d)} = e_d`.
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
theorem char_weylRepOfShape_diagonal_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivSymPowerRep k n μ h),
    char_symPowerRep_diagonal, diagramSchurPoly_eq_hsymm_of_colLen_le_one h]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagonal_of_colLen_le_one`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
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
theorem char_weylRepOfShape_diagonal_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivExtPowerRep k n μ h),
    char_extPowerRep_diagonal, diagramSchurPoly_eq_esymm_of_rowLen_le_one h]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagonal_of_rowLen_le_one`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
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

/-! ### The partition-indexed form -/

section Partition

variable (k : Type) [Field k] [CharZero k] (n d : ℕ)

/-- **The character of `𝕊^{(d)}(kⁿ)` is the Schur polynomial of the partition `(d)`**, the
partition-indexed reading of `TauCeti.char_weylRepOfShape_diagonal_of_colLen_le_one`: the diagram of
`Nat.Partition.indiscrete d` is a single row of `d` cells. -/
theorem char_weylRepOfShape_diagramOf_indiscrete_diagonal (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n (diagramOf (Nat.Partition.indiscrete d))).toSubmodule)
        (weylRepOfShape k n (diagramOf (Nat.Partition.indiscrete d))) (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.indiscrete d)) := by
  rw [char_weylRepOfShape_diagonal_of_colLen_le_one k n _
      (colLen_diagramOf_indiscrete_le_one d),
    diagramSchurPoly_eq_hsymm_of_colLen_le_one (colLen_diagramOf_indiscrete_le_one d),
    card_diagramOf, schurPoly_indiscrete]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagramOf_indiscrete_diagonal`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
theorem char_weylFDRepOfShape_diagramOf_indiscrete_diagonal (t : Fin n → kˣ) :
    (weylFDRepOfShape k n (diagramOf (Nat.Partition.indiscrete d))).character (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.indiscrete d)) :=
  char_weylRepOfShape_diagramOf_indiscrete_diagonal k n d t

/-- **The character of `𝕊^{(1ᵈ)}(kⁿ)` is the Schur polynomial of the partition `(1ᵈ)`**, the
partition-indexed reading of `TauCeti.char_weylRepOfShape_diagonal_of_rowLen_le_one`: the diagram of
`TauCeti.Nat.Partition.ones d` is a single column of `d` cells. -/
theorem char_weylRepOfShape_diagramOf_ones_diagonal (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n (diagramOf (Nat.Partition.ones d))).toSubmodule)
        (weylRepOfShape k n (diagramOf (Nat.Partition.ones d))) (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.ones d)) := by
  rw [char_weylRepOfShape_diagonal_of_rowLen_le_one k n _ (rowLen_diagramOf_ones_le_one d 0),
    diagramSchurPoly_eq_esymm_of_rowLen_le_one (rowLen_diagramOf_ones_le_one d 0),
    card_diagramOf, schurPoly_ones]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagramOf_ones_diagonal`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
theorem char_weylFDRepOfShape_diagramOf_ones_diagonal (t : Fin n → kˣ) :
    (weylFDRepOfShape k n (diagramOf (Nat.Partition.ones d))).character (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.ones d)) :=
  char_weylRepOfShape_diagramOf_ones_diagonal k n d t

end Partition

end TauCeti
