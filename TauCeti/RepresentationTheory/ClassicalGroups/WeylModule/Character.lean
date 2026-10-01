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
`(kⁿ)^{⊗|μ|}` cut out by a Young symmetrizer of the shape `μ`, irreducible exactly when `μ` has at
most `n` rows, and the classical statement about its character is that on the diagonal torus it is
the Schur polynomial of `μ`:

`char (𝕊^μ(kⁿ)) (diag t) = s_μ(t₀, …, t_{n-1})`.

Both sides are already built: `TauCeti.weylRepOfShape` is the Weyl construction and
`TauCeti.diagGL` the diagonal torus, while `TauCeti.diagramSchurPoly` is the generating function of
the semistandard tableaux of `μ` in the `n`-letter alphabet. This file proves that they agree **for
the two extreme shapes** — a shape with at most one row, and a shape with at most one column —
where the Weyl module degenerates to a symmetric, respectively an exterior, power of the standard
representation.

No new computation happens here; three identifications meet. The Weyl module of an extreme shape
*is* a symmetric or an exterior power of the standard representation
(`TauCeti.weylRepOfShapeEquivSymPowerRep`, `TauCeti.weylRepOfShapeEquivExtPowerRep`); the
characters of those powers on the diagonal torus are the complete homogeneous and the elementary
symmetric polynomials in the diagonal entries (`TauCeti.char_symPowerRep_diagonal`,
`TauCeti.char_extPowerRep_diagonal`); and the Schur polynomial of an extreme shape is that same
symmetric polynomial (`TauCeti.diagramSchurPoly_eq_hsymm_of_colLen_le_one`,
`TauCeti.diagramSchurPoly_eq_esymm_of_rowLen_le_one`), which is the "character-level shadow" the
two Schur-polynomial files name without being able to state it.

The general shape is **not** proved here, and does not follow from anything below: for an
arbitrary `μ` one has to identify the weight multiplicities of `𝕊^μ(kⁿ)` with the Kostka numbers
that are the coefficients of `s_μ` (`TauCeti.coeff_diagramSchurPoly`), and that needs a
semistandard-tableau basis of the Weyl module. The two extreme shapes are exactly the cases where
the Weyl module is already known to be a power of the standard representation, so that no such
basis is required.

Evaluating at the identity turns the identity into a dimension count: the Weyl module of an extreme
shape has dimension the number of semistandard tableaux of that shape with entries below `n`, a
Schur polynomial at one counting those tableaux
(`TauCeti.eval_one_diagramSchurPoly_eq_card_boundedSSYT`). Cancelling the cast of that count back
to `ℕ` is what the characteristic-zero hypothesis is for; it costs nothing, since the Weyl
construction already asks for the stronger `ℚ`-algebra structure that a field of characteristic
zero carries.

## Main results

* `TauCeti.char_weylRepOfShape_diagGL_of_colLen_le_one` and
  `TauCeti.char_weylRepOfShape_diagGL_of_rowLen_le_one`: **the character of the Weyl module of a
  shape with at most one row, respectively at most one column, is the Schur polynomial of that
  shape** on the diagonal torus, with `TauCeti.char_weylFDRepOfShape_diagGL_of_colLen_le_one` and
  `TauCeti.char_weylFDRepOfShape_diagGL_of_rowLen_le_one` their bundled forms.
* `TauCeti.char_weylRepOfShape_diagramOf_indiscrete_diagGL` and
  `TauCeti.char_weylRepOfShape_diagramOf_ones_diagGL`: the same two identities indexed by the
  partitions `(d)` and `(1ᵈ)`, against the partition-indexed `TauCeti.schurPoly`.
* `TauCeti.finrank_weylModuleOfShape_of_colLen_le_one` and
  `TauCeti.finrank_weylModuleOfShape_of_rowLen_le_one`: **the dimension of the Weyl module of an
  extreme shape is the number of semistandard tableaux of that shape in the `n`-letter alphabet**,
  the value of its Schur polynomial at one.

The `k = ℂ` case of the bundled statements is the statement for `TauCeti.schurFunctor`, which is a
definitional re-export of `TauCeti.weylFDRepOfShape` over `ℂ`, so it needs no separate
declaration.

## Implementation notes

The carrier of the Weyl module is a `Submodule`, and its `AddCommMonoid` instance is the one
`Submodule` supplies rather than one obtained from an `AddCommGroup`. `Representation.character`
asks for the latter, and the unifier will not bridge the two while the carrier is still a
metavariable, so the unbundled statements pin the carrier with `(V := _)`. The two instances are
definitionally equal once it is pinned, which is why the bundled statements — where
`TauCeti.weylFDRepOfShape` has already pinned it — are the unbundled ones verbatim.

The one-row statements are over a base field in `Type`, not in `Type u`, exactly as
`TauCeti.weylRepOfShapeEquivSymPowerRep` is: Mathlib's `SymmetricPower R ι M` puts `R` and the
index type in the same universe, and the index type here is `Fin μ.card`. The one-column
statements carry no such restriction.

None of the results is a `simp` lemma. The partition-indexed statements carry
`TauCeti.schurPoly` on the right, which `TauCeti.schurPoly_indiscrete` and
`TauCeti.schurPoly_ones` already rewrite to a symmetric polynomial, so their right-hand sides are
not in simp normal form; the shape-indexed statements are conditional on a degeneracy hypothesis
about the shape, and `TauCeti.char_symPowerRep_diagonal` and `TauCeti.char_extPowerRep_diagonal`
are the unconditional `simp` lemmas this area already has.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 4, "Characters are Schur polynomials", whose general statement
  `char (irreducible n μ) (diagonal x) = schurPoly n μ (x)` is proved here for the two extreme
  shapes, and Layer 5, whose dimension reading is the value at one.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, "The decomposition and Schur functors", which asks the Schur functor to have character
  `schurPoly` and dimension `schurPoly` at `(1, …, 1)`.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, where
  `𝕊^{(d)}V = Sym^d V` and `𝕊^{(1^d)}V = ⋀^d V`, and Appendix A.1 for the Schur polynomials of the
  extreme shapes, `s_{(d)} = h_d` and `s_{(1^d)} = e_d`.
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
theorem char_weylRepOfShape_diagGL_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivSymPowerRep k n μ h),
    char_symPowerRep_diagonal, diagramSchurPoly_eq_hsymm_of_colLen_le_one h]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagGL_of_colLen_le_one`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
theorem char_weylFDRepOfShape_diagGL_of_colLen_le_one (h : μ.colLen 0 ≤ 1) (t : Fin n → kˣ) :
    (weylFDRepOfShape k n μ).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) :=
  char_weylRepOfShape_diagGL_of_colLen_le_one k n μ h t

/-- **The dimension of the Weyl module of a shape with at most one row** is the number of
semistandard tableaux of that shape in the alphabet `{0, …, n - 1}`: the character at the identity
is the dimension, and a Schur polynomial at one counts the tableaux of its shape. -/
theorem finrank_weylModuleOfShape_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Module.finrank k (weylModuleOfShape k n μ).toSubmodule = Nat.card (BoundedSSYT n μ) := by
  have key := char_weylRepOfShape_diagGL_of_colLen_le_one k n μ h 1
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
theorem char_weylRepOfShape_diagGL_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k n μ).toSubmodule)
        (weylRepOfShape k n μ) (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) := by
  rw [Representation.char_iso (weylRepOfShapeEquivExtPowerRep k n μ h),
    char_extPowerRep_diagonal, diagramSchurPoly_eq_esymm_of_rowLen_le_one h]

/-- The bundled form of `TauCeti.char_weylRepOfShape_diagGL_of_rowLen_le_one`: the carrier of
`TauCeti.weylFDRepOfShape` is the same module with the same action, so this is that statement
verbatim. -/
theorem char_weylFDRepOfShape_diagGL_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) (t : Fin n → kˣ) :
    (weylFDRepOfShape k n μ).character (diagGL t) =
      eval (fun i => (t i : k)) (diagramSchurPoly n k μ) :=
  char_weylRepOfShape_diagGL_of_rowLen_le_one k n μ h t

/-- **The dimension of the Weyl module of a shape with at most one column** is the number of
semistandard tableaux of that shape in the alphabet `{0, …, n - 1}`: the character at the identity
is the dimension, and a Schur polynomial at one counts the tableaux of its shape. -/
theorem finrank_weylModuleOfShape_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    Module.finrank k (weylModuleOfShape k n μ).toSubmodule = Nat.card (BoundedSSYT n μ) := by
  have key := char_weylRepOfShape_diagGL_of_rowLen_le_one k n μ h 1
  rw [map_one] at key
  simp only [Pi.one_apply, Units.val_one] at key
  rw [Representation.char_one, eval_one_diagramSchurPoly_eq_card_boundedSSYT] at key
  exact Nat.cast_injective key

end OneColumn

/-! ### The partition-indexed form -/

section Partition

variable (k : Type) [Field k] [CharZero k] (n d : ℕ)

/-- **The character of `𝕊^{(d)}(kⁿ)` is the Schur polynomial of the partition `(d)`**, the
partition-indexed reading of `TauCeti.char_weylRepOfShape_diagGL_of_colLen_le_one`: the diagram of
`Nat.Partition.indiscrete d` is a single row of `d` cells. -/
theorem char_weylRepOfShape_diagramOf_indiscrete_diagGL (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n (diagramOf (Nat.Partition.indiscrete d))).toSubmodule)
        (weylRepOfShape k n (diagramOf (Nat.Partition.indiscrete d))) (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.indiscrete d)) := by
  rw [char_weylRepOfShape_diagGL_of_colLen_le_one k n _
      (colLen_diagramOf_indiscrete_le_one d),
    diagramSchurPoly_eq_hsymm_of_colLen_le_one (colLen_diagramOf_indiscrete_le_one d),
    card_diagramOf, schurPoly_indiscrete]

/-- **The character of `𝕊^{(1ᵈ)}(kⁿ)` is the Schur polynomial of the partition `(1ᵈ)`**, the
partition-indexed reading of `TauCeti.char_weylRepOfShape_diagGL_of_rowLen_le_one`: the diagram of
`TauCeti.Nat.Partition.ones d` is a single column of `d` cells. -/
theorem char_weylRepOfShape_diagramOf_ones_diagGL (t : Fin n → kˣ) :
    Representation.character
        (V := ↥(weylModuleOfShape k n (diagramOf (Nat.Partition.ones d))).toSubmodule)
        (weylRepOfShape k n (diagramOf (Nat.Partition.ones d))) (diagGL t) =
      eval (fun i => (t i : k)) (schurPoly (Fin n) k (Nat.Partition.ones d)) := by
  rw [char_weylRepOfShape_diagGL_of_rowLen_le_one k n _ (rowLen_diagramOf_ones_le_one d 0),
    diagramSchurPoly_eq_esymm_of_rowLen_le_one (rowLen_diagramOf_ones_le_one d 0),
    card_diagramOf, schurPoly_ones]

end Partition

end TauCeti
