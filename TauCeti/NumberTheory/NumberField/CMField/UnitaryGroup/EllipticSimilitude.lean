/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.LinearAlgebra.Matrix.Hermitian.Similitude
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import TauCeti.NumberTheory.NumberField.CMField.Basic

/-!
# Elliptic similitudes over a CM field

Let `E` be a CM field with complex conjugation `x ↦ star x`. For a square matrix `β` over `E` and
`ν ∈ ℚ`, a matrix `y` over `E` is an **elliptic similitude of `β` with multiplier `ν`**
(`Matrix.IsEllipticSimilitude`) if its characteristic polynomial is irreducible over `E`,
`ν ≠ 0`, `yᴴ * β * y = ν • β`, and every complex root `r` of the characteristic polynomial under
every complex embedding of `E` satisfies `star r * r = ν`, that is `|r| ^ 2 = ν`. These are the
elements whose orbital integrals the comparison of traces between unitary groups with different
signs at the infinite places relates.

At each complex embedding `φ : E →+* ℂ` the form `β` becomes diagonal in an eigenbasis of `y`
(`Matrix.IsEllipticSimilitude.exists_mul_eq_mul_diagonal`): the characteristic polynomial of `y`
is separable, being irreducible in characteristic zero, so the complex eigenvalues of `y` are
distinct, and the eigenvectors for two distinct eigenvalues are orthogonal for `β` because all the
eigenvalues have absolute value `√ν`
(`Matrix.exists_mul_eq_mul_diagonal_and_conjTranspose_mul_mul_eq_diagonal`).
In such a basis the form `β * p(y)` is diagonal with entries `b i * p (d i)`, where `d` are the
eigenvalues and `b` the diagonal of the form `β`; so its positive definiteness is decided by the
signs of the real numbers `b i * p (d i)` (`Matrix.posDef_mul_aeval_iff`). Replacing `β` by
`β * δ(y)` for a polynomial `δ` over `E` keeps `y` an elliptic similitude with the same multiplier
(`Matrix.IsEllipticSimilitude.mul_aeval`), and multiplies these diagonal entries by the `δ (d i)`
(`Matrix.posDef_mul_aeval_mul_aeval_iff`). This is how the signs of a form at the infinite places
are changed while the elliptic similitude `y` is kept.

The nonzero multiplier forces `y` to be invertible (`Matrix.IsEllipticSimilitude.isUnit`),
as required in §7.9 of the roadmap. The general matrix identities used here also apply to zero
multipliers.

## Main definitions

* `Matrix.IsEllipticSimilitude y β ν`: `y` is an elliptic similitude of `β` with multiplier `ν`.

## Main results

* `Matrix.IsEllipticSimilitude.separable_charpoly`: the characteristic polynomial is separable.
* `Matrix.IsEllipticSimilitude.isUnit`: the matrix is invertible.
* `Matrix.IsEllipticSimilitude.conjTranspose_map_mul_mul_map`: at every complex embedding `y` is a
  similitude of `β` with multiplier `ν`.
* `Matrix.IsEllipticSimilitude.exists_mul_eq_mul_diagonal`: at every complex embedding `β` is
  diagonal in an eigenbasis of `y`, whose eigenvalues have `star (d i) * d i = ν`.
* `Matrix.IsEllipticSimilitude.mul_aeval`: `y` is an elliptic similitude of `β * δ(y)`.

## Provenance

The definition and the diagonalisation at the infinite places follow the shorter formal proof of
the ShortGRH family, grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), `src/Lib/Adelic/TraceFormula/ChangingSigns.lean`
(`New.Variety.IsEllipticSimilitude`, `New.Variety.exists_eigenbasis_diag_form`, and the change
of form `β ↦ β * δ(y)` in `New.Variety.exists_aeval_hasSignType_mul_iff`); the formal proofs
here are written independently.
-/

public section

open Polynomial NumberField NumberField.IsCMField

namespace Matrix

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix `y` over a CM field `E` is an **elliptic similitude of `β` with multiplier `ν`** if
its characteristic polynomial is irreducible, `ν ≠ 0`, `yᴴ * β * y = ν • β`, and every complex
root `r` of the characteristic polynomial under every complex embedding of `E` satisfies
`star r * r = ν`. Invertibility of `y` follows from these conditions. -/
structure IsEllipticSimilitude (y β : Matrix n n E) (ν : ℚ) : Prop where
  /-- The multiplier is nonzero. -/
  multiplier_ne_zero : ν ≠ 0
  /-- The characteristic polynomial is irreducible. -/
  irreducible_charpoly : Irreducible y.charpoly
  /-- The similitude identity `yᴴ * β * y = ν • β`. -/
  conjTranspose_mul_mul : yᴴ * β * y = (ν : E) • β
  /-- Every complex root `r` of the characteristic polynomial has `star r * r = ν`. -/
  star_mul_self_of_mem_roots :
    ∀ φ : E →+* ℂ, ∀ r ∈ (y.charpoly.map φ).roots, star r * r = (ν : ℂ)

namespace IsEllipticSimilitude

variable {y β : Matrix n n E} {ν : ℚ}

/-- The characteristic polynomial of an elliptic similitude is separable. -/
theorem separable_charpoly (h : y.IsEllipticSimilitude β ν) : y.charpoly.Separable :=
  h.irreducible_charpoly.separable

/-- An elliptic similitude is invertible, since zero cannot be a complex eigenvalue when the
multiplier is nonzero. -/
theorem isUnit (h : y.IsEllipticSimilitude β ν) : IsUnit y := by
  classical
  let φ : E →+* ℂ := Classical.choice inferInstance
  apply (isUnit_iff_isUnit_det y).2
  apply isUnit_iff_ne_zero.2
  intro hy
  have hzero : 0 ∈ (y.charpoly.map φ).roots := by
    rw [← charpoly_map]
    apply (mem_roots (charpoly_monic _).ne_zero).2
    simp only [IsRoot, eval_charpoly, map_zero, zero_sub, det_neg]
    rw [← RingHom.mapMatrix_apply, ← φ.map_det, hy, map_zero, mul_zero]
  have hν := h.star_mul_self_of_mem_roots φ 0 hzero
  exact h.multiplier_ne_zero (by simpa using hν.symm)

/-- At every complex embedding `φ`, an elliptic similitude of `β` with multiplier `ν` is a
similitude of the complex form `β.map φ` with multiplier `ν`. -/
theorem conjTranspose_map_mul_mul_map (h : y.IsEllipticSimilitude β ν) (φ : E →+* ℂ) :
    (y.map φ)ᴴ * β.map φ * y.map φ = (ν : ℂ) • β.map φ := by
  -- a complex embedding of a CM field carries its conjugation to complex conjugation
  have hφ : Function.Semiconj φ star star := fun x ↦ by
    rw [star_eq_complexConj, complexEmbedding_complexConj, Complex.star_def]
  rw [← conjTranspose_map φ hφ, ← Matrix.map_mul, ← Matrix.map_mul,
    h.conjTranspose_mul_mul, map_smul' φ _ _ (map_mul φ), map_ratCast]

/-- **The form of an elliptic similitude is diagonal in an eigenbasis at each complex embedding.**
For every complex embedding `φ` there are an invertible complex matrix `P` and `d`, `b` with
`y.map φ * P = P * diagonal d`, `Pᴴ * β.map φ * P = diagonal b`, and `star (d i) * d i = ν` for
all `i`. -/
theorem exists_mul_eq_mul_diagonal (h : y.IsEllipticSimilitude β ν) (φ : E →+* ℂ) :
    ∃ (P : GL n ℂ) (d b : n → ℂ), y.map φ * P = P * diagonal d ∧
      (P : Matrix n n ℂ)ᴴ * β.map φ * P = diagonal b ∧ ∀ i, star (d i) * d i = ν := by
  have hc : (y.map φ).charpoly = y.charpoly.map φ := charpoly_map y φ
  refine exists_mul_eq_mul_diagonal_and_conjTranspose_mul_mul_eq_diagonal
    (h.conjTranspose_map_mul_mul_map φ) (IsAlgClosed.splits _) ?_ ?_
  · rw [hc]
    exact h.separable_charpoly.map
  · rw [hc]
    exact h.star_mul_self_of_mem_roots φ

/-- If `y` is an elliptic similitude of `β` with multiplier `ν`, then it is an elliptic similitude
of `β * δ(y)` with multiplier `ν`, for every polynomial `δ` over `E`. -/
theorem mul_aeval (h : y.IsEllipticSimilitude β ν) (δ : E[X]) :
    y.IsEllipticSimilitude (β * aeval y δ) ν where
  multiplier_ne_zero := h.multiplier_ne_zero
  irreducible_charpoly := h.irreducible_charpoly
  conjTranspose_mul_mul := conjTranspose_mul_mul_aeval_mul_eq_smul h.conjTranspose_mul_mul δ
  star_mul_self_of_mem_roots := h.star_mul_self_of_mem_roots

end IsEllipticSimilitude

end Matrix
