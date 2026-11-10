/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Natural diagonal elements of `GL_n(ℚ)`

The diagonal matrix `diag(a₁,...,aₙ)` with positive natural number entries, as an element of
`GL_n(ℚ)`. These elements name the double cosets of the arithmetic Hecke triple
(`TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets`). Over `n = 2`, `diag(d, 1)` is also the
rational form of the matrix that defines the level-raising operator on modular forms
(`TauCeti.map_natDiagGL_d_one_eq_scaleGL`). This file keeps only the definition and its two
defining equations, so that both uses can import it without the Hecke ring.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GLn.natDiagGL`: the diagonal matrix `diag(a₁,...,aₙ)` as an element of `GL_n(ℚ)`,
  with the identity as junk value when some entry is zero.

## Main results

* `HeckeRing.GLn.natDiagGL_coe`: for positive entries, the underlying matrix is
  `Matrix.diagonal (fun i ↦ (a i : ℚ))`.
* `HeckeRing.GLn.natDiagGL_of_not_pos`: otherwise `natDiagGL` is the identity.
-/

public section

namespace HeckeRing.GLn

variable (n : ℕ)

/-- The diagonal `GL_n(ℚ)` element `diag(a₁,...,aₙ)` with positive natural number entries.
Returns `1` (the identity matrix) when the positivity condition `∀ i, 0 < a i` fails;
this is a junk value that simplifies the API by avoiding an explicit positivity argument.
Only positivity is needed for a meaningful value — a positive tuple that is not a
divisibility chain still names its genuine diagonal coset. -/
noncomputable def natDiagGL (a : Fin n → ℕ) : GL (Fin n) ℚ :=
  if h : ∀ i, 0 < a i then
    TauCeti.diagGL fun i ↦ Units.mk0 (a i : ℚ) (by exact_mod_cast (h i).ne')
  else 1

@[simp] lemma natDiagGL_coe (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (↑(natDiagGL n a) : Matrix (Fin n) (Fin n) ℚ) =
    Matrix.diagonal (fun i ↦ (a i : ℚ)) := by
  rw [natDiagGL, dite_eq_left ha, TauCeti.diagGL_coe]
  simp

/-- The junk branch of `natDiagGL`: without positivity the value is the identity. -/
@[simp] lemma natDiagGL_of_not_pos {a : Fin n → ℕ} (ha : ¬ ∀ i, 0 < a i) :
    natDiagGL n a = 1 :=
  dite_eq_right ha

end HeckeRing.GLn
