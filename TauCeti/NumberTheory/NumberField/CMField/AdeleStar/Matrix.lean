/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar

/-!
# The conjugate transpose of a matrix over the finite adeles of a CM field

The star structure on the finite adeles of a CM field `E` is complex conjugation
`NumberField.IsCMField.finiteAdeleConj` (`NumberField.IsCMField.coe_finiteAdeleConj`). So the
conjugate transpose `star M` of a square matrix over `𝔸_f` is the transpose of the entrywise
conjugate `M.map (finiteAdeleConj E)`, the twisted transpose that congruence lemmas for a ring
endomorphism `σ` (such as `Matrix.transpose_map_mul_mul_mul`) are stated with.

## Main results

* `Matrix.star_eq_transpose_map_finiteAdeleConj`: `star M = (M.map (finiteAdeleConj E))ᵀ`.
-/

public section

open NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace Matrix

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n : Type*}

/-- The conjugate transpose over the finite adeles of a CM field is the transpose of the entrywise
complex conjugate `finiteAdeleConj`. -/
theorem star_eq_transpose_map_finiteAdeleConj (M : Matrix n n 𝔸ᶠ[E]) :
    star M = (M.map (finiteAdeleConj E : 𝔸ᶠ[E] →+* 𝔸ᶠ[E]))ᵀ := by
  ext i j
  simp

end Matrix
