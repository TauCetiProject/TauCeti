/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.BoundedProduct

/-!
# The C⋆-algebra `∏ₙ M_{n+1} / ⊕ₙ M_{n+1}`

For the family `M n = CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ`, instance search finds the
unital C⋆-algebra structure of `lp.QuotientC0 M = lp M ∞ ⧸ lp.c0Ideal M` and the structures it
projects to, and the quotient norm of `lp.QuotientC0.norm_mk` applies.
-/

public section

open Filter
open scoped ENNReal ComplexOrder

namespace TauCeti.MatrixQuotientC0Example

/-- The matrix algebras `M_{n+1}(ℂ)` with their C⋆-norm. -/
abbrev M (n : ℕ) : Type := CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ

noncomputable example : CStarAlgebra (lp.QuotientC0 M) := inferInstance

noncomputable example : StarRing (lp.QuotientC0 M) := inferInstance

noncomputable example : NormedAlgebra ℂ (lp.QuotientC0 M) := inferInstance

example (a : lp.QuotientC0 M) : ‖star a * a‖ = ‖a‖ * ‖a‖ :=
  CStarRing.norm_star_mul_self

example (a : lp M ∞) : ‖lp.QuotientC0.mk M a‖ = limsup (fun n ↦ ‖a n‖) cofinite :=
  lp.QuotientC0.norm_mk a

end TauCeti.MatrixQuotientC0Example
