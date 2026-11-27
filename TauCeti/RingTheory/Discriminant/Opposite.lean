/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Discriminant.Regular
import TauCeti.RingTheory.Trace.Regular.Opposite

/-!
# Regular discriminants of opposite algebras

Passing to an opposite algebra preserves regular-trace discriminants when the ambient regular
trace form is nondegenerate. This comparison underlies the right class-index bound in Masser
and Wüstholz, *Factorization estimates for abelian varieties*, §3, last paragraph.
-/

public section

open MulOpposite

namespace Algebra

variable {K A ι : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Fintype ι] [DecidableEq ι]

/-- Passing to the opposite algebra preserves the regular discriminant of every finite family. -/
@[simp]
theorem regularDiscr_op (hB : (regularTraceForm K A).Nondegenerate) (b : ι → A) :
    regularDiscr K (op ∘ b) = regularDiscr K b := by
  simp only [regularDiscr_def, Function.comp_apply, regularTraceForm_op hB]

end Algebra
