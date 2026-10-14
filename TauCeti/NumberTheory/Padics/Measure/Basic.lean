/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic

/-!
# Pointwise zero for abstract measures

Mathlib's abstract measures inherit their additive group from continuous linear maps.
This file supplies the pointwise-zero instance so that the generic `zero_apply` lemma
simplifies evaluation of the zero measure, just as `add_apply` simplifies sums.
-/

public section

namespace TauCeti

variable {X R E : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module R E]

/-- Evaluation of the zero abstract measure is zero. -/
instance isZeroApply_abstractMeasure : IsZeroApply (AbstractMeasure X R E) C(X, R) E :=
  inferInstanceAs (IsZeroApply (C(X, R) →L[R] E) C(X, R) E)

end TauCeti
