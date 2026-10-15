/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Projectivity of principal ideals of idempotents

For an idempotent `e` in a semiring `R`, right multiplication by `e` retracts the regular
module onto its principal left ideal `Re`. Thus `Re` is projective. This is the projectivity
input for constructing projective covers from primitive idempotents.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., §21.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [Semiring R] {e : R}

/-- The principal left ideal of an idempotent is projective: right multiplication by the
idempotent retracts the regular module onto that ideal. -/
theorem projective_span_singleton (he : IsIdempotentElem e) :
    Module.Projective R (Ideal.span {e} : Ideal R) := by
  apply Module.Projective.of_split (Ideal.span {e} : Ideal R).subtype
    (LinearMap.toSpanSingleton R _ (TauCeti.spanSingletonGenerator e))
  apply LinearMap.ext
  intro x
  exact TauCeti.smul_spanSingletonGenerator he x

end IsIdempotentElem
