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
If `R` is projective over a coefficient semiring `k` acting compatibly with multiplication
(`IsScalarTower k R R`), the same retraction makes `Re` projective over those coefficients.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., §21.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [Semiring R] {e : R}

/-- A principal idempotent ideal of a semiring that is projective over a compatible coefficient
semiring is projective over those coefficients. The retraction is right multiplication by the
idempotent. -/
theorem projective_span_singleton_restrictScalars {k : Type*} [Semiring k] [Module k R]
    [IsScalarTower k R R] [Module.Projective k R] (he : IsIdempotentElem e) :
    Module.Projective k (Ideal.span {e} : Ideal R) := by
  apply Module.Projective.of_split ((Ideal.span {e} : Ideal R).subtype.restrictScalars k)
    ((LinearMap.toSpanSingleton R _ (TauCeti.spanSingletonGenerator e)).restrictScalars k)
  exact LinearMap.ext (TauCeti.smul_spanSingletonGenerator he)

/-- The principal left ideal of an idempotent is projective: right multiplication by the
idempotent retracts the regular module onto that ideal. -/
theorem projective_span_singleton (he : IsIdempotentElem e) :
    Module.Projective R (Ideal.span {e} : Ideal R) :=
  he.projective_span_singleton_restrictScalars (k := R)

end IsIdempotentElem
