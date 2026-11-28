/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.HahnSeries.BoundedDenominators
public import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# Bounded denominators under `X ↦ X ^ d`

The substitution `X ↦ X ^ d` of Laurent series (`LaurentSeries.expand`) preserves and reflects
bounded denominators (`HahnSeries.HasBoundedDenominators`), so whether a Laurent series has
bounded denominators does not depend on the choice of a root of the expansion variable.

## Main results

* `LaurentSeries.hasBoundedDenominators_expand_iff`: `expand A d f` has bounded denominators
  exactly when `f` does.
-/

public section

open scoped LaurentSeries

namespace LaurentSeries

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The substitution `X ↦ X ^ d` preserves and reflects bounded denominators: it moves the
coefficient of `X ^ k` to `X ^ (d * k)` and fills in zeros. -/
@[simp]
theorem hasBoundedDenominators_expand_iff (d : ℕ+) {f : A⸨X⸩} :
    (expand A d f).HasBoundedDenominators R ↔ f.HasBoundedDenominators R := by
  rw [expand_apply, HahnSeries.hasBoundedDenominators_embDomain_iff]

end LaurentSeries
