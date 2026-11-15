/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# The bounded product of unital C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra, `lp.inftyCStarAlgebra`. Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one.

With the closed `c₀` ideal `lp.c0Ideal` of `TauCeti.Analysis.Normed.Lp.C0Ideal`, the quotient
`lp A ∞ ⧸ lp.c0Ideal A` is then a unital C⋆-algebra by `TwoSidedIdeal.Quotient.cstarAlgebra`.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open scoped ENNReal

namespace lp

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end lp
