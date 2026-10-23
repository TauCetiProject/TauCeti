/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FinGroupCharZero
public import TauCeti.CategoryTheory.Simple.Endomorphism

/-!
# The endomorphism-division criterion over arbitrary fields

For a finite group whose order is nonzero in the coefficient field, a finite-dimensional
representation is simple exactly when its endomorphism ring is nontrivial and every nonzero
endomorphism is a unit. In particular this applies to induced representations, without
requiring the coefficient field to split the group algebra. Over a nonsplitting field, a
simple representation can have endomorphisms of dimension greater than one.

Maschke's theorem supplies injectivity of every finite-dimensional representation, so the
categorical converse to Schur's lemma applies. Neither characteristic zero nor algebraic
closure is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*.
* Mathlib's injective-object instance in `Mathlib.RepresentationTheory.FinGroupCharZero`.
-/

public section

open CategoryTheory

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]

/-- Over any field in which the group order is nonzero, a representation is simple exactly
when its endomorphism ring is nontrivial and all its nonzero endomorphisms are invertible.
Applied to `TauCeti.indFDRep A`, this is the endomorphism-division criterion for induction. -/
theorem simple_iff_nontrivial_end_and_isUnit (V : FDRep k G) :
    Simple V ↔ Nontrivial (End V) ∧ ∀ f : End V, f ≠ 0 → IsUnit f :=
  CategoryTheory.simple_iff_nontrivial_end_and_isUnit V

end FDRep
