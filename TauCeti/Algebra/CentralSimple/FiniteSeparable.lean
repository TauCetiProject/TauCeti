/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the finite descent theorem and the separable-closure and intermediate-field API occur in
-- the exported theorem.
public import TauCeti.Algebra.CentralSimple.SplittingDescent

/-!
# Finite separable splitting fields

Every finite-dimensional central simple algebra over a field has a finite separable splitting
field. The separable closure splits the algebra, and finite descent produces a finite intermediate
field which is automatically separable over the base field.

## Main result

* `TauCeti.Algebra.exists_isSplittingField_finiteDimensional_isSeparable`: every
  finite-dimensional central simple algebra has a finite separable splitting field.

## References

See P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2,
and R. S. Pierce, *Associative Algebras*, Chapter 13.
-/

public section

namespace TauCeti

namespace Algebra

universe u w

variable (K : Type u) [Field K] (A : Type w) [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- **Every finite-dimensional central simple algebra has a finite separable splitting field.**

The result exposes a finite intermediate field of the separable closure which splits the algebra.
It is automatically separable over `K` by the intermediate-field instance. -/
theorem exists_isSplittingField_finiteDimensional_isSeparable :
    ∃ L : IntermediateField K (SeparableClosure K),
      FiniteDimensional K L ∧ IsSplittingField K A L :=
  exists_intermediateField_isSplittingField_finiteDimensional (K := K) (A := A)
    (isSplittingField_of_isSepClosed K A (SeparableClosure K))

end Algebra

end TauCeti

end
