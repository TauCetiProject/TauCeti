/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Canonical
public import TauCeti.Algebra.Lie.Killing.Prod
import TauCeti.Algebra.Lie.AdjointAction.Prod
import TauCeti.LinearAlgebra.End.Prod

/-!
# The internal Jordan decomposition of a product

For finite-dimensional Killing Lie algebras `L` and `L'` over an algebraically closed field, the
product `L × L'` is again Killing, and its internal Jordan decomposition is computed factor by
factor: the nilpotent and semisimple parts of `(x, x')` are the pairs of the nilpotent and
semisimple parts of `x` and `x'`. Since the adjoint action of the product is the componentwise
product of the adjoint actions, componentwise nilpotence and semisimplicity give a commuting
decomposition of the right kind, and the uniqueness characterization of the canonical parts does
the rest.

## Main statements

* `TauCeti.LieAlgebra.jordanDecomposition_prod`: the internal Jordan decomposition of a product.
* `TauCeti.LieAlgebra.nilpotentPart_prod` and `TauCeti.LieAlgebra.semisimplePart_prod`: the
  nilpotent and semisimple parts of an element of a product.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.4.
-/

public section

open LieAlgebra Module.End

namespace TauCeti.LieAlgebra

variable (K : Type*) {L L' : Type*} [Field K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L'] [IsKilling K L']

/-- The internal Jordan decomposition of an element of a product is computed in each factor. -/
theorem jordanDecomposition_prod (x : L × L') :
    jordanDecomposition K x =
      ((nilpotentPart K x.1, nilpotentPart K x.2),
        (semisimplePart K x.1, semisimplePart K x.2)) := by
  symm
  refine (eq_jordanDecomposition_iff K x _ _).2 ⟨?_, ?_, ?_, ?_⟩
  · rw [ad_prod]
    exact (isNilpotent_ad_nilpotentPart K x.1).prodMap (isNilpotent_ad_nilpotentPart K x.2)
  · rw [ad_prod]
    exact (isSemisimple_ad_semisimplePart K x.1).prodMap (isSemisimple_ad_semisimplePart K x.2)
  · simp
  · ext <;> simp

/-- The nilpotent part of an element of a product is the pair of the nilpotent parts of its
coordinates. -/
@[simp]
theorem nilpotentPart_prod (x : L × L') :
    nilpotentPart K x = (nilpotentPart K x.1, nilpotentPart K x.2) := by
  rw [nilpotentPart_def, jordanDecomposition_prod]

/-- The semisimple part of an element of a product is the pair of the semisimple parts of its
coordinates. -/
@[simp]
theorem semisimplePart_prod (x : L × L') :
    semisimplePart K x = (semisimplePart K x.1, semisimplePart K x.2) := by
  rw [semisimplePart_def, jordanDecomposition_prod]

end TauCeti.LieAlgebra
