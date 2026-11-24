/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Ring homomorphisms out of finite-dimensional `ℚ`-algebras

A ring homomorphism between `ℚ`-algebras is automatically `ℚ`-linear (`RingHom.equivRatAlgHom`),
so a finite-dimensional `ℚ`-algebra has only finitely many ring homomorphisms into an integral
domain that is a `ℚ`-algebra. For instance a finite product of number fields has finitely many
complex embeddings.

## Main declarations

* `Finite.ringHom_of_rat`: `R →+* K` is finite for a finite-dimensional `ℚ`-algebra
  `R` and an integral domain `K`.
-/

public section

/-- A finite-dimensional `ℚ`-algebra has finitely many ring homomorphisms into an integral domain:
they are its `ℚ`-algebra homomorphisms, which are linearly independent. -/
instance Finite.ringHom_of_rat {R K : Type*} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R]
    [CommRing K] [IsDomain K] [Algebra ℚ K] : Finite (R →+* K) :=
  .of_equiv _ (RingHom.equivRatAlgHom R K).symm
