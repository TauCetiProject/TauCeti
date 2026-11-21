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
so a finite-dimensional `ℚ`-algebra has only finitely many ring homomorphisms into a field that is
a `ℚ`-algebra. For instance a finite product of number fields has finitely many complex embeddings.

## Main declarations

* `RingHom.finite_of_moduleFinite_rat`: `R →+* K` is finite for a finite-dimensional `ℚ`-algebra
  `R` and a field `K`.
-/

public section

namespace RingHom

/-- A finite-dimensional `ℚ`-algebra has finitely many ring homomorphisms into a field: they are
its `ℚ`-algebra homomorphisms, which are linearly independent. -/
instance finite_of_moduleFinite_rat {R K : Type*} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R]
    [Field K] [Algebra ℚ K] : _root_.Finite (R →+* K) :=
  .of_equiv _ (equivRatAlgHom R K).symm

end RingHom
