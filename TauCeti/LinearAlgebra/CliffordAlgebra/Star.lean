/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Star

/-!
# Clifford conjugation as a star module structure

Mathlib's Clifford conjugation `star = reverse ∘ involute` is linear over the coefficient ring
(`CliffordAlgebra.star_smul`) and does not conjugate scalars. Over a coefficient ring with trivial
star, such as `ℝ`, this is exactly the `StarModule` law. It is recorded here as a theorem rather
than a global instance, since over a coefficient ring with nontrivial star Clifford conjugation is
not a `StarModule`; consumers enable it locally, for instance to equip the complexification
`ℂ ⊗[ℝ] Cℓ(V, Q)` of a real Clifford algebra with Mathlib's tensor-product `star`.
-/

public section

namespace CliffordAlgebra

/-- Over a coefficient ring with trivial star, Clifford conjugation makes a Clifford algebra a
star module. This is a theorem rather than an instance; enable it with
`attribute [local instance]`. -/
theorem starModule_of_trivialStar {R M : Type*} [CommRing R] [StarRing R] [TrivialStar R]
    [AddCommGroup M] [Module R M] {Q : QuadraticForm R M} : StarModule R (CliffordAlgebra Q) where
  star_smul r x := by rw [CliffordAlgebra.star_smul, star_trivial r]

end CliffordAlgebra
