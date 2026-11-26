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
(`CliffordAlgebra.star_smul`) and does not conjugate scalars. Over scalars with trivial star that
act through the coefficient ring, such as `ℝ` acting on a real or a complex Clifford algebra, this
is exactly the `StarModule` law. It is recorded here as a theorem rather than a global instance,
since over a coefficient ring with nontrivial star Clifford conjugation is not a `StarModule`;
consumers enable it locally, for instance to equip the complexification `ℂ ⊗[ℝ] Cℓ(V, Q)` of a real
Clifford algebra with Mathlib's tensor-product `star`.
-/

public section

namespace CliffordAlgebra

/-- Clifford conjugation makes a Clifford algebra a star module over every type of scalars `S`
with trivial star that acts through the coefficient ring, in the sense of
`IsScalarTower S R (CliffordAlgebra Q)`. For `S` the coefficient ring itself this needs a trivial
star on the coefficients, as over `ℝ`; for `S = ℝ` and complex coefficients it says that complex
Clifford conjugation is real-linear. This is a theorem rather than an instance; enable it with
`attribute [local instance]`. -/
theorem starModule_of_trivialStar {S R M : Type*} [Star S] [TrivialStar S] [CommRing R]
    [AddCommGroup M] [Module R M] {Q : QuadraticForm R M} [SMul S R]
    [SMul S (CliffordAlgebra Q)] [IsScalarTower S R (CliffordAlgebra Q)] :
    StarModule S (CliffordAlgebra Q) where
  star_smul s x := by
    rw [star_trivial s, ← smul_one_smul R s x, CliffordAlgebra.star_smul, smul_one_smul]

end CliffordAlgebra
