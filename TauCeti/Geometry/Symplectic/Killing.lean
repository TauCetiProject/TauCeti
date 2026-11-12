/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Killing
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The Killing form of the symplectic Lie algebra of a symplectic vector space

Let `(V, ω)` be a finite-dimensional real symplectic vector space. Its symplectic Lie algebra
`sp(V, ω)`, the Lie algebra `skewAdjointLieSubalgebra ω.toBilinForm` of endomorphisms skew-adjoint
for `ω`, has trivial radical (`TauCeti.SymplecticForm.hasTrivialRadical_skewAdjointLieSubalgebra`).
This is `LinearMap.BilinForm.IsAlt.hasTrivialRadical_skewAdjointLieSubalgebra` for the
nondegenerate alternating form `ω`. By Cartan's criterion the Killing form of `sp(V, ω)` is then
nondegenerate, so `sp(V, ω)` is a Killing Lie algebra and the theory of Cartan subalgebras of
Killing Lie algebras applies to it.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The symplectic Lie algebra `sp(V, ω)` has trivial radical, so its Killing form is
nondegenerate. -/
instance hasTrivialRadical_skewAdjointLieSubalgebra (ω : SymplecticForm V) :
    LieAlgebra.HasTrivialRadical ℝ (skewAdjointLieSubalgebra ω.toBilinForm) :=
  ω.isAlt.hasTrivialRadical_skewAdjointLieSubalgebra ω.nondegenerate

end TauCeti.SymplecticForm
