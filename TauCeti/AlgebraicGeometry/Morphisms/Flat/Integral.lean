/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced

/-!
# Descent of integrality along a flat surjective morphism

Integrality of a scheme descends along any flat surjective morphism, with no Noetherian
assumption: reducedness descends by `AlgebraicGeometry.Scheme.Hom.isReduced_of_flat_of_surjective`,
and irreducibility is pushed forward by surjectivity.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Integrality of a scheme descends along any flat surjective morphism, with no Noetherian
assumption. -/
theorem isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsIntegral X] : IsIntegral Y :=
  have := f.isReduced_of_flat_of_surjective
  have := f.surjective.irreducibleSpace f.continuous
  isIntegral_of_irreducibleSpace_of_isReduced Y

end AlgebraicGeometry

end TauCeti
