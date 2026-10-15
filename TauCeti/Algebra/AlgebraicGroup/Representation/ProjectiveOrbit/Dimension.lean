/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Krull dimension of projective orbits

The projective orbit scheme of a line is a locally closed subscheme of projective space whose
underlying set is the orbit, the full image of the projective orbit morphism. Since an
immersion is a homeomorphism onto its image, the orbit scheme and the orbit have the same Krull
dimension. The orbit has finite Krull dimension because projective space over a field is
quasi-compact and of finite type. Only finite-dimensionality of the representation is needed
for the latter.

## Main declarations

* `TauCeti.Comodule.topologicalKrullDim_projectiveOrbitScheme`: the orbit scheme has the Krull
  dimension of the orbit.
* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_ne_top`: the orbit has finite
  Krull dimension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

section Range

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The orbit of a line, the image of its projective orbit morphism, has finite Krull
dimension. No finiteness or algebraic closedness hypothesis is needed beyond finite
dimensionality of the representation. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_ne_top
    (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) ≠ ⊤ :=
  ne_top_of_le_ne_top (TauCeti.AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType
    (SymmetricAlgebra.projToSpec k (Module.Dual k M))) (topologicalKrullDim_subspace_le _ _)

end Range

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- The projective orbit scheme of a line has the Krull dimension of the orbit. -/
theorem topologicalKrullDim_projectiveOrbitScheme (m : M) (hm : Module.IsUnimodular k m) :
    topologicalKrullDim (projectiveOrbitScheme (H := H) m hm) =
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  rw [← range_projectiveOrbitι,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_range_of_isPreimmersion]

end TauCeti.Comodule
