/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Boundaryless models with corners

A model with corners on a zero-dimensional vector space has no boundary
(`ModelWithCorners.boundaryless_of_subsingleton`): its range is the whole one-point space.
-/

public section

namespace ModelWithCorners

/-- A model with corners on a zero-dimensional vector space has no boundary. -/
instance boundaryless_of_subsingleton {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : I.Boundaryless :=
  ⟨Set.eq_univ_of_forall fun x ↦ ⟨I.symm x, Subsingleton.elim _ _⟩⟩

end ModelWithCorners
