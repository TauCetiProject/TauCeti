/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Star.NonUnitalSubalgebra.Finite

/-!
# Finite-dimensional nonunital `⋆`-subalgebras are closed

A finite-dimensional nonunital `⋆`-subalgebra of a Hausdorff topological `⋆`-algebra over a
complete nontrivially normed field is closed, since its underlying submodule is.

## Main statements

* `NonUnitalStarSubalgebra.isClosed_of_finiteDimensional`: finite-dimensional nonunital
  `⋆`-subalgebras are closed.
-/

public section

namespace NonUnitalStarSubalgebra

/-- A finite-dimensional nonunital `⋆`-subalgebra of a Hausdorff topological `⋆`-algebra over a
complete field is closed. -/
theorem isClosed_of_finiteDimensional {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NonUnitalNonAssocRing A] [Star A] [TopologicalSpace A] [T2Space A] [IsTopologicalAddGroup A]
    [Module 𝕜 A] [ContinuousSMul 𝕜 A] (S : NonUnitalStarSubalgebra 𝕜 A) [FiniteDimensional 𝕜 S] :
    IsClosed (S : Set A) :=
  have := finite_toSubmodule.2 ‹FiniteDimensional 𝕜 S›
  S.toNonUnitalSubalgebra.toSubmodule.isClosed_of_finiteDimensional

end NonUnitalStarSubalgebra
