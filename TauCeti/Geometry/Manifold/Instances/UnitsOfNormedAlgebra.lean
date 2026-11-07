/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Smooth star on the units of a normed algebra

For a complete normed star algebra over a field with trivial star, the star operation on the
group of units is smooth at every regularity order. This applies in particular to conjugate
transpose on invertible real or complex matrices, viewed as a real smooth map.

## Main declarations

* `Units.contMDiff_star`: star is smooth on the group of units.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 7 (Lie Groups), Basic Definitions, for smooth group operations.
-/

public section

open scoped ContDiff Manifold

namespace Units

variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R] [StarRing R] [ContinuousStar R]
  [StarModule 𝕜 R] {k : ℕ∞ω}

/-- Star on the units of a complete normed star algebra is smooth over a field with trivial star. -/
theorem contMDiff_star : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) k (star : Rˣ → Rˣ) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact (starL' 𝕜 : R ≃L[𝕜] R).contDiff.contMDiff.comp contMDiff_val

end Units
