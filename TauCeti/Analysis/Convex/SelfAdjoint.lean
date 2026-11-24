/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.Convex.Basic

/-!
# Convexity of self-adjoint parts of submodules and star subalgebras

In a `⋆`-module over a semiring `𝕜`, scalars from an ordered semiring `R` with trivial involution
acting compatibly through `𝕜` commute with the involution. Consequently, the self-adjoint part
`(S : Set A) ∩ selfAdjoint A` of any `𝕜`-submodule (`Submodule.convex_inter_selfAdjoint`) and in
particular of any unital `⋆`-subalgebra (`StarSubalgebra.convex_inter_selfAdjoint`) is `R`-convex.

For algebras of bounded operators over `ℝ` or `ℂ`, this provides the real convexity of the
self-adjoint part used to compare closures in locally convex operator topologies.
-/

public section

namespace Submodule

/-- The self-adjoint part of a `𝕜`-submodule of a `⋆`-module is convex over any ordered scalar
semiring `R` with trivial involution acting compatibly through `𝕜`. -/
theorem convex_inter_selfAdjoint {𝕜 A : Type*} [Semiring 𝕜] [StarMul 𝕜] [AddCommGroup A]
    [StarAddMonoid A] [Module 𝕜 A] [StarModule 𝕜 A] (S : Submodule 𝕜 A) (R : Type*)
    [Semiring R] [PartialOrder R] [StarMul R] [TrivialStar R] [SMul R 𝕜] [Module R A]
    [IsScalarTower R 𝕜 A] [StarModule R 𝕜] :
    Convex R ((S : Set A) ∩ selfAdjoint A) := by
  -- Scalars in `R` act through `𝕜`, so they commute with `star` and `selfAdjoint.submodule R`
  -- applies without requiring a pre-existing `StarModule R A` instance.
  have : StarModule R A := ⟨fun r a ↦ by
    rw [← smul_one_smul 𝕜 r a, star_smul, star_smul, star_one, smul_one_smul]⟩
  exact (S.restrictScalars R).convex.inter (selfAdjoint.submodule R A).convex

end Submodule

namespace StarSubalgebra

/-- The self-adjoint part of a unital `⋆`-subalgebra over `𝕜` is convex over any ordered scalar
semiring `R` with trivial involution acting compatibly through `𝕜`. -/
theorem convex_inter_selfAdjoint {𝕜 A : Type*} [CommSemiring 𝕜] [StarRing 𝕜] [Ring A]
    [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] (S : StarSubalgebra 𝕜 A) (R : Type*)
    [Semiring R] [PartialOrder R] [StarMul R] [TrivialStar R] [SMul R 𝕜] [Module R A]
    [IsScalarTower R 𝕜 A] [StarModule R 𝕜] :
    Convex R ((S : Set A) ∩ selfAdjoint A) :=
  S.toSubalgebra.toSubmodule.convex_inter_selfAdjoint R

end StarSubalgebra
