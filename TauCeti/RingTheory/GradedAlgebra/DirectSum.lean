/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# The external direct sum of a graded algebra as an internally graded algebra

Let `M : ι → Type*` be a family of `R`-modules. Its external direct sum `⨁ i, M i` is the
internal direct sum of its summands `DirectSum.summand R M i`, the copies
`DirectSum.lof R ι M i` of the `M i` (`DirectSum.isInternal_summand`). When `M` is a graded
`R`-algebra, that is `[DirectSum.GSemiring M] [DirectSum.GAlgebra R M]`, these submodules make
`⨁ i, M i` an internally graded algebra in the sense of `GradedAlgebra`.

Mathlib's constructions with graded rings, such as homogeneous localization and the projective
spectrum `AlgebraicGeometry.Proj`, take an internal grading `𝒜 : ι → Submodule R A` of a ring `A`.
The summand grading is how they apply to a graded ring given externally as a family of homogeneous
components with a graded multiplication, for instance the graded ring `⨁ n, Γ(Aₙ, U)` of sections
of a graded algebra on a scheme.

## Main definitions

* `DirectSum.instGradedAlgebraSummand`: for a graded `R`-algebra `M`, the summands are a
  grading of the algebra `⨁ i, M i`.
-/

public section

open scoped DirectSum

namespace DirectSum

variable {ι R : Type*} {M : ι → Type*} [DecidableEq ι] [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddMonoid ι] [DirectSum.GSemiring M] [DirectSum.GAlgebra R M]

/-- The summands of the direct sum of a graded algebra are closed under the graded
multiplication. -/
instance instGradedMonoidSummand : SetLike.GradedMonoid (summand R M) where
  one_mem := of_mem_summand 0 _
  mul_mem := by
    rintro i j _ _ ha hb
    obtain ⟨a, rfl⟩ := mem_summand.mp ha
    obtain ⟨b, rfl⟩ := mem_summand.mp hb
    simpa [DirectSum.of_mul_of] using of_mem_summand (R := R) _ _

/-- **The direct sum of a graded algebra is internally graded by its summands.** -/
noncomputable instance instGradedAlgebraSummand : GradedAlgebra (summand R M) where

end DirectSum
