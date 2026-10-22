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
internal direct sum of its summands: the copies `DirectSum.lof R ι M i` of the `M i`, as
`R`-submodules `DirectSum.summand R M i`. When `M` is a graded `R`-algebra, that is
`[DirectSum.GSemiring M] [DirectSum.GAlgebra R M]`, these submodules make `⨁ i, M i` an internally
graded algebra in the sense of `GradedAlgebra`.

Mathlib's constructions with graded rings, such as homogeneous localization and the projective
spectrum `AlgebraicGeometry.Proj`, take an internal grading `𝒜 : ι → Submodule R A` of a ring `A`.
The summand grading is how they apply to a graded ring given externally as a family of homogeneous
components with a graded multiplication, for instance the graded ring `⨁ n, Γ(Aₙ, U)` of sections
of a graded algebra on a scheme.

## Main definitions

* `DirectSum.summand R M i`: the `i`-th summand of `⨁ i, M i`, as an `R`-submodule.
* `DirectSum.instDecompositionSummand`: `⨁ i, M i` decomposes as the direct sum of its
  summands, which form an internal direct sum (`DirectSum.isInternal_summand`), with `i`-th
  component `lof R ι M i (x i)` (`DirectSum.coe_decompose_summand`).
* `DirectSum.instGradedAlgebraSummand`: for a graded `R`-algebra `M`, the summands are a
  grading of the algebra `⨁ i, M i`.
-/

public section

open scoped DirectSum

namespace DirectSum

section Module

variable {ι : Type*} (R : Type*) (M : ι → Type*) [DecidableEq ι] [Semiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The `i`-th summand of the external direct sum `⨁ i, M i`: the image of `M i` under the
inclusion `DirectSum.lof R ι M i`. -/
def summand (i : ι) : Submodule R (⨁ i, M i) :=
  LinearMap.range (DirectSum.lof R ι M i)

variable {R M}

/-- An element of `⨁ i, M i` lies in the `i`-th summand exactly when it is `DirectSum.of M i m`
for some `m : M i`. -/
theorem mem_summand {i : ι} {x : ⨁ i, M i} :
    x ∈ summand R M i ↔ ∃ m : M i, DirectSum.of M i m = x := by
  simp [summand, DirectSum.lof_eq_of]

/-- The element `DirectSum.lof R ι M i m` lies in the `i`-th summand. -/
theorem lof_mem_summand (i : ι) (m : M i) : DirectSum.lof R ι M i m ∈ summand R M i :=
  LinearMap.mem_range_self _ m

/-- The element `DirectSum.of M i m` lies in the `i`-th summand. -/
theorem of_mem_summand (i : ι) (m : M i) : DirectSum.of M i m ∈ summand R M i :=
  mem_summand.mpr ⟨m, rfl⟩

/-- The summands of the external direct sum form an internal direct sum: they are the ranges of
the inclusions `DirectSum.lof R ι M i`. -/
theorem isInternal_summand : DirectSum.IsInternal (summand R M) :=
  TauCeti.DirectSum.isInternal_of_lof
    (e := fun i ↦ LinearEquiv.ofInjective (DirectSum.lof R ι M i) (DirectSum.of_injective i))
    (E := LinearEquiv.refl R _) fun _ _ ↦ rfl

/-- The external direct sum decomposes as the direct sum of its summands. -/
noncomputable instance instDecompositionSummand : DirectSum.Decomposition (summand R M) :=
  isInternal_summand.chooseDecomposition

/-- The `i`-th component of an element `x` of `⨁ i, M i` for the summand decomposition is the
summand `x i`. -/
@[simp]
theorem coe_decompose_summand (x : ⨁ i, M i) (i : ι) :
    (DirectSum.decompose (summand R M) x i : ⨁ i, M i) = DirectSum.of M i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j m =>
    rw [DirectSum.decompose_of_mem (summand R M) (of_mem_summand j m)]
    by_cases h : j = i
    · subst h
      simp
    · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add x y hx hy => simp [hx, hy]

end Module

variable {ι R : Type*} {M : ι → Type*} [DecidableEq ι] [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddMonoid ι] [DirectSum.GSemiring M] [DirectSum.GAlgebra R M]

/-- The summands of the direct sum of a graded algebra are closed under the graded
multiplication. -/
instance instGradedMonoidSummand : SetLike.GradedMonoid (summand R M) where
  one_mem := of_mem_summand 0 _
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    simpa [DirectSum.lof_eq_of, DirectSum.of_mul_of] using of_mem_summand (R := R) _ _

/-- **The direct sum of a graded algebra is internally graded by its summands.** -/
noncomputable instance instGradedAlgebraSummand : GradedAlgebra (summand R M) where

end DirectSum
