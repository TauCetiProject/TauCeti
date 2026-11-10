/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.PositiveDegrees.Basic

/-!
# Positive gradings

Let `d` be positive degree data on `N`, with allowed monoid `P` and degree `δ`. A family of
submodules `ℳ n` is a positive grading for `d` (`TauCeti.IsPositiveGrading`) when `ℳ n = 0`
unless `n` is a nonzero element of `P`. Nonzero homogeneous elements of a positive grading then
have strictly positive degree. Positivity passes to the internal grading of a decomposition and to
quotients by homogeneous submodules.

## Main definitions

* `TauCeti.IsPositiveGrading`: the pieces outside the nonzero allowed degrees vanish.

## Main results

* `TauCeti.IsPositiveGrading.degree_pos`: nonzero homogeneous elements have positive degree.
* `TauCeti.IsPositiveGrading.quotient`: the quotient of a positive grading by a homogeneous
  submodule is positive.
-/

public section

open DirectSum

namespace TauCeti

section Grading

variable {N R M : Type*} [AddCommMonoid N] [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family of submodules indexed by `N` is a positive grading for the positive degree data `d`
when its pieces vanish outside the nonzero allowed degrees, that is, unless the index lies in
`d.monoid` and is nonzero. -/
class IsPositiveGrading (d : PositiveDegrees N) (ℳ : N → Submodule R M) : Prop where
  /-- The pieces indexed outside the allowed monoid vanish. -/
  eq_bot_of_notMem : ∀ ⦃n⦄, n ∉ d.monoid → ℳ n = ⊥
  /-- The piece of degree zero vanishes. -/
  eq_bot_zero : ℳ 0 = ⊥

variable (d : PositiveDegrees N) (ℳ : N → Submodule R M) [IsPositiveGrading d ℳ]

/-- A nonzero homogeneous element of a positive grading has strictly positive degree. -/
theorem IsPositiveGrading.degree_pos {n : N} {x : M} (hx : x ∈ ℳ n) (hx0 : x ≠ 0) :
    0 < d.degree n := by
  by_cases hn : n ∈ d.monoid
  · refine d.degree_pos hn fun hn0 ↦ hx0 ?_
    rw [hn0, IsPositiveGrading.eq_bot_zero (d := d) (ℳ := ℳ)] at hx
    exact (Submodule.mem_bot R).1 hx
  · rw [IsPositiveGrading.eq_bot_of_notMem (d := d) (ℳ := ℳ) hn] at hx
    exact absurd ((Submodule.mem_bot R).1 hx) hx0

/-- A homogeneous element of a positive grading whose degree is not positive vanishes. -/
theorem IsPositiveGrading.eq_zero_of_degree_nonpos {n : N} {x : M} (hx : x ∈ ℳ n)
    (hn : d.degree n ≤ 0) : x = 0 := by
  by_contra hx0
  exact absurd (IsPositiveGrading.degree_pos d ℳ hx hx0) (not_lt.2 hn)

end Grading

section InternalGrading

variable {N : Type} {R M : Type*} [AddCommMonoid N] [DecidableEq N] (d : PositiveDegrees N)

/-- The internal grading carried by a positive decomposition is positive. -/
instance IsPositiveGrading.ofDecomposition [Semiring R] [AddCommMonoid M] [Module R M]
    (ℳ : N → Submodule R M) [Decomposition ℳ] [IsPositiveGrading d ℳ] :
    IsPositiveGrading d (InternalGrading.ofDecomposition ℳ).piece := by
  rwa [InternalGrading.ofDecomposition_piece]

variable {S : Type*} [Ring R] [Ring S] [SMul R S] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- The quotient of a positive grading by a homogeneous submodule is positive. In particular,
the truncations of a positively graded Lie algebra are positively graded. -/
instance IsPositiveGrading.quotient (G : InternalGrading R M N) [IsPositiveGrading d G.piece]
    (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U) :
    IsPositiveGrading d (G.quotient U hU).piece where
  eq_bot_of_notMem n hn := by
    rw [InternalGrading.quotient_piece,
      IsPositiveGrading.eq_bot_of_notMem (d := d) (ℳ := G.piece) hn, Submodule.map_bot]
  eq_bot_zero := by
    rw [InternalGrading.quotient_piece, IsPositiveGrading.eq_bot_zero (d := d) (ℳ := G.piece),
      Submodule.map_bot]

end InternalGrading

end TauCeti
