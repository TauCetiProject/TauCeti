/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Projection
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Infinite and properly infinite projections

A projection `p` of a star-ordered ring is **infinite** (`TauCeti.IsInfiniteProjection`) if it
is Murray–von Neumann equivalent to a proper subprojection of itself: some `v` has `v⋆v = p`,
`vv⋆ ≤ p` and `vv⋆ ≠ p`. It is **properly infinite** (`TauCeti.IsProperlyInfiniteProjection`) if
it contains two orthogonal subprojections each equivalent to `p`: some `v, w` have
`v⋆v = w⋆w = p`, `vv⋆ ≤ p`, `ww⋆ ≤ p` and `vv⋆ · ww⋆ = 0` (Rørdam, §4.1).

Nonzeroness is kept explicit: `p = 0` is properly infinite but not infinite. In a ring with a
proper star (for instance a C⋆-algebra) an infinite projection is nonzero
(`TauCeti.IsInfiniteProjection.ne_zero`), while `p = 0` is properly infinite
(`TauCeti.isProperlyInfiniteProjection_zero`). A nonzero properly infinite projection is infinite
(`TauCeti.IsProperlyInfiniteProjection.isInfiniteProjection`): if `vv⋆ = p`, then `ww⋆ ≤ p` and
`p · ww⋆ = 0` force `ww⋆ = 0`, hence `w = 0` and `p = w⋆w = 0`.

The matrix algebra `M_n(𝕜)` over `𝕜 = ℝ` or `ℂ` has no infinite projection
(`Matrix.not_isInfiniteProjection`): `p - vv⋆` is positive semidefinite with trace
`tr(v⋆v) - tr(vv⋆) = 0`, so `vv⋆ = p`.

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

namespace TauCeti

variable {R : Type*} [NonUnitalRing R] [StarRing R] [PartialOrder R]

/-- A projection `p` is **infinite** if it is Murray–von Neumann equivalent to a proper
subprojection: some `v` has `v⋆v = p`, `vv⋆ ≤ p` and `vv⋆ ≠ p`. -/
def IsInfiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧ ∃ v : R, star v * v = p ∧ v * star v ≤ p ∧ v * star v ≠ p

/-- A projection `p` is **properly infinite** if it contains two orthogonal subprojections each
Murray–von Neumann equivalent to `p`. The zero projection is properly infinite. -/
def IsProperlyInfiniteProjection (p : R) : Prop :=
  IsStarProjection p ∧ ∃ v w : R, star v * v = p ∧ star w * w = p ∧
    v * star v ≤ p ∧ w * star w ≤ p ∧ v * star v * (w * star w) = 0

/-- Unfold the definition of an infinite projection. -/
theorem isInfiniteProjection_iff {p : R} : IsInfiniteProjection p ↔
    IsStarProjection p ∧ ∃ v : R, star v * v = p ∧ v * star v ≤ p ∧ v * star v ≠ p :=
  Iff.rfl

/-- Unfold the definition of a properly infinite projection. -/
theorem isProperlyInfiniteProjection_iff {p : R} : IsProperlyInfiniteProjection p ↔
    IsStarProjection p ∧ ∃ v w : R, star v * v = p ∧ star w * w = p ∧
      v * star v ≤ p ∧ w * star w ≤ p ∧ v * star v * (w * star w) = 0 :=
  Iff.rfl

/-- An infinite projection is a star projection. -/
theorem IsInfiniteProjection.isStarProjection {p : R} (hp : IsInfiniteProjection p) :
    IsStarProjection p :=
  hp.1

/-- A properly infinite projection is a star projection. -/
theorem IsProperlyInfiniteProjection.isStarProjection {p : R}
    (hp : IsProperlyInfiniteProjection p) : IsStarProjection p :=
  hp.1

/-- The zero projection is properly infinite, with `v = w = 0`. -/
@[simp]
theorem isProperlyInfiniteProjection_zero : IsProperlyInfiniteProjection (0 : R) :=
  ⟨.zero R, 0, 0, by simp⟩

/-- An infinite projection is nonzero. -/
theorem IsInfiniteProjection.ne_zero [IsProperStar R] {p : R} (hp : IsInfiniteProjection p) :
    p ≠ 0 := by
  rintro rfl
  obtain ⟨-, v, hv, -, hne⟩ := hp
  rw [star_mul_self_eq_zero] at hv
  simp [hv] at hne

/-- The zero projection is not infinite, although it is properly infinite. -/
@[simp]
theorem not_isInfiniteProjection_zero [IsProperStar R] : ¬ IsInfiniteProjection (0 : R) :=
  fun h ↦ h.ne_zero rfl

variable [StarOrderedRing R] [IsProperStar R]

/-- A nonzero properly infinite projection is infinite. -/
theorem IsProperlyInfiniteProjection.isInfiniteProjection {p : R}
    (h : IsProperlyInfiniteProjection p) (hp : p ≠ 0) : IsInfiniteProjection p := by
  obtain ⟨hpp, v, w, hv, hw, hvp, hwp, hvw⟩ := h
  refine ⟨hpp, v, hv, hvp, fun hvv ↦ hp ?_⟩
  have hwproj := (isPartialIsometry_iff_isStarProjection_star_mul_self.mpr
    (hw ▸ hpp)).isStarProjection_mul_star_self
  have hw0 : w * star w = 0 := by
    rw [← (hwproj.le_iff_mul_eq_right hpp).mp hwp, ← hvv, hvw]
  rw [mul_star_self_eq_zero] at hw0
  rw [← hw, hw0, star_zero, zero_mul]

/-! ### Matrix algebras -/

open scoped MatrixOrder

/-- The matrix algebra `M_n(𝕜)` has no infinite projection. -/
theorem _root_.Matrix.not_isInfiniteProjection {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (p : _root_.Matrix n n 𝕜) : ¬ IsInfiniteProjection p := by
  -- `p - vv⋆` is positive semidefinite of trace `tr(v⋆v) - tr(vv⋆) = 0`, so `vv⋆ = p`.
  rintro ⟨-, v, hv, hle, hne⟩
  refine hne (sub_eq_zero.mp ?_).symm
  refine ((_root_.Matrix.le_iff.mp hle).trace_eq_zero_iff).mp ?_
  rw [_root_.Matrix.trace_sub, ← hv, _root_.Matrix.trace_mul_comm, sub_self]

end TauCeti
