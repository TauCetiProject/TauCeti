/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.C1OffFinitePath

/-!
# Closed piecewise `C¹` curves and immersions (Hungerbühler–Wasem)

This file defines the paper-faithful notion of a closed piecewise `C¹` curve and
immersion in the sense of Hungerbühler–Wasem (arXiv:1808.00997v2, page 3):

> A closed piecewise `C¹` immersion `Λ : [a, b] → ℂ` is a closed curve such that
> there is a partition `a = a₀ < a₁ < … < aₙ = b` with `Λ|_{[aₖ, aₖ₊₁]}` of class
> `C¹` and `Λ̇|_{[aₖ, aₖ₊₁]} ≠ 0` for all `k = 0, …, n − 1`.

The regularity here is genuine `C¹` regularity **on each closed piece**, and the
immersion condition is non-vanishing of the derivative **on each closed piece,
including the piece endpoints**. This is strictly stronger than the base carriers
`C1OffFinitePathOn` / `C1OffFinitePath`, which only require differentiability with a
continuous derivative on the *open* interiors between breakpoints. Those carriers are
the raw substrate; `ClosedPwC1Curve` / `ClosedPwC1Immersion` are the mathematically
faithful curve types the residue theorem is stated for.

## Main definitions

* `Finset.IsConsecutive S a b` — `(a, b)` are consecutive members of `S`: both lie in
  `S`, `a < b`, and no element of `S` lies strictly between them.
* `ClosedPwC1Curve x` — a closed path at `x` with a partition `0 = a₀ < … < aₙ = 1`
  (endpoints included) such that the path is `C¹` on each closed sub-interval
  `[aₖ, aₖ₊₁]`.
* `ClosedPwC1Immersion x` — a `ClosedPwC1Curve x` whose within-piece derivative is
  non-vanishing on each closed sub-interval, including the endpoints.

## Design notes

`ClosedPwC1Curve` extends `C1OffFinitePath x x`. The inherited `partition` field is the
open-interior (`Ioo`-style) partition; the new `closedPartition` is the `Icc`-style
partition with the endpoints `0` and `1` adjoined, tied together by
`closedPartition_eq`. The non-vanishing condition uses `derivWithin _ (Icc a b)` rather
than the global `deriv`, because at a corner partition point the global `deriv` is `0`
by the mathlib convention (the function is not differentiable there), which would
spuriously contradict non-vanishing.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997v2, page 3.
-/

public section

noncomputable section

open Set Filter Topology

/-- The pair `(a, b)` are *consecutive* members of `S : Finset ℝ` when both lie in `S`,
`a < b`, and no element of `S` lies strictly between them. -/
def Finset.IsConsecutive (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, c ∉ Set.Ioo a b

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **closed piecewise `C¹` curve** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a path `[0, 1] → E` returning to its starting point,
together with a partition `0 = a₀ < a₁ < … < aₙ = 1` whose endpoints are included, such
that the path is `C¹` on each *closed* sub-interval `[aₖ, aₖ₊₁]`.

This extends `C1OffFinitePath x x`. The inherited `partition` field is the `Ioo`-style
(open-interior) partition, while `closedPartition` is the `Icc`-style partition with
endpoints included; the two are related by `closedPartition_eq`. -/
@[ext]
structure ClosedPwC1Curve (x : E) extends C1OffFinitePath x x where
  /-- Closed partition *with* endpoints. Required because the inherited `partition` is
  `Ioo`-style (interior only). -/
  closedPartition : Finset ℝ
  /-- `0` is a closed-partition point. -/
  zero_mem_closedPartition : (0 : ℝ) ∈ closedPartition
  /-- `1` is a closed-partition point. -/
  one_mem_closedPartition : (1 : ℝ) ∈ closedPartition
  /-- Every closed-partition point lies in `[0, 1]`. -/
  closedPartition_subset : (closedPartition : Set ℝ) ⊆ Icc 0 1
  /-- The closed partition is the `Ioo`-style `partition` with `0` and `1` adjoined. -/
  closedPartition_eq : closedPartition = insert 0 (insert 1 partition)
  /-- On every closed sub-interval `[a, b]` whose endpoints are consecutive
  closed-partition members, the extended path is `C¹`. -/
  contDiffOn_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ContDiffOn ℝ 1 toPath.extend (Icc a b)

/-- A **closed piecewise `C¹` immersion** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a closed piecewise `C¹` curve whose derivative is
non-vanishing on every closed sub-interval between consecutive partition points. -/
@[ext]
structure ClosedPwC1Immersion (x : E) extends ClosedPwC1Curve x where
  /-- On every closed sub-interval between consecutive closed-partition members, the
  *within*-derivative of the extended path is non-zero — i.e. `Λ̇|_{[aₖ, aₖ₊₁]} ≠ 0` in
  the paper. We use `derivWithin _ (Icc a b)` rather than the global `deriv` because at
  corner partition points the global `deriv` is `0` by the mathlib convention (the
  function is not differentiable there), which would spuriously contradict
  non-vanishing. -/
  derivWithin_ne_zero_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ∀ t ∈ Icc a b, derivWithin toPath.extend (Icc a b) t ≠ 0

namespace ClosedPwC1Curve

variable {x : E}

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : ClosedPwC1Curve x) : Continuous γ.toPath.extend :=
  γ.toPath.continuous_extend

/-- Membership in the inherited `Ioo`-style `partition` is equivalent to lying in
`closedPartition` while not being an endpoint. -/
theorem mem_partition_iff (γ : ClosedPwC1Curve x) {t : ℝ} :
    t ∈ γ.partition ↔ t ∈ γ.closedPartition ∧ t ≠ 0 ∧ t ≠ 1 := by
  refine ⟨fun ht ↦ ?_, fun ⟨h_in, h_ne0, h_ne1⟩ ↦ ?_⟩
  · have h_in_Ioo : t ∈ Ioo (0 : ℝ) 1 := γ.partition_subset ht
    exact ⟨γ.closedPartition_eq ▸ by simp [Finset.mem_insert, ht],
      ne_of_gt h_in_Ioo.1, ne_of_lt h_in_Ioo.2⟩
  · rw [γ.closedPartition_eq, Finset.mem_insert, Finset.mem_insert] at h_in
    exact h_in.resolve_left h_ne0 |>.resolve_left h_ne1

end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : ClosedPwC1Immersion x) : Continuous γ.toPath.extend :=
  γ.toClosedPwC1Curve.continuous

end ClosedPwC1Immersion

end TauCeti.Contour

end
