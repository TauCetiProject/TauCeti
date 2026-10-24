/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Spherically complete spaces

A pseudometric space is *spherically complete* if every decreasing sequence of closed balls has a
common point. Unlike completeness, the radii are not required to tend to zero. For a
nonarchimedean field this is the hypothesis of the nonarchimedean Hahn–Banach theorem, and
Bhatt and Scholze use it to show that bounded lattices saturated with respect to the maximal
ideal are finite free.

Every proper space, for instance every locally compact nonarchimedean field such as `ℚ_p`, is
spherically complete. The field `ℂ_p` is complete but not spherically complete.

## Main definitions

* `TauCeti.SphericallyCompleteSpace α`: every decreasing sequence of closed balls in `α` with
  nonnegative radii has nonempty intersection.

## Main results

* `TauCeti.SphericallyCompleteSpace.exists_forall_mem_of_dist_le`: in a spherically complete
  ultrametric space `X`, let `A n` be sets of families `ι → X` and `r` an antitone sequence of
  nonnegative radii. Suppose that each `A n` contains the closed polydisc of radius `r n` about
  each of its points, that every point of `A n` is within `r n` of a point of `A (n + 1)`, and
  that `A 0` is nonempty. Then the sets `A n` have a common point.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally convex spaces over non-Archimedean valued fields*,
  Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010, §2.4.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 6.14.
-/

public section

open Metric

namespace TauCeti

/-- A pseudometric space is *spherically complete* if every decreasing sequence of closed balls
with nonnegative radii has a common point. The radii need not tend to zero. -/
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  /-- Every decreasing sequence of closed balls with nonnegative radii has a common point. -/
  nonempty_iInter_closedBall {c : ℕ → α} {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (h : Antitone fun n ↦ closedBall (c n) (r n)) : (⋂ n, closedBall (c n) (r n)).Nonempty

/-- Every proper space is spherically complete: closed balls are compact. -/
instance (priority := 100) SphericallyCompleteSpace.of_properSpace (α : Type*)
    [PseudoMetricSpace α] [ProperSpace α] : SphericallyCompleteSpace α where
  nonempty_iInter_closedBall hr h :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n ↦ h (Nat.le_succ n)) (fun n ↦ nonempty_closedBall.2 (hr n))
      (isCompact_closedBall _ _) fun _ ↦ isClosed_closedBall

/-- In a spherically complete ultrametric space `X`, let `A n` be sets of families `ι → X` such
that `A n` contains the closed polydisc of radius `r n` about each of its points, and every point
of `A n` is within `r n` of some point of `A (n + 1)`. If the radii decrease and `A 0` is
nonempty, the sets `A n` have a common point. -/
theorem SphericallyCompleteSpace.exists_forall_mem_of_dist_le {X ι : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] [SphericallyCompleteSpace X] {A : ℕ → Set (ι → X)} {r : ℕ → ℝ}
    (hr : Antitone r) (hr0 : ∀ n, 0 ≤ r n) (h0 : (A 0).Nonempty)
    (hstep : ∀ n, ∀ c ∈ A n, ∃ c' ∈ A (n + 1), ∀ i, dist (c' i) (c i) ≤ r n)
    (hball : ∀ n, ∀ c ∈ A n, ∀ t : ι → X, (∀ i, dist (t i) (c i) ≤ r n) → t ∈ A n) :
    ∃ t : ι → X, ∀ n, t ∈ A n := by
  choose! g hgA hg using hstep
  obtain ⟨c₀, hc₀⟩ := h0
  -- The centres `c n ∈ A n`, defined recursively by `c (n + 1) = g n (c n)`.
  let c : ℕ → ι → X := fun n ↦ Nat.rec c₀ g n
  have hcA (n : ℕ) : c n ∈ A n := by
    induction n with
    | zero => exact hc₀
    | succ n ih => exact hgA n (c n) ih
  have hball' (i : ι) : (⋂ n, closedBall (c n i) (r n)).Nonempty := by
    refine SphericallyCompleteSpace.nonempty_iInter_closedBall hr0
      (antitone_nat_of_succ_le fun n ↦ ?_)
    have hmem : c (n + 1) i ∈ closedBall (c n i) (r n) := hg n (c n) (hcA n) i
    rw [IsUltrametricDist.closedBall_eq_of_mem hmem]
    exact closedBall_subset_closedBall (hr n.le_succ)
  choose t ht using hball'
  exact ⟨t, fun n ↦ hball n (c n) (hcA n) t fun i ↦ Set.mem_iInter.1 (ht i) n⟩

end TauCeti
