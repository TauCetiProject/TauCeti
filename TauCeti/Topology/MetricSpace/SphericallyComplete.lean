/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace

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

end TauCeti
