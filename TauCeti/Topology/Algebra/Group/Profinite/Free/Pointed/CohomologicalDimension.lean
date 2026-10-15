/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.EmbeddingProblem

/-!
# The cohomological dimension of the free pro-`p` group on a pointed space is at most one

Let `F = F_p(X, x₀)` be the free pro-`p` group on a pointed topological space, that is the free
pro-`C` group `TauCeti.freeProCPointed C x₀` for `C` the class of finite `p`-groups. It is
projective (`TauCeti.isProjective_freeProCPointed`), and a projective pro-`p` group has
`p`-cohomological dimension at most one (`TauCeti.IsProjective.cohomologicalDimensionAt_le_one`),
because every profinite extension of it by a finite `p`-primary module splits. Hence `cd_p F ≤ 1`.

Neither compactness of `X` nor any bound on its size is used. This is the converse direction, for
the free pro-`p` groups on pointed spaces, of Serre's theorem at arbitrary rank
`IsProP.exists_convergesToOne_continuousMulEquiv_presentation_of_cohomologicalDimensionAt_le_one`
(in the `TauCeti` namespace), which recovers a pro-`p` group with `cd_p ≤ 1` as such a free group;
the two directions are combined in `TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Serre`.
For the free pro-`p` group on a discrete type the same statement is
`TauCeti.freeProP.cohomologicalDimensionAt_le_one`.

## Main results

* `TauCeti.freeProCPointed.cohomologicalDimensionAt_le_one`: **`cd_p F ≤ 1`** for the free
  pro-`p` group on a pointed space.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2 and §5.9.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 7.7.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) {X : Type u} [TopologicalSpace X] (x₀ : X)

namespace freeProCPointed

/-- **The cohomological dimension of the free pro-`p` group on a pointed space is at most one**:
`cd_p F_p(X, x₀) ≤ 1` for every pointed topological space `(X, x₀)` and `p ≠ 0`. -/
theorem cohomologicalDimensionAt_le_one (hp : p ≠ 0) :
    cohomologicalDimensionAt.{u} p (freeProCPointed (finiteGroupClassP.{u} p) x₀) ≤ 1 :=
  (isProjective_freeProCPointed p x₀).cohomologicalDimensionAt_le_one hp
    (isProC_finiteGroupClassP_iff.mp (isProC_freeProCPointed (finiteGroupClassP.{u} p) x₀))

end freeProCPointed

end TauCeti
