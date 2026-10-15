/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.EmbeddingProblem

/-!
# The cohomological dimension of a free pro-`p` group is at most one

Let `F = freeProP p X` be the free pro-`p` group on a type `X`. It is projective
(`TauCeti.isProjective_of_hasPGroupSolutions` at `TauCeti.hasPGroupSolutions_freeProP`), and a
projective pro-`p` group has `p`-cohomological dimension at most one
(`TauCeti.IsProjective.cohomologicalDimensionAt_le_one`): its second continuous cohomology
vanishes on every finite discrete `p`-primary module, because every profinite extension of it by
such a module splits, and the `p`-cohomological dimension of a compact group is detected in degree
two on finite coefficients. Hence `cd_p F ≤ 1`.

No finiteness of `X` is needed. This is the converse direction, for the free pro-`p` groups
themselves, of Serre's theorem
`TauCeti.IsProP.nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one`, which
recovers a topologically finitely generated pro-`p` group with `cd_p ≤ 1` as a free pro-`p` group.

## Main results

* `TauCeti.freeProP.cohomologicalDimensionAt_le_one`: **`cd_p F ≤ 1`** for a free pro-`p` group.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
* H. Koch, *Galois Theory of `p`-Extensions*, Springer (2002), Ch. 4.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} {X : Type u}

namespace freeProP

/-- **The cohomological dimension of a free pro-`p` group is at most one**: `cd_p F ≤ 1` for
`F = freeProP p X`, on any type `X` and for `p ≠ 0`. -/
theorem cohomologicalDimensionAt_le_one (hp : p ≠ 0) :
    cohomologicalDimensionAt.{u} p (freeProP p X) ≤ 1 :=
  IsProjective.cohomologicalDimensionAt_le_one hp
    (isProjective_of_hasPGroupSolutions (hasPGroupSolutions_freeProP p X)) (isProP_freeProP p X)

end freeProP

end TauCeti
