/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology

/-!
# The cohomological dimension of a free pro-`p` group is at most one

Let `F = freeProP p X` be the free pro-`p` group on a type `X`. Its second continuous cohomology
vanishes on every finite discrete `p`-primary `F`-module, because every profinite extension of `F`
by such a module splits
(`TauCeti.freeProP.subsingleton_continuousCohomology_two_of_isPPrimaryTorsion`, in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology`). Since the `p`-cohomological dimension
of a compact group is detected in a single degree on finite coefficients
(`TauCeti.cohomologicalDimensionAt_le_iff_forall_finite_subsingleton_succ`), this vanishing in
degree two is the statement `cd_p F ≤ 1`.

No finiteness of `X` is needed. This is the converse direction, for the free pro-`p` groups
themselves, of Serre's theorem
`TauCeti.IsProP.nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one`, which
recovers a topologically finitely generated pro-`p` group with `cd_p ≤ 1` as a free pro-`p` group.

## Main results

* `TauCeti.freeProP.cohomologicalDimensionLE_one`: the vanishing predicate `cd_p F ≤ 1`.
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

/-- **A free pro-`p` group has `cd_p ≤ 1`**, as the vanishing predicate: for `p ≠ 0`, `Hⁱ(F, M)`
vanishes for every `i ≥ 2` and every discrete `p`-primary torsion `F`-module `M`. -/
theorem cohomologicalDimensionLE_one (hp : p ≠ 0) :
    CohomologicalDimensionLE.{u} p (freeProP p X) 1 :=
  (cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ hp 1).2
    fun M _ _ _ _ _ _ hM ↦ subsingleton_continuousCohomology_two_of_isPPrimaryTorsion M hM

/-- **The cohomological dimension of a free pro-`p` group is at most one**: `cd_p F ≤ 1` for
`F = freeProP p X`, on any type `X` and for `p ≠ 0`. -/
theorem cohomologicalDimensionAt_le_one (hp : p ≠ 0) :
    cohomologicalDimensionAt.{u} p (freeProP p X) ≤ 1 :=
  mod_cast (cohomologicalDimensionAt_le_iff p (freeProP p X) 1).2 (cohomologicalDimensionLE_one hp)

end freeProP

end TauCeti
