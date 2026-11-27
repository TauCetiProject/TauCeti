/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The skew-adjoint elements of a topological star group

In a Hausdorff additive group with continuous negation and continuous star operation, the
skew-adjoint elements `{x | star x = -x}` form a closed subgroup
(`isClosed_skewAdjoint`). In particular they form a locally compact group when the ambient group
is locally compact, which is what a Haar measure on them needs.

## Main results

* `isClosed_skewAdjoint`: the skew-adjoint elements form a closed set.
* `skewAdjoint.instLocallyCompactSpace`, `skewAdjoint.instSecondCountableTopology`: they form a
  locally compact (resp. second countable) space when the ambient space does.
-/

public section

variable {R : Type*} [AddCommGroup R] [StarAddMonoid R] [TopologicalSpace R] [ContinuousStar R]
  [ContinuousNeg R] [T2Space R]

/-- The skew-adjoint elements of a Hausdorff topological star group form a closed set. -/
theorem isClosed_skewAdjoint : IsClosed (skewAdjoint R : Set R) :=
  isClosed_eq continuous_star continuous_neg

/-- The skew-adjoint elements of a locally compact Hausdorff topological star group form a locally
compact space. -/
instance skewAdjoint.instLocallyCompactSpace [LocallyCompactSpace R] :
    LocallyCompactSpace (skewAdjoint R) :=
  isClosed_skewAdjoint.locallyCompactSpace

/-- The skew-adjoint elements of a second countable topological star group form a second
countable space. -/
instance skewAdjoint.instSecondCountableTopology {R : Type*} [AddCommGroup R] [StarAddMonoid R]
    [TopologicalSpace R] [SecondCountableTopology R] : SecondCountableTopology (skewAdjoint R) :=
  inferInstanceAs (SecondCountableTopology (skewAdjoint R : Set R))
