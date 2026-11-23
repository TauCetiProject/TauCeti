/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
public import TauCeti.Topology.Algebra.PointTopology.Group
public import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# Discreteness of rational points in the finite adelic points

Let `G = Spec H` be an affine group scheme over the fraction field `K` of a Dedekind domain `R`.
Unlike the rational points in the full adelic points, the rational points `G(K)` need not be
discrete in the finite adelic points `G(𝔸_{K,f})`: for a number field `K`, the additive group `K`
is not discrete in `𝔸_{K,f}`, because it meets the compact open integral adeles in the infinite
ring of integers `𝒪_K`. This file proves the criterion: `G(K)` is discrete in `G(𝔸_{K,f})`
exactly when it meets one compact neighbourhood `U` of the identity, for instance a compact open
subgroup, in a finite set. Since the condition does not depend on `U`, it holds for one compact
neighbourhood exactly when it holds for every one.

The criterion is `Subgroup.discreteTopology_iff_finite_inter_of_isCompact` applied to the range of
the rational diagonal `TauCeti.AdelicPoints.finiteDiagonal`; the points `G(𝔸_{K,f})` form a
Hausdorff topological group in the point topology.

## Main results

* `TauCeti.AdelicPoints.discreteTopology_range_finiteDiagonal_iff`: the rational points are
  discrete in the finite adelic points exactly when they meet a compact neighbourhood of the
  identity in a finite set.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.8, p. 9.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Example 2.3, p. 3.
-/

public section

open IsDedekindDomain
open scoped Topology

namespace TauCeti.AdelicPoints

variable {R K H : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Semiring H] [HopfAlgebra K H]

/-- **Discreteness of rational points in the finite adelic points.** The rational points `G(K)`
are discrete in `G(𝔸_{K,f})` exactly when they meet a compact neighbourhood `U` of the identity,
for instance a compact open subgroup, in a finite set. -/
theorem discreteTopology_range_finiteDiagonal_iff {U : Set (FiniteAdelicPoints R K H)}
    (hU : IsCompact U) (hU1 : U ∈ 𝓝 1) :
    DiscreteTopology (finiteDiagonal R K H).range ↔
      (((finiteDiagonal R K H).range : Set (FiniteAdelicPoints R K H)) ∩ U).Finite :=
  (finiteDiagonal R K H).range.discreteTopology_iff_finite_inter_of_isCompact hU hU1

end TauCeti.AdelicPoints
