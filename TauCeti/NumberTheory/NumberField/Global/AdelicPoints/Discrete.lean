/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Rational points are discrete and closed in the adelic points

Let `K` be a number field with adele ring `𝔸_K`, and let `G = Spec H` be an affine group scheme
over `K`. The rational diagonal `G(K) → G(𝔸_K)` is injective
(`TauCeti.AdelicPoints.diagonal_injective`). This file shows that its image is closed in `G(𝔸_K)`
for every bialgebra `H`, and discrete when `H` is commutative of finite type. For a commutative
Hopf algebra of finite type, `G(K)` is therefore a discrete subgroup of the topological group
`G(𝔸_K)`, the subgroup by which the arithmetic quotient `G(K)\G(𝔸_K)` is formed.

Both statements reduce to the additive group: `K` is closed and discrete in `𝔸_K`
(`TauCeti.GlobalNumberFields.isClosed_principalSubgroup`,
`TauCeti.GlobalNumberFields.discreteTopology_principalSubgroup`). An adelic point is rational
exactly when all its values lie in `K`, and evaluation at finitely many generators of `H` embeds
`G(𝔸_K)` in a finite power of `𝔸_K`, carrying `G(K)` into the same power of `K`
(`AlgHom.isClosed_range_mapValue`, `AlgHom.isDiscrete_range_mapValue`).

Finite type cannot be dropped from the discreteness statement: for affine space in infinitely
many variables `σ`, the points are `𝔸_K^σ` with the product topology, in which every neighbourhood
of `0` constrains only finitely many coordinates and so contains nonzero points of `K^σ`. Nor can
the infinite component of the adeles: `K` is dense in the finite adeles.

## Main results

* `TauCeti.AdelicPoints.isClosed_range_diagonal`: `G(K)` is closed in `G(𝔸_K)`.
* `TauCeti.AdelicPoints.isDiscrete_range_diagonal`: `G(K)` is discrete in `G(𝔸_K)` when `H` is
  commutative of finite type.
* `TauCeti.AdelicPoints.discreteTopology_range_diagonal`: for a commutative Hopf algebra of finite
  type, `G(K)` is a discrete subgroup of `G(𝔸_K)`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Example 2.3, p. 3.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.2, p. 7.
-/

public section

open NumberField

namespace TauCeti.AdelicPoints

variable (K H : Type*) [Field K] [NumberField K]

/-- **Rational points are closed in the adelic points.** For a number field `K` and a bialgebra
`H` over `K`, the image of the rational diagonal `G(K) → G(𝔸_K)` is closed. No finiteness
assumption on `H` is needed. -/
theorem isClosed_range_diagonal [Semiring H] [Bialgebra K H] :
    IsClosed (Set.range (diagonal (𝓞 K) K H)) := by
  rw [diagonal_def]
  refine AlgHom.isClosed_range_mapValue (AdeleRing.algebraMap_injective (𝓞 K) K) ?_
  simpa [← AlgHom.coe_range] using GlobalNumberFields.isClosed_principalSubgroup K

/-- **Rational points are discrete in the adelic points.** For a number field `K` and a
commutative bialgebra `H` of finite type over `K`, the image of the rational diagonal
`G(K) → G(𝔸_K)` is discrete. -/
theorem isDiscrete_range_diagonal [CommSemiring H] [Bialgebra K H] [Algebra.FiniteType K H] :
    IsDiscrete (Set.range (diagonal (𝓞 K) K H)) := by
  rw [diagonal_def]
  refine AlgHom.isDiscrete_range_mapValue (AdeleRing.algebraMap_injective (𝓞 K) K) ?_
  simpa [← AlgHom.coe_range, ← SetLike.isDiscrete_iff_discreteTopology] using
    GlobalNumberFields.discreteTopology_principalSubgroup K

/-- For a number field `K` and a commutative Hopf algebra `H` of finite type over `K`, the
rational points `G(K)` form a discrete subgroup of the adelic points `G(𝔸_K)`. -/
instance discreteTopology_range_diagonal [CommSemiring H] [HopfAlgebra K H]
    [Algebra.FiniteType K H] : DiscreteTopology (diagonal (𝓞 K) K H).range := by
  rw [← SetLike.isDiscrete_iff_discreteTopology, MonoidHom.coe_range]
  exact isDiscrete_range_diagonal K H

end TauCeti.AdelicPoints
