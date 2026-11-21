/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology

/-!
# Eilenberg--Mac Lane spaces of torsion groups

Let `k` be a commutative ring and let `A` be an abelian group the order of each of whose elements
is a unit of `k`. Then every Eilenberg--Mac Lane space of type `K(A, n)`, `n ≥ 1`, has the
`k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`).
The main example: `A` is `S`-torsion for a submonoid `S` of `ℤ`, every element being killed by an
element of `S`, and `k` is a ring in which the elements of `S` are units, for instance the
localization `S⁻¹ℤ` (`Module.IsTorsion'.isUnit_addOrderOf`). For `k = ℚ`: every `K(A, n)` space of
a torsion abelian group has the rational homology of a point. No hypothesis of CW type is made on
the space.

The case `n = 1` is group homology: the positive-degree group homology of `A` with coefficients
in `k` vanishes (`TauCeti.subsingleton_groupHomology_of_forall_isUnit_addOrderOf`). The higher
cases follow through the based path fibration
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).

These are the inputs on Eilenberg--Mac Lane spaces of Serre's theorem that a simply connected
space with `S`-torsion homology has `S`-torsion homotopy groups.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`:
  a `K(A, 1)` space is `k`-acyclic when the order of every element of `A` is a unit of `k`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`:
  the same for `K(A, n)` spaces, `n ≥ 1`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, Section 10.
-/

public section

noncomputable section

namespace TauCeti

variable (k : Type) [CommRing k] {A : Type} [AddCommGroup A]

/-- **`K(A, 1)` spaces of torsion groups are acyclic.** If the order of every element of the
abelian group `A` is a unit of the commutative ring `k`, then every `K(A, 1)` space has no homology
in positive degrees with coefficients in `k`. -/
theorem IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_forall_isUnit_addOrderOf
    (hA : ∀ a : A, IsUnit (addOrderOf a : k)) {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_forall_isUnit_addOrderOf k hA n
  (hX.nonempty_singularHomologyIsoGroupHomology k (n + 1)).some.toLinearEquiv.toEquiv.subsingleton

/-- **`K(A, n)` spaces of torsion groups are acyclic.** If the order of every element of the
abelian group `A` is a unit of the commutative ring `k`, then every `K(A, n)` space, `n ≥ 1`, has
no homology in positive degrees with coefficients in `k`. For `k = ℚ`: a `K(A, n)` space of a
torsion abelian group has the rational homology of a point. -/
theorem IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf
    (hA : ∀ a : A, IsUnit (addOrderOf a : k)) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne k
    (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_forall_isUnit_addOrderOf k hA)
    hX i

end TauCeti
