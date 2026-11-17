/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Localization
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
public import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible

/-!
# Eilenberg--Mac Lane spaces of torsion groups

Let `S` be a submonoid of `ℤ`, let `k` be a localization of `ℤ` at `S`, for instance `ℚ` when `S`
consists of the nonzero integers or `ℤ[1/d]` when `S` consists of the powers of `d`, and let `A` be
an abelian group which is `S`-torsion: every element of `A` is killed by an element of `S`. Then
every Eilenberg--Mac Lane space of type `K(A, n)`, `n ≥ 1`, has the `k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`). For `k = ℚ`:
every `K(A, n)` space of a torsion abelian group has the rational homology of a point. No
hypothesis of CW type is made on the space.

The case `n = 1` is group homology: the order of every element of `A` divides an element of `S`,
so it is a unit of `k` (`Module.IsTorsion'.isUnit_addOrderOf`), and then the positive-degree group
homology of `A` with coefficients in `k` vanishes
(`TauCeti.subsingleton_groupHomology_of_forall_isUnit_addOrderOf`). The higher cases follow
through the based path fibration
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).

These are the inputs on Eilenberg--Mac Lane spaces of Serre's theorem that a simply connected
space with `S`-torsion homology has `S`-torsion homotopy groups.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isTorsion'`: a `K(A, 1)`
  space of an `S`-torsion group is acyclic over the localization of `ℤ` at `S`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`: the same for
  `K(A, n)` spaces, `n ≥ 1`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, Section 10.
-/

public section

noncomputable section

namespace TauCeti

variable {S : Submonoid ℤ} (k : Type) [CommRing k] [Algebra ℤ k] [IsLocalization S k]
  {A : Type} [AddCommGroup A]

/-- **`K(A, 1)` spaces of `S`-torsion groups are acyclic over `S⁻¹ℤ`.** If every element of the
abelian group `A` is killed by an element of a submonoid `S` of `ℤ`, then every `K(A, 1)` space
has no homology in positive degrees with coefficients in a localization `k` of `ℤ` at `S`. -/
theorem IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isTorsion'
    (hA : Module.IsTorsion' A S) {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_forall_isUnit_addOrderOf k (hA.isUnit_addOrderOf k) n
  (hX.nonempty_singularHomologyIsoGroupHomology k (n + 1)).some.toLinearEquiv.toEquiv.subsingleton

/-- **`K(A, n)` spaces of `S`-torsion groups are acyclic over `S⁻¹ℤ`.** If every element of the
abelian group `A` is killed by an element of a submonoid `S` of `ℤ`, then every `K(A, n)` space,
`n ≥ 1`, has no homology in positive degrees with coefficients in a localization `k` of `ℤ` at
`S`. For `k = ℚ`: a `K(A, n)` space of a torsion abelian group has the rational homology of a
point. -/
theorem IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'
    (hA : Module.IsTorsion' A S) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne k
    (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isTorsion' k hA) hX i

end TauCeti
