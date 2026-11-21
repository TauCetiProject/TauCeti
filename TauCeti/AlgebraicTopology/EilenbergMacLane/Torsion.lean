/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Torsion
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration
public import TauCeti.AlgebraicTopology.SerreClass.SubmonoidTorsion
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange

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

Combining this with flat base change to a localization of `ℤ` at `S` verifies Serre's `K(A, n)`
property for `S`-torsion (`TauCeti.IsEilenbergMacLaneSpace.isTorsion'_singularHomology`) and for
torsion abelian groups (`TauCeti.IsEilenbergMacLaneSpace.isAddTorsion_singularHomology`).

These are the inputs on Eilenberg--Mac Lane spaces of Serre's theorem that a simply connected
space with `S`-torsion homology has `S`-torsion homotopy groups.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`:
  a `K(A, 1)` space is `k`-acyclic when the order of every element of `A` is a unit of `k`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`:
  the same for `K(A, n)` spaces, `n ≥ 1`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`:
  `H_{i + 1}(K(A, n); R) = 0` for an `S`-torsion abelian group `A` and a localization `R` of `ℤ`
  at `S`.
* `TauCeti.IsEilenbergMacLaneSpace.isTorsion'_singularHomology`,
  `TauCeti.IsEilenbergMacLaneSpace.isSubmonoidTorsion_singularHomology`:
  if `A` is `S`-torsion, then `H_{i + 1}(K(A, n); ℤ)` is `S`-torsion.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_rat`,
  `TauCeti.IsEilenbergMacLaneSpace.isAddTorsion_singularHomology`,
  `TauCeti.IsEilenbergMacLaneSpace.isTorsion_singularHomology`:
  if `A` is torsion, then `H_{i + 1}(K(A, n); ℚ) = 0` and `H_{i + 1}(K(A, n); ℤ)` is torsion.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter III, Section 10.
-/

public section

noncomputable section

open AlgebraicTopology

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

namespace IsEilenbergMacLaneSpace

/-- **Acyclicity of `K(A, n)` over a localization `R` of `ℤ` at `S` when `A` is `S`-torsion.** -/
theorem subsingleton_singularHomology_of_isTorsion'
    {A : Type} [AddCommGroup A] {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    {S : Submonoid ℤ} (hA : Module.IsTorsion' A S)
    (R : Type) [CommRing R] [Algebra ℤ R] [IsLocalization S R] (i : ℕ) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (i + 1)) :=
  hX.subsingleton_singularHomology_of_forall_isUnit_addOrderOf R
    (hA.isUnit_addOrderOf fun s hs ↦ by simpa using IsLocalization.map_units R ⟨s, hs⟩) i

/-- Multiplicative-group variant of
`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isTorsion'`, for a commutative
group `G` whose additive counterpart `Additive G` is `S`-torsion (such as a higher homotopy group
`π_{m + 2}(Z, z)`). -/
theorem subsingleton_singularHomology_of_isTorsion'_additive
    {G : Type} [CommGroup G] {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace G n X x)
    {S : Submonoid ℤ} (hG : Module.IsTorsion' (Additive G) S)
    (R : Type) [CommRing R] [Algebra ℤ R] [IsLocalization S R] (i : ℕ) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (i + 1)) :=
  (hX.of_mulEquiv (MulEquiv.multiplicativeAdditive
    G).symm).subsingleton_singularHomology_of_isTorsion' hG R i

/-- **Integral positive-degree homology of `K(A, n)` is `S`-torsion when `A` is `S`-torsion.**
This verifies Serre's `K(A, n)` property for every submonoid-torsion class. -/
theorem isTorsion'_singularHomology
    {A : Type} [AddCommGroup A] {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    {S : Submonoid ℤ} (hA : Module.IsTorsion' A S) (i : ℕ) :
    Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1)) S :=
  haveI : IsLocalization S (Localization S) := Localization.isLocalization
  (isTorsion'_singularChains_int_homology_iff S (Localization S) (TopCat.of X) (i + 1)).2
    (hX.subsingleton_singularHomology_of_isTorsion' hA (Localization S) i)

/-- **Serre's `K(A, n)` property for the `S`-torsion Serre class.** If `A` belongs to
`AddCommGrpCat.isSubmonoidTorsion S`, then so does `H_{i + 1}(K(A, n); ℤ)` for every `i`. -/
theorem isSubmonoidTorsion_singularHomology
    {A : AddCommGrpCat.{0}} {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    {S : Submonoid ℤ} (hA : AddCommGrpCat.isSubmonoidTorsion S A) (i : ℕ) :
    AddCommGrpCat.isSubmonoidTorsion S
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1))) :=
  (AddCommGrpCat.prop_isSubmonoidTorsion_iff S _).2 <|
    hX.isTorsion'_singularHomology ((AddCommGrpCat.prop_isSubmonoidTorsion_iff S A).1 hA) i

/-- **Rational acyclicity of `K(A, n)` for a torsion abelian group `A`**:
`H_{i + 1}(K(A, n); ℚ) = 0` for `n ≥ 1` and `i : ℕ`. -/
theorem subsingleton_singularHomology_rat
    {A : Type} [AddCommGroup A] {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (hA : IsAddTorsion A) (i : ℕ) :
    Subsingleton (((singularChains ℚ).obj (TopCat.of X)).homology (i + 1)) :=
  hX.subsingleton_singularHomology_of_isTorsion' (S := nonZeroDivisors ℤ)
    (isAddTorsion_iff_isTorsion_int.1 hA) ℚ i

/-- **Integral positive-degree homology of `K(A, n)` is torsion when `A` is torsion.** -/
theorem isAddTorsion_singularHomology
    {A : Type} [AddCommGroup A] {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (hA : IsAddTorsion A) (i : ℕ) :
    IsAddTorsion (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1)) :=
  (isAddTorsion_singularChains_homology_iff (TopCat.of X) (i + 1)).2
    (hX.subsingleton_singularHomology_rat hA i)

/-- **Serre's `K(A, n)` property for the torsion Serre class.** If `A` belongs to
`AddCommGrpCat.isTorsion`, then so does `H_{i + 1}(K(A, n); ℤ)` for every `i`. -/
theorem isTorsion_singularHomology
    {A : AddCommGrpCat.{0}} {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (hA : AddCommGrpCat.isTorsion A) (i : ℕ) :
    AddCommGrpCat.isTorsion
      (AddCommGrpCat.of (((singularChains ℤ).obj (TopCat.of X)).homology (i + 1))) :=
  (AddCommGrpCat.prop_isTorsion_iff _).2 <|
    hX.isAddTorsion_singularHomology ((AddCommGrpCat.prop_isTorsion_iff A).1 hA) i

end IsEilenbergMacLaneSpace

end TauCeti
