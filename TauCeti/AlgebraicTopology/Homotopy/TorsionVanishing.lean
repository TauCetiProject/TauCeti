/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.EilenbergMacLane.Torsion
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
import TauCeti.Topology.PathComponent

/-!
# Homotopy groups of spaces with torsion homology

**Theorem** (Serre). Let `Y` be a pointed space `(Y, y)` with trivial fundamental group `π₁(Y, y)`
whose integral homology in degrees `2 ≤ q ≤ n + 2` is a torsion group. Then `π_{n + 2}(Y, y)` is a
torsion group (`TauCeti.isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology`). This is the
vanishing half of the Hurewicz theorem modulo the Serre class of torsion groups: when the homology
up to degree `n + 2` lies in the class, so does `π_{n + 2}`.

The theorem is proved for every submonoid `S` of `ℤ` at once: if every class of `H_q(Y; ℤ)`,
`2 ≤ q ≤ n + 2`, is killed by an element of `S`, then so is every element of `π_{n + 2}(Y, y)`
(`TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology`). Taking for `S` the nonzero
integers gives the torsion groups. Taking for `S` the powers of an integer `d` gives the groups in
which every element is killed by some power of `d`; for finitely generated groups these are the
groups annihilated by a single power of `d`. No finite generation, path-connectedness, Hausdorff, or
CW assumption is assumed.

Equivalently, by flat base change (`TauCeti.isTorsion'_singularChains_homology_iff`), the
hypothesis says that `Y` has the homology of a point in degrees `2 ≤ q ≤ n + 2` with coefficients
in the localization `S⁻¹ℤ`, for instance `ℚ` or `ℤ[1/d]`, and in this form the theorem is
`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology`. The proof climbs the
Whitehead tower (`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`), exactly as the
mod-two vanishing theorem
(`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`), with two inputs.

* **First homotopy group.** If `Z` is `(n + 1)`-connected, the Hurewicz isomorphism
  `πₙ₊₂(Z) ≅ Hₙ₊₂(Z; ℤ)` makes `πₙ₊₂(Z)` an `S`-torsion group as soon as `Hₙ₊₂(Z; S⁻¹ℤ)` vanishes,
  by flat base change.
* **Eilenberg--Mac Lane spaces.** Every `K(A, n)` space of an `S`-torsion group `A` has the
  `S⁻¹ℤ`-homology of a point
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf`),
  since the order of every element of `A` is a unit of `S⁻¹ℤ`
  (`Module.IsTorsion'.isUnit_addOrderOf`).

When only the path component of `y` has vanishing `S⁻¹ℤ`-homology (with no assumption on the other
path components of `Y`), the theorem also applies to `pathComponent y`
(`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent`).

## Main results

* `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology`: `π_{n + 2}(Y, y)` is
  `S`-torsion when `π₁(Y, y)` is trivial and `H_q(Y; S⁻¹ℤ) = 0` for `2 ≤ q ≤ n + 2`.
* `TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology`: `π_{n + 2}(Y, y)` is
  `S`-torsion when `π₁(Y, y)` is trivial and `H_q(Y; ℤ)` is `S`-torsion for `2 ≤ q ≤ n + 2`.
* `TauCeti.isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology`: `π_{n + 2}(Y, y)` is a
  torsion group when `π₁(Y, y)` is trivial and `H_q(Y; ℤ)` is torsion for `2 ≤ q ≤ n + 2`.
* `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent`: if the
  fundamental group of `Y` at `y` is trivial and the path component of `y` has the homology of a
  point over `S⁻¹ℤ`, the higher homotopy groups of `Y` at `y` are `S`-torsion.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter III.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.12.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable (S : Submonoid ℤ)

/-- The first possible homotopy group: the homotopy group `πₙ₊₂` of an `(n + 1)`-connected space
with the homology of a point over a localization `k` of `ℤ` at `S` is `S`-torsion. Through the
Hurewicz isomorphism it is `Hₙ₊₂(Z; ℤ)`, which is `S`-torsion since `Hₙ₊₂(Z; k)` vanishes. -/
private theorem isTorsion'_homotopyGroup_of_connected (k : Type) [CommRing k] [Algebra ℤ k]
    [IsLocalization S k] {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ)
    (hZ : ∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z))
    (hZk : ∀ q, n + 2 ≤ q → q ≤ n + 2 + 0 →
      Subsingleton (((singularChains k).obj (TopCat.of Z)).homology q)) :
    Module.IsTorsion' (Additive (π_ (n + 2) Z z)) S := by
  have hZ' (j : ℕ) (hj : j < n + 2) : Subsingleton (HomotopyGroup (Fin j) Z z) := by
    rcases eq_or_ne j 0 with rfl | hj0
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
    · exact hZ j hj0 hj
  have hH := (isTorsion'_singularChains_int_homology_iff S k (TopCat.of Z) (n + 2)).2
    (hZk (n + 2) le_rfl le_rfl)
  exact (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hZ').isTorsion'_iff.2 hH

/-- **Serre's theorem modulo `S`-torsion, with localized coefficients.** Let `S` be a submonoid of
`ℤ` and `k` a localization of `ℤ` at `S`, for instance `ℚ` or `ℤ[1/d]`. If `π₁(Y, y)` is trivial
and `H_q(Y; k)` vanishes for `2 ≤ q ≤ n + 2`, then `π_{n + 2}(Y, y)` is `S`-torsion: every element
is killed by an element of `S`. No finite generation, path-connectedness, Hausdorff, or CW
assumption is needed on `Y`. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology (k : Type) [CommRing k]
    [Algebra ℤ k] [IsLocalization S k] {Y : Type} [TopologicalSpace Y] {y : Y}
    [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 2 →
      Subsingleton (((singularChains k).obj (TopCat.of Y)).homology q)) :
    Module.IsTorsion' (Additive (π_ (n + 2) Y y)) S :=
  prop_homotopyGroup_of_subsingleton_singularHomology k (fun G _ ↦ Module.IsTorsion' G S) 0
    (fun e ↦ e.isTorsion'_iff.1)
    (isTorsion'_homotopyGroup_of_connected S k)
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_forall_isUnit_addOrderOf k
        (hA.isUnit_addOrderOf fun s hs ↦ by simpa using IsLocalization.map_units k ⟨s, hs⟩) hX)
    y n hY

/-- **Serre's theorem modulo `S`-torsion.** Let `S` be a submonoid of `ℤ`. If `π₁(Y, y)` is trivial
and every class of `H_q(Y; ℤ)`, `2 ≤ q ≤ n + 2`, is killed by an element of `S`, then so is every
element of `π_{n + 2}(Y, y)`. For `S` the powers of an integer `d`: if every class of the reduced
integral homology of `Y` in degrees `2 ≤ q ≤ n + 2` is killed by a power of `d`, so is every
element of `π_{n + 2}(Y, y)`. -/
theorem isTorsion'_homotopyGroup_of_isTorsion'_singularHomology {Y : Type} [TopologicalSpace Y]
    {y : Y} [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 2 →
      Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology q) S) :
    Module.IsTorsion' (Additive (π_ (n + 2) Y y)) S :=
  -- Instance search does not find this through the semiring structure of `ℤ` that `S` carries.
  haveI : IsLocalization S (Localization S) := Localization.isLocalization
  isTorsion'_homotopyGroup_of_subsingleton_singularHomology S (Localization S)
    fun q hq1 hq2 ↦ (isTorsion'_singularChains_int_homology_iff S _ (TopCat.of Y) q).1
      (hY q hq1 hq2)

/-- **Serre's theorem modulo torsion groups.** If `π₁(Y, y)` is trivial and `H_q(Y; ℤ)` is a
torsion group for `2 ≤ q ≤ n + 2`, then `π_{n + 2}(Y, y)` is a torsion group. -/
theorem isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 2 →
      IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology q)) :
    IsMulTorsion (π_ (n + 2) Y y) := by
  have hπ := isAddTorsion_iff_isTorsion_int.2
    (isTorsion'_homotopyGroup_of_isTorsion'_singularHomology (nonZeroDivisors ℤ) (y := y) (n := n)
      fun q hq1 hq2 ↦ isAddTorsion_iff_isTorsion_int.1 (hY q hq1 hq2))
  exact fun g ↦ isOfFinAddOrder_ofMul_iff.1 (hπ (Additive.ofMul g))

/-- **Serre's theorem modulo `S`-torsion for a path component.** Let `S` be a submonoid of `ℤ` and
`k` a localization of `ℤ` at `S`. If the fundamental group of `Y` at `y` is trivial and the path
component of `y` has the `k`-homology of a point, then every homotopy group `πₙ₊₂(Y, y)` is
`S`-torsion. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent (k : Type)
    [CommRing k] [Algebra ℤ k] [IsLocalization S k] {Y : Type} [TopologicalSpace Y] (y : Y)
    [Subsingleton (FundamentalGroup Y y)]
    (hY : ∀ i, Subsingleton
      (((singularChains k).obj (TopCat.of (pathComponent y))).homology (i + 1)))
    (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 2) Y y)) S :=
  have : Subsingleton (π_ 1 (pathComponent y) (pathComponentSelf y)) :=
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      HomotopyGroup.pi1MulEquivFundamentalGroup).toEquiv.subsingleton
  (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).toAdditive.isTorsion'_iff.1
    (isTorsion'_homotopyGroup_of_subsingleton_singularHomology S k (y := pathComponentSelf y)
      (n := n) fun q hq _ ↦ subsingleton_singularChains_homology_of_forall_succ k hY (by omega))

end TauCeti
