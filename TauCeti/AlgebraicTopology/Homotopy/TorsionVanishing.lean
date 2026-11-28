/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.AlgebraicTopology.PathComponent
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ModuloTorsion
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Homotopy groups of spaces with torsion homology

**Theorem** (Serre). Let `Y` be a simply connected space whose reduced integral homology is a
torsion group. Then every homotopy group of `Y` is a torsion group
(`TauCeti.isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology`). This is the vanishing
half of the Hurewicz theorem modulo the Serre class of torsion groups: when all the homology lies
in the class, so do all the homotopy groups.

The theorem is proved for every submonoid `S` of `ℤ` at once: if every class of `Hᵢ(Y; ℤ)`,
`i > 0`, is killed by an element of `S`, then so is every element of `πᵢ(Y)`
(`TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology`). Taking for `S` the nonzero
integers gives the torsion groups. Taking for `S` the powers of an integer `d` gives the groups in
which every element is killed by some power of `d`; for finitely generated groups these are the
groups annihilated by a single power of `d`. No finite generation and no CW structure is assumed.

Equivalently, by flat base change (`TauCeti.isTorsion'_singularChains_homology_iff`), the
hypothesis says that `Y` has the homology of a point with coefficients in the localization
`S⁻¹ℤ`, for instance `ℚ` or `ℤ[1/d]`, and in this form the theorem is
`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology`. Both forms are derived from
Serre's connectivity equivalence modulo `S`-torsion
(`TauCeti.forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology`,
`TauCeti.forall_isTorsion'_homotopyGroup_iff_forall_singularHomology`).

Since a path component is simply connected exactly when the fundamental group at any of its points
is trivial (`TauCeti.simplyConnectedSpace_pathComponent_iff`), the theorem also applies to a single
path component: if the fundamental group of `Y` at `y` is trivial and the path component of `y`
has the `S⁻¹ℤ`-homology of a point, every `πₙ₊₂(Y, y)` is `S`-torsion
(`TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology_pathComponent`). No hypothesis
is made on the other path components of `Y`.

## Main results

* `TauCeti.isTorsion'_homotopyGroup_of_subsingleton_singularHomology`: the homotopy groups of a
  simply connected space with the homology of a point over `S⁻¹ℤ` are `S`-torsion.
* `TauCeti.isTorsion'_homotopyGroup_of_isTorsion'_singularHomology`: the homotopy groups of a
  simply connected space with `S`-torsion reduced integral homology are `S`-torsion.
* `TauCeti.isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology`: the homotopy groups of a
  simply connected space with torsion reduced integral homology are torsion groups.
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

/-- **Serre's theorem modulo `S`-torsion, with localized coefficients.** Let `S` be a submonoid of
`ℤ` and `k` a localization of `ℤ` at `S`, for instance `ℚ` or `ℤ[1/d]`. The homotopy groups
`πᵢ(Y)`, `i ≥ 2`, of a simply connected space `Y` with the `k`-homology of a point are
`S`-torsion: every element is killed by an element of `S`. No finite generation or CW structure is
assumed. -/
theorem isTorsion'_homotopyGroup_of_subsingleton_singularHomology (k : Type) [CommRing k]
    [Algebra ℤ k] [IsLocalization S k] {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 2) Y y)) S :=
  have : Subsingleton (π_ 1 Y y) := HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  (forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology y S k).2
    (fun m ↦ hY (m + 1)) n

/-- **Serre's theorem modulo `S`-torsion.** Let `S` be a submonoid of `ℤ`. If every class of the
positive-degree integral homology of a simply connected space `Y` is killed by an element of `S`,
then so is every element of every homotopy group `πᵢ(Y)`, `i ≥ 2`. For `S` the powers of an integer
`d`: if every class of the reduced integral homology of `Y` is killed by a power of `d`, so is
every element of every homotopy group of `Y`. -/
theorem isTorsion'_homotopyGroup_of_isTorsion'_singularHomology {Y : Type} [TopologicalSpace Y]
    [SimplyConnectedSpace Y]
    (hY : ∀ i, Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology (i + 1)) S)
    (y : Y) (n : ℕ) : Module.IsTorsion' (Additive (π_ (n + 2) Y y)) S :=
  have : Subsingleton (π_ 1 Y y) := HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  (forall_isTorsion'_homotopyGroup_iff_forall_singularHomology y S).2 (fun m ↦ hY (m + 1)) n

/-- **Serre's theorem modulo torsion groups.** If the positive-degree integral homology of a simply
connected space `Y` is a torsion group, then so is every homotopy group `πᵢ(Y)`, `i ≥ 2`. -/
theorem isMulTorsion_homotopyGroup_of_isAddTorsion_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsMulTorsion (π_ (n + 2) Y y) := by
  have hπ := isAddTorsion_iff_isTorsion_int.2
    (isTorsion'_homotopyGroup_of_isTorsion'_singularHomology (nonZeroDivisors ℤ)
      (fun i ↦ isAddTorsion_iff_isTorsion_int.1 (hY i)) y n)
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
  have := (simplyConnectedSpace_pathComponent_iff y).2 ‹_›
  (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).toAdditive.isTorsion'_iff.1
    (isTorsion'_homotopyGroup_of_subsingleton_singularHomology S k hY (pathComponentSelf y) n)

end TauCeti
