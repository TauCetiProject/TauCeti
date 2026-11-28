/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
public import TauCeti.Topology.PathComponent
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ZMod
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-`m` and mod-two vanishing theorems for higher homotopy groups

**Theorem** (Serre). Let `Y` be a topological space with a base point `y` such that `π₁(Y, y)` is
trivial, and let `m : ℕ`. If the singular homology `H_q(Y; ℤ/m)` vanishes in the finite range
`2 ≤ q ≤ n + 3`, then multiplication by `m` is a bijection on `π_{n + 2}(Y, y)`
(`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`). No Hausdorff,
path-connectedness, CW, or finite-generation assumption is needed on `Y`, and `m` need not be
prime or nonzero. For `m = 2` this is the **mod-two vanishing theorem**: if `π₁(Y, y)` is trivial
and the reduced mod-two singular homology of `Y` vanishes in every degree, then multiplication by
`2` is bijective on every higher homotopy group `π_{n + 2}(Y, y)`
(`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod`), so
`π_{n + 2}(Y, y)` is uniquely two-divisible, becomes a `ℤ[1/2]`-module, and satisfies
`π_{n + 2}(Y, y) ⊗ 𝔽₂ = 0`.

Since a path component has the homotopy groups of the ambient space in positive degrees, the theorem
also applies to a single path component (`pathComponent y`) with no assumption on the other
components
(`TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_singularHomology_pathComponent`, and for
`m = 2`,
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`).

The class of groups `G` with `G ⊗ ℤ/2 = 0` is not a Serre class (it contains `ℚ` but not `ℤ`), so
this is not a case of the Hurewicz theorem modulo a Serre class; it is proved directly, one
homotopy group at a time, along the Whitehead tower
(`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`), with two inputs:

* **First homotopy group.** When `π_k(Z, z)` vanishes for `1 ≤ k < j + 2`, the Hurewicz
  isomorphism on the CW approximation of the path component of `z` and the mod-`m` coefficient
  exact sequence make multiplication by `m` bijective on `π_{j + 2}(Z, z)` from vanishing of
  `H_{j + 2}(Z; ℤ/m)` and `H_{j + 3}(Z; ℤ/m)`
  (`TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_ringEquiv`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod`).
* **Eilenberg--Mac Lane spaces.** Every fibre of the `(j + 2)`-connected cover `W⟨j + 2⟩ → W` of
  the `(j + 1)`-connected Hausdorff CW approximation `W` is a `K(π_{j + 2} W, j + 1)`. Once
  `π_{j + 2} W` is uniquely `m`-divisible, every such fibre is acyclic modulo `m`
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`), so
  `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber` makes `W⟨j + 2⟩ → W` an
  isomorphism on `H_*(-; k)`.

The hypothesis on mod-two homology cannot be dropped: for `n ≥ 2`, the sphere `Sⁿ` is simply
connected, its `πₙ ≅ ℤ` is not uniquely two-divisible
(`TauCeti.not_isUniquelyTwoDivisible_homotopyGroup_sphere`), and indeed `Hₙ(Sⁿ; 𝔽₂) ≠ 0`. Also, over
`S^{n+2}`, no Serre fibration whose fibre has trivial `π_{n+1}` has a total space with trivial
`π_{n+2}` (`TauCeti.nontrivial_homotopyGroup_of_mem_serreFibrations_sphere`).

## Main results

* `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_ringEquiv`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_ringEquiv`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod`: sharp
  finite-range and reduced-homology mod-`m` vanishing theorems in any universe `u`.
* `TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_singularHomology_pathComponent`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`:
  mod-`m` and mod-two vanishing when only the path component of `y` has vanishing positive-degree
  homology.
* `TauCeti.not_isUniquelyTwoDivisible_homotopyGroup_sphere`: `π_{n+2}(S^{n+2}) ≅ ℤ` is not
  uniquely two-divisible, so the conclusion fails for spheres, which are not mod-two acyclic.
* `TauCeti.nontrivial_homotopyGroup_of_mem_serreFibrations_sphere`: a Serre fibration over
  `S^{n+2}` whose fibre has trivial `π_{n+1}` has a total space with nontrivial `π_{n+2}`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.2 and 4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

/-- **Sharp finite-range mod-`m` vanishing theorem with ring coefficients.** Let `Y` be a space in
any universe `u` with a base point `y` such that `π₁(Y, y)` is trivial, and let `k ≃+* ZMod m` be
a ring in the universe of `Y`. If `H_q(Y; k) = 0` for all `2 ≤ q ≤ n + 3`, then multiplication by
`m` is a bijection on `π_{n + 2}(Y, y)`. No Hausdorff, path-connectedness, CW, or finite-generation
assumption is required on `Y`, and `m` need not be prime or nonzero. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_singularHomology_ringEquiv {k : Type u} [CommRing k]
    {m : ℕ} (e : k ≃+* ZMod m) {Y : Type u} [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
    {n : ℕ} (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularChains k).obj (TopCat.of Y)).homology q)) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  have hmk : ((m : ℤ) : k) = 0 :=
    e.injective (by rw [map_intCast, Int.cast_natCast, ZMod.natCast_self, map_zero])
  prop_homotopyGroup_of_subsingleton_singularHomology k
    (fun G _ ↦ Function.Bijective fun a : G ↦ (m : ℤ) • a) 1
    (fun hE h ↦ (hE.bijective_zsmul_iff (m : ℤ)).1 h)
    (fun z j hZ hZk ↦
      bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_ringEquiv e
        (fun l hl1 hl2 ↦ hZ l (by omega) hl2)
        (ModuleCat.isZero_iff_subsingleton.2 (hZk (j + 2) le_rfl (by omega)))
        (ModuleCat.isZero_iff_subsingleton.2 (hZk (j + 3) (by omega) le_rfl)))
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul k hmk hA hX)
    y n fun q hq1 hq2 ↦ ModuleCat.isZero_iff_subsingleton.1 (hY q hq1 hq2)

/-- **Sharp finite-range mod-`m` vanishing theorem.** Let `Y` be a space in any universe `u` with a
base point `y` such that `π₁(Y, y)` is trivial, and let `m, n : ℕ`. If `H_q(Y; ℤ/m) = 0` (with
lifted integer-module coefficients) for all `2 ≤ q ≤ n + 3`, then multiplication by `m` is a
bijection on `π_{n + 2}(Y, y)`. No Hausdorff, path-connectedness, CW, or finite-generation
assumption is required on `Y`, and `m` need not be prime or nonzero. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod {Y : Type u}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) q).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj (TopCat.of Y))) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  bijective_zsmul_homotopyGroup_of_isZero_singularHomology_ringEquiv
    (ULift.ringEquiv : ULift.{u} (ZMod m) ≃+* ZMod m) fun q hq1 hq2 ↦ by
      rw [← singularHomologyFunctor_obj_obj]
      exact ((TopCat.of Y).isZero_singularHomology_zmod_iff_of_ringEquiv m
        (ULift.ringEquiv : ULift.{u} (ZMod m) ≃+* ZMod m) q).1 (hY q hq1 hq2)

/-- **Reduced-homology mod-`m` vanishing theorem with ring coefficients.** If `π₁(Y, y)` is trivial
and the reduced singular homology of `Y` with coefficients in a ring `k ≃+* ZMod m` in the universe
of `Y` vanishes in every degree, then multiplication by `m` is a bijection on every higher homotopy
group `π_{n + 2}(Y, y)`. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_ringEquiv {k : Type u}
    [CommRing k] {m : ℕ} (e : k ≃+* ZMod m) {Y : Type u} [TopologicalSpace Y] {y : Y}
    [Subsingleton (π_ 1 Y y)]
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor (ModuleCat.of k k) q).obj (TopCat.of Y)))
    (n : ℕ) : Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  bijective_zsmul_homotopyGroup_of_isZero_singularHomology_ringEquiv e fun q hq _ ↦ by
    rw [← singularHomologyFunctor_obj_obj,
      isZero_singularHomologyFunctor_iff_isZero_reducedSingularHomologyFunctor (ModuleCat.of k k)
        (TopCat.of Y) (by omega)]
    exact hY q

/-- **Reduced-homology mod-`m` vanishing theorem.** If `π₁(Y, y)` is trivial and the reduced
singular homology of `Y` with coefficients in the lifted integer module `ℤ/m` vanishes in every
degree, then multiplication by `m` is a bijection on every higher homotopy group `π_{n + 2}(Y, y)`.
-/
theorem bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod {Y : Type u}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m : ℕ}
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor
      (ModuleCat.of ℤ (ULift.{u} (ZMod m))) q).obj (TopCat.of Y))) (n : ℕ) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod fun q hq _ ↦
    (isZero_singularHomologyFunctor_iff_isZero_reducedSingularHomologyFunctor
      (ModuleCat.of ℤ (ULift.{u} (ZMod m))) (TopCat.of Y) (by omega)).2 (hY q)

/-- **Mod-`m` vanishing for a path component.** If `π₁(Y, y)` is trivial and the path component of
`y` has vanishing positive-degree homology with coefficients in a ring `k ≃+* ZMod m` in the
universe of `Y`, then multiplication by `m` is a bijection on every higher homotopy group
`π_{n + 2}(Y, y)`. -/
theorem bijective_zsmul_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    {k : Type u} [CommRing k] {m : ℕ} (e : k ≃+* ZMod m) {Y : Type u} [TopologicalSpace Y]
    (y : Y) [Subsingleton (π_ 1 Y y)]
    (hY : ∀ i, Subsingleton
      (((singularChains k).obj (TopCat.of (pathComponent y))).homology (i + 1)))
    (n : ℕ) : Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  have : Subsingleton (π_ 1 (pathComponent y) (pathComponentSelf y)) :=
    (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl
      rfl).toEquiv.subsingleton_congr.2 ‹_›
  ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl
    rfl).toAdditive.bijective_zsmul_iff (m : ℤ)).1
    (bijective_zsmul_homotopyGroup_of_isZero_singularHomology_ringEquiv e
      (y := pathComponentSelf y) (n := n) fun q hq _ ↦
        ModuleCat.isZero_iff_subsingleton.2
          (subsingleton_singularChains_homology_of_forall_succ k hY (by omega)))

/-- **Mod-two vanishing for a path component.** If `π₁(Y, y)` is trivial and the path component of
`y` has the mod-two homology of a point, with coefficients in a ring `k ≃+* ZMod 2` in the
universe of `Y`, then every higher homotopy group `π_{n + 2}(Y, y)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    {k : Type u} [CommRing k] (e : k ≃+* ZMod 2) {Y : Type u} [TopologicalSpace Y] (y : Y)
    [Subsingleton (π_ 1 Y y)]
    (hY : ∀ i, Subsingleton
      (((singularChains k).obj (TopCat.of (pathComponent y))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  (isUniquelyTwoDivisible_iff _).2
    (bijective_zsmul_homotopyGroup_of_subsingleton_singularHomology_pathComponent e y hY n)

/-! ### Spheres -/

section Sphere

open Metric

variable {n : ℕ}

/-- **The conclusion of mod-two vanishing fails for spheres.** For every `n`, the homotopy group
`π_{n+2}(S^{n+2}, x) ≅ ℤ` of the simply connected sphere `S^{n+2}`, the unit sphere of an
`(n + 3)`-dimensional real normed space, is not uniquely two-divisible. This is consistent with
the theorem, whose hypothesis fails for `S^{n+2}` since `H_{n+2}(S^{n+2}; 𝔽₂) ≠ 0`
(`TauCeti.nontrivial_singularHomology_sphere`). -/
theorem not_isUniquelyTwoDivisible_homotopyGroup_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : Module.finrank ℝ E = n + 3) (x : sphere (0 : E) 1) :
    ¬ IsUniquelyTwoDivisible (Additive (π_ (n + 2) (sphere (0 : E) 1) x)) := fun hx ↦
  not_isUniquelyTwoDivisible_int (hx.of_addEquiv (homotopyGroupSphereAddEquivOfFinrankEq hE x))

/-- **No fibre with trivial `π_{n+1}` over `S^{n+2}` has a total space with trivial
`π_{n+2}`.** Let `p : X → S^{n+2}` be a Serre fibration whose fibre over `y` has trivial
`π_{n+1}` at `e`, as a `K(A, n + 2)` space does. Then `π_{n+2}(X, e)` is nontrivial, since
`π_{n+2}(S^{n+2}) ≅ ℤ` is (`TauCeti.TopCat.nontrivial_homotopyGroup_of_mem_serreFibrations`). In
particular, for `n = 0`, there is no fibration `K(π₃(S²), 2) → X → S²` with `X` `3`-connected. -/
theorem nontrivial_homotopyGroup_of_mem_serreFibrations_sphere {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : Module.finrank ℝ E = n + 3) {X : TopCat.{u}}
    {p : X ⟶ TopCat.of (sphere (0 : E) 1)} (hp : TopCat.serreFibrations p)
    {y : sphere (0 : E) 1} (e : p.fiber y) [Subsingleton (π_ (n + 1) (p.fiber y) e)] :
    Nontrivial (π_ (n + 2) X e.val) :=
  have := nontrivial_homotopyGroup_sphere hE y
  TopCat.nontrivial_homotopyGroup_of_mem_serreFibrations hp

end Sphere

end TauCeti
