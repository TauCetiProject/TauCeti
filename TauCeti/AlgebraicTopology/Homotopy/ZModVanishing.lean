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
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ZMod

/-!
# Mod-`m` and mod-two vanishing theorems for higher homotopy groups

**Theorem** (Serre). Let `Y` be a topological space with a base point `y` such that `π₁(Y, y)` is
trivial, and let `m : ℕ`. If the singular homology `H_q(Y; ℤ/m)` vanishes in the finite range
`2 ≤ q ≤ n + 3`, then multiplication by `m` is a bijection on `π_{n + 2}(Y, y)`
(`TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`). No Hausdorff,
path-connectedness, CW, or finite-generation assumption is needed on `Y`, and `m` need not be
prime or nonzero. For `m = 2` this is the **mod-two vanishing theorem**: if `π₁(Y, y)` is trivial
and the reduced mod-two singular homology of `Y` vanishes in every degree, then every higher
homotopy group `π_{n + 2}(Y, y)` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo`), hence
becomes a `ℤ[1/2]`-module and satisfies `π_{n + 2}(Y, y) ⊗ 𝔽₂ = 0`.

The class of groups `G` with `G ⊗ ℤ/2 = 0` is not a Serre class (it contains `ℚ` but not `ℤ`), so
this is not a case of the Hurewicz theorem modulo a Serre class; it is proved directly, one
homotopy group at a time, along the Whitehead tower
(`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`), with two inputs:

* **First homotopy group.** When `π_k(Z, z)` vanishes for `1 ≤ k < j + 2`, the Hurewicz
  isomorphism on the CW approximation of the path component of `z` and the mod-`m` coefficient
  exact sequence make multiplication by `m` bijective on `π_{j + 2}(Z, z)` from vanishing of
  `H_{j + 2}(Z; ℤ/m)` and `H_{j + 3}(Z; ℤ/m)`
  (`TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod`).
* **Eilenberg--Mac Lane spaces.** Every fibre of the `(j + 2)`-connected cover `W⟨j + 2⟩ → W` of
  the `(j + 1)`-connected Hausdorff CW approximation `W` is a `K(π_{j + 2} W, j + 1)`. Once
  `π_{j + 2} W` is uniquely `m`-divisible, every such fibre is acyclic modulo `m`
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`), so
  `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber` makes `W⟨j + 2⟩ → W` an
  isomorphism on `H_*(-; ℤ/m)`.

## Main results

* `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod`,
  `TauCeti.bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod`: sharp
  finite-range and reduced-homology mod-`m` vanishing theorems.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo`: the
  mod-two vanishing theorems.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.2 and 4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti

/-- **Sharp finite-range mod-`m` vanishing theorem.** Let `Y` be a space with a base point `y` such
that `π₁(Y, y)` is trivial, and let `m, n : ℕ`. If `H_q(Y; ℤ/m) = 0` for all `2 ≤ q ≤ n + 3`, then
multiplication by `m` is a bijection on `π_{n + 2}(Y, y)`. No Hausdorff, path-connectedness, CW,
or finite-generation assumption is required on `Y`, and `m` need not be prime or nonzero. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularChains (ZMod m)).obj (TopCat.of Y)).homology q)) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  prop_homotopyGroup_of_subsingleton_singularHomology (ZMod m)
    (fun G _ ↦ Function.Bijective fun a : G ↦ (m : ℤ) • a) 1
    (fun e h ↦ (e.bijective_zsmul_iff (m : ℤ)).1 h)
    (fun z j hZ hZk ↦
      bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod
        (fun k hk1 hk2 ↦ hZ k (by omega) hk2)
        (ModuleCat.isZero_iff_subsingleton.2 (hZk (j + 2) le_rfl (by omega)))
        (ModuleCat.isZero_iff_subsingleton.2 (hZk (j + 3) (by omega) le_rfl)))
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul (ZMod m)
        (by rw [Int.cast_natCast, ZMod.natCast_self]) hA hX)
    y n fun q hq1 hq2 ↦ ModuleCat.isZero_iff_subsingleton.1 (hY q hq1 hq2)

/-- **Reduced-homology mod-`m` vanishing theorem.** If `π₁(Y, y)` is trivial and the reduced
singular homology of `Y` with coefficients in `ZMod m` vanishes in every degree, then
multiplication by `m` is a bijection on every higher homotopy group `π_{n + 2}(Y, y)`. -/
theorem bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {m : ℕ}
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor
      (ModuleCat.of (ZMod m) (ZMod m)) q).obj (TopCat.of Y))) (n : ℕ) :
    Function.Bijective fun a : Additive (π_ (n + 2) Y y) ↦ (m : ℤ) • a :=
  bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod fun q hq _ ↦ by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact (hY (q' + 1)).of_iso
      ((reducedSingularHomologySuccIso (ModuleCat.of (ZMod m) (ZMod m)) q').app (TopCat.of Y)).symm

/-- **Sharp finite-range mod-two vanishing theorem.** If `π₁(Y, y)` is trivial and `H_q(Y; 𝔽₂) = 0`
for all `2 ≤ q ≤ n + 3`, then `π_{n + 2}(Y, y)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)] {n : ℕ}
    (hY : ∀ q, 2 ≤ q → q ≤ n + 3 →
      IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  (isUniquelyTwoDivisible_iff _).2
    (bijective_zsmul_homotopyGroup_of_isZero_singularHomology_zmod hY)

/-- **The mod-two vanishing theorem.** If `π₁(Y, y)` is trivial and the reduced mod-two singular
homology of `Y` vanishes in every degree, then every higher homotopy group `π_{n + 2}(Y, y)` is
uniquely two-divisible (hence is a `ℤ[1/2]`-module and satisfies `π_{n + 2}(Y, y) ⊗ 𝔽₂ = 0`). -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_modTwo {Y : Type}
    [TopologicalSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
    (hY : ∀ q, IsZero ((reducedSingularHomologyFunctor
      (ModuleCat.of (ZMod 2) (ZMod 2)) q).obj (TopCat.of Y))) (n : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  (isUniquelyTwoDivisible_iff _).2
    (bijective_zsmul_homotopyGroup_of_isZero_reducedSingularHomology_zmod hY n)

end TauCeti
