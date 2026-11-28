/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.Algebra.Group.Equiv.Pow
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.AlgebraicTopology.Singular.Coefficients.ZModCoefficientSequence
import TauCeti.AlgebraicTopology.Singular.Homotopy.CWApproximation

/-!
# Mod-`m` Hurewicz theorem for the first possible homotopy group

For a pointed space `(X, x)` whose positive homotopy groups `π_k(X, x)` vanish for `1 ≤ k < n + 2`
and any `m : ℕ`, vanishing of mod-`m` singular homology in the two adjacent degrees `n + 2` and
`n + 3` implies that multiplication by `m` is bijective on `π_{n + 2}(X, x)`
(`TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod`).
No path-connectedness, Hausdorff, CW, or finite-generation assumption is imposed on `X`, and `m`
need not be prime or nonzero.

The proof passes to the CW approximation of the path component of `x` (preserving positive homotopy
groups via `TauCeti.cwApproximationPathComponentHomotopyGroupMulEquiv` and singular homology
vanishing via `TauCeti.isZero_singularHomologyFunctor_cwApproximation_of_isZero`), identifies
`π_{n + 2}`
with lifted integral homology via `HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv`, and
applies the mod-`m` coefficient sequence (`TopCat.bijective_zsmul_singularHomology_of_isZero_zmod`).
Both adjacent vanishing hypotheses matter: degree `n + 2` gives surjectivity of multiplication by
`m`, and degree `n + 3` rules out `m`-torsion.

## Main results

* `TauCeti.bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod`:
  unique `m`-divisibility of the first possible nonzero homotopy group from vanishing of
  `H_{n + 2}(-; ℤ/m)` and `H_{n + 3}(-; ℤ/m)`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.A and 4.2.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258--294.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

/-- **First nonzero homotopy group modulo `m`.** For a pointed space `(X, x)` in any universe `u`
whose positive homotopy groups `π_k(X, x)` vanish for `1 ≤ k < n + 2` and any `m : ℕ`, vanishing
of `H_{n + 2}(X; ℤ/m)` and `H_{n + 3}(X; ℤ/m)` (with lifted integer-module coefficients) makes
multiplication by `m` bijective on `π_{n + 2}(X, x)`. No path-connectedness, separation, or CW
assumption is needed on `X`. -/
theorem bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod
    {X : Type u} [TopologicalSpace X] {x : X} {n m : ℕ}
    (hX : ∀ k, 1 ≤ k → k < n + 2 → Subsingleton (π_ k X x))
    (hn : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj (TopCat.of X)))
    (hn' : IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 3)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod m)))).obj (TopCat.of X))) :
    Function.Bijective fun a : Additive (π_ (n + 2) X x) ↦ (m : ℤ) • a := by
  let Z := cwApproximation (TopCat.of X) (Quotient.out (ZerothHomotopy.mk x))
  let z := cwApproximationBasepoint (TopCat.of X) (Quotient.out (ZerothHomotopy.mk x))
  have hZ : ∀ k < n + 2, Subsingleton (π_ k Z z) := fun k hk ↦ match k with
    | 0 => HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    | k + 1 =>
      have : Subsingleton (π_ (k + 1) X x) := hX (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hk
      (cwApproximationPathComponentHomotopyGroupMulEquiv x k).toEquiv.subsingleton
  have hbij := (TopCat.of Z).bijective_zsmul_singularHomology_of_isZero_zmod m (n + 2)
    (isZero_singularHomologyFunctor_cwApproximation_of_isZero x
      (ModuleCat.of ℤ (ULift.{u} (ZMod m))) (n + 2) hn)
    (isZero_singularHomologyFunctor_cwApproximation_of_isZero x
      (ModuleCat.of ℤ (ULift.{u} (ZMod m))) (n + 3) hn')
  have hπ : Function.Bijective fun a : Additive (π_ (n + 2) Z z) ↦ (m : ℤ) • a :=
    ((HomotopyGroup.cubicalHurewiczSingularHomologyUliftAddEquiv hZ).bijective_zsmul_iff
      (m : ℤ)).2 hbij
  exact ((cwApproximationPathComponentHomotopyGroupMulEquiv x
    (n + 1)).toAdditive.bijective_zsmul_iff (m : ℤ)).1 hπ

/-- **First nonzero homotopy group modulo `m` with ring coefficients.** For a pointed space `(X, x)`
in any universe `u` whose positive homotopy groups `π_j(X, x)` vanish for `1 ≤ j < n + 2` and any
commutative ring `k ≃+* ZMod m` in the universe of `X`, vanishing of `H_{n + 2}(X; k)` and
`H_{n + 3}(X; k)` makes multiplication by `m` bijective on `π_{n + 2}(X, x)`. -/
theorem bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_ringEquiv
    {k : Type u} [CommRing k] {m : ℕ} (e : k ≃+* ZMod m) {X : Type u} [TopologicalSpace X]
    {x : X} {n : ℕ}
    (hX : ∀ j, 1 ≤ j → j < n + 2 → Subsingleton (π_ j X x))
    (hn : IsZero (((singularChains k).obj (TopCat.of X)).homology (n + 2)))
    (hn' : IsZero (((singularChains k).obj (TopCat.of X)).homology (n + 3))) :
    Function.Bijective fun a : Additive (π_ (n + 2) X x) ↦ (m : ℤ) • a := by
  rw [← singularHomologyFunctor_obj_obj] at hn hn'
  exact bijective_zsmul_homotopyGroup_of_subsingleton_lower_homotopyGroups_of_isZero_zmod hX
    (((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv m e (n + 2)).2 hn)
    (((TopCat.of X).isZero_singularHomology_zmod_iff_of_ringEquiv m e (n + 3)).2 hn')

end TauCeti
