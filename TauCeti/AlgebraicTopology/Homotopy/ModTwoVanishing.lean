/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.PathComponent
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two vanishing of homotopy groups

**Theorem** (Serre). Let `Y` be a simply connected space with the mod-two homology of a point,
`Hᵢ(Y; 𝔽₂) = 0` for `i > 0`. Then every homotopy group `πᵢ(Y)` is uniquely two-divisible:
multiplication by two is a bijection, so `πᵢ(Y)` is a module over `ℤ[1/2]` and `πᵢ(Y) ⊗ ℤ/2 = 0`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). No finite
generation and no CW structure is assumed.

The space `Y` lies in an arbitrary universe `u`. Mod-two homology is then taken with coefficients
in a ring `k` in the universe `u` together with a ring isomorphism `k ≃+* ZMod 2`, for instance
`ZMod 2` itself when `u` is the lowest universe, or its lift `ULift.{u} (ZMod 2)`. The hypothesis
can also be stated with coefficients in the integer module `ℤ/2`, lifted to the universe `u`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`).

Since a path component has the homotopy groups of the ambient space in positive degrees, and is
simply connected as soon as the ambient fundamental group is trivial
(`TauCeti.simplyConnectedSpace_pathComponent_iff`), the theorem also applies to a single path
component: if the fundamental group of `Y` at `y` is trivial and the path component of `y` has
the mod-two homology of a point, every `πₙ₊₂(Y, y)` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`).
No hypothesis is made on the other path components of `Y`.

The class of groups `G` with `G ⊗ ℤ/2 = 0` is not a Serre class (it contains `ℚ` but not `ℤ`), so
this is not a case of the Hurewicz theorem modulo a Serre class; it is proved directly, one
homotopy group at a time, along the Whitehead tower.

* **First homotopy group.** If `Z` is `(n - 1)`-connected, `n ≥ 2`, the Hurewicz isomorphism
  `πₙ(Z) ≅ Hₙ(Z; ℤ)` and the coefficient sequence `ℤ → ℤ → ℤ/2` make `πₙ(Z)` uniquely
  two-divisible as soon as `Hₙ(Z; 𝔽₂)` and `Hₙ₊₁(Z; 𝔽₂)` vanish
  (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).
* **One step up the tower.** If moreover `Z` is Hausdorff and has the mod-two homology of a point,
  then so does its `n`-connected cover `Z⟨n⟩`
  (`TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`).
  The projection `Z⟨n⟩ → Z` is a fibration whose fibres are `K(πₙ(Z), n - 1)` spaces
  (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Since `πₙ(Z)` is uniquely
  two-divisible, these have the mod-two homology of a point
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`), so
  such a fibration is a mod-two homology isomorphism
  (`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`).
* **The induction.** The cover `Z⟨n⟩` is `n`-connected and has the homotopy groups of `Z` above
  `n`, so the first step applies to it in degree `n + 1`. Each stage is replaced by its CW
  approximation, which is Hausdorff and changes neither homotopy nor homology. This induction is
  shared with the rational form of Serre's theorem
  (`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`).

The Eilenberg--Mac Lane fibre sits over the `(n - 1)`-connected stage `Z`, never over the original
space: only the fibration `K(πₙ Z, n - 1) → Z⟨n⟩ → Z` between successive stages is used.

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`: the same,
  with the hypothesis on singular homology with coefficients in the integer module `ℤ/2`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`:
  if the fundamental group of `Y` at `y` is trivial and the path component of `y` has the mod-two
  homology of a point, the higher homotopy groups of `Y` at `y` are uniquely two-divisible.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

variable {k : Type u} [CommRing k]

/-- The first possible homotopy group, in the form used by the induction: the homotopy group
`πₙ₊₂` of an `(n + 1)`-connected space with the mod-two homology of a point is uniquely
two-divisible. -/
private theorem isUniquelyTwoDivisible_homotopyGroup_of_connected (e : k ≃+* ZMod 2)
    {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ)
    (hZ : ∀ j, j ≠ 0 → j < n + 2 → Subsingleton (π_ j Z z))
    (hZ₂ : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Z)).homology (i + 1))) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Z z)) := by
  refine isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two e (fun j hj ↦ ?_)
    (hZ₂ (n + 1)) (hZ₂ (n + 2))
  rcases eq_or_ne j 0 with rfl | hj0
  · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
  · exact hZ j hj0 hj

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. The homology is taken with coefficients in the field `𝔽₂`, given
as any ring `k` isomorphic to `ZMod 2` in the universe of `Y`. No finite generation or CW
structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology (e : k ≃+* ZMod 2)
    {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  have : IsSemisimpleRing k := e.symm.isSemisimpleRing
  have hk : (2 : k) = 0 := e.injective (by rw [map_ofNat, map_zero]; decide)
  prop_homotopyGroup_of_subsingleton_singularHomology k
    (fun G _ ↦ IsUniquelyTwoDivisible G) (fun e h ↦ h.of_addEquiv e)
    (isUniquelyTwoDivisible_homotopyGroup_of_connected e)
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk hA hX)
    hY y n

/-- **Mod-two vanishing with integer-module coefficients.** The homotopy groups `πᵢ(Y)`, `i ≥ 2`,
of a simply connected space `Y` whose singular homology with coefficients in the integer module
`ℤ/2` vanishes in positive degrees are uniquely two-divisible. This is the form in which the
coefficients `ℤ/2` appear in the coefficient sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two {Y : Type u}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (i + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of Y)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology ULift.ringEquiv
    (fun i ↦ ModuleCat.isZero_iff_subsingleton.1
      (((TopCat.of Y).isZero_singularHomology_modTwo_iff_of_ringEquiv ULift.ringEquiv _).1
        (hY i))) y n

/-- **Mod-two vanishing for a path component.** If the fundamental group of `Y` at `y` is trivial
and the path component of `y` has the mod-two homology of a point, with coefficients in a ring `k`
isomorphic to `ZMod 2`, then every homotopy group `πₙ₊₂(Y, y)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    (e : k ≃+* ZMod 2) {Y : Type u} [TopologicalSpace Y] (y : Y)
    [Subsingleton (FundamentalGroup Y y)]
    (hY : ∀ i, Subsingleton
      (((singularChains k).obj (TopCat.of (pathComponent y))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  have := (simplyConnectedSpace_pathComponent_iff y).2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology e hY
    (pathComponentSelf y) n).of_addEquiv
      (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).toAdditive

end TauCeti
