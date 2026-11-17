/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible

/-!
# Mod-two vanishing of homotopy groups

**Theorem** (Serre). Let `Y` be a simply connected space with the mod-two homology of a point,
`Hᵢ(Y; 𝔽₂) = 0` for `i > 0`. Then every homotopy group `πᵢ(Y)` is uniquely two-divisible:
multiplication by two is a bijection, so `πᵢ(Y)` is a module over `ℤ[1/2]` and `πᵢ(Y) ⊗ ℤ/2 = 0`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). No finite
generation and no CW structure is assumed.

The class of groups `G` with `G ⊗ ℤ/2 = 0` is not a Serre class (it contains `ℚ` but not `ℤ`), so
this is not a case of the Hurewicz theorem modulo a Serre class; it is proved directly, one
homotopy group at a time, along the Whitehead tower.

* **First homotopy group.** If `Z` is `(n - 1)`-connected, `n ≥ 2`, the Hurewicz isomorphism
  `πₙ(Z) ≅ Hₙ(Z; ℤ)` and the coefficient sequence `ℤ → ℤ → ℤ/2` make `πₙ(Z)` uniquely
  two-divisible as soon as `Hₙ(Z; 𝔽₂)` and `Hₙ₊₁(Z; 𝔽₂)` vanish
  (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).
* **One step up the tower.** If moreover `Z` is Hausdorff and has the mod-two homology of a point,
  then so does its `n`-connected cover `Z⟨n⟩`
  (`TauCeti.subsingleton_singularHomology_nConnectedCover`).
  The projection `Z⟨n⟩ → Z` is a fibration whose fibres are `K(πₙ(Z), n - 1)` spaces
  (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Since `πₙ(Z)` is uniquely
  two-divisible, such a fibration is a mod-two homology isomorphism
  (`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`).
* **The induction.** The cover `Z⟨n⟩` is `n`-connected and has the homotopy groups of `Z` above
  `n`, so the first step applies to it in degree `n + 1`. Each stage is replaced by its CW
  approximation, which is Hausdorff and changes neither homotopy nor homology. This induction is
  shared with the rational form of Serre's theorem
  (`TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology`).

The Eilenberg--Mac Lane fibre sits over the `(n - 1)`-connected stage `Z`, never over the original
space: only the fibration `K(πₙ Z, n - 1) → Z⟨n⟩ → Z` between successive stages is used.

## Main results

* `TauCeti.subsingleton_singularHomology_nConnectedCover`: the `n`-connected cover of an
  `(n - 1)`-connected Hausdorff space with the mod-two homology of a point has the mod-two
  homology of a point.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 4.1–4.3.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

/-- The first possible homotopy group, in the form used by the induction: the homotopy group
`πₙ₊₂` of an `(n + 1)`-connected space with the mod-two homology of a point is uniquely
two-divisible. -/
private theorem isUniquelyTwoDivisible_homotopyGroup_of_connected
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) (n : ℕ)
    (hZ : ∀ k, k ≠ 0 → k < n + 2 → Subsingleton (π_ k Z z))
    (hZ₂ : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Z)).homology (i + 1))) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) Z z)) := by
  refine isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two (fun k hk ↦ ?_)
    (hZ₂ (n + 1)) (hZ₂ (n + 2))
  rcases eq_or_ne k 0 with rfl | hk0
  · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
  · exact hZ k hk0 hk

/-- **The `n`-connected cover of a mod-two acyclic space is mod-two acyclic.** Let `X` be a
Hausdorff, path-connected space whose homotopy groups `πₖ` vanish for `1 ≤ k < n`, `n ≥ 2`, and
which has the mod-two homology of a point. Then its `n`-connected cover `X⟨n⟩` has the mod-two
homology of a point. -/
theorem subsingleton_singularHomology_nConnectedCover (X : TopCat.{0}) [T2Space X]
    [PathConnectedSpace X] (x : X) (m : ℕ)
    (hX : ∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k X x))
    (hX₂ : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj X).homology (i + 1))) (i : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (nConnectedCover (m + 2) X x)).homology
      (i + 1)) :=
  -- `πₘ₊₂(X)` is uniquely two-divisible, by the Hurewicz theorem, so the fibres of the
  -- projection, which are `K(πₘ₊₂(X), m + 1)` spaces, have the mod-two homology of a point.
  subsingleton_singularHomology_nConnectedCover_of_fiber (ZMod 2) X x m hX hX₂
    (fun hY ↦ IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible
      (isUniquelyTwoDivisible_homotopyGroup_of_connected x m hX hX₂)
      (hY.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm)) i

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. No finite generation or CW structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  prop_homotopyGroup_of_subsingleton_singularHomology (ZMod 2)
    (fun G _ ↦ IsUniquelyTwoDivisible G) (fun e h ↦ h.of_addEquiv e)
    isUniquelyTwoDivisible_homotopyGroup_of_connected
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible hA hX)
    hY y n

end TauCeti
