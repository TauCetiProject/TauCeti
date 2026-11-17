/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ZMod

/-!
# Mod-two vanishing of homotopy groups

**Theorem** (Serre). Let `Y` be a simply connected space with the mod-two homology of a point,
`Hᵢ(Y; 𝔽₂) = 0` for `i > 0`. Then every homotopy group `πᵢ(Y)` is uniquely two-divisible:
multiplication by two is a bijection, so `πᵢ(Y)` is a module over `ℤ[1/2]` and `πᵢ(Y) ⊗ ℤ/2 = 0`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). No finite
generation and no CW structure is assumed.

This theorem specializes the sharp finite-range mod-`m` vanishing theorem in
`TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ZMod` (`m = 2`,
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo`). We also keep
the one-step connected-cover preservation lemma
`TauCeti.subsingleton_singularHomology_nConnectedCover`: if `X` is Hausdorff, path-connected,
`(n - 1)`-connected (`n ≥ 2`), and has the mod-two homology of a point, then so does its
`n`-connected cover `X⟨n⟩`, since the fibres of `X⟨n⟩ → X` are `K(πₙ X, n - 1)` spaces
(`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`) and `πₙ X` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).

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

/-- The first possible homotopy group, in the form used by
`subsingleton_singularHomology_nConnectedCover`: the homotopy group `πₙ₊₂` of an
`(n + 1)`-connected space with the mod-two homology of a point is uniquely two-divisible. -/
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
      (i + 1)) := by
  -- `πₘ₊₂(X)` is uniquely two-divisible, by the Hurewicz theorem.
  have hπ := isUniquelyTwoDivisible_homotopyGroup_of_connected x m hX hX₂
  -- Every fibre of the projection is a `K(πₘ₊₂(X), m + 1)` space, so it has the mod-two
  -- homology of a point and the projection is a mod-two homology isomorphism.
  have := isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber (ZMod 2) (m := 2)
    (by decide) ((isUniquelyTwoDivisible_iff _).1 hπ)
    (serreFibrations_nConnectedCoverProj (m + 2) X x)
    (fun b ↦ (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj X x m hX b).imp fun _ h ↦
      h.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm) (i + 1)
  exact (subsingleton_singularChains_homology_iff_of_isIso _
    (nConnectedCoverProj (m + 2) X x) _).2 (hX₂ i)

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. No finite generation or CW structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  have : Subsingleton (π_ 1 Y y) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo fun q hq _ ↦
    ModuleCat.isZero_iff_subsingleton.2 <| by
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact hY i

end TauCeti
