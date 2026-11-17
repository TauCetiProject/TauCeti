/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.PathComponent
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two vanishing of homotopy groups

**Theorem** (Serre). Let `Y` be a simply connected space with the mod-two homology of a point,
`Hᵢ(Y; 𝔽₂) = 0` for `i > 0`. Then every homotopy group `πᵢ(Y)` is uniquely two-divisible:
multiplication by two is a bijection, so `πᵢ(Y)` is a module over `ℤ[1/2]` and `πᵢ(Y) ⊗ ℤ/2 = 0`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). No finite
generation and no CW structure is assumed.

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
  (`TauCeti.subsingleton_singularHomology_nConnectedCover`).
  The projection `Z⟨n⟩ → Z` is a fibration whose fibres are `K(πₙ(Z), n - 1)` spaces
  (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Since `πₙ(Z)` is uniquely
  two-divisible, such a fibration is a mod-two homology isomorphism
  (`TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`).
* **The induction.** The cover `Z⟨n⟩` is `n`-connected and has the homotopy groups of `Z` above
  `n`, so the first step applies to it in degree `n + 1`. Each stage is replaced by its CW
  approximation, which is Hausdorff and changes neither homotopy nor homology.

The Eilenberg--Mac Lane fibre sits over the `(n - 1)`-connected stage `Z`, never over the original
space: only the fibration `K(πₙ Z, n - 1) → Z⟨n⟩ → Z` between successive stages is used.

## Main results

* `TauCeti.subsingleton_singularHomology_nConnectedCover`: the `n`-connected cover of an
  `(n - 1)`-connected Hausdorff space with the mod-two homology of a point has the mod-two
  homology of a point.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.
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

/-- The induction along the Whitehead tower: for an `(n + 1)`-connected space with the mod-two
homology of a point, every homotopy group `π_{N + 2}` with `N ≥ n` is uniquely two-divisible. The
degree is `N = n + d`, by induction on `d`. -/
private theorem isUniquelyTwoDivisible_homotopyGroup_of_add (d : ℕ) :
    ∀ (n : ℕ) {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z),
      (∀ k, k ≠ 0 → k < n + 2 → Subsingleton (π_ k Z z)) →
      (∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Z)).homology (i + 1))) →
        ∀ N, N = n + d → IsUniquelyTwoDivisible (Additive (π_ (N + 2) Z z)) := by
  induction d with
  | zero =>
    intro n Z _ _ z hZ hZ₂ N hN
    rw [hN]
    exact isUniquelyTwoDivisible_homotopyGroup_of_connected z n hZ hZ₂
  | succ d ih =>
    intro n Z _ _ z hZ hZ₂ N hN
    rw [hN]
    -- Replace `Z` by its CW approximation `X`, which is Hausdorff.
    let X := cwApproximation (TopCat.of Z) z
    let f := (cwApproximationMap (TopCat.of Z) z).hom
    let x₀ := cwApproximationBasepoint (TopCat.of Z) z
    have hf : f.IsWeakHomotopyEquivalence :=
      isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Z) z
    -- `f` identifies the homotopy groups of `X` at `x₀` with those of `Z` at `z`.
    let e (k : ℕ) [NeZero k] : π_ k X x₀ ≃* π_ k Z z :=
      MulEquiv.ofBijective
        (HomotopyGroup.mapHom f (cwApproximationMap_cwApproximationBasepoint (TopCat.of Z) z))
        ((HomotopyGroup.bijective_map_congr rfl rfl _).1 (hf.bijective k x₀))
    have hX : ∀ k, k ≠ 0 → k < n + 2 → Subsingleton (π_ k X x₀) := fun k hk0 hk ↦ by
      have : NeZero k := ⟨hk0⟩
      have := hZ k hk0 hk
      exact (e k).toEquiv.subsingleton
    -- The `(n + 2)`-connected cover `C` of `X` is `(n + 2)`-connected and mod-two acyclic.
    let C := nConnectedCover (n + 2) X x₀
    let c₀ := nConnectedCoverBasepoint (n + 2) X x₀
    have hC : ∀ k, k ≠ 0 → k < n + 1 + 2 → Subsingleton (π_ k C c₀) := fun k _ hk ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2) X x₀ c₀
        (by omega)
    -- `f` is a homology isomorphism, so `X` is mod-two acyclic.
    have hX₂ (i : ℕ) : Subsingleton (((singularChains (ZMod 2)).obj X).homology (i + 1)) := by
      have := hf.isIso_singularHomologyMap (ModuleCat.of (ZMod 2) (ZMod 2)) (i + 1)
      exact (subsingleton_singularChains_homology_iff_of_isIso _
        (cwApproximationMap (TopCat.of Z) z) _).2 (hZ₂ i)
    have hC₂ := subsingleton_singularHomology_nConnectedCover X x₀ n hX hX₂
    -- The cover has the homotopy groups of `X`, hence of `Z`, above dimension `n + 2`.
    exact (ih (n + 1) c₀ hC hC₂ _ (by omega)).of_addEquiv
      ((nConnectedCoverHomotopyGroupMulEquiv (n + 2) X x₀ _ (by omega)).trans
        (e _)).toAdditive

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. No finite generation or CW structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) := by
  -- `Y` is `1`-connected: its fundamental group is trivial.
  have h₁ (k : ℕ) (hk0 : k ≠ 0) (hk : k < 2) : Subsingleton (π_ k Y y) := by
    obtain rfl : k = 1 := by omega
    exact HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton
  exact isUniquelyTwoDivisible_homotopyGroup_of_add n 0 y h₁ hY n (Nat.zero_add n).symm

/-- **Mod-two vanishing for a path component.** If the fundamental group of `Y` at `y` is trivial
and the path component of `y` has the mod-two homology of a point, then every homotopy group
`πₙ₊₂(Y, y)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    {Y : Type} [TopologicalSpace Y] (y : Y) [Subsingleton (FundamentalGroup Y y)]
    (hY : ∀ i, Subsingleton
      (((singularChains (ZMod 2)).obj (TopCat.of (pathComponent y))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  have := (simplyConnectedSpace_pathComponent_iff y).2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology hY
    (pathComponentSelf y) n).of_addEquiv
      (HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).toAdditive

end TauCeti
