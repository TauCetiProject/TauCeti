/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo
import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

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
  (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two`).
* **One step up the tower.** If moreover `Z` is Hausdorff and has the mod-two homology of a point,
  then so does its `n`-connected cover `Z⟨n⟩`
  (`TauCeti.subsingleton_singularHomology_nConnectedCover`).
  The projection `Z⟨n⟩ → Z` is a fibration whose fibres are homotopy equivalent to a
  `K(πₙ(Z), n - 1)` space, which has the mod-two homology of a point because `πₙ(Z)` is uniquely
  two-divisible
  (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`). A
  Serre fibration whose fibres have the homology of a point is a homology isomorphism
  (`TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber`).
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
  -- The Hurewicz step takes integral homology with coefficients in the integer module `ℤ/2`.
  refine isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two (fun k hk ↦ ?_)
    (((TopCat.of Z).isZero_singularHomology_modTwo_iff' _).2
      (@ModuleCat.isZero_of_subsingleton _ _ _ (hZ₂ (n + 1))))
    (((TopCat.of Z).isZero_singularHomology_modTwo_iff' _).2
      (@ModuleCat.isZero_of_subsingleton _ _ _ (hZ₂ (n + 2))))
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
  -- `X` with its higher homotopy groups killed is a `K(πₘ₊₂(X), m + 2)` space.
  have hK := (isEilenbergMacLaneSpace_killHomotopyGroups (m + 2) X x hX).of_mulEquiv
    (MulEquiv.multiplicativeAdditive _).symm
  have := hK.pathConnectedSpace
  -- Every fibre of the projection is homotopy equivalent to the loop space of that space, a
  -- `K(πₘ₊₂(X), m + 1)` space.
  have hfib (b : X) : ∃ y, IsEilenbergMacLaneSpace (Multiplicative (Additive (π_ (m + 2) X x)))
      (m + 1) ((nConnectedCoverProj (m + 2) X x).fiber b) y := by
    -- The projection is the source projection of the mapping-path fibre.
    have hset : ⇑(nConnectedCoverProj (m + 2) X x) ⁻¹' {b} =
        MappingPathFiber.proj (killHomotopyGroupsIncl (m + 2 + 1) X x).hom
          (killHomotopyGroupsIncl (m + 2 + 1) X x x) ⁻¹' {b} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, MappingPathFiber.proj_apply]
      exact Iff.of_eq (congrArg (· = b) (TopCat.Hom.homotopyFiberProj_apply _ x z))
    let e := ((Homeomorph.setCongr hset).toHomotopyEquiv.trans
      (MappingPathFiber.projFiberHomotopyEquivLoopSpace _ _ b
        (PathConnectedSpace.somePath _ _))).symm
    exact ⟨e (Path.refl _), hK.loopSpace.of_homotopyEquiv e _⟩
  have hiso := TauCeti.TopCat.isIso_singularHomologyMap_of_isZero_fiber
    (serreFibrations_nConnectedCoverProj (m + 2) X x) (ZMod 2) (i + 1)
    (fun b ↦ (hfib b).choose_spec.pathConnectedSpace) fun b q hq0 _ ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      -- `TopCat.of` of the carrier of the fibre is the fibre itself, up to unfolding.
      exact @ModuleCat.isZero_of_subsingleton _ _ _
        ((hfib b).choose_spec.subsingleton_singularHomology_of_isUniquelyTwoDivisible hπ q)
  exact ModuleCat.subsingleton_of_isZero <|
    (@ModuleCat.isZero_of_subsingleton _ _ _ (hX₂ i)).of_iso
      (@asIso _ _ _ _ _ hiso)

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
    have hπ (k : ℕ) [NeZero k] : Nonempty (π_ k X x₀ ≃* π_ k Z z) :=
      (nonempty_homotopyGroupMulEquiv (N := Fin k) (x := f x₀) (y := z)).map
        (MulEquiv.ofBijective (HomotopyGroup.mapHom f rfl) (hf.bijective k x₀)).trans
    have hX : ∀ k, k ≠ 0 → k < n + 2 → Subsingleton (π_ k X x₀) := fun k hk0 hk ↦ by
      have : NeZero k := ⟨hk0⟩
      have := hZ k hk0 hk
      exact (hπ k).some.toEquiv.subsingleton
    -- The `(n + 2)`-connected cover `C` of `X` is `(n + 2)`-connected and mod-two acyclic.
    let C := nConnectedCover (n + 2) X x₀
    let c₀ := nConnectedCoverBasepoint (n + 2) X x₀
    have hC : ∀ k, k ≠ 0 → k < n + 1 + 2 → Subsingleton (π_ k C c₀) := fun k _ hk ↦
      subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace (n + 2) X x₀ c₀
        (by omega)
    -- `f` is a homology isomorphism, so `X` is mod-two acyclic.
    have hX₂ (i : ℕ) : Subsingleton (((singularChains (ZMod 2)).obj X).homology (i + 1)) :=
      ModuleCat.subsingleton_of_isZero <| (@ModuleCat.isZero_of_subsingleton _ _ _ (hZ₂ i)).of_iso
        (@asIso _ _ _ _ _ (hf.isIso_singularHomologyMap (ModuleCat.of (ZMod 2) (ZMod 2)) (i + 1)))
    have hC₂ := subsingleton_singularHomology_nConnectedCover X x₀ n hX hX₂
    -- The cover has the homotopy groups of `X`, hence of `Z`, above dimension `n + 2`.
    exact (ih (n + 1) c₀ hC hC₂ _ (by omega)).of_addEquiv
      ((nConnectedCoverHomotopyGroupMulEquiv (n + 2) X x₀ _ (by omega)).trans
        (hπ _).some).toAdditive

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

end TauCeti
