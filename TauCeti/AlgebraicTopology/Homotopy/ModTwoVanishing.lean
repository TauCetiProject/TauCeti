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
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two vanishing of homotopy groups

**Theorem** (Serre). Let `(Y, y)` be a path-connected topological space with trivial fundamental
group `π₁(Y, y)` and let `m : ℕ`. If the singular homology of `Y` with `𝔽₂ = ZMod 2` coefficients
vanishes in the finite range of degrees `2, …, m + 3` (`H_{q+2}(Y; 𝔽₂) = 0` for `q ≤ m + 1`), then
the homotopy group `π_{m+2}(Y, y)` is uniquely two-divisible — equivalently, multiplication by two
is a bijection, so `π_{m+2}(Y, y)` is a module over `ℤ[1/2]`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`) — and in
particular `π_{m+2}(Y, y) ⊗_ℤ ℤ/2 = 0`
(`TauCeti.subsingleton_homotopyGroup_tensorProduct_zmod_two_of_isZero_singularHomology_mod_two`).
In particular, if `Y` is simply connected and has the mod-two homology of a point
(`Hᵢ(Y; 𝔽₂) = 0` for all `i > 0`), every higher homotopy group `πᵢ(Y)` (`i ≥ 2`) is uniquely
two-divisible (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`).
No CW, separation, or finite-generation hypothesis is imposed on `Y` or on its homotopy groups.

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

* **First homotopy group.** If `(Z, z)` is `(m + 1)`-connected, the Hurewicz isomorphism
  `π_{m+2}(Z) ≅ H_{m+2}(Z; ℤ)` and the coefficient sequence `ℤ → ℤ → ℤ/2` make `π_{m+2}(Z)`
  uniquely two-divisible as soon as `H_{m+2}(Z; 𝔽₂)` and `H_{m+3}(Z; 𝔽₂)` vanish
  (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two`).
* **One step up the tower.** If moreover `Z` is Hausdorff, every fibre of the projection
  `Z⟨m + 2⟩ → Z` is a `K(π_{m+2}(Z), m + 1)` space
  (`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Since `π_{m+2}(Z)` is uniquely
  two-divisible, `Z⟨m + 2⟩ → Z` induces isomorphisms on mod-two homology in **every** degree `q`
  (`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`, via
  `TauCeti.isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber`). Hence vanishing of
  `H_q(Z; 𝔽₂)` passes to `Z⟨m + 2⟩` for any individual degree `q`
  (`TauCeti.isZero_singularHomology_nConnectedCover_mod_two`).
* **The induction.** Replacing `Y` once by its Hausdorff CW approximation
  `Z₀ = cwApproximation (TopCat.of Y) y` preserves path-connectedness, all homotopy groups, and
  mod-two singular homology. Iterating `Z ↦ Z⟨r + 2⟩` for `r < m` (each cover remains Hausdorff)
  produces an `(m + 1)`-connected Hausdorff space `(Z_m, z_m)` with vanishing mod-two homology in
  degrees `2, …, m + 3` and `π_k(Z_m, z_m) ≃* π_k(Y, y)` for `k > m + 1`, from which unique
  two-divisibility of `π_{m+2}(Y, y)` follows.

The Eilenberg--Mac Lane fibre sits over the `(n - 1)`-connected stage `Z`, never over the original
space: only the fibration `K(πₙ Z, n - 1) → Z⟨n⟩ → Z` between successive stages is used.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`,
  `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two`: if `(Z, z)` is Hausdorff,
  `(m + 1)`-connected, and has vanishing mod-two homology in degrees `m + 2` and `m + 3`, then
  `nConnectedCoverProj (m + 2) Z z` induces isomorphisms on mod-two homology in all degrees.
* `TauCeti.isZero_singularHomology_nConnectedCover_mod_two`: under the same hypotheses, vanishing
  of `H_q(Z; 𝔽₂)` passes from `Z` to `nConnectedCover (m + 2) Z z`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two`, and
  `isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_isZero_singularHomology_mod_two`
  (in `TauCeti`): if `(Y, y)` is simply connected and has vanishing mod-two homology in degrees
  `2, …, m + 3`, then `π_{m+2}(Y, y)` is uniquely two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`:
  if the fundamental group of `Y` at `y` is trivial and the path component of `y` has the mod-two
  homology of a point, the higher homotopy groups of `Y` at `y` are uniquely two-divisible.
* `TauCeti.subsingleton_homotopyGroup_tensorProduct_zmod_two_of_isZero_singularHomology_mod_two`:
  consequently `π_{m+2}(Y, y) ⊗_ℤ (ZMod 2) = 0`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter III, Theorem 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Sections 4.1–4.3.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

section OneStep

variable {Z : TopCat.{0}} [T2Space Z] {z : Z} {m : ℕ}

/-- **One-step connected-cover mod-two homology isomorphism.** Let `(Z, z)` be a Hausdorff,
`(m + 1)`-connected space whose mod-two homology vanishes in degrees `m + 2` and `m + 3`. Then the
projection `Z⟨m + 2⟩ ⟶ Z` of the `(m + 2)`-connected cover induces an isomorphism on `ZMod 2`
singular homology in every degree `q`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_mod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hm₂ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 2)))
    (hm₃ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 3))) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map (nConnectedCoverProj (m + 2) Z z)) := by
  have : PathConnectedSpace Z :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).2 (hZ 0 (Nat.zero_lt_succ _))
  have hdiv : IsUniquelyTwoDivisible (Additive (π_ (m + 2) Z z)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two hZ
      (ModuleCat.isZero_iff_subsingleton.1 hm₂) (ModuleCat.isZero_iff_subsingleton.1 hm₃)
  exact isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber (ZMod 2)
    (serreFibrations_nConnectedCoverProj (m + 2) Z z)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj Z z m fun k _ hk ↦ hZ k hk)
    (fun hX ↦ IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible hdiv
      (hX.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
    q

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hm₂ : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj Z))
    (hm₃ : IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 3)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj Z)) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ZMod 2))).map (nConnectedCoverProj (m + 2) Z z)) := by
  have hm₂' := (Z.isZero_singularHomology_modTwo_iff' (m + 2)).1 hm₂
  have hm₃' := (Z.isZero_singularHomology_modTwo_iff' (m + 3)).1 hm₃
  rw [singularHomologyFunctor_obj_obj] at hm₂' hm₃'
  exact (TopCat.Hom.isIso_singularHomologyMap_modTwo_iff' _ q).2
    (isIso_singularHomologyMap_nConnectedCoverProj_mod_two hZ hm₂' hm₃' q)

/-- **One-step preservation of mod-two homology vanishing.** If `(Z, z)` is Hausdorff,
`(m + 1)`-connected, and has vanishing mod-two homology in degrees `m + 2`, `m + 3`, and `q`, then
its `(m + 2)`-connected cover `nConnectedCover (m + 2) Z z` also has vanishing mod-two homology in
degree `q`. -/
theorem isZero_singularHomology_nConnectedCover_mod_two
    (hZ : ∀ k < m + 2, Subsingleton (π_ k Z z))
    (hm₂ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 2)))
    (hm₃ : IsZero (((singularChains (ZMod 2)).obj Z).homology (m + 3))) {q : ℕ}
    (hq : IsZero (((singularChains (ZMod 2)).obj Z).homology q)) :
    IsZero (((singularChains (ZMod 2)).obj (nConnectedCover (m + 2) Z z)).homology q) := by
  have := isIso_singularHomologyMap_nConnectedCoverProj_mod_two hZ hm₂ hm₃ q
  exact ModuleCat.isZero_iff_subsingleton.2
    ((subsingleton_singularChains_homology_iff_of_isIso (ZMod 2)
      (nConnectedCoverProj (m + 2) Z z) q).2 (ModuleCat.isZero_iff_subsingleton.1 hq))

end OneStep

section WhiteheadTower

/-- Inductive Whitehead-tower stages over a Hausdorff simply connected space `Z₀` whose mod-two
homology vanishes in degrees `2, …, N + 3`: for each `m ≤ N` there exists a Hausdorff,
path-connected, `(m + 1)`-connected space `(Z, z)` with vanishing mod-two homology in degrees
`2, …, N + 3` whose homotopy groups above dimension `m + 1` are isomorphic to those of `(Z₀, z₀)`.
-/
private theorem exists_whitehead_stage_of_t2Space (Z₀ : TopCat.{0}) [T2Space Z₀]
    [PathConnectedSpace Z₀] (z₀ : Z₀) (hπ₁ : Subsingleton (π_ 1 Z₀ z₀)) (N : ℕ)
    (hH₀ : ∀ q ≤ N + 1, IsZero (((singularChains (ZMod 2)).obj Z₀).homology (q + 2)))
    (m : ℕ) (hm : m ≤ N) :
    ∃ (Z : TopCat.{0}) (_ : T2Space Z) (_ : PathConnectedSpace Z) (z : Z),
      (∀ k < m + 2, Subsingleton (π_ k Z z)) ∧
      (∀ q ≤ N + 1, IsZero (((singularChains (ZMod 2)).obj Z).homology (q + 2))) ∧
      ∀ k : ℕ, [NeZero k] → m + 1 < k → Nonempty (π_ k Z z ≃* π_ k Z₀ z₀) := by
  induction m with
  | zero =>
    refine ⟨Z₀, inferInstance, inferInstance, z₀, fun k hk ↦ ?_, hH₀,
      fun k _ _ ↦ ⟨MulEquiv.refl _⟩⟩
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z₀).1 inferInstance
    · exact hπ₁
  | succ m ih =>
    obtain ⟨Z, hT2, hPC, z, hConn, hHZ, hEquiv⟩ := ih (by omega)
    let Z' := nConnectedCover (m + 2) Z z
    let z' := nConnectedCoverBasepoint (m + 2) Z z
    refine ⟨Z', inferInstance, inferInstance, z',
      fun k hk ↦ subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace
        (m + 2) Z z z' (by omega),
      fun q hq ↦ isZero_singularHomology_nConnectedCover_mod_two hConn
        (hHZ m (by omega)) (hHZ (m + 1) (by omega)) (hHZ q hq),
      fun k _ hk ↦ ?_⟩
    obtain ⟨e⟩ := hEquiv k (by omega)
    exact ⟨(nConnectedCoverHomotopyGroupMulEquiv (m + 2) Z z k (by omega)).trans e⟩

/-- **Mod-two vanishing of higher homotopy groups** (Serre). Let `(Y, y)` be a path-connected
topological space with trivial fundamental group `π₁(Y, y)` and let `m : ℕ`. If
`H_{q+2}(Y; ZMod 2) = 0` for every `q ≤ m + 1`, then the homotopy group `π_{m+2}(Y, y)` is uniquely
two-divisible (a module over `ℤ[1/2]`). No CW, separation, or finite-generation hypothesis is
assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 2))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) := by
  -- Replace `Y` by its Hausdorff CW approximation `Z₀`.
  let Z₀ := cwApproximation (TopCat.of Y) y
  let z₀ := cwApproximationBasepoint (TopCat.of Y) y
  let g := cwApproximationMap (TopCat.of Y) y
  have hg₀ : g.hom z₀ = y := cwApproximationMap_cwApproximationBasepoint (TopCat.of Y) y
  have he₁ : π_ 1 Z₀ z₀ ≃* π_ 1 Y y :=
    g.hom.homotopyGroupMulEquivOfBijective hg₀
      ((HomotopyGroup.bijective_map_congr rfl rfl hg₀).1
        (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y 0 z₀))
  have hπ₁Z₀ : Subsingleton (π_ 1 Z₀ z₀) := he₁.toEquiv.subsingleton_congr.2 hπ₁
  have hHZ₀ (q : ℕ) (hq : q ≤ m + 1) :
      IsZero (((singularChains (ZMod 2)).obj Z₀).homology (q + 2)) := by
    have :=
      (isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of Y) y).isIso_singularHomologyMap
        (ModuleCat.of (ZMod 2) (ZMod 2)) (q + 2)
    exact ModuleCat.isZero_iff_subsingleton.2
      ((subsingleton_singularChains_homology_iff_of_isIso (ZMod 2) g (q + 2)).2
        (ModuleCat.isZero_iff_subsingleton.1 (hH q hq)))
  obtain ⟨Z, _, _, z, hConn, hHZ, hEquiv⟩ :=
    exists_whitehead_stage_of_t2Space Z₀ z₀ hπ₁Z₀ m hHZ₀ m le_rfl
  have hdivZ : IsUniquelyTwoDivisible (Additive (π_ (m + 2) Z z)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two hConn
      (ModuleCat.isZero_iff_subsingleton.1 (hHZ m (by omega)))
      (ModuleCat.isZero_iff_subsingleton.1 (hHZ (m + 1) le_rfl))
  obtain ⟨eZ⟩ := hEquiv (m + 2) (by omega)
  have heY : π_ (m + 2) Z₀ z₀ ≃* π_ (m + 2) Y y :=
    g.hom.homotopyGroupMulEquivOfBijective hg₀
      ((HomotopyGroup.bijective_map_congr rfl rfl hg₀).1
        (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of Y) y (m + 1) z₀))
  exact hdivZ.of_addEquiv (eZ.trans heY).toAdditive

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of Y))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two hπ₁ fun q hq ↦ by
    have hq' := ((TopCat.of Y).isZero_singularHomology_modTwo_iff' (q + 2)).1 (hH q hq)
    rwa [singularHomologyFunctor_obj_obj] at hq'

/-- `SimplyConnectedSpace` form of
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`. -/
theorem
    isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_isZero_singularHomology_mod_two
    {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 2))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance) hH

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. No finite generation or CW structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_isZero_singularHomology_mod_two y
    fun q _ ↦ ModuleCat.isZero_iff_subsingleton.2 (hY (q + 1))

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

/-- **Vanishing of `π_{m+2}(Y, y) ⊗_ℤ (ZMod 2)` for a simply connected space with vanishing mod-two
homology in degrees `2, …, m + 3`.** -/
theorem subsingleton_homotopyGroup_tensorProduct_zmod_two_of_isZero_singularHomology_mod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularChains (ZMod 2)).obj (TopCat.of Y)).homology (q + 2))) :
    Subsingleton (TensorProduct ℤ (Additive (π_ (m + 2) Y y)) (ZMod 2)) :=
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two hπ₁ hH)
    |>.subsingleton_tensorProduct_zmod_two

end WhiteheadTower

end TauCeti
