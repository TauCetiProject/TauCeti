/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.Homotopy.WhiteheadTower
import TauCeti.AlgebraicTopology.PathComponent
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
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le`) — and in
particular `π_{m+2}(Y, y) ⊗_ℤ ℤ/2 = 0`
(`TauCeti.subsingleton_homotopyGroup_tensorProduct_zmod_two_of_isZero_singularHomology_mod_two`).
In particular, if `Y` is simply connected and has the mod-two homology of a point
(`Hᵢ(Y; 𝔽₂) = 0` for all `i > 0`), every higher homotopy group `πᵢ(Y)` (`i ≥ 2`) is uniquely
two-divisible (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`).
No CW, separation, or finite-generation hypothesis is imposed on `Y` or on its homotopy groups.

The space `Y` lies in an arbitrary universe `u`. Mod-two homology is then taken with coefficients
in a ring `k` in the universe `u` together with a ring isomorphism `k ≃+* ZMod 2`, for instance
`ZMod 2` itself when `u` is the lowest universe, or its lift `ULift.{u} (ZMod 2)`. The hypothesis
can also be stated with coefficients in the integer module `ℤ/2`, lifted to the universe `u`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`, and
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le` in bounded
degrees).

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
  two-divisibility of `π_{m+2}(Y, y)` follows via `TauCeti.whiteheadTower_induction`.

The Eilenberg--Mac Lane fibre sits over the `(n - 1)`-connected stage `Z`, never over the original
space: only the fibration `K(πₙ Z, n - 1) → Z⟨n⟩ → Z` between successive stages is used.

## Main results

* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`,
  `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two`: if `(Z, z)` is Hausdorff,
  `(m + 1)`-connected, and has vanishing mod-two homology in degrees `m + 2` and `m + 3`, then
  `nConnectedCoverProj (m + 2) Z z` induces isomorphisms on mod-two homology in all degrees.
* `TauCeti.isZero_singularHomology_nConnectedCover_mod_two`: under the same hypotheses, vanishing
  of `H_q(Z; 𝔽₂)` passes from `Z` to `nConnectedCover (m + 2) Z z`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two`, and
  `isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_isZero_singularHomology_mod_two`
  (in `TauCeti`): if `(Y, y)` is simply connected and has vanishing mod-two homology in degrees
  `2, …, m + 3`, then `π_{m+2}(Y, y)` is uniquely two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`: the same,
  with the hypothesis on singular homology with coefficients in the integer module `ℤ/2`.
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

universe u

namespace TauCeti

variable {k : Type u} [CommRing k]

section OneStep

variable {Z : TopCat.{u}} [T2Space Z] {z : Z} {m : ℕ}

/-- **One-step connected-cover mod-two homology isomorphism.** Let `(Z, z)` be a Hausdorff,
`(m + 1)`-connected space whose mod-two homology vanishes in degrees `m + 2` and `m + 3`, with
coefficients in a ring `k ≃+* ZMod 2`. Then the projection `Z⟨m + 2⟩ ⟶ Z` of the
`(m + 2)`-connected cover induces an isomorphism on `k`-homology in every degree `q`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_mod_two (e : k ≃+* ZMod 2)
    (hZ : ∀ j < m + 2, Subsingleton (π_ j Z z))
    (hm₂ : IsZero (((singularChains k).obj Z).homology (m + 2)))
    (hm₃ : IsZero (((singularChains k).obj Z).homology (m + 3))) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} k) q).obj
      (ModuleCat.of k k)).map (nConnectedCoverProj (m + 2) Z z)) := by
  have : PathConnectedSpace Z :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).2 (hZ 0 (Nat.zero_lt_succ _))
  have : IsSemisimpleRing k := e.symm.isSemisimpleRing
  have hk : (2 : k) = 0 := e.injective (by rw [map_ofNat, map_zero]; decide)
  have hdiv : IsUniquelyTwoDivisible (Additive (π_ (m + 2) Z z)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two e hZ
      (ModuleCat.isZero_iff_subsingleton.1 hm₂) (ModuleCat.isZero_iff_subsingleton.1 hm₃)
  exact isIso_singularHomologyMap_of_isEilenbergMacLaneSpace_fiber k
    (serreFibrations_nConnectedCoverProj (m + 2) Z z)
    (isEilenbergMacLaneSpace_fiber_nConnectedCoverProj Z z m fun j _ hj ↦ hZ j hj)
    (fun hX ↦ IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk
      hdiv (hX.of_mulEquiv (MulEquiv.multiplicativeAdditive _).symm))
    q

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_mod_two`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_int_zmod_two
    {Z : TopCat.{0}} [T2Space Z] {z : Z} {m : ℕ}
    (hZ : ∀ j < m + 2, Subsingleton (π_ j Z z))
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
    (isIso_singularHomologyMap_nConnectedCoverProj_mod_two (RingEquiv.refl (ZMod 2))
      hZ hm₂' hm₃' q)

/-- **One-step preservation of mod-two homology vanishing.** If `(Z, z)` is Hausdorff,
`(m + 1)`-connected, and has vanishing mod-two homology in degrees `m + 2`, `m + 3`, and `q`, then
its `(m + 2)`-connected cover `nConnectedCover (m + 2) Z z` also has vanishing mod-two homology in
degree `q`. -/
theorem isZero_singularHomology_nConnectedCover_mod_two (e : k ≃+* ZMod 2)
    (hZ : ∀ j < m + 2, Subsingleton (π_ j Z z))
    (hm₂ : IsZero (((singularChains k).obj Z).homology (m + 2)))
    (hm₃ : IsZero (((singularChains k).obj Z).homology (m + 3))) {q : ℕ}
    (hq : IsZero (((singularChains k).obj Z).homology q)) :
    IsZero (((singularChains k).obj (nConnectedCover (m + 2) Z z)).homology q) := by
  have := isIso_singularHomologyMap_nConnectedCoverProj_mod_two e hZ hm₂ hm₃ q
  exact ModuleCat.isZero_iff_subsingleton.2
    ((subsingleton_singularChains_homology_iff_of_isIso k
      (nConnectedCoverProj (m + 2) Z z) q).2 (ModuleCat.isZero_iff_subsingleton.1 hq))

end OneStep

section WhiteheadTower

/-- **Mod-two vanishing of higher homotopy groups from bounded-degree homology** (Serre). Let
`(Y, y)` be a path-connected topological space with trivial fundamental group `π₁(Y, y)` and let
`m : ℕ`. If `H_{q+2}(Y; k) = 0` for every `q ≤ m + 1`, where `k ≃+* ZMod 2`, then the homotopy
group `π_{m+2}(Y, y)` is uniquely two-divisible (a module over `ℤ[1/2]`). No CW, separation, or
finite-generation hypothesis is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le (e : k ≃+* ZMod 2)
    {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (q + 2))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) := by
  have h₁ (j : ℕ) (hj0 : j ≠ 0) (hj : j < 2) : Subsingleton (π_ j Y y) := by
    obtain rfl : j = 1 := by omega
    exact hπ₁
  refine whiteheadTower_induction (N := m)
    (fun X ↦ ∀ q ≤ m + 1, Subsingleton (((singularChains k).obj X).homology (q + 2)))
    (fun G _ ↦ IsUniquelyTwoDivisible (Additive G))
    (fun _ _ f hf hXk q hq ↦ ?_)
    (fun _ _ _ _ eqv h ↦ h.of_addEquiv eqv.toAdditive)
    (fun {Z} _ _ z hZ hZk ↦ isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two e
      (fun j hj ↦ ?_) (hZk m (by omega)) (hZk (m + 1) le_rfl))
    (fun r hr X _ _ x hX hXk q hq ↦ ?_)
    (Nat.zero_le m) y h₁ hH
  · have := hf.isIso_singularHomologyMap (ModuleCat.of k k) (q + 2)
    exact (subsingleton_singularChains_homology_iff_of_isIso k f (q + 2)).2 (hXk q hq)
  · rcases eq_or_ne j 0 with rfl | hj0
    · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
    · exact hZ j hj0 hj
  · have hX' (j : ℕ) (hj : j < r + 2) : Subsingleton (π_ j X x) := by
      rcases eq_or_ne j 0 with rfl | hj0
      · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).1 inferInstance
      · exact hX j hj0 hj
    have := isIso_singularHomologyMap_nConnectedCoverProj_mod_two e hX'
      (ModuleCat.isZero_iff_subsingleton.2 (hXk r (by omega)))
      (ModuleCat.isZero_iff_subsingleton.2 (hXk (r + 1) (by omega))) (q + 2)
    exact (subsingleton_singularChains_homology_iff_of_isIso k
      (nConnectedCoverProj (r + 2) X x) (q + 2)).2 (hXk q hq)

/-- Bounded-degree mod-two vanishing with integer-module coefficients `ℤ/2` (lifted to the universe
of `Y`). -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le {Y : Type u}
    [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (q + 2)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of Y))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le ULift.ringEquiv hπ₁
    fun q hq ↦ ModuleCat.isZero_iff_subsingleton.1
      (((TopCat.of Y).isZero_singularHomology_modTwo_iff_of_ringEquiv ULift.ringEquiv _).1
        (hH q hq))

/-- Integral-coefficient `ZMod 2` form of
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le` in `Type`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_int_zmod_two
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (q + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of Y))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le
    (RingEquiv.refl (ZMod 2)) hπ₁ fun q hq ↦ by
      have hq' := ((TopCat.of Y).isZero_singularHomology_modTwo_iff' (q + 2)).1 (hH q hq)
      rw [singularHomologyFunctor_obj_obj] at hq'
      exact ModuleCat.isZero_iff_subsingleton.1 hq'

/-- `SimplyConnectedSpace` bounded-degree form of mod-two vanishing. -/
theorem
    isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_isZero_singularHomology_mod_two
    (e : k ≃+* ZMod 2) {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularChains k).obj (TopCat.of Y)).homology (q + 2))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le e
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance)
    fun q hq ↦ ModuleCat.isZero_iff_subsingleton.1 (hH q hq)

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

/-- **Vanishing of `π_{m+2}(Y, y) ⊗_ℤ (ZMod 2)` for a simply connected space with vanishing mod-two
homology in degrees `2, …, m + 3`.** -/
theorem subsingleton_homotopyGroup_tensorProduct_zmod_two_of_isZero_singularHomology_mod_two
    (e : k ≃+* ZMod 2) {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularChains k).obj (TopCat.of Y)).homology (q + 2))) :
    Subsingleton (TensorProduct ℤ (Additive (π_ (m + 2) Y y)) (ZMod 2)) :=
  (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le e hπ₁
    fun q hq ↦ ModuleCat.isZero_iff_subsingleton.1 (hH q hq))
    |>.subsingleton_tensorProduct_zmod_two

end WhiteheadTower

end TauCeti
