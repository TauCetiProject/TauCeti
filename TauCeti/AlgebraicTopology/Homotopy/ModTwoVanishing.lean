/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.AcyclicCover
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
import TauCeti.AlgebraicTopology.EilenbergMacLane.UniquelyDivisible
import TauCeti.AlgebraicTopology.PathComponent
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField
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
particular `π_{m+2}(Y, y) ⊗_ℤ ℤ/2 = 0`.
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
  (`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_fiber`), so vanishing of
  `H_q(Z; 𝔽₂)` passes to `Z⟨m + 2⟩` for any individual degree `q`
  (`TauCeti.subsingleton_singularHomology_nConnectedCover_of_fiber`).
* **The induction.** The shared Whitehead-tower driver
  `TauCeti.prop_homotopyGroup_of_subsingleton_singularHomology` climbs the tower one homotopy group
  at a time, using `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two` for the
  first homotopy group and
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible` for the
  Eilenberg--Mac Lane fibres.

The Eilenberg--Mac Lane fibre sits over the `(m + 1)`-connected stage `Z`, never over the original
space: only the fibration `K(π_{m+2} Z, m + 1) → Z⟨m + 2⟩ → Z` between successive stages is used.
Over the two-sphere, for instance, a Serre fibration whose fibre is simply connected, such as a
`K(π₃(S²), 2)`, has a total space with nontrivial `π₂`, since `π₂(S²) ≅ ℤ`
(`TauCeti.nontrivial_homotopyGroup_of_mem_serreFibrations_sphere` with `n = 0`). So no
fibration `K(π₃(S²), 2) → E → S²` has a `3`-connected total space, as the tower over `S²` itself
would need.

The hypothesis on mod-two homology cannot be dropped: for `n ≥ 2`, the sphere `Sⁿ` is simply
connected, its `πₙ ≅ ℤ` is not uniquely two-divisible
(`TauCeti.not_isUniquelyTwoDivisible_homotopyGroup_sphere`), and indeed `Hₙ(Sⁿ; 𝔽₂) ≠ 0`
(`TauCeti.nontrivial_singularHomology_sphere`).

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le`: if
  `(Y, y)` is path-connected with trivial `π₁(Y, y)` and has vanishing mod-two homology in degrees
  `2, …, m + 3`, then `π_{m+2}(Y, y)` is uniquely two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`: the homotopy
  groups of a simply connected space with the mod-two homology of a point are uniquely
  two-divisible.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two`: the same,
  with the hypothesis on singular homology with coefficients in the integer module `ℤ/2`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`:
  if the fundamental group of `Y` at `y` is trivial and the path component of `y` has the mod-two
  homology of a point, the higher homotopy groups of `Y` at `y` are uniquely two-divisible.
* `TauCeti.not_isUniquelyTwoDivisible_homotopyGroup_sphere`: `π_{n+2}(S^{n+2}) ≅ ℤ` is not
  uniquely two-divisible, so the conclusion fails for spheres, which are not mod-two acyclic.
* `TauCeti.nontrivial_homotopyGroup_of_mem_serreFibrations_sphere`: a Serre fibration over
  `S^{n+2}` whose fibre has trivial `π_{n+1}` has a total space with nontrivial `π_{n+2}`.

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

/-- **Mod-two vanishing of higher homotopy groups from bounded-degree homology** (Serre). Let
`(Y, y)` be a path-connected topological space with trivial fundamental group `π₁(Y, y)` and let
`m : ℕ`. If `H_{q+2}(Y; k) = 0` for every `q ≤ m + 1`, where `k ≃+* ZMod 2`, then the homotopy
group `π_{m+2}(Y, y)` is uniquely two-divisible (a module over `ℤ[1/2]`). No CW, separation, or
finite-generation hypothesis is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le (e : k ≃+* ZMod 2)
    {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y}
    (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (q + 2))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  have : IsSemisimpleRing k := e.symm.isSemisimpleRing
  have hk : (2 : k) = 0 := e.injective (by rw [map_ofNat, map_zero]; decide)
  prop_homotopyGroup_of_subsingleton_singularHomology k
    (fun G _ ↦ IsUniquelyTwoDivisible G) (fun eqv h ↦ h.of_addEquiv eqv)
    (fun z n hZ hZ₁ hZ₂ ↦ isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_mod_two e
      (fun j hj ↦ by
        rcases eq_or_ne j 0 with rfl | hj0
        · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero z).1 inferInstance
        · exact hZ j hj0 hj)
      hZ₁ hZ₂)
    (fun hA _ _ _ _ _ hX ↦
      IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk hA hX)
    y hπ₁ m hH

/-- Bounded-degree mod-two vanishing with integer-module coefficients `ℤ/2` (lifted to the universe
of `Y`). -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le {Y : Type u}
    [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} (hπ₁ : Subsingleton (π_ 1 Y y)) {m : ℕ}
    (hH : ∀ q ≤ m + 1, IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (q + 2)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of Y))) :
    IsUniquelyTwoDivisible (Additive (π_ (m + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le ULift.ringEquiv hπ₁
    fun q hq ↦ ModuleCat.isZero_iff_subsingleton.1
      (((TopCat.of Y).isZero_singularHomology_zmod_iff_of_ringEquiv 2 ULift.ringEquiv _).1
        (hH q hq))

/-- **Mod-two vanishing** (Serre). The homotopy groups `πᵢ(Y)`, `i ≥ 2`, of a simply connected
space `Y` with the mod-two homology of a point are uniquely two-divisible: multiplication by two
is a bijection on each of them. The homology is taken with coefficients in the field `𝔽₂`, given
as any ring `k` isomorphic to `ZMod 2` in the universe of `Y`. No finite generation or CW
structure is assumed. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology (e : k ≃+* ZMod 2)
    {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, Subsingleton (((singularChains k).obj (TopCat.of Y)).homology (i + 1)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_le e
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance)
    fun q _ ↦ hY (q + 1)

/-- **Mod-two vanishing with integer-module coefficients.** The homotopy groups `πᵢ(Y)`, `i ≥ 2`,
of a simply connected space `Y` whose singular homology with coefficients in the integer module
`ℤ/2` vanishes in positive degrees are uniquely two-divisible. This is the form in which the
coefficients `ℤ/2` appear in the coefficient sequence of `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0`. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two {Y : Type u}
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (hY : ∀ i, IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) (i + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj (TopCat.of Y)))
    (y : Y) (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 2) Y y)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_mod_two_le
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.2 inferInstance)
    fun q _ ↦ hY (q + 1)

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
