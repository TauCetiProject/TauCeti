/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.MappingPath.Exact
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# The `n`-connected cover of a space

Let `X` be a Hausdorff space with a base point `x` and let `n` be a natural number. Attaching
cells of dimension at least `n + 2` to `X` kills its homotopy groups above dimension `n` and keeps
the others (`TauCeti.killHomotopyGroups`); this is the `n`-th Postnikov section `j : X → Pₙ X`.
The **`n`-connected cover** `X⟨n⟩` of `X` (`TauCeti.nConnectedCover n X x`) is the homotopy fibre
of `j` over `j x`: the space of the points `z` of `X` together with a path from `j z` to `j x` in
`Pₙ X`. Its projection `X⟨n⟩ → X`, `(z, γ) ↦ z` (`TauCeti.nConnectedCoverProj`), is a Hurewicz
fibration whose fibre over `x` is the loop space of `Pₙ X`, and

* `X⟨n⟩` is `n`-connected: its homotopy groups `πₖ` vanish for `1 ≤ k ≤ n`
  (`TauCeti.subsingleton_homotopyGroup_nConnectedCover`), and it is path-connected when `X` is
  (`TauCeti.pathConnectedSpace_nConnectedCover`);
* the projection induces an isomorphism `πₖ(X⟨n⟩) ≅ πₖ(X)` for every `k > n`
  (`TauCeti.nConnectedCoverHomotopyGroupMulEquiv`).

No connectivity hypothesis on `X` is needed for these. When `X` is `(n - 1)`-connected, `Pₙ X` is
an Eilenberg--Mac Lane space `K(πₙ X, n)` (`TauCeti.isEilenbergMacLaneSpace_killHomotopyGroups`),
so the fibre of `X⟨n⟩ → X` is a `K(πₙ X, n - 1)`
(`TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`). Iterating the construction gives
the stages of the Whitehead tower of `X`, along which homotopy groups are studied one at a time
through the fibrations `K(πₙ X, n - 1) → X⟨n⟩ → X`.

The proof reads off the homotopy groups of `X⟨n⟩` from the exact homotopy sequence of the map `j`
(`TopCat.Hom.mem_range_homotopyGroupMap_homotopyFiberProj_iff`,
`TopCat.Hom.eq_const_of_homotopyGroupMap_homotopyFiberProj_eq_const`): `j` is bijective on
`πₖ` for `k ≤ n` and `πₖ(Pₙ X)` is trivial for `k > n`, so `j` is surjective on every homotopy
group (`TauCeti.surjective_homotopyGroupMap_killHomotopyGroupsIncl`).

## Main declarations

* `TauCeti.nConnectedCover`: the `n`-connected cover `X⟨n⟩`, with its projection
  `TauCeti.nConnectedCoverProj` to `X` and base point `TauCeti.nConnectedCoverBasepoint`.
* `TauCeti.isHurewiczFibration_nConnectedCoverProj`: the projection is a Hurewicz fibration.
* `TauCeti.subsingleton_homotopyGroup_nConnectedCover`: `πₖ(X⟨n⟩)` is trivial for `1 ≤ k ≤ n`.
* `TauCeti.subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace`: for a path-connected
  `X`, `πₖ(X⟨n⟩, y)` is trivial for every `k ≤ n` and every point `y`.
* `TauCeti.bijective_homotopyGroupMap_nConnectedCoverProj`,
  `TauCeti.nConnectedCoverHomotopyGroupMulEquiv`: `πₖ(X⟨n⟩) ≅ πₖ(X)` for `k > n`, at every point.
* `TauCeti.nConnectedCoverFiberHomeomorph`: the fibre of `X⟨n⟩ → X` over `x` is a loop space.
* `TauCeti.isEilenbergMacLaneSpace_fiber_nConnectedCoverProj`: for `n ≥ 2` and `X`
  `(n - 1)`-connected, that fibre is a `K(πₙ X, n - 1)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.3, Postnikov towers and Whitehead towers.
-/

public section

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

universe u w

namespace TauCeti

variable (n : ℕ) (X : TopCat.{u}) (x : X)

/-- The **`n`-connected cover** `X⟨n⟩` of `X`: the homotopy fibre of the inclusion
`j : X → TauCeti.killHomotopyGroups (n + 1) X x` over `j x`, of the points `z` of `X` with a path
from `j z` to `j x`. -/
abbrev nConnectedCover : TopCat.{u} :=
  TopCat.of (MappingPathFiber (killHomotopyGroupsIncl (n + 1) X x).hom
    (killHomotopyGroupsIncl (n + 1) X x x))

/-- The projection `(z, γ) ↦ z` of the `n`-connected cover to `X`, a Hurewicz fibration
(`TopCat.Hom.isHurewiczFibration_homotopyFiberProj`). -/
abbrev nConnectedCoverProj : nConnectedCover n X x ⟶ X :=
  (killHomotopyGroupsIncl (n + 1) X x).homotopyFiberProj x

/-- The base point of the `n`-connected cover: the point `x` with the constant path. -/
abbrev nConnectedCoverBasepoint : nConnectedCover n X x :=
  ((killHomotopyGroupsIncl (n + 1) X x).homotopyFiberBasepoint x).1

/-- The base point of the `n`-connected cover lies over `x`. -/
@[simp]
theorem nConnectedCoverProj_nConnectedCoverBasepoint :
    nConnectedCoverProj n X x (nConnectedCoverBasepoint n X x) = x :=
  Set.mem_singleton_iff.1 (TopCat.Hom.homotopyFiberBasepoint _ x).2

/-- **The projection of the `n`-connected cover is a Hurewicz fibration**, for test spaces in
every universe. -/
theorem isHurewiczFibration_nConnectedCoverProj :
    IsHurewiczFibration.{w} (nConnectedCoverProj n X x) :=
  TopCat.Hom.isHurewiczFibration_homotopyFiberProj _ x

/-- The projection of the `n`-connected cover is a Serre fibration. -/
theorem serreFibrations_nConnectedCoverProj :
    TopCat.serreFibrations (nConnectedCoverProj n X x) :=
  TopCat.Hom.serreFibrations_homotopyFiberProj _ x

/-- The fibre over `x` of the projection of the `n`-connected cover is the loop space of
`TauCeti.killHomotopyGroups (n + 1) X x` at the image of `x`. -/
def nConnectedCoverFiberHomeomorph :
    (nConnectedCoverProj n X x).fiber x ≃ₜ
      Ω (killHomotopyGroups (n + 1) X x) (killHomotopyGroupsIncl (n + 1) X x x) :=
  TopCat.Hom.homotopyFiberFiberHomeomorph _ x

@[simp]
theorem nConnectedCoverFiberHomeomorph_apply (p : (nConnectedCoverProj n X x).fiber x) (t : I) :
    nConnectedCoverFiberHomeomorph n X x p t = p.1.val.2 t :=
  TopCat.Hom.homotopyFiberFiberHomeomorph_apply _ x p t

/-! ### The endpoint fibration -/

section Endpoint

/-- The endpoint map of the mapping-path replacement of the inclusion of `X` into
`killHomotopyGroups (n + 1) X x`, as a morphism of `TopCat`. -/
private abbrev endpointHom :
    TopCat.of (MappingPathSpace (killHomotopyGroupsIncl (n + 1) X x).hom) ⟶
      killHomotopyGroups (n + 1) X x :=
  TopCat.ofHom (MappingPathSpace.endpoint _)

private theorem endpointHom_mem_serreFibrations : TopCat.serreFibrations (endpointHom n X x) :=
  (MappingPathSpace.isHurewiczFibration_endpoint.{0} _).mem_serreFibrations

/-- The `n`-connected cover is the fibre of the endpoint map over the image of `x`. -/
private def nConnectedCoverHomeomorphFiber :
    nConnectedCover n X x ≃ₜ (endpointHom n X x).fiber (killHomotopyGroupsIncl (n + 1) X x x) :=
  MappingPathFiber.endpointHomeomorph _ _

/-- The endpoint map is `(n + 1)`-connected, since the inclusion of `X` is and the constant-path
inclusion of `X` into its mapping-path replacement is a homotopy equivalence. -/
private theorem isNConnected_endpointHom [T2Space X] [PathConnectedSpace X] :
    (endpointHom n X x).hom.IsNConnected (n + 1) := by
  let e := MappingPathSpace.homotopyEquiv (killHomotopyGroupsIncl (n + 1) X x).hom
  have h : (endpointHom n X x).hom.comp e.toFun = (killHomotopyGroupsIncl (n + 1) X x).hom :=
    ContinuousMap.ext fun y ↦ (congrArg (MappingPathSpace.endpoint _)
      (MappingPathSpace.homotopyEquiv_apply _ y)).trans
        (DFunLike.congr_fun (MappingPathSpace.endpoint_comp_incl _) y)
  rw [← e.isWeakHomotopyEquivalence.isNConnected_comp_iff', h]
  exact isNConnected_killHomotopyGroupsIncl (n + 1) X x

end Endpoint

/-- **The `n`-connected cover of a path-connected space is `n`-connected at every point**: for a
Hausdorff, path-connected space `X`, the homotopy groups `πₖ(X⟨n⟩, y)` are trivial for every
`k ≤ n` and every point `y`, including `k = 0`. -/
theorem subsingleton_homotopyGroup_nConnectedCover_of_pathConnectedSpace [T2Space X]
    [PathConnectedSpace X] (y : nConnectedCover n X x) {k : ℕ} (hk : k ≤ n) :
    Subsingleton (π_ k (nConnectedCover n X x) y) :=
  (HomotopyGroup.homeomorphEquiv (nConnectedCoverHomeomorphFiber n X x) y).subsingleton_congr.2 <|
    ((TopCat.isNConnected_iff_of_mem_serreFibrations (endpointHom_mem_serreFibrations n X x)
      (n + 1)).1 (isNConnected_endpointHom n X x) _).2 _ k (Nat.lt_succ_of_le hk)

variable [T2Space X]

/-- A class of `πₖ(X⟨n⟩)` which projects to the trivial class of `X` is trivial. -/
private theorem eq_const_of_homotopyGroupMap_nConnectedCoverProj_eq_const {k : ℕ}
    {c : π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)}
    (hc : HomotopyGroup.map (nConnectedCoverProj n X x).hom
      (nConnectedCoverProj_nConnectedCoverBasepoint n X x) c = ⟦GenLoop.const⟧) :
    c = ⟦GenLoop.const⟧ :=
  TopCat.Hom.eq_const_of_homotopyGroupMap_homotopyFiberProj_eq_const _ x
    (surjective_homotopyGroupMap_killHomotopyGroupsIncl (n + 1) X x) hc

/-- **The `n`-connected cover is `n`-connected**: its homotopy groups `πₖ` vanish for
`1 ≤ k ≤ n`. -/
theorem subsingleton_homotopyGroup_nConnectedCover {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ n) :
    Subsingleton (π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨fun c c' ↦ ?_⟩
  -- Every class projects to a class of `X` killed by the inclusion, which is injective on
  -- `π_{m + 1}`; so it projects to the trivial class, and is trivial.
  suffices h : ∀ c : π_ (m + 1) (nConnectedCover n X x) (nConnectedCoverBasepoint n X x),
      c = ⟦GenLoop.const⟧ from (h c).trans (h c').symm
  intro c
  refine eq_const_of_homotopyGroupMap_nConnectedCoverProj_eq_const n X x ?_
  have hinj := (bijective_homotopyGroupMap_killHomotopyGroupsIncl (n + 1) X x
    (N := Option (Fin m)) (by simp; omega)).1
  have hrange := (TopCat.Hom.mem_range_homotopyGroupMap_homotopyFiberProj_iff
    (killHomotopyGroupsIncl (n + 1) X x) x).1 ⟨HomotopyGroup.congrEquiv (finSuccEquiv m) c, rfl⟩
  rw [← GenLoop.map_const (killHomotopyGroupsIncl (n + 1) X x).hom rfl,
    ← HomotopyGroup.map_mk] at hrange
  apply (HomotopyGroup.congrEquiv (X := X) (x := x) (finSuccEquiv m)).injective
  rw [← HomotopyGroup.map_congrEquiv, hinj hrange, HomotopyGroup.congrEquiv_const]

/-- **The `n`-connected cover of a path-connected space is path-connected.** -/
instance pathConnectedSpace_nConnectedCover [PathConnectedSpace X] :
    PathConnectedSpace (nConnectedCover n X x) := by
  have : Subsingleton (π_ 0 X x) := HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
  have : Subsingleton (π_ 0 (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) :=
    ⟨fun c c' ↦ (eq_const_of_homotopyGroupMap_nConnectedCoverProj_eq_const n X x
      (Subsingleton.elim _ _)).trans (eq_const_of_homotopyGroupMap_nConnectedCoverProj_eq_const
        n X x (Subsingleton.elim _ _)).symm⟩
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨⟦nConnectedCoverBasepoint n X x⟧⟩,
      (HomotopyGroup.pi0EquivZerothHomotopy
        (x := nConnectedCoverBasepoint n X x)).symm.subsingleton⟩

/-- **The `n`-connected cover has the homotopy groups of `X` above dimension `n`**: the map
`πₖ(X⟨n⟩, y) → πₖ(X, z)` induced by the projection, for `z` the image of `y`, is bijective for
every `k > n` and every point `y`. -/
theorem bijective_homotopyGroupMap_nConnectedCoverProj (y : nConnectedCover n X x) {z : X}
    (hz : nConnectedCoverProj n X x y = z) {k : ℕ} (hk : n < k) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (nConnectedCoverProj n X x).hom hz) := by
  -- Above dimension `n` the homotopy groups of `killHomotopyGroups (n + 1) X x` vanish.
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hK (i : ℕ) (hi : n < i + 1) : Subsingleton (π_ (i + 1) (killHomotopyGroups (n + 1) X x)
      (killHomotopyGroupsIncl (n + 1) X x x)) :=
    subsingleton_homotopyGroup_killHomotopyGroups (n + 1) X x hi
  -- The projection factors as the identification `ψ` with the fibre of the endpoint map, the
  -- fibre inclusion, and the projection of the mapping-path replacement onto `X`; each factor is
  -- bijective on `πₖ`.
  let ψ := (nConnectedCoverHomeomorphFiber n X x).toHomotopyEquiv
  have hψ (y : nConnectedCover n X x) : nConnectedCoverProj n X x y =
      MappingPathSpace.proj (killHomotopyGroupsIncl (n + 1) X x).hom (ψ.toFun y).1 := by
    rw [TopCat.Hom.homotopyFiberProj_apply, MappingPathSpace.proj_apply]
    exact congrArg Prod.fst (MappingPathFiber.endpointHomeomorph_val _ _ y).symm
  have hcomp : (MappingPathSpace.proj (killHomotopyGroupsIncl (n + 1) X x).hom).comp
      (((endpointHom n X x).fiberι (killHomotopyGroupsIncl (n + 1) X x x)).hom.comp ψ.toFun) =
        (nConnectedCoverProj n X x).hom :=
    ContinuousMap.ext fun y ↦ (congrArg (MappingPathSpace.proj _)
      (TopCat.Hom.fiberι_apply _ _ (ψ.toFun y))).trans (hψ y).symm
  have hproj : (MappingPathSpace.proj
      (killHomotopyGroupsIncl (n + 1) X x).hom).IsWeakHomotopyEquivalence := by
    have h : (MappingPathSpace.homotopyEquiv (killHomotopyGroupsIncl (n + 1) X x).hom).symm.toFun =
        MappingPathSpace.proj _ :=
      ContinuousMap.ext (MappingPathSpace.homotopyEquiv_symm_apply _)
    exact h ▸ (MappingPathSpace.homotopyEquiv _).symm.isWeakHomotopyEquivalence
  have h := (hproj.bijective (j + 1) (ψ.toFun y).1).comp
    ((TopCat.bijective_homotopyGroupMap_fiberι_of_mem_serreFibrations
      (endpointHom_mem_serreFibrations n X x) (hK j hk) (hK (j + 1) (by omega)) (ψ.toFun y)).comp
        (ψ.isWeakHomotopyEquivalence.bijective (j + 1) y))
  rw [HomotopyGroup.map_comp_map, HomotopyGroup.map_comp_map] at h
  -- The base point `z` is the image of `y` under the factorization.
  obtain rfl : z = _ := hz.symm.trans (hψ y)
  convert h using 1
  exact funext (HomotopyGroup.map_congr hcomp.symm _ _)

/-- For `k > n`, the projection of the `n`-connected cover induces an isomorphism
`πₖ(X⟨n⟩) ≃* πₖ(X)`. -/
def nConnectedCoverHomotopyGroupMulEquiv (k : ℕ) [NeZero k] (hk : n < k) :
    π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x) ≃* π_ k X x :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom (nConnectedCoverProj n X x).hom
    (nConnectedCoverProj_nConnectedCoverBasepoint n X x))
    (bijective_homotopyGroupMap_nConnectedCoverProj n X x _ _ hk)

@[simp]
theorem nConnectedCoverHomotopyGroupMulEquiv_apply (k : ℕ) [NeZero k] (hk : n < k)
    (c : π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) :
    nConnectedCoverHomotopyGroupMulEquiv n X x k hk c =
      HomotopyGroup.map (nConnectedCoverProj n X x).hom
        (nConnectedCoverProj_nConnectedCoverBasepoint n X x) c :=
  HomotopyGroup.mapHom_apply _ _ c

/-- **The fibre of the `n`-connected cover of an `(n - 1)`-connected space is a `K(πₙ X, n - 1)`**,
for `n ≥ 2`: it is the loop space of the Eilenberg--Mac Lane space `K(πₙ X, n)` obtained from `X`
by killing its homotopy groups above `n`. -/
theorem isEilenbergMacLaneSpace_fiber_nConnectedCoverProj [PathConnectedSpace X] (m : ℕ)
    (hX : ∀ k, k ≠ 0 → k < m + 2 → Subsingleton (π_ k X x)) :
    IsEilenbergMacLaneSpace (π_ (m + 2) X x) (m + 1) ((nConnectedCoverProj (m + 2) X x).fiber x)
      (TopCat.Hom.homotopyFiberBasepoint _ x) :=
  (isEilenbergMacLaneSpace_killHomotopyGroups (m + 2) X x hX).loopSpace.of_homotopyEquiv
    (nConnectedCoverFiberHomeomorph (m + 2) X x).symm.toHomotopyEquiv _

end TauCeti
