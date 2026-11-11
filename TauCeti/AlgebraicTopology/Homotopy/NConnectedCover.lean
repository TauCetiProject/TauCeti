/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# `n`-connected covers

Let `X` be a Hausdorff, path-connected space with a base point `x`, and let `n` be a natural
number. Killing the homotopy groups of `X` above dimension `n` gives a space
`K = killHomotopyGroups (n + 1) X x` containing `X`, whose homotopy groups are those of `X` up to
dimension `n` and vanish above it. The **`n`-connected cover** `X⟨n⟩ → X`
(`TauCeti.nConnectedCover n X x`, with projection `TauCeti.nConnectedCoverProj n X x`) is the
homotopy fibre of the inclusion `ι : X → K` over `ι x`: its points are the points `y` of `X`
together with a path in `K` from `ι y` to `ι x`. It is the space `Z'` in the fibre sequence
`ΩK → Z' → Z` of the one-step argument behind Serre's mod-`𝒞` Hurewicz theorem, and the
successive stages of the Whitehead tower of `X` are obtained by iterating it.

* The projection `X⟨n⟩ → X` is a Hurewicz fibration
  (`TauCeti.isHurewiczFibration_nConnectedCoverProj`), whose fibre over `y` is the space of paths
  from `ι y` to `ι x`, the loop space `Ω K (ι x)` over `y = x`
  (`TauCeti.MappingPathFiber.projFiberHomeomorphPath`).
* The space `X⟨n⟩` is `n`-connected: it is path-connected and `πₖ(X⟨n⟩)` vanishes for `k ≤ n`
  at every point (`TauCeti.subsingleton_homotopyGroup_nConnectedCover`).
* Above dimension `n` the projection is an isomorphism: `πₖ(X⟨n⟩) → πₖ(X)` is bijective for
  `k > n` at every point (`TauCeti.bijective_homotopyGroupMap_nConnectedCoverProj`).
* For an `(n + 1)`-connected `X`, the fibre of the projection of `X⟨n + 2⟩` over `x` is an
  Eilenberg--Mac Lane space of type `K(πₙ₊₂(X, x), n + 1)`
  (`TauCeti.isEilenbergMacLaneSpace_nConnectedCoverProj_fiber`): it is the loop space of the
  `K(πₙ₊₂(X, x), n + 2)` space `killHomotopyGroups (n + 3) X x`.

## Main definitions

* `TauCeti.nConnectedCover n X x`: the `n`-connected cover of `(X, x)`.
* `TauCeti.nConnectedCoverProj n X x`: its projection to `X`.
* `TauCeti.nConnectedCoverBasepoint n X x`: its base point, over `x`.
* `TauCeti.nConnectedCoverHomotopyGroupMulEquiv n X x k`: for `k > n`, the isomorphism
  `πₖ(X⟨n⟩) ≃* πₖ(X)` induced by the projection.

## Main results

* `TauCeti.isHurewiczFibration_nConnectedCoverProj`: the projection is a Hurewicz fibration.
* `TauCeti.subsingleton_homotopyGroup_nConnectedCover`: `πₖ(X⟨n⟩)` vanishes for `k ≤ n`.
* `TauCeti.bijective_homotopyGroupMap_nConnectedCoverProj`: the projection is bijective on `πₖ`
  for `k > n`.
* `TauCeti.isEilenbergMacLaneSpace_nConnectedCoverProj_fiber`: for an `(n + 1)`-connected `X`, the
  fibre of `X⟨n + 2⟩ → X` over `x` is a `K(πₙ₊₂(X, x), n + 1)`.

## Implementation notes

The connectivity statements are read off the endpoint map `E → K` of the mapping-path replacement
`E ≃ X` of `ι`, a Hurewicz fibration whose fibre over `ι x` is `X⟨n⟩`. Since `ι` is
`(n + 1)`-connected (`TauCeti.isNConnected_killHomotopyGroupsIncl`), so is the endpoint map, and
its fibres are therefore `n`-connected (`TauCeti.TopCat.isNConnected_iff_of_mem_serreFibrations`).
Above dimension `n` the homotopy groups of `K` vanish, so the fibre inclusion `X⟨n⟩ → E` is
bijective on `πₖ` for `k > n`
(`TauCeti.TopCat.bijective_homotopyGroupMap_fiberι_of_mem_serreFibrations`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3, Whitehead towers.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

noncomputable section

open CategoryTheory Topology
open scoped Topology.Homotopy unitInterval

universe u w

namespace TauCeti

variable (n : ℕ) (X : TopCat.{u}) (x : X)

/-- The **`n`-connected cover** of `(X, x)`: the homotopy fibre, over the image of `x`, of the
inclusion of `X` into the space `killHomotopyGroups (n + 1) X x` obtained by killing the homotopy
groups of `X` above dimension `n`. A point is a point `y` of `X` together with a path from the
image of `y` to the image of `x`. -/
abbrev nConnectedCover : Type u :=
  MappingPathFiber (killHomotopyGroupsIncl (n + 1) X x).hom (killHomotopyGroupsIncl (n + 1) X x x)

/-- The projection of the `n`-connected cover to `X`, forgetting the path. -/
def nConnectedCoverProj : C(nConnectedCover n X x, X) :=
  MappingPathFiber.proj _ _

@[simp]
theorem nConnectedCoverProj_apply (y : nConnectedCover n X x) :
    nConnectedCoverProj n X x y = y.val.1 :=
  MappingPathFiber.proj_apply _ _ y

/-- The base point of the `n`-connected cover: the base point of `X` with the constant path. -/
def nConnectedCoverBasepoint : nConnectedCover n X x :=
  ⟨(x, .const I (killHomotopyGroupsIncl (n + 1) X x x)), rfl, rfl⟩

@[simp]
theorem nConnectedCoverBasepoint_val :
    (nConnectedCoverBasepoint n X x).val = (x, .const I (killHomotopyGroupsIncl (n + 1) X x x)) :=
  (rfl)

theorem nConnectedCoverProj_basepoint :
    nConnectedCoverProj n X x (nConnectedCoverBasepoint n X x) = x := by
  simp

/-- **The projection of the `n`-connected cover is a Hurewicz fibration**, for test spaces in
every universe. -/
theorem isHurewiczFibration_nConnectedCoverProj :
    IsHurewiczFibration.{w} (nConnectedCoverProj n X x) :=
  MappingPathFiber.isHurewiczFibration_proj _ _

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

/-! ### Homotopy groups of the connected cover -/

/-- **The `n`-connected cover is `n`-connected**: for a Hausdorff, path-connected space `X`, the
homotopy groups `πₖ(X⟨n⟩, y)` are trivial for every `k ≤ n` and every point `y`. For `k = 0` this
says that `X⟨n⟩` is path-connected. -/
theorem subsingleton_homotopyGroup_nConnectedCover [T2Space X] [PathConnectedSpace X]
    (y : nConnectedCover n X x) {k : ℕ} (hk : k ≤ n) :
    Subsingleton (π_ k (nConnectedCover n X x) y) :=
  (HomotopyGroup.homeomorphEquiv (nConnectedCoverHomeomorphFiber n X x) y).subsingleton_congr.2 <|
    ((TopCat.isNConnected_iff_of_mem_serreFibrations (endpointHom_mem_serreFibrations n X x)
      (n + 1)).1 (isNConnected_endpointHom n X x) _).2 _ k (Nat.lt_succ_of_le hk)

/-- The `n`-connected cover of a Hausdorff, path-connected space is path-connected. -/
instance instPathConnectedSpaceNConnectedCover [T2Space X] [PathConnectedSpace X] :
    PathConnectedSpace (nConnectedCover n X x) :=
  (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (nConnectedCoverBasepoint n X x)).2
    (subsingleton_homotopyGroup_nConnectedCover n X x _ n.zero_le)

/-- **Above dimension `n`, the projection of the `n`-connected cover is bijective on homotopy
groups**: for a Hausdorff space `X`, the map `πₖ(X⟨n⟩, y) → πₖ(X, z)` induced by the projection,
for `z` the image of `y`, is bijective for every `k > n` and every point `y`. -/
theorem bijective_homotopyGroupMap_nConnectedCoverProj [T2Space X] (y : nConnectedCover n X x)
    {z : X} (hz : nConnectedCoverProj n X x y = z) {k : ℕ} (hk : n < k) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (nConnectedCoverProj n X x) hz) := by
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
    rw [nConnectedCoverProj_apply, MappingPathSpace.proj_apply]
    exact congrArg Prod.fst (MappingPathFiber.endpointHomeomorph_val _ _ y).symm
  have hcomp : (MappingPathSpace.proj (killHomotopyGroupsIncl (n + 1) X x).hom).comp
      (((endpointHom n X x).fiberι (killHomotopyGroupsIncl (n + 1) X x x)).hom.comp ψ.toFun) =
        nConnectedCoverProj n X x :=
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

/-- For `k > n`, the projection of the `n`-connected cover of a Hausdorff space `X` induces an
isomorphism `πₖ(X⟨n⟩) ≃* πₖ(X)` at the base points. -/
def nConnectedCoverHomotopyGroupMulEquiv [T2Space X] (k : ℕ) [NeZero k] (hk : n < k) :
    π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x) ≃* π_ k X x :=
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (nConnectedCoverProj n X x) (nConnectedCoverProj_basepoint n X x))
    (bijective_homotopyGroupMap_nConnectedCoverProj n X x _ _ hk)

/-- The isomorphism of `πₖ` is the map induced by the projection. -/
@[simp]
lemma nConnectedCoverHomotopyGroupMulEquiv_apply [T2Space X] (k : ℕ) [NeZero k] (hk : n < k)
    (a : π_ k (nConnectedCover n X x) (nConnectedCoverBasepoint n X x)) :
    nConnectedCoverHomotopyGroupMulEquiv n X x k hk a =
      HomotopyGroup.map (nConnectedCoverProj n X x) (nConnectedCoverProj_basepoint n X x) a :=
  HomotopyGroup.mapHom_apply _ _ a

/-! ### The fibre of the projection -/

/-- **The fibre of the projection of a connected cover is an Eilenberg--Mac Lane space.** For a
Hausdorff, path-connected space `X` whose homotopy groups `πₖ(X, x)` vanish for `0 < k < n + 2`,
the fibre over `x` of the projection `X⟨n + 2⟩ → X` is an Eilenberg--Mac Lane space of type
`K(πₙ₊₂(X, x), n + 1)`: it is the loop space of the `K(πₙ₊₂(X, x), n + 2)` space
`killHomotopyGroups (n + 3) X x`. -/
theorem isEilenbergMacLaneSpace_nConnectedCoverProj_fiber [T2Space X] [PathConnectedSpace X]
    (hX : ∀ k, k ≠ 0 → k < n + 2 → Subsingleton (π_ k X x)) :
    IsEilenbergMacLaneSpace (π_ (n + 2) X x) (n + 1)
      {y : nConnectedCover (n + 2) X x // nConnectedCoverProj (n + 2) X x y = x}
      ⟨nConnectedCoverBasepoint (n + 2) X x, nConnectedCoverProj_basepoint (n + 2) X x⟩ :=
  (isEilenbergMacLaneSpace_killHomotopyGroups (n + 2) X x hX).loopSpace.of_homotopyEquiv
    (MappingPathFiber.projFiberHomeomorphPath _ _ x).symm.toHomotopyEquiv _

end TauCeti
