/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.StableOrthogonalGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.Stability
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Connectivity and homotopy-group stability for `O` and `SO`

Combining the step connectivity results for the block inclusions
(`TauCeti.isNConnected_specialOrthogonalBlockSucc` and `TauCeti.isNConnected_orthogonalBlockSucc`)
with `TauCeti.SequentialColimitGroup.isNConnected_of`, each finite-stage inclusion
`SO(n) → SO` and `O(n) → O` (`n ≥ 1`) is `(n - 1)`-connected and induces isomorphisms
`π_N(SO(n)) ≃* π_N(SO)` and `π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and `Nat.card N + 2 ≤ n`.
Furthermore, since `SO` embeds onto the identity path component of `O`, the inclusion `SO → O`
induces isomorphisms `π_N(SO) ≃* π_N(O)` for every nonempty `N`.

## Main results

* `TauCeti.StableSpecialOrthogonalGroup.isNConnected_of`,
  `TauCeti.StableOrthogonalGroup.isNConnected_of`: `SO(n) → SO` and `O(n) → O` (`n ≥ 1`) are
  `(n - 1)`-connected.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf`,
  `TauCeti.StableOrthogonalGroup.homotopyGroupMulEquivOf`: stable homotopy group isomorphisms
  `π_N(SO(n)) ≃* π_N(SO)` and `π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and
  `Nat.card N + 2 ≤ n`.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup`:
  `π_N(SO) ≃* π_N(O)` for all nonempty `N`.
-/

public section

noncomputable section

open Topology Set

namespace TauCeti

section Connectivity

attribute [local instance] starRingOfComm

/-- **Stability connectivity for `SO`**: the stage inclusion `SO(n) → SO` is
`(n - 1)`-connected. -/
theorem StableSpecialOrthogonalGroup.isNConnected_of (n : ℕ) :
    (SequentialColimitGroup.of
      (continuousSpecialOrthogonalBlockSucc ℝ) n).toContinuousMap.IsNConnected (n - 1) :=
  SequentialColimitGroup.isNConnected_of (continuousSpecialOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousSpecialOrthogonalBlockSucc ℝ) n (n - 1) fun k hnk ↦
    (isNConnected_specialOrthogonalBlockSucc k).mono (Nat.sub_le_sub_right hnk 1)

/-- **Stability connectivity for `O`**: for `n ≥ 1`, the stage inclusion `O(n) → O` is
`(n - 1)`-connected. -/
theorem StableOrthogonalGroup.isNConnected_of (n : ℕ) (hn : 1 ≤ n) :
    (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n).toContinuousMap.IsNConnected
      (n - 1) := by
  refine SequentialColimitGroup.isNConnected_of (continuousOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousOrthogonalBlockSucc ℝ) n (n - 1) fun k hnk ↦ ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (isNConnected_orthogonalBlockSucc m).mono (by omega : n - 1 ≤ m)

/-- **Homotopy group stability for `SO`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `SO(n) → SO` induces a group isomorphism
`π_N(SO(n), x) ≃* π_N(SO, of n x)`. -/
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableSpecialOrthogonalGroup
        (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n x) :=
  let hc := StableSpecialOrthogonalGroup.isNConnected_of n
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N)
      (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

/-- `StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf` acts on homotopy classes by
`HomotopyGroup.map`. -/
@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map
        (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n).toContinuousMap
        rfl a :=
  (rfl)

/-- **Homotopy group stability for `O`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `O(n) → O` induces a group isomorphism
`π_N(O(n), x) ≃* π_N(O, of n x)`. -/
def StableOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableOrthogonalGroup
        (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n x) :=
  let hc := StableOrthogonalGroup.isNConnected_of n (by omega)
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N)
      (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

/-- `StableOrthogonalGroup.homotopyGroupMulEquivOf` acts on homotopy classes by
`HomotopyGroup.map`. -/
@[simp]
theorem StableOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x) :
    StableOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map
        (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n).toContinuousMap rfl a :=
  (rfl)

/-- **Positive-dimensional homotopy groups of `SO` and `O` coincide**: since `SO` embeds onto the
identity path component of `O`, the inclusion `SO → O` induces a group isomorphism
`π_N(SO, x) ≃* π_N(O, toStableOrthogonalGroup x)` for every nonempty cube-index type `N`. -/
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup) :
    HomotopyGroup N StableSpecialOrthogonalGroup x ≃*
      HomotopyGroup N StableOrthogonalGroup
        (StableSpecialOrthogonalGroup.toStableOrthogonalGroup x) :=
  HomotopyGroup.mulEquivOfIsEmbeddingOfPathComponentSubset
    (f := StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap)
    StableSpecialOrthogonalGroup.isClosedEmbedding_toStableOrthogonalGroup.isEmbedding
    (fun y hy ↦ by
      rw [mem_pathComponent_iff, StableOrthogonalGroup.joined_iff_det_eq,
        StableSpecialOrthogonalGroup.det_toStableOrthogonalGroup] at hy
      simpa [StableSpecialOrthogonalGroup.range_toStableOrthogonalGroup] using hy.symm)
    rfl

/-- `StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup` acts on homotopy
classes by `HomotopyGroup.map`. -/
@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup_apply
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup)
    (a : HomotopyGroup N StableSpecialOrthogonalGroup x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup x a =
      HomotopyGroup.map
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl a :=
  HomotopyGroup.mulEquivOfIsEmbeddingOfPathComponentSubset_apply _ _ rfl a

end Connectivity

end TauCeti
