/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback.Basic

/-!
# Pullbacks and Whitney sums of finite-rank bundle cores

Pulling back a point-indexed finite-rank bundle core commutes strictly with Whitney sums
(`pullback_whitneySum`), and `pullbackMap` commutes strictly with the Whitney projections,
inclusions, pairings, copairings, and direct sums of bundle morphisms (`pullbackMap_whitneyFst`,
`pullbackMap_whitneySnd`, `pullbackMap_whitneyInl`, `pullbackMap_whitneyInr`,
`pullbackMap_whitneyLift`, `pullbackMap_whitneyDesc`, `pullbackMap_whitneyMap`), as well as
with the fibrewise coordinate identification `whitneySumFiberEquiv`
(`whitneySumFiberEquiv_pullback_apply`).
-/

public section

open Bundle CategoryTheory VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back commutes strictly with Whitney sums. -/
@[simp] theorem pullback_whitneySum (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (whitneySum A D).pullback f = whitneySum (A.pullback f) (D.pullback f) := (rfl)

/-- Pulling back the first projection of a Whitney sum gives the first projection of the pulled-back
Whitney sum. -/
@[simp] theorem pullbackMap_whitneyFst (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyFst A D) f = whitneyFst (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyFst]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit source core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyFst _ _ x)

/-- Pulling back the second projection of a Whitney sum gives the second projection of the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneySnd (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneySnd A D) f = whitneySnd (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneySnd]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit source core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneySnd _ _ x)

/-- Pulling back the first inclusion into a Whitney sum gives the first inclusion into the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneyInl (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyInl A D) f = whitneyInl (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyInl]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit target core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyInl _ _ x)

/-- Pulling back the second inclusion into a Whitney sum gives the second inclusion into the
pulled-back Whitney sum. -/
@[simp] theorem pullbackMap_whitneyInr (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (whitneyInr A D) f = whitneyInr (A.pullback f) (D.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_whitneyInr]
  -- `(whitneySum A D).pullback f` is definitionally `whitneySum (A.pullback f) (D.pullback f)`
  -- (`pullback_whitneySum`), identifying the implicit target core of `fiberMap` on the right.
  exact Eq.symm (fiberMap_whitneyInr _ _ x)

/-- Pulling back commutes with pairing into a Whitney sum. -/
@[simp] theorem pullbackMap_whitneyLift {A D E : FiniteRankBundleCore 𝕜 Y}
    (a : E ⟶ A) (b : E ⟶ D) (f : C(X, Y)) :
    pullbackMap (whitneyLift a b) f = whitneyLift (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyLift_def, pullbackMap_add, pullbackMap_comp, pullbackMap_whitneyInl,
    pullbackMap_whitneyInr]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- Pulling back commutes with copairing out of a Whitney sum. -/
@[simp] theorem pullbackMap_whitneyDesc {A D E : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ E) (b : D ⟶ E) (f : C(X, Y)) :
    pullbackMap (whitneyDesc a b) f = whitneyDesc (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyDesc_def, pullbackMap_add, pullbackMap_comp, pullbackMap_whitneyFst,
    pullbackMap_whitneySnd]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- Pulling back commutes with direct sums of bundle morphisms. -/
@[simp] theorem pullbackMap_whitneyMap {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ A') (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (whitneyMap a b) f = whitneyMap (pullbackMap a f) (pullbackMap b f) := by
  simp only [whitneyMap_def, pullbackMap_whitneyLift, pullbackMap_comp, pullbackMap_whitneyFst,
    pullbackMap_whitneySnd]
  -- `(whitneySum A D).pullback f` and `whitneySum (A.pullback f) (D.pullback f)` coincide
  -- definitionally, as recorded by `pullback_whitneySum`.
  rfl

/-- On every fibre, `whitneySumFiberEquiv` on a pulled-back Whitney sum agrees with
`whitneySumFiberEquiv` at the image base point. -/
@[simp] theorem whitneySumFiberEquiv_pullback_apply (A D : FiniteRankBundleCore 𝕜 Y)
    (f : C(X, Y)) (x : X) (v : (whitneySum (A.pullback f) (D.pullback f)).core.Fiber x) :
    whitneySumFiberEquiv (A.pullback f) (D.pullback f) x v = whitneySumFiberEquiv A D (f x) v := by
  rw [whitneySumFiberEquiv_apply]
  -- Both fibres are `Fin (A.rank + D.rank) → 𝕜` (`rank_pullback`), matching
  -- `whitneySumFiberEquiv_apply` on the right.
  exact Eq.symm (whitneySumFiberEquiv_apply _ _ (f x) v)

end TauCeti.FiniteRankBundleCore
