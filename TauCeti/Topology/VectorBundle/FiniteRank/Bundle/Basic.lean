/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Glued
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Variable-rank finite-rank topological vector bundles

`TauCeti.FiniteRankVectorBundle 𝕜 X` is the category of variable-rank finite-rank topological
`𝕜`-vector bundles over `X` with fibres in `Type w`: a locally constant rank `LocallyConstant X ℕ`,
fibres `Fiber : X → Type w`, and Mathlib `VectorBundle 𝕜 (Fin n → 𝕜)` structures on all clopen rank
strata `{x : X // rank x = n}` without bounded-rank, finite-cover, compactness, or separation
hypotheses. Preferred charts (`preferredChartEquiv`) equip every fibre with `IsTopologicalAddGroup`,
`ContinuousSMul`, and `Module.Finite`; glued total-space topology, morphisms, and preadditive
category structure come from `TauCeti.VariableRankBundle`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section
open Bundle CategoryTheory Topology
namespace TauCeti
universe u v w

/-- A variable-rank finite-rank topological `𝕜`-vector bundle over `X` with fibres in `Type w`.
On each clopen stratum where `rank` takes value `n`, the restricted fibre family is a Mathlib
topological vector bundle with model fibre `Fin n → 𝕜`. -/
structure FiniteRankVectorBundle (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] where
  /-- The locally constant, not necessarily bounded, rank function. -/
  rank : LocallyConstant X ℕ
  /-- The fibre over each point of `X`, in an arbitrary universe `Type w`. -/
  Fiber : X → Type w
  [addCommGroupFiber : ∀ x, AddCommGroup (Fiber x)]
  [moduleFiber : ∀ x, Module 𝕜 (Fiber x)]
  [topologicalSpaceFiber : ∀ x, TopologicalSpace (Fiber x)]
  [topologicalSpaceStratumTotalSpace :
    ∀ n : ℕ, TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun x : {x // rank x = n} ↦ Fiber x.val))]
  [fiberBundleStratum : ∀ n, FiberBundle (Fin n → 𝕜) (fun x : {x // rank x = n} ↦ Fiber x.val)]
  [vectorBundleStratum : ∀ n, VectorBundle 𝕜 (Fin n → 𝕜) (fun x : {x // rank x = n} ↦ Fiber x.val)]

namespace FiniteRankVectorBundle
attribute [instance] addCommGroupFiber moduleFiber topologicalSpaceFiber
  topologicalSpaceStratumTotalSpace fiberBundleStratum vectorBundleStratum
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X] (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)

/-- The fibre family restricted to the `n`th clopen rank stratum `{x : X // V.rank x = n}`. -/
abbrev StratumFiber (n : ℕ) : {x : X // V.rank x = n} → Type w := fun x ↦ V.Fiber x.val

/-- The continuous linear equivalence from `V.Fiber x` to `Fin (V.rank x) → 𝕜` read in the
preferred stratum trivialization at `x`. -/
noncomputable def preferredChartEquiv (x : X) : V.Fiber x ≃L[𝕜] (Fin (V.rank x) → 𝕜) :=
  (trivializationAt (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
    ⟨x, rfl⟩).continuousLinearEquivAt 𝕜 ⟨x, rfl⟩ (mem_baseSet_trivializationAt _ _ _)
@[simp] theorem preferredChartEquiv_apply (x : X) (v : V.Fiber x) : V.preferredChartEquiv x v =
    (trivializationAt (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
      ⟨x, rfl⟩ ⟨⟨x, rfl⟩, v⟩).2 := by rfl
@[simp] theorem preferredChartEquiv_symm_apply (x : X) (w : Fin (V.rank x) → 𝕜) :
    (V.preferredChartEquiv x).symm w =
      (trivializationAt (Fin (V.rank x) → 𝕜) (V.StratumFiber (V.rank x))
        ⟨x, rfl⟩).symm ⟨x, rfl⟩ w := by rfl

instance (x : X) : IsTopologicalAddGroup (V.Fiber x) :=
  (V.preferredChartEquiv x).toContinuousAddEquiv.isTopologicalAddGroup
instance (x : X) : ContinuousSMul 𝕜 (V.Fiber x) := (V.preferredChartEquiv x).continuousSMul
instance (x : X) : Module.Finite 𝕜 (V.Fiber x) :=
  Module.Finite.of_surjective (V.preferredChartEquiv x).symm.toLinearMap
    (V.preferredChartEquiv x).symm.surjective

/-- Variable-rank vector bundles implement `VariableRankBundle` directly through their native
stratum bundles and identity fibre identifications. -/
instance instVariableRankBundle : VariableRankBundle (FiniteRankVectorBundle.{u, v, w} 𝕜 X) 𝕜 X
    FiniteRankVectorBundle.Fiber where
  rank V := V.rank
  StratumFiber V n := V.StratumFiber n
  stratumFiberEquiv V {_} y := LinearEquiv.refl 𝕜 (V.Fiber y.val)
@[simp] theorem variableRankBundle_rank : VariableRankBundle.rank V = V.rank := by rfl
@[simp] theorem stratumFiberEquiv_apply {n : ℕ} (y : {x : X // VariableRankBundle.rank V x = n})
    (v : VariableRankBundle.StratumFiber V n y) :
    VariableRankBundle.stratumFiberEquiv V y v = v := by rfl
@[simp] theorem stratumFiberEquiv_symm_apply {n : ℕ}
    (y : {x : X // VariableRankBundle.rank V x = n}) (v : V.Fiber y.val) :
    (VariableRankBundle.stratumFiberEquiv V y).symm v = v := by rfl

/-- Equip `TotalSpace Unit V.Fiber` with the glued topology of the native stratum bundles. -/
instance : TopologicalSpace (TotalSpace Unit V.Fiber) :=
  VariableRankBundle.instTopologicalSpaceTotalSpace V
@[simp high] theorem totalSpaceHomeomorph_apply (n : ℕ)
    (q : TotalSpace (Fin n → 𝕜) (V.StratumFiber n)) :
    VariableRankBundle.totalSpaceHomeomorph V ⟨n, q⟩ = ⟨q.proj.val, q.snd⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_apply V ⟨n, q⟩
@[simp high] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    (VariableRankBundle.totalSpaceHomeomorph V).symm p = ⟨V.rank p.proj, ⟨⟨p.proj, rfl⟩, p.snd⟩⟩ :=
  VariableRankBundle.totalSpaceHomeomorph_symm_apply V p

/-- Variable-rank vector bundles form a category of continuous fibrewise-linear maps. -/
instance : Category (FiniteRankVectorBundle.{u, v, w} 𝕜 X) := VariableRankBundle.category
/-- Composition of variable-rank vector-bundle morphisms is bilinear on the hom groups. -/
instance : Preadditive (FiniteRankVectorBundle.{u, v, w} 𝕜 X) := VariableRankBundle.preadditive

end FiniteRankVectorBundle
end TauCeti
