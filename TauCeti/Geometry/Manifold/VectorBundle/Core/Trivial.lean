/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
public import TauCeti.Topology.VectorBundle.Core.Trivial

/-!
# Smooth global trivialization of a core with identity transitions

`VectorBundleCore.globalTrivializationOfCoordChangeEqId_mem_maximalAtlas`: the global product
trivialization of a vector bundle core whose transitions are the identity on chart overlaps
belongs to the maximal `C^n` atlas for every regularity and every model of the base. This gives
global `C^n` triviality, including smooth and holomorphic triviality, for such cores, for
instance for bundles associated with the trivial representation of a deck group, without any
finite-rank or completeness assumption on the fibre.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace VectorBundleCore

variable {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {n : ℕ∞ω} (Z : VectorBundleCore 𝕜 B F ι)
  (hcoord : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, ∀ v, Z.coordChange i j x v = v)

/-- The global product trivialization of a core whose transitions are the identity on chart
overlaps belongs to the maximal `C^n` atlas, for every model of the base and every regularity
`n`. -/
theorem globalTrivializationOfCoordChangeEqId_mem_maximalAtlas :
    (Z.globalTrivializationOfCoordChangeEqId hcoord).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas Z.TotalSpace := by
  let e := Z.globalTrivializationOfCoordChangeEqId hcoord
  refine (Trivialization.mem_maximalAtlas_contMDiffFiberwiseLinear_iff IB n e).2 ?_
  rintro e' ⟨i, rfl⟩
  have h₁ (x : B) (hx : x ∈ e.baseSet ∩ (Z.localTriv i).baseSet) :
      (e.coordChangeL 𝕜 (Z.localTriv i) x : F →L[𝕜] F) = ContinuousLinearMap.id 𝕜 F := by
    ext v
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply,
      Trivialization.coordChangeL_apply _ _ hx, localTriv_apply]
    simp only [e, globalTrivializationOfCoordChangeEqId_symm_apply,
      hcoord _ _ x ⟨Z.mem_baseSet_at x, hx.2⟩]
  have h₂ (x : B) (hx : x ∈ e.baseSet ∩ (Z.localTriv i).baseSet) :
      ((Z.localTriv i).coordChangeL 𝕜 e x : F →L[𝕜] F) = ContinuousLinearMap.id 𝕜 F := by
    ext v
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply,
      Trivialization.coordChangeL_apply _ _ ⟨hx.2, hx.1⟩]
    simp only [e, globalTrivializationOfCoordChangeEqId_apply,
      localTriv_symm_apply Z i hx.2, hcoord _ _ x ⟨hx.2, Z.mem_baseSet_at x⟩]
  exact ⟨contMDiffOn_const.congr h₁, contMDiffOn_const.congr h₂⟩

end VectorBundleCore
