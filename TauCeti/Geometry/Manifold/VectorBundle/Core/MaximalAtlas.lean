/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas
public import TauCeti.Topology.VectorBundle.Core.Basic

/-!
# Transition-cocycle cores from covering families in the maximal atlas

Given a `C^n` vector bundle `E → B` with model fibre `F` over `IB`, a family
`e : ι → Trivialization F (π F E)` of linear trivializations in
`(contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)`, and a point selector
`idx : B → ι` satisfying `b ∈ (e (idx b)).baseSet`, the pairwise coordinate changes
`(e i).coordChangeL 𝕜 (e j)` assemble into a `C^n` transition-cocycle core
`VectorBundleCore.ofMaximalAtlas`. Reconstructing a vector bundle from this cocycle recovers `E` up
to a canonical `C^n` bundle diffeomorphism `VectorBundleCore.ofMaximalAtlasDiffeomorph` covering the
identity on `B` via `VectorBundleCore.ofMaximalAtlasFiberEquiv` on every fibre and intertwining
`(ofMaximalAtlas ...).localTriv i` with `e i` (`VectorBundleCore.apply_ofMaximalAtlasDiffeomorph`).

This module adapts the topological core reconstruction `TauCeti.pointIndexedCore` and
`TauCeti.pointIndexedCoreHomeomorph` (factored through `VectorBundleCore.ofTrivializations` in
`TauCeti.Topology.VectorBundle.Core.Basic`) to `C^n` maximal-atlas covering families.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace VectorBundleCore

variable {𝕜 B F EB HB ι : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB] [ChartedSpace HB B]
  {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : ι → Trivialization F (π F E)) [∀ i, (e i).IsLinear 𝕜]
  (he : ∀ i, (e i).toOpenPartialHomeomorph ∈
    (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
  (idx : B → ι) (hidx : ∀ b, b ∈ (e (idx b)).baseSet)

/-- The `VectorBundleCore` whose open cover and transition cocycle are extracted from a covering
family `e : ι → Trivialization F (π F E)` of linear trivializations in the `C^n` maximal atlas of
`E`, with preferred chart `idx b` at each base point `b : B`. -/
def ofMaximalAtlas : VectorBundleCore 𝕜 B F ι :=
  ofTrivializations e
    (fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
      (he j)).continuousOn)
    idx hidx

@[simp]
theorem ofMaximalAtlas_localTriv_baseSet (i : ι) :
    ((ofMaximalAtlas e he idx hidx).localTriv i).baseSet = (e i).baseSet :=
  ofTrivializations_localTriv_baseSet e _ idx hidx i

/-- The `i`-th base set of `ofMaximalAtlas e he idx hidx` is `(e i).baseSet`. (Note that `simp`
reduces `(ofMaximalAtlas ...).baseSet i` via `VectorBundleCore.baseSet_at` and
`ofMaximalAtlas_localTriv_baseSet`.) -/
theorem ofMaximalAtlas_baseSet (i : ι) :
    (ofMaximalAtlas e he idx hidx).baseSet i = (e i).baseSet := by
  rw [baseSet_at, ofMaximalAtlas_localTriv_baseSet]

@[simp]
theorem ofMaximalAtlas_indexAt (b : B) : (ofMaximalAtlas e he idx hidx).indexAt b = idx b :=
  ofTrivializations_indexAt e _ idx hidx b

@[simp]
theorem ofMaximalAtlas_coordChange (i j : ι) (b : B) :
    (ofMaximalAtlas e he idx hidx).coordChange i j b =
      ((e i).coordChangeL 𝕜 (e j) b : F →L[𝕜] F) :=
  ofTrivializations_coordChange e _ idx hidx i j b

/-- The transition cocycle of `ofMaximalAtlas` is `C^n`. -/
instance isContMDiff_ofMaximalAtlas : (ofMaximalAtlas e he idx hidx).IsContMDiff IB n where
  contMDiffOn_coordChange i j := by
    rw [funext (ofMaximalAtlas_coordChange e he idx hidx i j), ofMaximalAtlas_baseSet,
      ofMaximalAtlas_baseSet]
    exact Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i) (he j)

/-- The continuous linear equivalence identifying the reconstructed fibre of `ofMaximalAtlas` at
`b` with `E b` via the inverse of the selected chart `e (idx b)`. -/
def ofMaximalAtlasFiberEquiv (b : B) : (ofMaximalAtlas e he idx hidx).Fiber b ≃L[𝕜] E b :=
  ofTrivializationsFiberEquiv e
    (fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
      (he j)).continuousOn)
    idx hidx b

@[simp]
theorem ofMaximalAtlasFiberEquiv_apply (b : B) (v : (ofMaximalAtlas e he idx hidx).Fiber b) :
    ofMaximalAtlasFiberEquiv e he idx hidx b v = (e (idx b)).symm b v :=
  ofTrivializationsFiberEquiv_apply e _ idx hidx b v

@[simp]
theorem ofMaximalAtlasFiberEquiv_symm_apply (b : B) (v : E b) :
    (ofMaximalAtlasFiberEquiv e he idx hidx b).symm v = (e (idx b) ⟨b, v⟩).2 :=
  ofTrivializationsFiberEquiv_symm_apply e _ idx hidx b v

variable [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]

private theorem contMDiff_ofMaximalAtlasTotalEquiv :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (ofTrivializationsTotalEquiv e
        (fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
          (he j)).continuousOn)
        idx hidx) := fun p ↦ by
  let hcont := fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
    (he j)).continuousOn
  let Z := ofTrivializations e hcont idx hidx
  have hp : ofTrivializationsTotalEquiv e hcont idx hidx p ∈ (e (idx p.proj)).source := by
    rw [(e (idx p.proj)).mem_source, ofTrivializationsTotalEquiv_apply]
    exact hidx p.proj
  rw [(e (idx p.proj)).contMDiffAt_iff_of_mem_maximalAtlas (he (idx p.proj)) hp]
  refine ⟨(contMDiffAt_proj Z.Fiber).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq <| funext fun q ↦ by simp),
    ((Bundle.contMDiffAt_totalSpace_iff.1 (contMDiffAt_id (x := p))).2).congr_of_eventuallyEq ?_⟩
  have hmem : p ∈ (Z.localTriv (idx p.proj)).source := by
    rw [Z.mem_localTriv_source, ofTrivializations_baseSet]
    exact hidx p.proj
  filter_upwards [(Z.localTriv (idx p.proj)).open_source.mem_nhds hmem] with r hr
  rw [Z.trivializationAt, ← Z.localTrivAt_def, ofTrivializations_indexAt]
  refine congrArg Prod.snd (apply_ofTrivializationsTotalEquiv e hcont idx hidx (idx p.proj) r ?_)
  rwa [Z.mem_localTriv_source, ofTrivializations_baseSet] at hr

private theorem contMDiff_ofMaximalAtlasTotalEquiv_symm :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (ofTrivializationsTotalEquiv e
        (fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
          (he j)).continuousOn)
        idx hidx).symm := fun q ↦ by
  let hcont := fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
    (he j)).continuousOn
  let Z := ofTrivializations e hcont idx hidx
  have hq : q ∈ (e (idx q.proj)).source := (e (idx q.proj)).mem_source.2 (hidx q.proj)
  refine Bundle.contMDiffAt_totalSpace_iff.2
    ⟨(contMDiffAt_proj E).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq <| funext fun s ↦ by simp),
      ((((e (idx q.proj)).contMDiffAt_iff_of_mem_maximalAtlas (he (idx q.proj)) hq).1
        (contMDiffAt_id (x := q))).2).congr_of_eventuallyEq ?_⟩
  filter_upwards [(e (idx q.proj)).open_source.mem_nhds hq] with s hs
  rw [Z.trivializationAt, ← Z.localTrivAt_def, ofTrivializationsTotalEquiv_symm_apply,
    ofTrivializations_indexAt]
  have h := apply_ofTrivializationsTotalEquiv e hcont idx hidx (idx q.proj)
    ((ofTrivializationsTotalEquiv e hcont idx hidx).symm s) (by
      rw [ofTrivializationsTotalEquiv_symm_apply]
      exact (e (idx q.proj)).mem_source.1 hs)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg Prod.snd h.symm

/-- **Cocycle-to-bundle `C^n` diffeomorphism.** The vector bundle glued from the transition cocycle
`ofMaximalAtlas e he idx hidx` is `C^n`-diffeomorphic to `TotalSpace F E` via
`ofMaximalAtlasFiberEquiv` on every fibre.

Unlike `TauCeti.bundleDiffeomorph` (which requires `[CompleteSpace 𝕜]` and
`[FiniteDimensional 𝕜 F]` to invert operators in Banach charts), this diffeomorphism holds for
arbitrary normed fibres `F` and nontrivially normed fields `𝕜` because each `e (idx b)` already
belongs to the `C^n` maximal atlas. -/
def ofMaximalAtlasDiffeomorph :
    (ofMaximalAtlas e he idx hidx).TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯
      TotalSpace F E where
  toEquiv := ofTrivializationsTotalEquiv e
    (fun i j ↦ (Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas (he i)
      (he j)).continuousOn)
    idx hidx
  contMDiff_toFun := contMDiff_ofMaximalAtlasTotalEquiv e he idx hidx
  contMDiff_invFun := contMDiff_ofMaximalAtlasTotalEquiv_symm e he idx hidx

@[simp]
theorem ofMaximalAtlasDiffeomorph_apply (p : (ofMaximalAtlas e he idx hidx).TotalSpace) :
    ofMaximalAtlasDiffeomorph e he idx hidx p =
      ⟨p.proj, ofMaximalAtlasFiberEquiv e he idx hidx p.proj p.2⟩ := by
  rw [← Diffeomorph.coe_toEquiv, ofMaximalAtlasDiffeomorph.eq_def, ofMaximalAtlasFiberEquiv.eq_def]
  exact ofTrivializationsTotalEquiv_apply _ _ _ _ p

@[simp]
theorem ofMaximalAtlasDiffeomorph_symm_apply (q : TotalSpace F E) :
    (ofMaximalAtlasDiffeomorph e he idx hidx).symm q =
      ⟨q.proj, (ofMaximalAtlasFiberEquiv e he idx hidx q.proj).symm q.2⟩ := by
  rw [← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv, ofMaximalAtlasDiffeomorph.eq_def,
    ofMaximalAtlasFiberEquiv.eq_def]
  exact ofTrivializationsTotalEquiv_symm_apply _ _ _ _ q

/-- `ofMaximalAtlasDiffeomorph` intertwines every core chart `localTriv i` with the corresponding
maximal-atlas trivialization `e i` over `(e i).baseSet`. -/
theorem apply_ofMaximalAtlasDiffeomorph (i : ι)
    (p : (ofMaximalAtlas e he idx hidx).TotalSpace) (hp : p.proj ∈ (e i).baseSet) :
    e i (ofMaximalAtlasDiffeomorph e he idx hidx p) =
      (ofMaximalAtlas e he idx hidx).localTriv i p := by
  rw [ofMaximalAtlasDiffeomorph.eq_def]
  exact apply_ofTrivializationsTotalEquiv _ _ _ _ i p hp

end VectorBundleCore
