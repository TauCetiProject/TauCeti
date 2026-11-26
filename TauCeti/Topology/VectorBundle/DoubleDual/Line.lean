/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.DoubleDual
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Double duality with values in a line bundle

For a finite-rank vector bundle `V` and a line bundle `L`, evaluation identifies `V` with
`Hom(Hom(V, L), L)`. In the induced Hom frames the two occurrences of the line transition
cancel, and evaluation is the ordinary scalar double-dual map on the model fibre.
-/

public noncomputable section

open Bundle FiberBundle
open scoped Topology

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (V L : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module 𝕜 (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace 𝕜 L)] [FiberBundle 𝕜 L] [VectorBundle 𝕜 𝕜 L]

namespace TauCeti

/-- Evaluation identifies a finite-dimensional fibre with its double dual taken with values
in a line. Transporting `bundleDoubleDualEquiv` through a local frame of the line gives this
identification without a global nonvanishing section. -/
def bundleLineDoubleDualEquiv (x : B) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    V x ≃L[𝕜] ((V x →L[𝕜] L x) →L[𝕜] L x) :=
  letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  letI := VectorBundle.continuousSMul 𝕜 𝕜 L
  let d := (trivializationAt 𝕜 L x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt 𝕜 L x)
  (bundleDoubleDualEquiv (F := F) V x).trans
    (((ContinuousLinearEquiv.refl 𝕜 (V x)).arrowCongr d.symm).arrowCongr d.symm)

/-- The line-valued double-dual equivalence evaluates a line-valued functional on the vector. -/
@[simp]
theorem bundleLineDoubleDualEquiv_apply (x : B) (v : V x) (φ : V x →L[𝕜] L x) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    bundleLineDoubleDualEquiv (F := F) V L x v φ = φ v := by
  simp [bundleLineDoubleDualEquiv,
    (trivializationAt 𝕜 L x).symm_apply_apply_mk (mem_baseSet_trivializationAt 𝕜 L x)]

/-- A line-valued functional on the inverse image evaluates by the original double-dual element. -/
@[simp]
theorem apply_bundleLineDoubleDualEquiv_symm (x : B) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    ∀ (Φ : (V x →L[𝕜] L x) →L[𝕜] L x) (φ : V x →L[𝕜] L x),
      φ ((bundleLineDoubleDualEquiv (F := F) V L x).symm Φ) = Φ φ := by
  intro Φ φ
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  rw [← bundleLineDoubleDualEquiv_apply (F := F) V L x,
    ContinuousLinearEquiv.apply_symm_apply]

end TauCeti

namespace Bundle.Trivialization

open TauCeti

attribute [local instance] Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  Bundle.ContinuousLinearMap.fiberBundle Bundle.ContinuousLinearMap.vectorBundle

variable {V L} (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (d : Trivialization 𝕜 (π 𝕜 L)) [MemTrivializationAtlas d]

/-- In any pair of vector and line frames, the line-valued identification is ordinary
double-dual evaluation in the induced Hom frames. -/
theorem bundleLineDoubleDualEquiv_inFrame {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet)
    (v : V x) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    (((e.continuousLinearMap (RingHom.id 𝕜) d).continuousLinearMap (RingHom.id 𝕜) d)
      ⟨x, bundleLineDoubleDualEquiv (F := F) V L x v⟩).2 =
        NormedSpace.inclusionInDoubleDual 𝕜 F (e ⟨x, v⟩).2 := by
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  have hxd : x ∈ (e.continuousLinearMap (RingHom.id 𝕜) d).baseSet ∩ d.baseSet :=
    ⟨hx, hx.2⟩
  rw [Trivialization.apply_eq_prod_continuousLinearEquivAt 𝕜 _ x hxd,
    Trivialization.apply_eq_prod_continuousLinearEquivAt 𝕜 e x hx.1]
  simp only [Trivialization.continuousLinearEquivAt_continuousLinearMap _ _ hxd,
    Trivialization.continuousLinearEquivAt_continuousLinearMap _ _ hx]
  ext φ
  simp [NormedSpace.dual_def, d.apply_mk_symm hx.2]

/-- Applying scalar double-dual evaluation to the frame coordinates of the inverse
identification recovers the original coordinates in the induced Hom frame. -/
theorem bundleLineDoubleDualEquiv_symm_inFrame {x : B} (hx : x ∈ e.baseSet ∩ d.baseSet) :
    letI := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
    letI := VectorBundle.continuousSMul 𝕜 𝕜 L
    ∀ Φ : (V x →L[𝕜] L x) →L[𝕜] L x, NormedSpace.inclusionInDoubleDual 𝕜 F
      (e ⟨x, (bundleLineDoubleDualEquiv (F := F) V L x).symm Φ⟩).2 =
        (((e.continuousLinearMap (RingHom.id 𝕜) d).continuousLinearMap (RingHom.id 𝕜) d)
          ⟨x, Φ⟩).2 := by
  intro Φ
  let := VectorBundle.isTopologicalAddGroup 𝕜 𝕜 L
  let := VectorBundle.continuousSMul 𝕜 𝕜 L
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (e.bundleLineDoubleDualEquiv_inFrame d hx
      ((bundleLineDoubleDualEquiv (F := F) V L x).symm Φ)).symm

end Bundle.Trivialization
