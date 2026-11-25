/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic

/-!
# Endomorphisms of a vector bundle read in a local orthonormal frame

Let `𝕜` be `ℝ` or `ℂ` (an `RCLike` field), let `E → B` be a vector bundle over `𝕜` with model
fibre `F` whose fibres are inner product spaces over `𝕜` with continuous fibre norm
(`TauCeti.ContinuousFiberNorm F E`), and let `e` be a linear chart of `E`. Over `e.baseSet` the
local Gram–Schmidt orthonormal frame `σ_y = e.orthonormalFrameAt c b y : V ≃ₗᵢ[𝕜] E y` identifies
the endomorphisms of the fibre `E y` with the endomorphisms of the model inner product space `V`
by conjugation. This file shows that this identification is continuous in both directions between
the total space of the endomorphism bundle `Hom(E, E)` and `B × (V →L[𝕜] V)`.

## Main results

* `Bundle.Trivialization.continuousOn_conjStarAlgEquiv_orthonormalFrameAt_symm`: reading an
  endomorphism of a fibre as `σ_y⁻¹ A σ_y` is continuous on the part of the total space of
  `Hom(E, E)` over `e.baseSet`.
* `Bundle.Trivialization.continuousOn_totalSpaceMk_conjStarAlgEquiv_orthonormalFrameAt`:
  conjugating a model endomorphism `Q` to `σ_y Q σ_y⁻¹` is continuous on `e.baseSet × univ` into
  the total space of `Hom(E, E)`.
-/

public section

noncomputable section

open Bundle Set Topology TauCeti

namespace Bundle.Trivialization

-- `CompleteSpace V` follows from `FiniteDimensional 𝕜 V`, but instance search does not find it for
-- a variable field `𝕜`; it is needed for the star structure on `V →L[𝕜] V`.
variable {𝕜 : Type*} [RCLike 𝕜] {B F V : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)] [∀ b, CompleteSpace (E b)]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V] [FiniteDimensional 𝕜 V]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
  (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (c : Module.Basis ι 𝕜 F) (b : OrthonormalBasis ι 𝕜 V)

/-- Over `e.baseSet`, reading an endomorphism of a fibre in the local orthonormal frame
`e.orthonormalFrameAt c b` is continuous on the total space of the endomorphism bundle. -/
theorem continuousOn_conjStarAlgEquiv_orthonormalFrameAt_symm :
    ContinuousOn (fun q : TotalSpace (F →L[𝕜] F) (fun y ↦ E y →L[𝕜] E y) ↦
        (e.orthonormalFrameAt c b q.proj).symm.conjStarAlgEquiv q.snd)
      (TotalSpace.proj ⁻¹' e.baseSet) := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  -- The endomorphism applied to the frame vector over its base point, read in the total space.
  have hid : ContinuousOn (fun q : TotalSpace (F →L[𝕜] F) (fun y ↦ E y →L[𝕜] E y) ↦
      TotalSpace.mk' (F →L[𝕜] F) (E := fun y ↦ E y →L[𝕜] E y) q.proj q.snd)
      (TotalSpace.proj ⁻¹' e.baseSet) :=
    continuous_id.continuousOn
  have hσ : ContinuousOn (fun q : TotalSpace (F →L[𝕜] F) (fun y ↦ E y →L[𝕜] E y) ↦
      TotalSpace.mk' F q.proj (e.orthonormalFrameAt c b q.proj v))
      (TotalSpace.proj ⁻¹' e.baseSet) :=
    (e.continuousOn_totalSpaceMk_orthonormalFrameAt c b v).comp
      (FiberBundle.continuous_proj _ _).continuousOn fun _ hq ↦ hq
  have hv : ContinuousOn (fun q : TotalSpace (F →L[𝕜] F) (fun y ↦ E y →L[𝕜] E y) ↦
      TotalSpace.mk' F q.proj (q.snd (e.orthonormalFrameAt c b q.proj v)))
      (TotalSpace.proj ⁻¹' e.baseSet) :=
    hid.clm_bundle_apply hσ
  exact ((e.continuousOn_orthonormalFrameAt_symm c b).comp hv fun _ hq ↦ hq).congr
    fun q _ ↦ by simp

/-- Over `e.baseSet`, conjugating model endomorphisms by the local orthonormal frame
`e.orthonormalFrameAt c b` is continuous into the total space of the endomorphism bundle. -/
theorem continuousOn_totalSpaceMk_conjStarAlgEquiv_orthonormalFrameAt [FiniteDimensional 𝕜 F] :
    ContinuousOn (fun q : B × (V →L[𝕜] V) ↦
        TotalSpace.mk' (F →L[𝕜] F) (E := fun y ↦ E y →L[𝕜] E y) q.1
          ((e.orthonormalFrameAt c b q.1).conjStarAlgEquiv q.2))
      (e.baseSet ×ˢ univ) := by
  rintro ⟨y₀, Q₀⟩ ⟨hy₀, -⟩
  rw [continuousWithinAt_hom_bundle]
  refine ⟨continuous_fst.continuousWithinAt, ?_⟩
  let φ := trivializationAt F E y₀
  have hU : e.baseSet ∩ φ.baseSet ∈ 𝓝 y₀ :=
    (e.open_baseSet.inter φ.open_baseSet).mem_nhds ⟨hy₀, mem_baseSet_trivializationAt F E y₀⟩
  -- The local frame read in `φ`, and its inverse read in `φ`, are continuous near `y₀`.
  have hA : ContinuousOn (fun y ↦ (φ.continuousLinearMapAt 𝕜 y).comp
      ((e.orthonormalFrameAt c b y).toContinuousLinearEquiv : V →L[𝕜] E y))
      (e.baseSet ∩ φ.baseSet) := by
    refine continuousOn_clm_apply.2 fun v ↦ ?_
    refine (continuous_snd.comp_continuousOn (φ.continuousOn.comp
      ((e.continuousOn_totalSpaceMk_orthonormalFrameAt c b v).mono inter_subset_left)
      fun y hy ↦ φ.mem_source.2 hy.2)).congr fun y hy ↦ ?_
    simp [φ.continuousLinearMapAt_apply_of_mem (R := 𝕜) hy.2]
  have hC : ContinuousOn (fun y ↦ ((e.orthonormalFrameAt c b y).symm.toContinuousLinearEquiv :
      E y →L[𝕜] V).comp (φ.symmL 𝕜 y)) (e.baseSet ∩ φ.baseSet) := by
    refine continuousOn_clm_apply.2 fun w ↦ ?_
    have hs : ContinuousOn (fun y ↦ TotalSpace.mk' F y (φ.symm y w)) (e.baseSet ∩ φ.baseSet) :=
      φ.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        fun y (hy : y ∈ e.baseSet ∩ φ.baseSet) ↦ ⟨hy.2, mem_univ w⟩
    exact ((e.continuousOn_orthonormalFrameAt_symm c b).comp hs fun y hy ↦ hy.1).congr
      fun y hy ↦ by simp [φ.symmL_apply hy.2]
  have hA' : ContinuousAt (fun q : B × (V →L[𝕜] V) ↦ (φ.continuousLinearMapAt 𝕜 q.1).comp
      ((e.orthonormalFrameAt c b q.1).toContinuousLinearEquiv : V →L[𝕜] E q.1)) (y₀, Q₀) := by
    have h := hA.continuousAt hU
    exact h.comp_of_eq continuous_fst.continuousAt rfl
  have hC' : ContinuousAt (fun q : B × (V →L[𝕜] V) ↦
      ((e.orthonormalFrameAt c b q.1).symm.toContinuousLinearEquiv : E q.1 →L[𝕜] V).comp
        (φ.symmL 𝕜 q.1)) (y₀, Q₀) := by
    have h := hC.continuousAt hU
    exact h.comp_of_eq continuous_fst.continuousAt rfl
  have hcomp := hA'.clm_comp (continuous_snd.continuousAt.clm_comp hC')
  refine hcomp.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q _
    ext w
    simp [ContinuousLinearMap.inCoordinates, φ]
  · ext w
    simp [ContinuousLinearMap.inCoordinates, φ]

end Bundle.Trivialization
