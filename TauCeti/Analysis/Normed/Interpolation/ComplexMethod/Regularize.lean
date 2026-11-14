/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
public import TauCeti.Analysis.Normed.Interpolation.Regular
import Mathlib.Analysis.Normed.Group.Submodule

/-!
# Endpoint inclusions and regularization invariance in the complex method

Using Calderón's density lemma (`CompatibleCouple.dense_elementaryStripTraces`), this file proves
parts (b) and (c) of Bergh–Löfström, Theorem 4.2.2:

1. **Endpoint closures and inclusions (Theorem 4.2.2 (b)).** For a Banach couple `(X₀, X₁)`, every
   admissible boundary trace takes values in `(X₀°, X₁°) = (C.fstClosure, C.sndClosure)`, and
   evaluation at `0` and `1` induces contractive injections `ComplexMethodSpace.toFst :
   [X₀, X₁]_0 →L[ℂ] X₀` and `ComplexMethodSpace.toSnd : [X₀, X₁]_1 →L[ℂ] X₁` valued in `X₀°` and
   `X₁°`.

2. **Regularization invariance (Theorem 4.2.2 (c)).** For any Banach couple `(X₀, X₁)` and any
   `θ : ℝ`, inclusion of `(X₀°, X₁°)` into `(X₀, X₁)` induces surjective linear isometries
   `regularizeStripTracesEquiv : C.regularize.stripTraces ≃ₗᵢ[ℂ] C.stripTraces` and
   `ComplexMethodSpace.regularizeEquiv : [X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`, reducing complex
   interpolation of arbitrary Banach couples to regular couples.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.2 (Theorem 4.2.2 (b)–(c)).
-/

public noncomputable section

open Set
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Endpoint closures and inclusions (Bergh–Löfström, Theorem 4.2.2 (b)) -/

section Endpoint

private theorem stripTraces_eval_mem_closure [CompleteSpace X₀] [CompleteSpace X₁] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Submodule ℂ E) [IsClosed (S : Set E)]
    (ev : C.stripTraces →L[ℂ] E)
    (helem : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter), ev (C.expGaussianTrace hδ ω x) ∈ S)
    (g : C.stripTraces) : ev g ∈ S := by
  have hsub : C.elementaryStripTraces ≤ S.comap ev.toLinearMap :=
    C.elementaryStripTraces_le fun hδ ω x => helem hδ ω x
  have hcl : IsClosed (S.comap ev.toLinearMap : Set C.stripTraces) :=
    (inferInstance : IsClosed (S : Set E)).preimage ev.continuous
  exact Submodule.mem_comap.1 (hcl.closure_subset_iff.2 hsub (C.dense_elementaryStripTraces g))

/-- Every admissible boundary trace takes values in the closure `C.fstClosure` (`X₀°`) on the left
boundary line when `X₀` and `X₁` are complete. -/
theorem stripTraces_fst_apply_mem_fstClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t ∈ C.fstClosure := by
  simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
    stripTraces_eval_mem_closure C C.fstClosure
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
        ((ContinuousLinearMap.fst ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
      (fun hδ ω x => by
        simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
          C.fstClosure.smul_mem _ (C.interFst_mem_fstClosure x)) g

/-- Every admissible boundary trace takes values in the closure `C.sndClosure` (`X₁°`) on the right
boundary line when `X₀` and `X₁` are complete. -/
theorem stripTraces_snd_apply_mem_sndClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t ∈ C.sndClosure := by
  simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
    stripTraces_eval_mem_closure C C.sndClosure
      ((ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
        ((ContinuousLinearMap.snd ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
      (fun hδ ω x => by
        simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
          C.sndClosure.smul_mem _ (C.interSnd_mem_sndClosure x)) g

namespace ComplexMethodSpace

variable {C}

/-- The canonical contractive injection `[X₀, X₁]_0 →L[ℂ] X₀`, sending the class of `g` to
`g₀ 0`. -/
def toFst : C.ComplexMethodSpace 0 →L[ℂ] X₀ :=
  lift ((ZeroAtInftyContinuousMap.evalCLM ℂ 0).comp
      ((ContinuousLinearMap.fst ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    fun g hg => C.fstToSum_injective <| by
      simpa [show C.stripEval (0 : ℂ) g = C.fstToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0) by
        simpa using C.stripFunction_mul_I g 0] using hg

@[simp]
theorem toFst_mk (g : C.stripTraces) :
    toFst (mk 0 g) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 0 := by
  simp [toFst, ZeroAtInftyContinuousMap.evalCLM_apply]

@[simp]
theorem fstToSum_toFst (u : C.ComplexMethodSpace 0) : C.fstToSum (toFst u) = toSum u := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa [toSum_mk] using (C.stripFunction_mul_I g 0).symm

theorem toFst_injective : Function.Injective (toFst (C := C)) := fun _ _ huv =>
  toSum_injective <| by rw [← fstToSum_toFst, ← fstToSum_toFst, huv]

theorem norm_toFst_le (u : C.ComplexMethodSpace 0) : ‖toFst u‖ ≤ ‖u‖ :=
  le_of_forall_gt fun _ hr => by
    obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr; rw [toFst_mk]
    exact (((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1.norm_coe_le_norm 0).trans
      (norm_fst_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)))).trans_lt hg

@[simp]
theorem toFst_ofInter (x : C.inter) : toFst (ofInter 0 x) = C.interFst x :=
  C.fstToSum_injective <| by rw [fstToSum_toFst, toSum_ofInter ⟨le_rfl, zero_le_one⟩]

theorem toFst_mem_fstClosure [CompleteSpace X₀] [CompleteSpace X₁] (u : C.ComplexMethodSpace 0) :
    toFst u ∈ C.fstClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  exact toFst_mk g ▸ C.stripTraces_fst_apply_mem_fstClosure g 0

/-- The canonical contractive injection `[X₀, X₁]_1 →L[ℂ] X₁`, sending the class of `g` to
`g₁ 0`. -/
def toSnd : C.ComplexMethodSpace 1 →L[ℂ] X₁ :=
  lift ((ZeroAtInftyContinuousMap.evalCLM ℂ 0).comp
      ((ContinuousLinearMap.snd ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    fun g hg => C.sndToSum_injective <| by
      simpa [show C.stripEval (1 : ℂ) g = C.sndToSum ((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0) by
        simpa using C.stripFunction_one_add_mul_I g 0] using hg

@[simp]
theorem toSnd_mk (g : C.stripTraces) :
    toSnd (mk 1 g) = (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 0 := by
  simp [toSnd, ZeroAtInftyContinuousMap.evalCLM_apply]

@[simp]
theorem sndToSum_toSnd (u : C.ComplexMethodSpace 1) : C.sndToSum (toSnd u) = toSum u := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  simpa [toSum_mk] using (C.stripFunction_one_add_mul_I g 0).symm

theorem toSnd_injective : Function.Injective (toSnd (C := C)) := fun _ _ huv =>
  toSum_injective <| by rw [← sndToSum_toSnd, ← sndToSum_toSnd, huv]

theorem norm_toSnd_le (u : C.ComplexMethodSpace 1) : ‖toSnd u‖ ≤ ‖u‖ :=
  le_of_forall_gt fun _ hr => by
    obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr; rw [toSnd_mk]
    exact (((g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2.norm_coe_le_norm 0).trans
      (norm_snd_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)))).trans_lt hg

@[simp]
theorem toSnd_ofInter (x : C.inter) : toSnd (ofInter 1 x) = C.interSnd x :=
  C.sndToSum_injective <| by
    rw [sndToSum_toSnd, toSum_ofInter ⟨zero_le_one, le_rfl⟩, C.fstToSum_interFst]

theorem toSnd_mem_sndClosure [CompleteSpace X₀] [CompleteSpace X₁] (u : C.ComplexMethodSpace 1) :
    toSnd u ∈ C.sndClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  exact toSnd_mk g ▸ C.stripTraces_snd_apply_mem_sndClosure g 0

end ComplexMethodSpace

end Endpoint

/-! ### Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)) -/

section Regularize

omit [T1Space V] in
private theorem regularize_compat (y : C.regularize.inter) :
    C.fstToSum (C.fstClosure.subtypeL (C.regularize.interFst y)) =
      C.sndToSum (C.sndClosure.subtypeL (C.regularize.interSnd y)) := by
  rw [Submodule.subtypeL_apply, Submodule.subtypeL_apply, ← C.interFst_regularizeInterEquiv,
    ← C.interSnd_regularizeInterEquiv]
  exact C.fstToSum_interFst (C.regularizeInterEquiv y)

omit [T1Space V] in
private theorem sumLift_regularize_eq :
    C.regularize.sumLift (C.fstToSum.comp C.fstClosure.subtypeL)
      (C.sndToSum.comp C.sndClosure.subtypeL) (regularize_compat C) = C.regularizeSumMap :=
  (C.regularize.sumLift_unique _ _ (regularize_compat C)
    (ContinuousLinearMap.ext fun _ => by simp) (ContinuousLinearMap.ext fun _ => by simp)).symm

/-- Inclusion of `(X₀°, X₁°)` into `(X₀, X₁)` embeds `C.regularize.stripTraces` isometrically
into `C.stripTraces`. -/
def regularizeStripTracesIsometry : C.regularize.stripTraces →ₗᵢ[ℂ] C.stripTraces where
  toLinearMap :=
    (stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
      (regularize_compat C)).toLinearMap
  norm_map' g := by
    rw [ContinuousLinearMap.coe_coe, ← Submodule.norm_coe, ← Submodule.norm_coe,
      Prod.norm_def, Prod.norm_def]
    congr 1 <;> rw [ZeroAtInftyContinuousMap.norm_eq_iSup_norm,
      ZeroAtInftyContinuousMap.norm_eq_iSup_norm]
    · simp only [stripTracesMap_apply_fst, Submodule.subtypeL_apply, Submodule.norm_coe]
    · simp only [stripTracesMap_apply_snd, Submodule.subtypeL_apply, Submodule.norm_coe]

@[simp]
theorem regularizeStripTracesIsometry_apply_fst (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).1 t : X₀) :=
  stripTracesMap_apply_fst C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g t

@[simp]
theorem regularizeStripTracesIsometry_apply_snd (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).2 t : X₁) :=
  stripTracesMap_apply_snd C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g t

theorem stripEval_regularizeStripTracesIsometry (z : ℂ) (g : C.regularize.stripTraces) :
    C.stripEval z (C.regularizeStripTracesIsometry g) =
      C.regularizeSumMap (C.regularize.stripEval z g) := by
  -- Unfold `regularizeStripTracesIsometry` to `stripTracesMap` on `g`.
  change C.stripEval z
    (stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) g) =
      _
  rw [stripEval_stripTracesMap, sumLift_regularize_eq]

private theorem surjective_regularizeStripTracesIsometry [CompleteSpace X₀] [CompleteSpace X₁] :
    Function.Surjective C.regularizeStripTracesIsometry := by
  have : CompleteSpace C.fstClosure :=
    (inferInstance : IsClosed (C.fstClosure : Set X₀)).completeSpace_coe
  have : CompleteSpace C.sndClosure :=
    (inferInstance : IsClosed (C.sndClosure : Set X₁)).completeSpace_coe
  have hcl : IsClosed (Set.range C.regularizeStripTracesIsometry) :=
    C.regularizeStripTracesIsometry.isometry.isUniformInducing.isComplete_range.isClosed
  have hsub : (C.elementaryStripTraces : Set C.stripTraces) ⊆
      Set.range C.regularizeStripTracesIsometry := by
    -- Express subset inclusion as a submodule inequality to induct over `span`.
    change C.elementaryStripTraces ≤ LinearMap.range C.regularizeStripTracesIsometry.toLinearMap
    refine C.elementaryStripTraces_le fun hδ ω x => ?_
    refine ⟨C.regularize.expGaussianTrace hδ ω (C.regularizeInterEquiv.symm x), Subtype.ext <|
      Prod.ext (ZeroAtInftyContinuousMap.ext fun t => ?_)
        (ZeroAtInftyContinuousMap.ext fun t => ?_)⟩
    · rw [LinearIsometry.coe_toLinearMap, regularizeStripTracesIsometry_apply_fst,
        expGaussianTrace_apply_fst, expGaussianTrace_apply_fst, SetLike.val_smul,
        coe_interFst_regularizeInterEquiv_symm]
    · rw [LinearIsometry.coe_toLinearMap, regularizeStripTracesIsometry_apply_snd,
        expGaussianTrace_apply_snd, expGaussianTrace_apply_snd, SetLike.val_smul,
        coe_interSnd_regularizeInterEquiv_symm]
  exact Set.range_eq_univ.1 <| hcl.closure_eq ▸ (C.dense_elementaryStripTraces.mono hsub).closure_eq

/-- **Regularization invariance of admissible traces.** When `X₀` and `X₁` are Banach spaces,
every admissible function for `(X₀, X₁)` arises from a unique admissible function for `(X₀°, X₁°)`
of equal trace norm. -/
def regularizeStripTracesEquiv [CompleteSpace X₀] [CompleteSpace X₁] :
    C.regularize.stripTraces ≃ₗᵢ[ℂ] C.stripTraces :=
  LinearIsometryEquiv.ofSurjective C.regularizeStripTracesIsometry
    (surjective_regularizeStripTracesIsometry C)

@[simp]
theorem regularizeStripTracesEquiv_apply [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.regularize.stripTraces) :
    C.regularizeStripTracesEquiv g = C.regularizeStripTracesIsometry g := (rfl)

namespace ComplexMethodSpace

variable {C} [CompleteSpace X₀] [CompleteSpace X₁]

private def regularizeInvMap (θ : ℝ) :
    C.ComplexMethodSpace θ →L[ℂ] C.regularize.ComplexMethodSpace θ :=
  lift ((mk θ).comp (C.regularizeStripTracesEquiv.symm.toContinuousLinearEquiv
      : C.stripTraces →L[ℂ] C.regularize.stripTraces))
    fun g hg => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [← map_zero (mk (C := C.regularize) θ), mk_eq_mk_iff, map_zero]
      apply C.regularizeSumMap_injective
      rw [map_zero, ← stripEval_regularizeStripTracesIsometry,
        ← regularizeStripTracesEquiv_apply, C.regularizeStripTracesEquiv.apply_symm_apply, hg]

@[simp]
private theorem regularizeInvMap_mk (θ : ℝ) (g : C.stripTraces) :
    regularizeInvMap θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) :=
  lift_mk _ _ g

private theorem regularizeInvMap_norm_le (θ : ℝ) (u : C.ComplexMethodSpace θ) :
    ‖regularizeInvMap θ u‖ ≤ ‖u‖ :=
  le_of_forall_gt fun _ hr => by
    obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr; rw [regularizeInvMap_mk]
    exact (norm_mk_le _).trans_lt ((C.regularizeStripTracesEquiv.symm.norm_map g).trans_lt hg)

/-- **Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)).** For any Banach couple
`(X₀, X₁)` and any `θ : ℝ`, passing to the endpoint closures `(X₀°, X₁°)` preserves the complex
interpolation space isometrically: `[X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`. -/
def regularizeEquiv (C : CompatibleCouple ℂ X₀ X₁ V) (θ : ℝ) :
    C.regularize.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.ComplexMethodSpace θ :=
  LinearIsometryEquiv.ofBounds
    { toFun := map θ C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C)
      invFun := regularizeInvMap θ
      left_inv u := by
        obtain ⟨g, rfl⟩ := mk_surjective u
        have hmap : stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
            (regularize_compat C) g = C.regularizeStripTracesEquiv g := rfl
        rw [map_mk, hmap, regularizeInvMap_mk, C.regularizeStripTracesEquiv.symm_apply_apply]
      right_inv u := by
        obtain ⟨g, rfl⟩ := mk_surjective u
        have hmap : stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
            (regularize_compat C) (C.regularizeStripTracesEquiv.symm g) = g :=
          C.regularizeStripTracesEquiv.apply_symm_apply g
        rw [regularizeInvMap_mk, map_mk, hmap]
      map_add' := map_add _
      map_smul' := map_smul _ }
    (norm_map_le_of_norm_le _ _ (regularize_compat C)
      (fun x => (Submodule.norm_coe x).le) (fun x => (Submodule.norm_coe x).le))
    (regularizeInvMap_norm_le θ)

@[simp]
theorem regularizeEquiv_mk (θ : ℝ) (g : C.regularize.stripTraces) :
    regularizeEquiv C θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv g) := by
  -- Unfold `regularizeEquiv` to its underlying `ComplexMethodSpace.map`.
  change map θ C.fstClosure.subtypeL C.sndClosure.subtypeL (regularize_compat C) (mk θ g) = _
  rw [map_mk]; rfl

@[simp]
theorem regularizeEquiv_symm_mk (θ : ℝ) (g : C.stripTraces) :
    (regularizeEquiv C θ).symm (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) :=
  regularizeInvMap_mk θ g

/-- `regularizeEquiv` lies over `C.regularizeSumMap : X₀° + X₁° → X₀ + X₁`. -/
@[simp]
theorem toSum_regularizeEquiv (θ : ℝ) (u : C.regularize.ComplexMethodSpace θ) :
    toSum (regularizeEquiv C θ u) = C.regularizeSumMap (toSum u) := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [regularizeEquiv_mk, toSum_mk, toSum_mk, regularizeStripTracesEquiv_apply,
    stripEval_regularizeStripTracesIsometry]

/-- `regularizeEquiv` intertwines the inclusions of the intersections `X₀° ∩ X₁°` and `X₀ ∩ X₁`. -/
@[simp]
theorem regularizeEquiv_ofInter {θ : ℝ} (hθ : θ ∈ Icc 0 1) (y : C.regularize.inter) :
    regularizeEquiv C θ (ofInter θ y) = ofInter θ (C.regularizeInterEquiv y) := by
  ext
  rw [toSum_regularizeEquiv, toSum_ofInter hθ, toSum_ofInter hθ, regularizeSumMap_fstToSum,
    interFst_regularizeInterEquiv]

end ComplexMethodSpace

end Regularize

end TauCeti.CompatibleCouple
