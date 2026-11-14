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
# Endpoint identifications and regularization invariance in the complex method

Using `CompatibleCouple.dense_elementaryStripTraces`, this file proves Bergh–Löfström,
Theorem 4.2.2 (b)–(c):
* **Endpoint identifications (Theorem 4.2.2 (b)):** `ComplexMethodSpace.norm_ofInter_zero`,
  `ComplexMethodSpace.norm_ofInter_one`, `ComplexMethodSpace.fstClosureEquiv`,
  `ComplexMethodSpace.sndClosureEquiv`, and `fstEquiv`, `sndEquiv` when `C.IsRegular`.
* **Regularization invariance (Theorem 4.2.2 (c)):** `regularizeStripTracesEquiv` and
  `ComplexMethodSpace.regularizeEquiv : [X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190, §6.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §4.2 (Theorem 4.2.2 (b)–(c)).
-/

public noncomputable section

open Complex Filter Set Topology
open scoped ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### Endpoint closures and isometric identifications (Bergh–Löfström, Theorem 4.2.2 (b)) -/

private theorem norm_expGaussianTrace_one_le (ω : ℝ) (x : C.inter) :
    ‖C.expGaussianTrace one_pos ω x‖ ≤ max ‖C.interFst x‖ (Real.exp (1 + ω) * ‖C.interSnd x‖) := by
  rw [← Submodule.norm_coe]
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_,
    (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_⟩
  · rw [expGaussianTrace_apply_fst, norm_smul, Complex.norm_exp]
    have hre : ((1 : ℂ) * ((t : ℂ) * I) ^ 2 + (ω : ℂ) * ((t : ℂ) * I)).re ≤ 0 := by
      have : ((1 : ℂ) * ((t : ℂ) * I) ^ 2 + (ω : ℂ) * ((t : ℂ) * I)).re = -t ^ 2 := by simp [sq]
      nlinarith [sq_nonneg t]
    exact ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.2 hre)
      (norm_nonneg _)).trans_eq (one_mul _)).trans (le_max_left _ _)
  · rw [expGaussianTrace_apply_snd, norm_smul, Complex.norm_exp]
    have hre : ((1 : ℂ) * (1 + (t : ℂ) * I) ^ 2 + (ω : ℂ) * (1 + (t : ℂ) * I)).re ≤ 1 + ω := by
      have : ((1 : ℂ) * (1 + (t : ℂ) * I) ^ 2 + (ω : ℂ) * (1 + (t : ℂ) * I)).re =
          1 - t ^ 2 + ω := by simp [sq]
      nlinarith [sq_nonneg t]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hre)
      (norm_nonneg _)).trans (le_max_right _ _)

private theorem stripTraces_eval_mem_closure [CompleteSpace X₀] [CompleteSpace X₁] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Submodule ℂ E) [IsClosed (S : Set E)]
    (ev : C.stripTraces →L[ℂ] E)
    (helem : ∀ {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) (x : C.inter), ev (C.expGaussianTrace hδ ω x) ∈ S)
    (g : C.stripTraces) : ev g ∈ S :=
  ((inferInstance : IsClosed (S : Set E)).preimage ev.continuous).closure_subset_iff.2
    (SetLike.coe_subset_coe.2 <|
      C.elementaryStripTraces_le (S := S.comap ev.toLinearMap) fun hδ ω x => helem hδ ω x)
    (C.dense_elementaryStripTraces g)

/-- Every admissible boundary trace takes values in `C.fstClosure` (`X₀°`) on `re z = 0`. -/
theorem stripTraces_fst_apply_mem_fstClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t ∈ C.fstClosure := by
  simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using stripTraces_eval_mem_closure C C.fstClosure
    ((ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
      ((ContinuousLinearMap.fst ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    (fun _ _ x => by simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
      C.fstClosure.smul_mem _ (C.interFst_mem_fstClosure x)) g

/-- Every admissible boundary trace takes values in `C.sndClosure` (`X₁°`) on `re z = 1`. -/
theorem stripTraces_snd_apply_mem_sndClosure [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) : (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t ∈ C.sndClosure := by
  simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using stripTraces_eval_mem_closure C C.sndClosure
    ((ZeroAtInftyContinuousMap.evalCLM ℂ t).comp
      ((ContinuousLinearMap.snd ℂ C₀(ℝ, X₀) C₀(ℝ, X₁)).comp C.stripTraces.subtypeL))
    (fun _ _ x => by simpa [ZeroAtInftyContinuousMap.evalCLM_apply] using
      C.sndClosure.smul_mem _ (C.interSnd_mem_sndClosure x)) g

namespace ComplexMethodSpace

variable {C}

/-- On `X₀ ∩ X₁`, the `[X₀, X₁]_0` norm coincides with the `X₀` norm. -/
@[simp] theorem norm_ofInter_zero (x : C.inter) : ‖ofInter 0 x‖ = ‖C.interFst x‖ := by
  have ht : Tendsto (fun ω : ℝ => max ‖C.interFst x‖ (Real.exp (1 + ω) * ‖C.interSnd x‖))
      atBot (𝓝 ‖C.interFst x‖) := by
    simpa [max_eq_left (norm_nonneg (C.interFst x))] using
      (tendsto_const_nhds (x := ‖C.interFst x‖)).max ((Real.tendsto_exp_atBot.comp
        (tendsto_atBot_add_const_left _ 1 tendsto_id)).mul_const ‖C.interSnd x‖)
  refine le_antisymm (ge_of_tendsto' ht fun ω => ?_) (toFst_ofInter x ▸ norm_toFst_le _)
  have heq : mk 0 (C.expGaussianTrace one_pos ω x) = ofInter 0 x := by simp
  exact heq ▸ (norm_mk_le _).trans (norm_expGaussianTrace_one_le C ω x)

/-- On `X₀ ∩ X₁`, the `[X₀, X₁]_1` norm coincides with the `X₁` norm. -/
@[simp] theorem norm_ofInter_one (x : C.inter) : ‖ofInter 1 x‖ = ‖C.interSnd x‖ := by
  have ht : Tendsto (fun ω : ℝ => max (Real.exp (-(1 + ω)) * ‖C.interFst x‖) ‖C.interSnd x‖)
      atTop (𝓝 ‖C.interSnd x‖) := by
    simpa [max_eq_right (norm_nonneg (C.interSnd x))] using
      ((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_atTop_add_const_left _ 1 tendsto_id))).mul_const ‖C.interFst x‖).max
        (tendsto_const_nhds (x := ‖C.interSnd x‖))
  refine le_antisymm (ge_of_tendsto' ht fun ω => ?_) (toSnd_ofInter x ▸ norm_toSnd_le _)
  have heq : mk 1 (Complex.exp (-(1 + ω : ℂ)) • C.expGaussianTrace one_pos ω x) =
      ofInter 1 x := by rw [map_smul, mk_expGaussianTrace, smul_smul, ← Complex.exp_add]; simp
  rw [← heq]; refine (norm_mk_le _).trans ((norm_smul _ _).trans_le ?_)
  rw [Complex.norm_exp, show (-(1 + ω : ℂ)).re = -(1 + ω) by simp]
  refine (mul_le_mul_of_nonneg_left (norm_expGaussianTrace_one_le C ω x)
    (Real.exp_pos _).le).trans_eq ?_
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul]

section Complete

variable [CompleteSpace X₀] [CompleteSpace X₁]

theorem toFst_mem_fstClosure (u : C.ComplexMethodSpace 0) : toFst u ∈ C.fstClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u; exact toFst_mk g ▸ C.stripTraces_fst_apply_mem_fstClosure g 0
theorem toSnd_mem_sndClosure (u : C.ComplexMethodSpace 1) : toSnd u ∈ C.sndClosure := by
  obtain ⟨g, rfl⟩ := mk_surjective u; exact toSnd_mk g ▸ C.stripTraces_snd_apply_mem_sndClosure g 0

@[simp] theorem norm_toFst (u : C.ComplexMethodSpace 0) : ‖toFst u‖ = ‖u‖ :=
  (denseRange_ofInter (C := C) 0).induction_on u
    (isClosed_eq (continuous_norm.comp (toFst (C := C)).continuous) continuous_norm) (by simp)
@[simp] theorem norm_toSnd (u : C.ComplexMethodSpace 1) : ‖toSnd u‖ = ‖u‖ :=
  (denseRange_ofInter (C := C) 1).induction_on u
    (isClosed_eq (continuous_norm.comp (toSnd (C := C)).continuous) continuous_norm) (by simp)

private def codRestrictEquiv {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℂ X] (ev : E →L[ℂ] X)
    (S : Submodule ℂ X) (hmem : ∀ u, ev u ∈ S) (hnorm : ∀ u, ‖ev u‖ = ‖u‖)
    (f : α → S) (hf : DenseRange f) (hrange : ∀ y, ∃ u, ev u = f y) : E ≃ₗᵢ[ℂ] S :=
  let iso : E →ₗᵢ[ℂ] S := ⟨(ev.codRestrict S hmem).toLinearMap, fun u => by
    rw [ContinuousLinearMap.coe_coe, ← Submodule.norm_coe,
      ContinuousLinearMap.coe_codRestrict_apply, hnorm]⟩
  LinearIsometryEquiv.ofSurjective iso <| Set.range_eq_univ.1 <|
    iso.isometry.isUniformInducing.isComplete_range.isClosed.closure_eq ▸
      (hf.mono <| by intro _ hx; rcases hx with ⟨y, rfl⟩; obtain ⟨u, hu⟩ := hrange y
                     exact ⟨u, Subtype.ext hu⟩).closure_eq

/-- **Endpoint identification at `0` (Bergh–Löfström, Theorem 4.2.2 (b)).** For any Banach couple
`(X₀, X₁)`, evaluation at `0` is a surjective linear isometry `[X₀, X₁]_0 ≃ₗᵢ[ℂ] X₀°`. -/
def fstClosureEquiv (C : CompatibleCouple ℂ X₀ X₁ V) :
    C.ComplexMethodSpace 0 ≃ₗᵢ[ℂ] C.fstClosure :=
  codRestrictEquiv toFst C.fstClosure toFst_mem_fstClosure norm_toFst C.regularize.interFst
    C.isRegular_regularize.denseRange_interFst fun y =>
      ⟨ofInter 0 (C.regularizeInterEquiv y), by simp [C.interFst_regularizeInterEquiv]⟩

@[simp] theorem coe_fstClosureEquiv (u : C.ComplexMethodSpace 0) :
    (fstClosureEquiv C u : X₀) = toFst u := by simp [fstClosureEquiv, codRestrictEquiv]
@[simp] theorem fstClosureEquiv_ofInter (x : C.inter) :
    fstClosureEquiv C (ofInter 0 x) = ⟨C.interFst x, C.interFst_mem_fstClosure x⟩ :=
  Subtype.ext (by simp)
@[simp] theorem toFst_fstClosureEquiv_symm (y : C.fstClosure) :
    toFst ((fstClosureEquiv C).symm y) = y := by
  rw [← coe_fstClosureEquiv, (fstClosureEquiv C).apply_symm_apply]
@[simp] theorem toSum_fstClosureEquiv_symm (y : C.fstClosure) :
    toSum ((fstClosureEquiv C).symm y) = C.fstToSum y := by
  rw [← fstToSum_toFst, toFst_fstClosureEquiv_symm]
@[simp] theorem fstClosureEquiv_symm_coe_fst (x : C.inter) (hx : (x : X₀ × X₁).1 ∈ C.fstClosure) :
    (fstClosureEquiv C).symm ⟨(x : X₀ × X₁).1, hx⟩ = ofInter 0 x :=
  (fstClosureEquiv C).injective (Subtype.ext (by simp))

/-- **Endpoint identification at `1` (Bergh–Löfström, Theorem 4.2.2 (b)).** For any Banach couple
`(X₀, X₁)`, evaluation at `1` is a surjective linear isometry `[X₀, X₁]_1 ≃ₗᵢ[ℂ] X₁°`. -/
def sndClosureEquiv (C : CompatibleCouple ℂ X₀ X₁ V) :
    C.ComplexMethodSpace 1 ≃ₗᵢ[ℂ] C.sndClosure :=
  codRestrictEquiv toSnd C.sndClosure toSnd_mem_sndClosure norm_toSnd C.regularize.interSnd
    C.isRegular_regularize.denseRange_interSnd fun y =>
      ⟨ofInter 1 (C.regularizeInterEquiv y), by simp [C.interSnd_regularizeInterEquiv]⟩

@[simp] theorem coe_sndClosureEquiv (u : C.ComplexMethodSpace 1) :
    (sndClosureEquiv C u : X₁) = toSnd u := by simp [sndClosureEquiv, codRestrictEquiv]
@[simp] theorem sndClosureEquiv_ofInter (x : C.inter) :
    sndClosureEquiv C (ofInter 1 x) = ⟨C.interSnd x, C.interSnd_mem_sndClosure x⟩ :=
  Subtype.ext (by simp)
@[simp] theorem toSnd_sndClosureEquiv_symm (y : C.sndClosure) :
    toSnd ((sndClosureEquiv C).symm y) = y := by
  rw [← coe_sndClosureEquiv, (sndClosureEquiv C).apply_symm_apply]
@[simp] theorem toSum_sndClosureEquiv_symm (y : C.sndClosure) :
    toSum ((sndClosureEquiv C).symm y) = C.sndToSum y := by
  rw [← sndToSum_toSnd, toSnd_sndClosureEquiv_symm]
@[simp] theorem sndClosureEquiv_symm_coe_snd (x : C.inter) (hx : (x : X₀ × X₁).2 ∈ C.sndClosure) :
    (sndClosureEquiv C).symm ⟨(x : X₀ × X₁).2, hx⟩ = ofInter 1 x :=
  (sndClosureEquiv C).injective (Subtype.ext (by simp))

/-- **Endpoint identification at `0` for regular Banach couples (Bergh–Löfström,
Theorem 4.2.2 (b)).** When `(X₀, X₁)` is regular, evaluation at `0` gives `[X₀, X₁]_0 ≃ₗᵢ[ℂ] X₀`. -/
def fstEquiv (hC : C.IsRegular) : C.ComplexMethodSpace 0 ≃ₗᵢ[ℂ] X₀ :=
  (fstClosureEquiv C).trans
    (.ofTop X₀ C.fstClosure (C.isRegular_iff_fstClosure_eq_top_and_sndClosure_eq_top.1 hC).1)

@[simp] theorem fstEquiv_apply (hC : C.IsRegular) (u : C.ComplexMethodSpace 0) :
    fstEquiv hC u = toFst u := by simp [fstEquiv]
@[simp] theorem toFst_fstEquiv_symm (hC : C.IsRegular) (x₀ : X₀) :
    toFst ((fstEquiv hC).symm x₀) = x₀ :=
  (fstEquiv_apply hC _).symm.trans ((fstEquiv hC).apply_symm_apply x₀)
@[simp] theorem toSum_fstEquiv_symm (hC : C.IsRegular) (x₀ : X₀) :
    toSum ((fstEquiv hC).symm x₀) = C.fstToSum x₀ := by rw [← fstToSum_toFst, toFst_fstEquiv_symm]
@[simp] theorem fstEquiv_symm_coe_fst (hC : C.IsRegular) (x : C.inter) :
    (fstEquiv hC).symm (x : X₀ × X₁).1 = ofInter 0 x := (fstEquiv hC).injective (by simp)

/-- **Endpoint identification at `1` for regular Banach couples (Bergh–Löfström,
Theorem 4.2.2 (b)).** When `(X₀, X₁)` is regular, evaluation at `1` gives `[X₀, X₁]_1 ≃ₗᵢ[ℂ] X₁`. -/
def sndEquiv (hC : C.IsRegular) : C.ComplexMethodSpace 1 ≃ₗᵢ[ℂ] X₁ :=
  (sndClosureEquiv C).trans
    (.ofTop X₁ C.sndClosure (C.isRegular_iff_fstClosure_eq_top_and_sndClosure_eq_top.1 hC).2)

@[simp] theorem sndEquiv_apply (hC : C.IsRegular) (u : C.ComplexMethodSpace 1) :
    sndEquiv hC u = toSnd u := by simp [sndEquiv]
@[simp] theorem toSnd_sndEquiv_symm (hC : C.IsRegular) (x₁ : X₁) :
    toSnd ((sndEquiv hC).symm x₁) = x₁ :=
  (sndEquiv_apply hC _).symm.trans ((sndEquiv hC).apply_symm_apply x₁)
@[simp] theorem toSum_sndEquiv_symm (hC : C.IsRegular) (x₁ : X₁) :
    toSum ((sndEquiv hC).symm x₁) = C.sndToSum x₁ := by rw [← sndToSum_toSnd, toSnd_sndEquiv_symm]
@[simp] theorem sndEquiv_symm_coe_snd (hC : C.IsRegular) (x : C.inter) :
    (sndEquiv hC).symm (x : X₀ × X₁).2 = ofInter 1 x := (sndEquiv hC).injective (by simp)

end Complete

end ComplexMethodSpace

/-! ### Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)) -/

/-- Inclusion of `(X₀°, X₁°)` into `(X₀, X₁)` embeds `C.regularize.stripTraces` isometrically
into `C.stripTraces`. -/
def regularizeStripTracesIsometry : C.regularize.stripTraces →ₗᵢ[ℂ] C.stripTraces where
  toLinearMap := (stripTracesMap (D := C) C.fstClosure.subtypeL C.sndClosure.subtypeL
    C.regularizeSum_compat).toLinearMap
  norm_map' g := by
    rw [ContinuousLinearMap.coe_coe, ← Submodule.norm_coe, ← Submodule.norm_coe,
      Prod.norm_def, Prod.norm_def]
    congr 1 <;> rw [ZeroAtInftyContinuousMap.norm_eq_iSup_norm,
      ZeroAtInftyContinuousMap.norm_eq_iSup_norm] <;> simp

private theorem regularizeStripTracesIsometry_apply (g : C.regularize.stripTraces) :
    C.regularizeStripTracesIsometry g = stripTracesMap (D := C) C.fstClosure.subtypeL
      C.sndClosure.subtypeL C.regularizeSum_compat g := (rfl)

@[simp] theorem regularizeStripTracesIsometry_apply_fst (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).1 t : X₀) := by
  rw [regularizeStripTracesIsometry_apply, stripTracesMap_apply_fst, Submodule.subtypeL_apply]
@[simp] theorem regularizeStripTracesIsometry_apply_snd (g : C.regularize.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesIsometry g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t =
      ((g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).2 t : X₁) := by
  rw [regularizeStripTracesIsometry_apply, stripTracesMap_apply_snd, Submodule.subtypeL_apply]

theorem stripEval_regularizeStripTracesIsometry (z : ℂ) (g : C.regularize.stripTraces) :
    C.stripEval z (C.regularizeStripTracesIsometry g) =
      C.regularizeSumMap (C.regularize.stripEval z g) := by
  rw [regularizeStripTracesIsometry_apply, stripEval_stripTracesMap,
    ← C.regularizeSumMap_eq_sumLift]

private theorem surjective_regularizeStripTracesIsometry [CompleteSpace X₀] [CompleteSpace X₁] :
    Function.Surjective C.regularizeStripTracesIsometry := by
  have : CompleteSpace C.fstClosure :=
    (inferInstance : IsClosed (C.fstClosure : Set X₀)).completeSpace_coe
  have : CompleteSpace C.sndClosure :=
    (inferInstance : IsClosed (C.sndClosure : Set X₁)).completeSpace_coe
  have hcl := C.regularizeStripTracesIsometry.isometry.isUniformInducing.isComplete_range.isClosed
  have hsub : (C.elementaryStripTraces : Set C.stripTraces) ⊆
      Set.range C.regularizeStripTracesIsometry := by
    rw [← LinearIsometry.coe_toLinearMap, ← LinearMap.coe_range, SetLike.coe_subset_coe]
    refine C.elementaryStripTraces_le fun hδ ω x =>
      ⟨C.regularize.expGaussianTrace hδ ω (C.regularizeInterEquiv.symm x), Subtype.ext <| Prod.ext
        (ZeroAtInftyContinuousMap.ext fun _ => by simp)
        (ZeroAtInftyContinuousMap.ext fun _ => by simp)⟩
  exact Set.range_eq_univ.1 <| hcl.closure_eq ▸ (C.dense_elementaryStripTraces.mono hsub).closure_eq

/-- **Regularization invariance of admissible traces.** When `X₀` and `X₁` are Banach spaces,
every admissible function for `(X₀, X₁)` arises from a unique admissible function for `(X₀°, X₁°)`
of equal trace norm. -/
def regularizeStripTracesEquiv [CompleteSpace X₀] [CompleteSpace X₁] :
    C.regularize.stripTraces ≃ₗᵢ[ℂ] C.stripTraces :=
  LinearIsometryEquiv.ofSurjective C.regularizeStripTracesIsometry
    (surjective_regularizeStripTracesIsometry C)

@[simp] theorem regularizeStripTracesEquiv_apply [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.regularize.stripTraces) :
    C.regularizeStripTracesEquiv g = C.regularizeStripTracesIsometry g := by
  simp [regularizeStripTracesEquiv]
@[simp] theorem regularizeStripTracesEquiv_symm_apply_fst [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesEquiv.symm g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).1 t =
      ⟨(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).1 t, C.stripTraces_fst_apply_mem_fstClosure g t⟩ :=
  Subtype.ext <| by
    rw [← regularizeStripTracesIsometry_apply_fst, ← regularizeStripTracesEquiv_apply,
      C.regularizeStripTracesEquiv.apply_symm_apply]
@[simp] theorem regularizeStripTracesEquiv_symm_apply_snd [CompleteSpace X₀] [CompleteSpace X₁]
    (g : C.stripTraces) (t : ℝ) :
    (C.regularizeStripTracesEquiv.symm g : C₀(ℝ, C.fstClosure) × C₀(ℝ, C.sndClosure)).2 t =
      ⟨(g : C₀(ℝ, X₀) × C₀(ℝ, X₁)).2 t, C.stripTraces_snd_apply_mem_sndClosure g t⟩ :=
  Subtype.ext <| by
    rw [← regularizeStripTracesIsometry_apply_snd, ← regularizeStripTracesEquiv_apply,
      C.regularizeStripTracesEquiv.apply_symm_apply]
@[simp] theorem regularizeSumMap_stripFunction_regularizeStripTracesEquiv_symm
    [CompleteSpace X₀] [CompleteSpace X₁] (g : C.stripTraces) (z : ℂ) :
    C.regularizeSumMap (C.regularize.stripFunction (C.regularizeStripTracesEquiv.symm g) z) =
      C.stripFunction g z := by
  simp only [← stripEval_apply, ← stripEval_regularizeStripTracesIsometry,
    ← regularizeStripTracesEquiv_apply, C.regularizeStripTracesEquiv.apply_symm_apply]

namespace ComplexMethodSpace

variable {C} [CompleteSpace X₀] [CompleteSpace X₁]

private def regularizeInvMap (θ : ℝ) :
    C.ComplexMethodSpace θ →L[ℂ] C.regularize.ComplexMethodSpace θ :=
  lift ((mk θ).comp (C.regularizeStripTracesEquiv.symm.toContinuousLinearEquiv
      : C.stripTraces →L[ℂ] C.regularize.stripTraces)) fun g hg => by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← map_zero (mk (C := C.regularize) θ), mk_eq_mk_iff, map_zero]
    exact C.regularizeSumMap_injective <| by simpa using hg
@[simp] private theorem regularizeInvMap_mk (θ : ℝ) (g : C.stripTraces) :
    regularizeInvMap θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) := lift_mk _ _ g
private theorem regularizeInvMap_norm_le (θ : ℝ) (u : C.ComplexMethodSpace θ) :
    ‖regularizeInvMap θ u‖ ≤ ‖u‖ :=
  le_of_forall_gt fun _ hr => by
    obtain ⟨g, rfl, hg⟩ := norm_lt_iff.1 hr; rw [regularizeInvMap_mk]
    exact (norm_mk_le _).trans_lt ((C.regularizeStripTracesEquiv.symm.norm_map g).trans_lt hg)

/-- **Regularization invariance (Bergh–Löfström, Theorem 4.2.2 (c)).** For any Banach couple
`(X₀, X₁)` and `θ : ℝ`, passing to `(X₀°, X₁°)` preserves the complex interpolation space
isometrically: `[X₀°, X₁°]_θ ≃ₗᵢ[ℂ] [X₀, X₁]_θ`. -/
def regularizeEquiv (C : CompatibleCouple ℂ X₀ X₁ V) (θ : ℝ) :
    C.regularize.ComplexMethodSpace θ ≃ₗᵢ[ℂ] C.ComplexMethodSpace θ where
  toFun := map θ C.fstClosure.subtypeL C.sndClosure.subtypeL C.regularizeSum_compat
  invFun := regularizeInvMap θ
  left_inv u := by
    obtain ⟨g, rfl⟩ := mk_surjective u
    rw [map_mk, ← C.regularizeStripTracesIsometry_apply, ← C.regularizeStripTracesEquiv_apply,
      regularizeInvMap_mk, C.regularizeStripTracesEquiv.symm_apply_apply]
  right_inv u := by
    obtain ⟨g, rfl⟩ := mk_surjective u
    rw [regularizeInvMap_mk, map_mk, ← C.regularizeStripTracesIsometry_apply,
      ← C.regularizeStripTracesEquiv_apply, C.regularizeStripTracesEquiv.apply_symm_apply]
  map_add' := map_add _
  map_smul' := map_smul _
  norm_map' u := by
    rw [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    refine le_antisymm (norm_map_le_of_norm_le _ _ C.regularizeSum_compat
      (fun x => (Submodule.norm_coe x).le) (fun x => (Submodule.norm_coe x).le) u) ?_
    obtain ⟨g, rfl⟩ := mk_surjective u
    rw [map_mk, ← C.regularizeStripTracesIsometry_apply]
    have h := regularizeInvMap_norm_le θ (mk θ (C.regularizeStripTracesEquiv g))
    rwa [regularizeInvMap_mk, C.regularizeStripTracesEquiv.symm_apply_apply,
      C.regularizeStripTracesEquiv_apply] at h

private theorem regularizeEquiv_apply (θ : ℝ) (u : C.regularize.ComplexMethodSpace θ) :
    regularizeEquiv C θ u =
      map θ C.fstClosure.subtypeL C.sndClosure.subtypeL C.regularizeSum_compat u := (rfl)
private theorem regularizeEquiv_symm_apply (θ : ℝ) (u : C.ComplexMethodSpace θ) :
    (regularizeEquiv C θ).symm u = regularizeInvMap θ u := (rfl)

@[simp] theorem regularizeEquiv_mk (θ : ℝ) (g : C.regularize.stripTraces) :
    regularizeEquiv C θ (mk θ g) = mk θ (C.regularizeStripTracesEquiv g) := by
  rw [regularizeEquiv_apply, map_mk, ← regularizeStripTracesIsometry_apply,
    ← regularizeStripTracesEquiv_apply]
@[simp] theorem regularizeEquiv_symm_mk (θ : ℝ) (g : C.stripTraces) :
    (regularizeEquiv C θ).symm (mk θ g) = mk θ (C.regularizeStripTracesEquiv.symm g) := by
  rw [regularizeEquiv_symm_apply, regularizeInvMap_mk]

/-- `regularizeEquiv` lies over `C.regularizeSumMap : X₀° + X₁° → X₀ + X₁`. -/
@[simp] theorem toSum_regularizeEquiv (θ : ℝ) (u : C.regularize.ComplexMethodSpace θ) :
    toSum (regularizeEquiv C θ u) = C.regularizeSumMap (toSum u) := by
  rw [regularizeEquiv_apply, toSum_map, ← C.regularizeSumMap_eq_sumLift]
@[simp] theorem regularizeSumMap_toSum_regularizeEquiv_symm (θ : ℝ) (u : C.ComplexMethodSpace θ) :
    C.regularizeSumMap (toSum ((regularizeEquiv C θ).symm u)) = toSum u := by
  rw [← toSum_regularizeEquiv, (regularizeEquiv C θ).apply_symm_apply]

/-- `regularizeEquiv` intertwines the inclusions of the intersections `X₀° ∩ X₁°` and `X₀ ∩ X₁`. -/
@[simp] theorem regularizeEquiv_ofInter (θ : ℝ) (y : C.regularize.inter) :
    regularizeEquiv C θ (ofInter θ y) = ofInter θ (C.regularizeInterEquiv y) := by
  by_cases hθ : θ ∈ Icc 0 1
  · rw [regularizeEquiv_apply]
    exact map_ofInter _ _ C.regularizeSum_compat hθ
      ((C.interFst_regularizeInterEquiv y).trans (Submodule.subtypeL_apply _ _).symm)
  · simp [eq_zero_of_notMem hθ]
@[simp] theorem regularizeEquiv_symm_ofInter (θ : ℝ) (x : C.inter) :
    (regularizeEquiv C θ).symm (ofInter θ x) = ofInter θ (C.regularizeInterEquiv.symm x) :=
  (regularizeEquiv C θ).injective (by simp)

end ComplexMethodSpace

end TauCeti.CompatibleCouple
