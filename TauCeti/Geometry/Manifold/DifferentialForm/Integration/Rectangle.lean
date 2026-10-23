/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Rectangle
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Prod

/-!
# Integration on the rectangle manifold with corners

The product of the increasing interval orientations gives the standard coordinate area
orientation. Integration uses the genuine manifold top-form integral; the omitted upper and
right faces of its bottom-left preferred chart are null, as part of the model boundary.
-/

public section

noncomputable section

open MeasureTheory Set Fact.Manifold
open scoped Manifold

namespace TauCeti

variable {a b c d : ℝ} [hab : Fact (a < b)] [hcd : Fact (c < d)]

private theorem integralTopForm_rectangle_chart
    (φ : RoughForm ((𝓡∂ 1).prod (𝓡∂ 1)) (Icc a b × Icc c d) ℝ 2)
    (hi : IntegrableTopForm φ) :
    integralTopForm
        ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d)) φ =
      ∫ z in (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target,
        φ.inChartAt ⊥ z (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
          (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv) := by
  let B := (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv)
  let l := (Manifold.OrientationLift.interval a b).prod
    (Manifold.OrientationLift.interval c d)
  have hmodel : l.modelOrientation = B.orientation := by
    rw [Manifold.OrientationLift.prod_modelOrientation,
      Manifold.OrientationLift.interval_modelOrientation,
      Manifold.OrientationLift.interval_modelOrientation]
    exact _root_.Orientation.prod_basis_orientation _ _ _ _
  have hsign (x : (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).source) :
      l.signAt ⊥ x = 1 := by
    have hx : x.val ∈ (chartAt (EuclideanHalfSpace 1) (⊥ : Icc a b)).source ×ˢ
        (chartAt (EuclideanHalfSpace 1) (⊥ : Icc c d)).source := by
      have hbot : (⊥ : Icc a b × Icc c d) = (⊥, ⊥) := rfl
      simpa only [extChartAt_source, prodChartedSpace_chartAt,
        OpenPartialHomeomorph.prod_source,
        hbot] using x.property
    rw [Manifold.OrientationLift.signAt_of_mem l
      (by simpa only [extChartAt_source] using x.property)]
    have h := Manifold.OrientationLift.prod_sign (Manifold.OrientationLift.interval a b)
      (Manifold.OrientationLift.interval c d) ⊥ ⟨x.val.1, hx.1⟩ ⟨x.val.2, hx.2⟩
    apply h.trans
    simp only [Manifold.OrientationLift.interval_sign]
    -- Expand the two interval orientation signs on their fixed real model lines.
    change (if a < b then (1 : ℤˣ) else -1) * (if c < d then 1 else -1) = 1
    simp only [hab.out, hcd.out, ↓reduceIte, mul_one]
  rw [Manifold.Orientation.interval_eq_mk, Manifold.Orientation.interval_eq_mk,
    Manifold.Orientation.prod_mk,
    integralTopForm_eq_chartIntegral_of_interior_subset l φ hi ⊥
      interior_rectangle_subset_extChartAt_bot_source,
    l.chartIntegral_eq_integral φ B ⊥, hmodel, Orientation.signBasis_orientation]
  simp only [Units.val_one, Int.cast_one, one_mul]
  have hhaar : B.addHaar = volume := by
    rw [Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar,
      (EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume]
    rfl
  rw [hhaar]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)]
  · exact integral_indicator (measurableSet_extChartAt_target _)
  · rw [RoughForm.signedInChartAt_apply]
    split_ifs with hz
    · rw [hsign ⟨_, (extChartAt _ _).map_target hz⟩]
      simp only [Units.val_one, Int.cast_one, one_mul, indicator_of_mem hz]
      rfl
    · simp only [indicator_of_notMem hz]

/-- In the increasing rectangle chart, the actual pullback of an ambient two-form has its
ordinary coordinate area coefficient. -/
theorem inChartAt_mpullback_rectangle_bot
    (ω : RoughForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ℝ 2)
    {z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)}
    (hz : z ∈ (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target) :
    (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
      (fun x : Icc a b × Icc c d ↦ (x.1.val, x.2.val)) ω).inChartAt ⊥ z
        (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
          (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv) =
      ω (z.1 0 + a, z.2 0 + c) (fun i ↦
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (z.1 0 + a, z.2 0 + c)).symm
          (![(1, 0), (0, 1)] i)) := by
  have hf := ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).comp
    contMDiff_fst).prodMk_space ((contMDiff_subtypeVal_Icc (x := c) (y := d) (n := 1)).comp
      contMDiff_snd)
  dsimp only [Function.comp_def] at hf
  rw [ω.inChartAt_mpullback_modelSpace _ ⊥ hz (hf.mdifferentiable one_ne_zero _)]
  have hd := (hasFDerivWithinAt_subtypeVal_extChartAt_rectangle_symm ⊥ hz).fderivWithin
    (((𝓡∂ 1).prod (𝓡∂ 1)).uniqueDiffOn _ (extChartAt_target_subset_range _ hz))
  have he := subtypeVal_extChartAt_rectangle_symm ⊥ hz
  have hfirst : ((⊥ : Icc a b × Icc c d).1 : ℝ) = a := rfl
  have hsecond : ((⊥ : Icc a b × Icc c d).2 : ℝ) = c := rfl
  simp only [hfirst, hsecond,
    hab.out, hcd.out, ↓reduceIte, one_smul] at hd he
  simp only [Function.comp_def]
  rw [hd]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [he]
  congr 1
  funext i
  have h0 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 :=
    finSumFinEquiv_symm_apply_castAdd (n := 1) (0 : Fin 1)
  have h1 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = Sum.inr 0 :=
    finSumFinEquiv_symm_apply_natAdd (m := 1) (0 : Fin 1)
  fin_cases i <;> simp [Module.Basis.prod_apply, h0, h1, EuclideanSpace.basisFun_apply]

private theorem rectangle_coordinate_integral (f : ℝ × ℝ → ℝ) :
    (IntegrableOn (fun z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ↦
      f (z.1 0 + a, z.2 0 + c))
        (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target ↔
      IntegrableOn f (Ico a b ×ˢ Ico c d)) ∧
    (∫ z in (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target,
      f (z.1 0 + a, z.2 0 + c)) = ∫ x in Ico a b ×ˢ Ico c d, f x := by
  let T : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) → ℝ × ℝ :=
    fun z ↦ (z.1 0 + a, z.2 0 + c)
  have hm : MeasurePreserving T volume volume := by
    exact ((measurePreserving_add_right (volume : Measure ℝ) a).prod
      (measurePreserving_add_right (volume : Measure ℝ) c)).comp
      ((TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).prod
        (TauCeti.volume_preserving_euclideanSpace_proj (ι := Fin 1) 0))
  have he : MeasurableEmbedding T :=
    (MeasurableEquiv.addRight (a, c)).measurableEmbedding.comp
      ((TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0).prodMap
        (TauCeti.measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0))
  have ht : (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target =
      T ⁻¹' (Ico a b ×ˢ Ico c d) := by
    rw [extChartAt_prod, PartialEquiv.prod_target, extChartAt_Icc_target,
      extChartAt_Icc_target]
    ext z
    simp only [mem_prod, mem_preimage, mem_Ico, T]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;> constructor <;> constructor <;> linarith
  rw [ht]
  exact ⟨(hm.restrict_preimage_emb he _).integrable_comp_emb he,
    hm.setIntegral_preimage_emb he f _⟩

/-- The canonical integral of an actual ambient two-form pulled back to the rectangle
manifold is ordinary coordinate area. Intrinsic integrability implies area integrability. -/
theorem integralTopForm_mpullback_rectangle
    (ω : RoughForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ℝ 2)
    (hi : IntegrableTopForm (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
      (fun x : Icc a b × Icc c d ↦ (x.1.val, x.2.val)) ω)) :
    let f := fun x : ℝ × ℝ ↦ ω x (fun i ↦
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (![(1, 0), (0, 1)] i))
    IntegrableOn f (Icc a b ×ˢ Icc c d) ∧
      integralTopForm
          ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d))
          (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
            (fun x : Icc a b × Icc c d ↦ (x.1.val, x.2.val)) ω) =
        ∫ x in Icc a b ×ˢ Icc c d, f x := by
  intro f
  let φ := mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
    (fun x : Icc a b × Icc c d ↦ (x.1.val, x.2.val)) ω
  let B := (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv)
  have hm := measurableSet_extChartAt_target (I := (𝓡∂ 1).prod (𝓡∂ 1))
    (⊥ : Icc a b × Icc c d)
  have hcoef := ((integrableTopForm_iff φ).mp hi).2.2 B ⊥
  have hcoord : IntegrableOn (fun z ↦ φ.inChartAt ⊥ z B)
      (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target B.addHaar :=
    hcoef.integrableOn.congr_fun (fun z hz ↦ by
      simp only [RoughForm.signedInChartAt_apply, dite_eq_left hz, Units.val_one,
        Int.cast_one, one_mul]) hm
  have hhaar : B.addHaar = volume := by
    rw [Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar,
      (EuclideanSpace.basisFun (Fin 1) ℝ).addHaar_eq_volume]
    rfl
  rw [hhaar] at hcoord
  have heq : EqOn (fun z ↦ φ.inChartAt ⊥ z B)
      (fun z ↦ f (z.1 0 + a, z.2 0 + c))
      (extChartAt ((𝓡∂ 1).prod (𝓡∂ 1)) (⊥ : Icc a b × Icc c d)).target :=
    fun _ hz ↦ inChartAt_mpullback_rectangle_bot ω hz
  have htrans := rectangle_coordinate_integral (a := a) (b := b) (c := c) (d := d) f
  have hsets : (Ico a b ×ˢ Ico c d : Set (ℝ × ℝ)) =ᵐ[volume] Icc a b ×ˢ Icc c d :=
    Measure.set_prod_ae_eq Ico_ae_eq_Icc Ico_ae_eq_Icc
  refine ⟨(integrableOn_congr_set_ae hsets).mp
    (htrans.1.mp (hcoord.congr_fun heq hm)), ?_⟩
  rw [integralTopForm_rectangle_chart _ hi]
  exact (setIntegral_congr_fun hm heq).trans
    (htrans.2.trans (setIntegral_congr_set hsets))

end TauCeti
