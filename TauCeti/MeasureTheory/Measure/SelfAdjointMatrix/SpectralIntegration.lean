/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.ChangeOfVariables
import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.SimpleSpectrum
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Spectral integration on self-adjoint matrices

The local Vandermonde Jacobian gives a global integration formula over the decreasing eigenvalue
chamber, with normalized Haar conjugation in the angular variable. A single transverse chart
meets a fixed positive Haar fraction of each simple orbit: its saturation in the unitary group
depends only on the diagonal stabilizer. Averaging over conjugation then removes the restriction
to that chart.

The spectral Jacobian and Haar disintegration are those of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory MeasureTheory.Measure Set UnitaryGroup
open scoped ENNReal Matrix Topology TauCeti.SelfAdjointMatrix

namespace TauCeti

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "Herm" => selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)
local notation "Frames" => unitaryGroup (Fin n) 𝕜
local notation "Angles" => FinStrictUpper n → 𝕜
private abbrev chamber (n : ℕ) : Set (Fin n → ℝ) := {d | StrictAnti d}

private abbrev ordered (A : Herm) : Fin n → ℝ :=
  (selfAdjoint.isHermitian_coe A).eigenvalues₀ ∘ Fin.cast (Fintype.card_fin n).symm

private theorem continuous_ordered : Continuous (ordered : Herm → Fin n → ℝ) :=
  continuous_pi fun i ↦
    (continuous_apply (Fin.cast (Fintype.card_fin n).symm i)).comp (continuous_eigenvalues₀.comp
      (Continuous.subtype_mk continuous_subtypeVal _))

private theorem ordered_spectralMatrix (U : Frames) (d : Fin n → ℝ) (a : Angles)
    (hd : Antitone d) : ordered (spectralMatrix U (d, a)) = d := by
  funext i
  simp [ordered, eigenvalues₀_spectralMatrix U (d, a) hd]

private theorem exists_selfAdjointConj_diagonal (A : Herm) :
    ∃ U : Frames, A = selfAdjointConj U (selfAdjointDiagonal (ordered A)) := by
  let hA := selfAdjoint.isHermitian_coe A
  have hd : Antitone (ordered A) := hA.eigenvalues₀_antitone.comp_monotone
    (Fin.castOrderIso (Fintype.card_fin n).symm).monotone
  let B := spectralMatrix (1 : Frames) (ordered A, (0 : Angles))
  have he : (selfAdjoint.isHermitian_coe B).eigenvalues₀ = hA.eigenvalues₀ := by
    funext i
    exact congrFun (ordered_spectralMatrix 1 (ordered A) 0 hd) (Fin.cast (Fintype.card_fin n) i)
  obtain ⟨U, hU, h⟩ := (selfAdjoint.isHermitian_coe B).exists_unitary_conj_of_eigenvalues₀_eq hA he
  refine ⟨⟨U, hU⟩, Subtype.ext ?_⟩
  rw [coe_selfAdjointConj_apply, ← star_eq_conjTranspose]
  simpa only [B, spectralMatrix_zero, selfAdjointConj_one, LinearIsometryEquiv.coe_refl, id_eq]
    using h

private theorem selfAdjointConj_diagonal_eq_iff {d : Fin n → ℝ}
    (hd : Function.Injective d) (U V : Frames) :
    selfAdjointConj U (selfAdjointDiagonal d) = selfAdjointConj V (selfAdjointDiagonal d) ↔
      Matrix.IsDiag ((star V * U : Frames) : Matrix (Fin n) (Fin n) 𝕜) := by
  rw [← Subtype.coe_inj]
  simpa only [coe_selfAdjointConj_apply, coe_selfAdjointDiagonal, Unitary.conjStarAlgAut_apply,
    star_eq_conjTranspose, Function.comp_def] using
    (conjStarAlgAut_diagonal_eq_conjStarAlgAut_iff (RCLike.ofReal_injective.comp hd) U V)

private theorem isOpen_chamber : IsOpen (chamber n) := by
  have h : (chamber n) =
      ⋂ ij : FinStrictUpper n, {d | d ij.val.2 < d ij.val.1} := by
    ext d
    simp only [Set.mem_ofPred_eq, mem_iInter]
    exact ⟨fun hd ij ↦ hd ij.property, fun hd i j hij ↦ hd ⟨(i, j), hij⟩⟩
  rw [h]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_lt (continuous_apply _) (continuous_apply _)

private theorem injOn_spectralMatrix_one {d₀ : Fin n → ℝ} (hd₀ : StrictAnti d₀)
    {B : Set Angles} (hB : InjOn (spectralMatrix (1 : Frames)) ({d₀} ×ˢ B)) :
    InjOn (spectralMatrix (1 : Frames)) (chamber n ×ˢ B) := by
  rintro ⟨d, a⟩ ⟨hd, ha⟩ ⟨e, b⟩ ⟨he, hb⟩ h
  have hde : d = e := by
    have hh := congrArg ordered h
    rwa [ordered_spectralMatrix 1 d a (StrictAnti.antitone hd),
      ordered_spectralMatrix 1 e b (StrictAnti.antitone he)] at hh
  subst e
  simp only [spectralMatrix_eq_selfAdjointConj, one_mul,
    selfAdjointConj_diagonal_eq_iff (StrictAnti.injective hd)] at h
  have h' : spectralMatrix (1 : Frames) (d₀, a) = spectralMatrix 1 (d₀, b) := by
    simpa only [spectralMatrix_eq_selfAdjointConj, one_mul,
      selfAdjointConj_diagonal_eq_iff hd₀.injective] using h
  have ha₀ : (d₀, a) ∈ {d₀} ×ˢ B := ⟨mem_singleton _, ha⟩
  have hb₀ : (d₀, b) ∈ {d₀} ×ˢ B := ⟨mem_singleton _, hb⟩
  have hab : a = b := congrArg Prod.snd (hB ha₀ hb₀ h')
  exact Prod.ext rfl hab

private theorem conj_diagonal_mem_spectralPatch_iff {d d₀ : Fin n → ℝ}
    (hd : StrictAnti d) (hd₀ : StrictAnti d₀) {B : Set Angles} (U : Frames) :
    selfAdjointConj U (selfAdjointDiagonal d) ∈ spectralMatrix 1 '' (chamber n ×ˢ B) ↔
      selfAdjointConj U (selfAdjointDiagonal d₀) ∈ spectralMatrix 1 '' (chamber n ×ˢ B) := by
  suffices ∀ e : Fin n → ℝ, StrictAnti e →
      (selfAdjointConj U (selfAdjointDiagonal e) ∈ spectralMatrix 1 '' (chamber n ×ˢ B) ↔
        ∃ a ∈ B, Matrix.IsDiag ((star (expStrictUpper a) * U : Frames) :
          Matrix (Fin n) (Fin n) 𝕜)) by
    exact (this d hd).trans (this d₀ hd₀).symm
  intro e he
  constructor
  · rintro ⟨⟨b, a⟩, ⟨hb, ha⟩, h⟩
    have hbe : b = e := by
      have hh := congrArg ordered (h.trans (spectralMatrix_zero U e).symm)
      rwa [ordered_spectralMatrix 1 b a (StrictAnti.antitone hb),
        ordered_spectralMatrix U e 0 he.antitone] at hh
    subst b
    have h' := h.symm
    simp only [spectralMatrix_eq_selfAdjointConj, one_mul,
      selfAdjointConj_diagonal_eq_iff he.injective] at h'
    exact ⟨a, ha, h'⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨(e, a), ⟨he, ha⟩, ?_⟩
    symm
    simpa only [spectralMatrix_eq_selfAdjointConj, one_mul,
      selfAdjointConj_diagonal_eq_iff he.injective] using h

private abbrev gap (𝕜 : Type*) [RCLike 𝕜] (d : Fin n → ℝ) : ℝ :=
  ∏ ij : FinStrictUpper n, |d ij.val.2 - d ij.val.1| ^ Module.finrank ℝ 𝕜

private theorem continuous_gap : Continuous (gap (n := n) 𝕜) :=
  continuous_finsetProd _ fun _ _ ↦ by fun_prop

private theorem strictAnti_neg_fin_val : StrictAnti (fun i : Fin n ↦ -((i : ℕ) : ℝ)) :=
  fun _ _ hij ↦ neg_lt_neg (Nat.cast_lt.mpr hij)

section Measure

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

private theorem ordered_mem_chamber_ae : ∀ᵐ A : Herm ∂volume, ordered A ∈ chamber n := by
  filter_upwards [Measure.ae_injective_eigenvalues_selfAdjoint (volume : Measure Herm)
    Measure.AbsolutelyContinuous.rfl] with A hA
  have hinj : Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues₀ := by
    intro i j hij
    apply (Fintype.equivOfCardEq (β := Fin n) (Fintype.card_fin _)).injective
    exact hA (by simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hij)
  exact ((selfAdjoint.isHermitian_coe A).eigenvalues₀_antitone.comp_monotone
    (Fin.castOrderIso (Fintype.card_fin n).symm).monotone).strictAnti_of_injective
      (hinj.comp (Fin.cast_injective (Fintype.card_fin n).symm))

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem exists_angularBall (d₀ : Fin n → ℝ) (hd₀ : StrictAnti d₀) :
    ∃ r > 0, InjOn (spectralMatrix (1 : Frames)) ({d₀} ×ˢ Metric.ball (0 : Angles) r) ∧
      (selfAdjointDiagonal (𝕜 := 𝕜) d₀) ∈
        interior (spectralMatrix 1 '' (chamber n ×ˢ Metric.ball (0 : Angles) r)) := by
  obtain ⟨e, he, hx⟩ := exists_spectralCoordinates_openPartialHomeomorph
    (𝕜 := 𝕜) d₀ hd₀.injective 1
  let E := e.transHomeomorph (selfAdjointCoordinates (𝕜 := 𝕜)).symm.toHomeomorph
  have hE : (E : _ → _) = spectralMatrix (1 : Frames) := by
    rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph, he]
    funext x
    apply selfAdjointCoordinates.injective
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      selfAdjointCoordinates_spectralMatrix]
  have hsource : (d₀, (0 : Angles)) ∈ E.source := hx
  have hnhds : E.source ∩ (chamber n ×ˢ (univ : Set Angles)) ∈ 𝓝 (d₀, 0) := by
    exact inter_mem (E.open_source.mem_nhds hsource)
      ((isOpen_chamber.prod isOpen_univ).mem_nhds ⟨hd₀, mem_univ _⟩)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hnhds
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨u, hus, huo, hdu⟩ := mem_nhds_iff.mp hs
  have hsub : u ×ˢ Metric.ball (0 : Angles) r ⊆ E.source :=
    subset_trans (prod_mono hus hrt) (hst.trans inter_subset_left)
  have huC : u ⊆ chamber n := by
    intro d hd
    have hmem : (d, (0 : Angles)) ∈ s ×ˢ t := ⟨hus hd, mem_of_mem_nhds ht⟩
    exact (hst hmem).2.1
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hE]
    exact E.injOn.mono ((prod_mono (singleton_subset_iff.2 hdu) subset_rfl).trans hsub)
  · have hcenter : spectralMatrix (1 : Frames) (d₀, 0) = selfAdjointDiagonal d₀ := by
      simp only [spectralMatrix_zero, selfAdjointConj_one, LinearIsometryEquiv.coe_refl, id_eq]
    rw [← hcenter, ← hE]
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset
      ((E.isOpen_image_of_subset_source (huo.prod Metric.isOpen_ball) hsub).mem_nhds
        (mem_image_of_mem _ ⟨hdu, Metric.mem_ball_self hr⟩)) ?_)
    exact image_mono (prod_mono huC subset_rfl)

private theorem lintegral_angularDet_pos_lt_top (ν : Measure Angles) [ν.IsAddHaarMeasure]
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ a in Metric.ball 0 r, ENNReal.ofReal |(spectralAngularFDeriv a).det| ∂ν) ∈
      Ioo 0 ⊤ := by
  let j : Angles → ℝ := fun a ↦ |(spectralAngularFDeriv a).det|
  have hj : Continuous j := continuous_abs_det_spectralAngularFDeriv
  have hj₀ : 0 < j 0 := by simp [j, spectralAngularFDeriv_zero, ContinuousLinearMap.det_id]
  have hball : 0 ∈ Metric.ball (0 : Angles) r := Metric.mem_ball_self hr
  let s := Metric.ball (0 : Angles) r ∩ {a | 0 < j a}
  have hs : IsOpen s := Metric.isOpen_ball.inter (isOpen_lt continuous_const hj)
  have hspos : 0 < ν s := hs.measure_pos ν ⟨0, hball, hj₀⟩
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Angles) r).bddAbove_image hj.continuousOn
  refine ⟨?_, ?_⟩
  · rw [lintegral_pos_iff_support hj.measurable.ennreal_ofReal,
      Measure.restrict_apply (measurableSet_support hj.measurable.ennreal_ofReal)]
    exact hspos.trans_le (measure_mono fun a ha ↦
      ⟨ENNReal.ofReal_pos.mpr ha.2 |>.ne', ha.1⟩)
  · calc
      _ ≤ ∫⁻ _ in Metric.ball (0 : Angles) r, ENNReal.ofReal M ∂ν :=
        lintegral_mono_ae ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono fun a ha ↦
          ENNReal.ofReal_le_ofReal (hM (mem_image_of_mem _ (Metric.ball_subset_closedBall ha))))
      _ < ⊤ := by
        rw [setLIntegral_const]
        have hclosed : ν (Metric.closedBall 0 r) < ⊤ :=
          (isCompact_closedBall (0 : Angles) r).measure_lt_top
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono Metric.ball_subset_closedBall).trans_lt hclosed)

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
private theorem ordered_conj (U : Frames) (A : Herm) :
    ordered (selfAdjointConj U A) = ordered A := by
  have h (M : Matrix (Fin n) (Fin n) 𝕜) (hM : M.IsHermitian)
      (he : M = (U : Matrix (Fin n) (Fin n) 𝕜) * A * star U.val) :
      hM.eigenvalues₀ = (selfAdjoint.isHermitian_coe A).eigenvalues₀ := by
    subst M
    exact (selfAdjoint.isHermitian_coe A).eigenvalues₀_mul_mul_star U.property hM
  exact congrArg (· ∘ Fin.cast (Fintype.card_fin n).symm)
    (h _ (selfAdjoint.isHermitian_coe (selfAdjointConj U A))
      (by rw [coe_selfAdjointConj_apply, star_eq_conjTranspose]))

private theorem haarProb_spectralPatch_preimage {d₀ : Fin n → ℝ} (hd₀ : StrictAnti d₀)
    {B : Set Angles} (hJ : MeasurableSet (spectralMatrix 1 '' (chamber n ×ˢ B)))
    (A : Herm) (hA : StrictAnti (ordered A)) :
    haarProb Frames ((fun U : Frames ↦ selfAdjointConj U A) ⁻¹'
      (spectralMatrix 1 '' (chamber n ×ˢ B))) =
    haarProb Frames ((fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) ⁻¹'
      (spectralMatrix 1 '' (chamber n ×ˢ B))) := by
  obtain ⟨V, hV⟩ := exists_selfAdjointConj_diagonal A
  let J : Set Herm := spectralMatrix 1 '' (chamber n ×ˢ B)
  let f : Frames → Herm := fun U ↦ selfAdjointConj U (selfAdjointDiagonal (ordered A))
  have hf : Continuous f := continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)
  have hpre : (fun U : Frames ↦ selfAdjointConj U A) ⁻¹' J = (· * V) ⁻¹' (f ⁻¹' J) := by
    ext U
    simp only [mem_preimage, f, selfAdjointConj_mul_apply]
    conv_lhs => rw [hV]
  rw [hpre, (measurePreserving_mul_right (haarProb Frames) V).measure_preimage
    (hJ.preimage hf.measurable).nullMeasurableSet]
  congr 1
  ext U
  exact conj_diagonal_mem_spectralPatch_iff hA hd₀ U

private theorem lintegral_eq_lintegral_haarProb_conj {f : Herm → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ A, f A ∂volume) =
      ∫⁻ A, ∫⁻ U : Frames, f (selfAdjointConj U A) ∂haarProb Frames ∂volume := by
  let F (A : Herm) (U : Frames) := f (selfAdjointConj U A)
  have hF : Measurable (Function.uncurry F) := hf.comp continuous_selfAdjointConj.measurable
  calc
    (∫⁻ A, f A ∂volume) = ∫⁻ U, ∫⁻ A, F A U ∂volume ∂haarProb Frames := by
      simp_rw [F, (measurePreserving_selfAdjointConj_volume _).lintegral_comp hf]
      simp
    _ = _ := (lintegral_lintegral_swap hF.aemeasurable).symm

private theorem setLIntegral_ordered_spectralPatch {d₀ : Fin n → ℝ} (hd₀ : StrictAnti d₀)
    {B : Set Angles} (hJ : MeasurableSet (spectralMatrix 1 '' (chamber n ×ˢ B)))
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ A : Herm in spectralMatrix 1 '' (chamber n ×ˢ B), g (ordered A) ∂volume) =
      haarProb Frames ((fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) ⁻¹'
        (spectralMatrix 1 '' (chamber n ×ˢ B))) * ∫⁻ A : Herm, g (ordered A) ∂volume := by
  let J : Set Herm := spectralMatrix 1 '' (chamber n ×ˢ B)
  let G : Herm → ℝ≥0∞ := J.indicator (g ∘ ordered)
  have hG : Measurable G := (hg.comp continuous_ordered.measurable).indicator hJ
  let H (A : Herm) (U : Frames) := G (selfAdjointConj U A)
  rw [← lintegral_indicator hJ]
  calc
    (∫⁻ A, G A ∂volume) = ∫⁻ A, ∫⁻ U, H A U ∂haarProb Frames ∂volume :=
      lintegral_eq_lintegral_haarProb_conj hG
    _ = _ := by
      have hm : Measurable (fun A : Herm ↦ g (ordered A)) :=
        hg.comp continuous_ordered.measurable
      rw [← lintegral_const_mul _ hm]
      refine lintegral_congr_ae (ordered_mem_chamber_ae.mono fun A hA ↦ ?_)
      have hconj : Measurable (fun U : Frames ↦ selfAdjointConj U A) :=
        (continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)).measurable
      -- On this orbit the test is constant, so only the Haar fraction contributes.
      have heq : (fun U : Frames ↦ J.indicator (fun M ↦ g (ordered M)) (selfAdjointConj U A)) =
          fun U ↦ J.indicator (fun _ ↦ g (ordered A)) (selfAdjointConj U A) := by
        funext U
        by_cases h : selfAdjointConj U A ∈ J <;> simp [h, ordered_conj]
      exact (congrArg (fun k ↦ ∫⁻ U : Frames, k U ∂haarProb Frames) heq).trans (by
        rw [lintegral_indicator_const_comp hconj hJ,
          haarProb_spectralPatch_preimage hd₀ hJ A hA, mul_comm])

private theorem setLIntegral_spectralPatch_eq_prod
    {B : Set Angles} (hB : MeasurableSet B)
    (hinj : InjOn (spectralMatrix (1 : Frames)) (chamber n ×ˢ B))
    (ν : Measure Angles) [SFinite ν] {c : ℝ≥0∞}
    (hc : (volume : Measure Herm).map selfAdjointCoordinates = c • volume.prod ν)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ A : Herm in spectralMatrix 1 '' (chamber n ×ˢ B), g (ordered A) ∂volume) =
      (c * ∫⁻ a in B, ENNReal.ofReal |(spectralAngularFDeriv a).det| ∂ν) *
        ∫⁻ d in chamber n, ENNReal.ofReal (gap 𝕜 d) * g d ∂volume := by
  let j (a : Angles) := ENNReal.ofReal |(spectralAngularFDeriv a).det|
  let w (d : Fin n → ℝ) := ENNReal.ofReal (gap 𝕜 d) * g d
  have hj : Measurable j :=
    (continuous_abs_det_spectralAngularFDeriv (𝕜 := 𝕜)).measurable.ennreal_ofReal
  have hw : Measurable w := (continuous_gap (𝕜 := 𝕜)).measurable.ennreal_ofReal.mul hg
  have hs := (isOpen_chamber (n := n)).measurableSet.prod hB
  rw [lintegral_image_spectralMatrix volume 1 hs.nullMeasurableSet hinj
    (fun A : Herm ↦ g (ordered A)), hc, setLIntegral_smul_measure]
  have heq : (∫⁻ x in chamber n ×ˢ B, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
      gap 𝕜 x.1) * g (ordered (spectralMatrix 1 x)) ∂volume.prod ν) =
        ∫⁻ x in chamber n ×ˢ B, w x.1 * j x.2 ∂volume.prod ν := by
    refine setLIntegral_congr_fun hs fun ⟨d, a⟩ ⟨hd, _⟩ ↦ ?_
    rw [ordered_spectralMatrix 1 d a (StrictAnti.antitone hd),
      ENNReal.ofReal_mul (abs_nonneg _)]
    dsimp only [w, j]
    ac_rfl
  have hW : Measurable (fun x : SelfAdjointCoordinates n 𝕜 ↦ w x.1 * j x.2) :=
    (hw.comp measurable_fst).mul (hj.comp measurable_snd)
  rw [heq, setLIntegral_prod _ hW.aemeasurable]
  simp_rw [lintegral_const_mul _ hj, lintegral_mul_const _ hw]
  rw [smul_eq_mul]
  dsimp only [j, w]
  ac_rfl

private theorem exists_lintegral_ordered_eq :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧
      ∀ g : (Fin n → ℝ) → ℝ≥0∞, Measurable g →
        (∫⁻ A : Herm, g (ordered A) ∂volume) =
          c * ∫⁻ d in chamber n, ENNReal.ofReal (gap 𝕜 d) * g d ∂volume := by
  let d₀ (i : Fin n) := -((i : ℕ) : ℝ)
  have hd₀ : StrictAnti d₀ := strictAnti_neg_fin_val
  obtain ⟨r, hr, hslice, hD⟩ := exists_angularBall (𝕜 := 𝕜) d₀ hd₀
  let B := Metric.ball (0 : Angles) r
  let J : Set Herm := spectralMatrix 1 '' (chamber n ×ˢ B)
  have hinj := injOn_spectralMatrix_one hd₀ hslice
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hJ : MeasurableSet J := (isOpen_chamber.measurableSet.prod hB)
    |>.image_of_continuousOn_injOn (continuous_spectralMatrix 1).continuousOn hinj
  let P : Set Frames := (fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) ⁻¹' J
  let q := haarProb Frames P
  have hcF : Continuous (fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) :=
    continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)
  have hq : 0 < q := Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2
    (hcF.continuousAt.preimage_mem_nhds (by
      simpa only [selfAdjointConj_one, LinearIsometryEquiv.coe_refl, id_eq] using
        mem_interior_iff_mem_nhds.1 hD))⟩
  have hqfin : q ≠ ⊤ := measure_ne_top _ _
  let ν : Measure Angles := Measure.addHaar
  let μ := (volume : Measure Herm).map selfAdjointCoordinates
  have : μ.IsAddHaarMeasure :=
    (selfAdjointCoordinates (n := n) (𝕜 := 𝕜)).isAddHaarMeasure_map volume
  let c₀ := addHaarScalarFactor μ (volume.prod ν)
  have hc₀ : μ = (c₀ : ℝ≥0∞) • volume.prod ν := isAddLeftInvariant_eq_smul _ _
  have hc₀pos : 0 < c₀ := addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  let k := ∫⁻ a in B, ENNReal.ofReal |(spectralAngularFDeriv a).det| ∂ν
  have hk : k ∈ Ioo 0 ⊤ := lintegral_angularDet_pos_lt_top ν hr
  refine ⟨q⁻¹ * (c₀ * k), ⟨ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hqfin)
    (ENNReal.mul_pos (ENNReal.coe_pos.mpr hc₀pos).ne' hk.1.ne').ne',
      ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hq)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hk.2)⟩, ?_⟩
  intro g hg
  have h := (setLIntegral_ordered_spectralPatch hd₀ hJ hg).symm.trans
    (setLIntegral_spectralPatch_eq_prod hB hinj ν hc₀ hg)
  apply (ENNReal.mul_right_inj hq.ne' hqfin).mp
  rw [mul_assoc q⁻¹, ENNReal.mul_inv_cancel_left hq.ne' hqfin, h]

/-- Global spectral integration on the real symmetric or complex Hermitian matrices.
Frobenius volume separates into the Vandermonde-weighted Lebesgue measure on the strictly
decreasing chamber and Haar probability on unitary frames acting by conjugation. The positive
finite scalar is common to all measurable nonnegative tests. -/
theorem exists_lintegral_selfAdjoint_spectral :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧ ∀ f : Herm → ℝ≥0∞, Measurable f →
      (∫⁻ A, f A ∂volume) = c * ∫⁻ d in {d : Fin n → ℝ | StrictAnti d},
        ENNReal.ofReal (∏ ij : FinStrictUpper n,
          |d ij.val.2 - d ij.val.1| ^ Module.finrank ℝ 𝕜) *
          ∫⁻ U : Frames, f (selfAdjointConj U (selfAdjointDiagonal d)) ∂haarProb Frames := by
  obtain ⟨c, hc, h⟩ := exists_lintegral_ordered_eq (n := n) (𝕜 := 𝕜)
  refine ⟨c, hc, fun f hf ↦ ?_⟩
  let G (A : Herm) (U : Frames) := f (selfAdjointConj U A)
  let g (d : Fin n → ℝ) := ∫⁻ U : Frames, G (selfAdjointDiagonal d) U ∂haarProb Frames
  have hG : Measurable (Function.uncurry G) := hf.comp continuous_selfAdjointConj.measurable
  have hg : Measurable g := Measurable.lintegral_prod_right (hG.comp
    ((selfAdjointDiagonal.continuous.measurable.comp measurable_fst).prodMk measurable_snd))
  calc
    (∫⁻ A, f A ∂volume) = ∫⁻ A, ∫⁻ U, G A U ∂haarProb Frames ∂volume :=
      lintegral_eq_lintegral_haarProb_conj hf
    _ = ∫⁻ A : Herm, g (ordered A) ∂volume := by
      refine lintegral_congr fun A ↦ ?_
      obtain ⟨V, hV⟩ := exists_selfAdjointConj_diagonal A
      have hm : Measurable (fun U : Frames ↦ G (selfAdjointDiagonal (ordered A)) U) :=
        hG.comp (measurable_const.prodMk measurable_id)
      calc
        _ = ∫⁻ U : Frames, G (selfAdjointDiagonal (ordered A)) (U * V) ∂haarProb Frames := by
          exact lintegral_congr fun U ↦ by simp only [G, selfAdjointConj_mul_apply, ← hV]
        _ = _ := (measurePreserving_mul_right (haarProb Frames) V).lintegral_comp hm
    _ = _ := h g hg

/-- Frobenius volume on self-adjoint matrices is a positive finite multiple of the pushforward of
the chamber's Vandermonde-weighted Lebesgue measure times Haar probability on unitary frames. -/
theorem exists_volume_eq_smul_map_selfAdjointConj_diagonal :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧ (volume : Measure Herm) =
      c • (((volume.restrict {d : Fin n → ℝ | StrictAnti d}).withDensity fun d ↦
        ENNReal.ofReal (∏ ij : FinStrictUpper n,
          |d ij.val.2 - d ij.val.1| ^ Module.finrank ℝ 𝕜)).prod (haarProb Frames)).map
            (fun p ↦ selfAdjointConj p.2 (selfAdjointDiagonal p.1)) := by
  obtain ⟨c, hc, h⟩ := exists_lintegral_selfAdjoint_spectral (n := n) (𝕜 := 𝕜)
  refine ⟨c, hc, Measure.ext_of_lintegral _ fun f hf ↦ ?_⟩
  let F (p : (Fin n → ℝ) × Frames) := selfAdjointConj p.2 (selfAdjointDiagonal p.1)
  have hF : Measurable F := continuous_selfAdjointConj.measurable.comp
    ((selfAdjointDiagonal.continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have htest : Measurable (fun p ↦ f (F p)) := hf.comp hF
  rw [lintegral_smul_measure, lintegral_map hf hF,
    lintegral_prod _ htest.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (continuous_gap (𝕜 := 𝕜)).measurable.ennreal_ofReal
      (Measurable.lintegral_prod_right htest), smul_eq_mul]
  exact h f hf

end Measure

end TauCeti
