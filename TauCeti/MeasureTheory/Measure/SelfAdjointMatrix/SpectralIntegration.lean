/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.ChangeOfVariables
import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.SimpleSpectrum
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.Order.FiniteFamily

/-!
# Spectral integration on self-adjoint matrices

Use `exists_lintegral_selfAdjoint_spectral` to integrate a nonnegative test against Frobenius
volume, or `exists_volume_eq_smul_map_selfAdjointConj_diagonal` to express that volume as a
pushforward. The ordered diagonal ranges over the strictly decreasing chamber, and its frame
is integrated against Haar probability. For a conjugation-invariant test the Haar average equals
the test on the diagonal, so only the ordered-eigenvalue integral remains.
The marginal formula `exists_lintegral_orderedEigenvalues_eq` gives this integral directly for
tests of the ordered eigenvalues.

The spectral Jacobian and Haar disintegration are those of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory MeasureTheory.Measure Set UnitaryGroup selfAdjoint
open scoped ENNReal Matrix Topology TauCeti.SelfAdjointMatrix

namespace TauCeti

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "Herm" => selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)
local notation "Frames" => unitaryGroup (Fin n) 𝕜
local notation "Angles" => FinStrictUpper n → 𝕜
local notation "chamber" => Set.ofPred (fun d : Fin n → ℝ ↦ StrictAnti d)

section Measure

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

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
  refine ⟨?_, ?_⟩
  · rw [setLIntegral_pos_iff hj.measurable.ennreal_ofReal]
    exact hspos.trans_le (measure_mono fun a ha ↦
      ⟨(ENNReal.ofReal_pos.mpr ha.2).ne', ha.1⟩)
  · have hi : IntegrableOn j (Metric.ball 0 r) ν :=
      (hj.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Angles) r)).mono_set
        Metric.ball_subset_closedBall
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)).mp
      hi.hasFiniteIntegral

private theorem lintegral_haarProb_conj_conj {f : Herm → ℝ≥0∞} (hf : Measurable f)
    (V : Frames) (A : Herm) :
    (∫⁻ U : Frames, f (selfAdjointConj U (selfAdjointConj V A)) ∂haarProb Frames) =
      ∫⁻ U : Frames, f (selfAdjointConj U A) ∂haarProb Frames := by
  have hm : Measurable (fun U : Frames ↦ f (selfAdjointConj U A)) :=
    hf.comp (continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)).measurable
  simpa only [selfAdjointConj_mul_apply] using
    (measurePreserving_mul_right (haarProb Frames) V).lintegral_comp hm

private theorem haarProb_spectralPatch_preimage {d₀ : Fin n → ℝ} (hd₀ : StrictAnti d₀)
    {B : Set Angles} (hJ : MeasurableSet (spectralMatrix 1 '' (chamber ×ˢ B)))
    (A : Herm) (hA : StrictAnti (orderedEigenvalues A)) :
    haarProb Frames ((fun U : Frames ↦ selfAdjointConj U A) ⁻¹'
      (spectralMatrix 1 '' (chamber ×ˢ B))) =
    haarProb Frames ((fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) ⁻¹'
      (spectralMatrix 1 '' (chamber ×ˢ B))) := by
  obtain ⟨V, hV⟩ := exists_selfAdjointConj_diagonal A
  let J : Set Herm := spectralMatrix 1 '' (chamber ×ˢ B)
  let f : Herm → ℝ≥0∞ := J.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hJ
  have hm (M : Herm) : Measurable (fun U : Frames ↦ selfAdjointConj U M) :=
    (continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)).measurable
  have hindicator (M : Herm) :
      (∫⁻ U : Frames, f (selfAdjointConj U M) ∂haarProb Frames) =
        haarProb Frames ((fun U : Frames ↦ selfAdjointConj U M) ⁻¹' J) := by
    simpa only [one_mul] using lintegral_indicator_const_comp (μ := haarProb Frames) (hm M) hJ 1
  have h := lintegral_haarProb_conj_conj hf V (selfAdjointDiagonal (orderedEigenvalues A))
  rw [← hV, hindicator, hindicator] at h
  refine h.trans ?_
  congr 1
  ext U
  exact conj_diagonal_mem_spectralPatch_iff hA hd₀ U

private theorem setLIntegral_ordered_spectralPatch {d₀ : Fin n → ℝ} (hd₀ : StrictAnti d₀)
    {B : Set Angles} (hJ : MeasurableSet (spectralMatrix 1 '' (chamber ×ˢ B)))
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ A : Herm in spectralMatrix 1 '' (chamber ×ˢ B), g (orderedEigenvalues A) ∂volume) =
      haarProb Frames ((fun U : Frames ↦ selfAdjointConj U (selfAdjointDiagonal d₀)) ⁻¹'
        (spectralMatrix 1 '' (chamber ×ˢ B))) * ∫⁻ A : Herm, g (orderedEigenvalues A) ∂volume := by
  let J : Set Herm := spectralMatrix 1 '' (chamber ×ˢ B)
  let G : Herm → ℝ≥0∞ := J.indicator (g ∘ orderedEigenvalues)
  have hG : Measurable G := (hg.comp continuous_orderedEigenvalues.measurable).indicator hJ
  let H (A : Herm) (U : Frames) := G (selfAdjointConj U A)
  rw [← lintegral_indicator hJ]
  calc
    (∫⁻ A, G A ∂volume) = ∫⁻ A, ∫⁻ U, H A U ∂haarProb Frames ∂volume :=
      lintegral_eq_lintegral_lintegral_of_measurePreserving
        continuous_selfAdjointConj.measurable.aemeasurable
        (.of_forall measurePreserving_selfAdjointConj_volume) hG.aemeasurable
    _ = _ := by
      have hm : Measurable (fun A : Herm ↦ g (orderedEigenvalues A)) :=
        hg.comp continuous_orderedEigenvalues.measurable
      rw [← lintegral_const_mul _ hm]
      refine lintegral_congr_ae ((ae_strictAnti_orderedEigenvalues (volume : Measure Herm)
        AbsolutelyContinuous.rfl).mono fun A hA ↦ ?_)
      have hconj : Measurable (fun U : Frames ↦ selfAdjointConj U A) :=
        (continuous_selfAdjointConj.comp (continuous_const.prodMk continuous_id)).measurable
      -- On this orbit the test is constant, so only the Haar fraction contributes.
      have heq : (fun U : Frames ↦ G (selfAdjointConj U A)) =
          fun U ↦ J.indicator (fun _ ↦ g (orderedEigenvalues A)) (selfAdjointConj U A) := by
        funext U
        by_cases h : selfAdjointConj U A ∈ J <;> simp [G, h]
      exact (congrArg (fun k ↦ ∫⁻ U : Frames, k U ∂haarProb Frames) heq).trans (by
        rw [lintegral_indicator_const_comp hconj hJ,
          haarProb_spectralPatch_preimage hd₀ hJ A hA, mul_comm])

private theorem setLIntegral_spectralPatch_eq_prod
    {B : Set Angles} (hB : MeasurableSet B)
    (hinj : InjOn (spectralMatrix (1 : Frames)) (chamber ×ˢ B))
    (ν : Measure Angles) [SFinite ν] {c : ℝ≥0∞}
    (hc : (volume : Measure Herm).map selfAdjointCoordinates = c • volume.prod ν)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ A : Herm in spectralMatrix 1 '' (chamber ×ˢ B), g (orderedEigenvalues A) ∂volume) =
      (c * ∫⁻ a in B, ENNReal.ofReal |(spectralAngularFDeriv a).det| ∂ν) *
        ∫⁻ d in chamber,
          ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) * g d ∂volume := by
  let j (a : Angles) := ENNReal.ofReal |(spectralAngularFDeriv a).det|
  let w (d : Fin n → ℝ) := ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) * g d
  have hj : Measurable j :=
    (continuous_abs_det_spectralAngularFDeriv (𝕜 := 𝕜)).measurable.ennreal_ofReal
  have hw : Measurable w :=
    ((continuous_abs_det_vandermonde_pow _).measurable.ennreal_ofReal).mul hg
  have hs : MeasurableSet (chamber ×ˢ B) := isOpen_setOf_strictAnti.measurableSet.prod hB
  rw [lintegral_image_spectralMatrix volume 1 hs.nullMeasurableSet hinj
    (fun A : Herm ↦ g (orderedEigenvalues A)), hc, setLIntegral_smul_measure]
  have heq : (∫⁻ x in chamber ×ˢ B, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
      |(vandermonde x.1).det| ^ Module.finrank ℝ 𝕜) *
        g (orderedEigenvalues (spectralMatrix 1 x)) ∂volume.prod ν) =
        ∫⁻ x in chamber ×ˢ B, w x.1 * j x.2 ∂volume.prod ν := by
    refine setLIntegral_congr_fun hs fun ⟨d, a⟩ ⟨hd, _⟩ ↦ ?_
    rw [orderedEigenvalues_spectralMatrix 1 (d, a) (StrictAnti.antitone hd),
      ENNReal.ofReal_mul (abs_nonneg _)]
    dsimp only [w, j]
    ac_rfl
  rw [heq, ← Measure.prod_restrict, lintegral_prod_mul hw.aemeasurable hj.aemeasurable]
  rw [smul_eq_mul]
  dsimp only [j, w]
  ac_rfl

/-- The ordered eigenvalue marginal of Frobenius volume is Lebesgue measure on the decreasing
chamber weighted by the absolute Vandermonde determinant to power one over the reals and power
two over the complexes, up to a positive finite constant. -/
theorem exists_lintegral_orderedEigenvalues_eq :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧
      ∀ g : (Fin n → ℝ) → ℝ≥0∞, Measurable g →
        (∫⁻ A : Herm, g (orderedEigenvalues A) ∂volume) =
          c * ∫⁻ d in chamber,
            ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) * g d ∂volume := by
  let d₀ (i : Fin n) := -((i : ℕ) : ℝ)
  have hd₀ : StrictAnti d₀ := (Nat.strictMono_cast.comp (Fin.valOrderEmb n).strictMono).neg
  obtain ⟨r, hr, hslice, hD⟩ := exists_spectralMatrix_angularBall (𝕜 := 𝕜) d₀ hd₀
  let B := Metric.ball (0 : Angles) r
  let J : Set Herm := spectralMatrix 1 '' (chamber ×ˢ B)
  have hinj := injOn_spectralMatrix_one hslice
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hJ : MeasurableSet J := (isOpen_setOf_strictAnti.measurableSet.prod hB)
    |>.image_of_continuousOn_injOn (contDiff_spectralMatrix (k := 0) 1).continuous.continuousOn hinj
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

private theorem exists_lintegral_selfAdjoint_spectral_measurable :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧ ∀ f : Herm → ℝ≥0∞, Measurable f →
      (∫⁻ A, f A ∂volume) = c * ∫⁻ d in chamber,
        ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) *
          ∫⁻ U : Frames, f (selfAdjointConj U (selfAdjointDiagonal d)) ∂haarProb Frames := by
  obtain ⟨c, hc, h⟩ := exists_lintegral_orderedEigenvalues_eq (n := n) (𝕜 := 𝕜)
  refine ⟨c, hc, fun f hf ↦ ?_⟩
  let G (A : Herm) (U : Frames) := f (selfAdjointConj U A)
  let g (d : Fin n → ℝ) := ∫⁻ U : Frames, G (selfAdjointDiagonal d) U ∂haarProb Frames
  have hG : Measurable (Function.uncurry G) := hf.comp continuous_selfAdjointConj.measurable
  have hg : Measurable g := Measurable.lintegral_prod_right (hG.comp
    ((selfAdjointDiagonal.continuous.measurable.comp measurable_fst).prodMk measurable_snd))
  calc
    (∫⁻ A, f A ∂volume) = ∫⁻ A, ∫⁻ U, G A U ∂haarProb Frames ∂volume :=
      lintegral_eq_lintegral_lintegral_of_measurePreserving
        continuous_selfAdjointConj.measurable.aemeasurable
        (.of_forall measurePreserving_selfAdjointConj_volume) hf.aemeasurable
    _ = ∫⁻ A : Herm, g (orderedEigenvalues A) ∂volume := by
      refine lintegral_congr fun A ↦ ?_
      obtain ⟨V, hV⟩ := exists_selfAdjointConj_diagonal A
      conv_lhs => rw [hV]
      exact lintegral_haarProb_conj_conj hf V (selfAdjointDiagonal (orderedEigenvalues A))
    _ = _ := h g hg

private theorem lintegral_map_spectral {f : Herm → ℝ≥0∞}
    (hf : AEMeasurable f
      ((((volume.restrict chamber).withDensity fun d ↦
        ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜)).prod (haarProb Frames)).map
          (fun p ↦ selfAdjointConj p.2 (selfAdjointDiagonal p.1)))) :
    (∫⁻ A, f A ∂(((volume.restrict chamber).withDensity fun d ↦
      ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜)).prod (haarProb Frames)).map
        (fun p ↦ selfAdjointConj p.2 (selfAdjointDiagonal p.1))) =
      ∫⁻ d in chamber, ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) *
        ∫⁻ U : Frames, f (selfAdjointConj U (selfAdjointDiagonal d)) ∂haarProb Frames := by
  let ρ : Measure (Fin n → ℝ) := (volume.restrict chamber).withDensity fun d ↦
    ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜)
  let F (p : (Fin n → ℝ) × Frames) := selfAdjointConj p.2 (selfAdjointDiagonal p.1)
  have hF : Measurable F := continuous_selfAdjointConj.measurable.comp
    ((selfAdjointDiagonal.continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have htest : AEMeasurable (fun p ↦ f (F p)) (ρ.prod (haarProb Frames)) :=
    hf.comp_quasiMeasurePreserving ⟨hF.aemeasurable, AbsolutelyContinuous.rfl⟩
  rw [lintegral_map' hf hF.aemeasurable, lintegral_prod _ htest,
    lintegral_withDensity_eq_lintegral_mul₀'
      (continuous_abs_det_vandermonde_pow _).measurable.ennreal_ofReal.aemeasurable
      htest.lintegral_prod_right']
  rfl

/-- Frobenius volume on self-adjoint matrices is a positive finite multiple of the pushforward of
the chamber's weighted Lebesgue measure times Haar probability on unitary frames. The weight is
the absolute Vandermonde determinant to power one over the reals and power two over the
complexes. -/
theorem exists_volume_eq_smul_map_selfAdjointConj_diagonal :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧ (volume : Measure Herm) =
      c • (((volume.restrict chamber).withDensity fun d ↦
        ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜)).prod (haarProb Frames)).map
          (fun p ↦ selfAdjointConj p.2 (selfAdjointDiagonal p.1)) := by
  obtain ⟨c, hc, h⟩ := exists_lintegral_selfAdjoint_spectral_measurable (n := n) (𝕜 := 𝕜)
  refine ⟨c, hc, Measure.ext_of_lintegral _ fun f hf ↦ ?_⟩
  rw [lintegral_smul_measure, lintegral_map_spectral hf.aemeasurable, smul_eq_mul]
  exact h f hf

/-- For every Frobenius-almost-everywhere measurable nonnegative test, integrate over the
strictly decreasing eigenvalues and average over Haar probability on the frames. The weight is
the absolute Vandermonde determinant to power one for real symmetric matrices and power two for
complex Hermitian matrices. The same positive finite constant works for every test. -/
theorem exists_lintegral_selfAdjoint_spectral :
    ∃ c : ℝ≥0∞, c ∈ Ioo 0 ⊤ ∧ ∀ f : Herm → ℝ≥0∞, AEMeasurable f volume →
      (∫⁻ A, f A ∂volume) = c * ∫⁻ d in chamber,
        ENNReal.ofReal (|(vandermonde d).det| ^ Module.finrank ℝ 𝕜) *
          ∫⁻ U : Frames, f (selfAdjointConj U (selfAdjointDiagonal d)) ∂haarProb Frames := by
  obtain ⟨c, hc, h⟩ := exists_volume_eq_smul_map_selfAdjointConj_diagonal (n := n) (𝕜 := 𝕜)
  refine ⟨c, hc, fun f hf ↦ ?_⟩
  rw [h] at hf
  rw [h, lintegral_smul_measure, smul_eq_mul,
    lintegral_map_spectral ((aemeasurable_smul_measure_iff hc.1.ne').mp hf)]

end Measure

end TauCeti
