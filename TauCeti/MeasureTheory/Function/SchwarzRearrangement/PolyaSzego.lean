/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.BoundedVariation.LevelSurface
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Convex.Continuous
import TauCeti.MeasureTheory.Function.Coarea.Integral
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# The Pólya–Szegő inequality for Lipschitz functions

Let `E` be a nontrivial finite-dimensional real inner product space, and let `Φ : ℝ → ℝ` be convex
and monotone on `[0, ∞)` with `Φ 0 = 0`. For a Lipschitz function `h : E → ℝ` whose positive
superlevel sets `{x | t < h x}` (`t > 0`) have finite Lebesgue volume, the real-valued Schwarz
rearrangement `h* x := (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal`
satisfies

`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)`

(`LipschitzWith.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le`), together with the signed
variant for `‖u ·‖`, Bochner-integral and integrability forms, and `Lᵖ` specializations for
`1 ≤ p`.

## References

* J. E. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  384 (1988), 153–179.
* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *Rearrangement and polarization inequalities
  for Sobolev functions*, J. Funct. Anal. 287 (2024), Theorem 5.8.
-/

public section

open Filter Function MeasureTheory Metric Module Set TauCeti
open scoped ENNReal NNReal Topology

section PrivateHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem setLIntegral_fiber_le_of_const_norm_fderiv {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {K : ℝ≥0} {v h : E → ℝ} {S_v S_h : Set E}
    (hSv_m : MeasurableSet S_v) (hSh_m : MeasurableSet S_h)
    (hSv_pos : ∀ x ∈ S_v, 0 < ‖fderiv ℝ v x‖) (hSh_pos : ∀ x ∈ S_h, 0 < ‖fderiv ℝ h x‖)
    (hSh_le : ∀ x ∈ S_h, ‖fderiv ℝ h x‖ ≤ K)
    (hconst : ∀ x ∈ S_v, ∀ y ∈ S_v, ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖)
    (hperim : μHE[finrank ℝ E - 1] S_v ≤ μHE[finrank ℝ E - 1] S_h)
    (hinv : (∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1])
    (hinv_fin : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) < ∞)
    (hΦ_fin : (∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
      ∂μHE[finrank ℝ E - 1]) < ∞) :
    (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  set μH : Measure E := μHE[finrank ℝ E - 1]
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  -- Stage 1: Finiteness of fiber measures from the Lipschitz bound and perimeter comparison.
  have hSh_fin : μH S_h < ∞ :=
    calc μH S_h = ∫⁻ _ in S_h, 1 ∂μH := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in S_h, (K : ℝ≥0∞) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          setLIntegral_mono ((measurable_fderiv ℝ h).eNorm.inv.const_mul _) fun x hx ↦ by
            have hne0 : ‖fderiv ℝ h x‖ₑ ≠ 0 := by
              rw [← ofReal_norm]; exact (ENNReal.ofReal_pos.2 (hSh_pos x hx)).ne'
            rw [← ENNReal.mul_inv_cancel hne0 (by simp [← ofReal_norm])]
            gcongr; rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (hSh_le x hx)
      _ = (K : ℝ≥0∞) * ∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          lintegral_const_mul _ (measurable_fderiv ℝ h).eNorm.inv
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hinv.trans_lt hinv_fin)
  have hSv_fin : μH S_v < ∞ := hperim.trans_lt hSh_fin
  by_cases hSv0 : μH S_v = 0
  · simp [Measure.restrict_eq_zero.2 hSv0]
  -- Stage 2: Evaluate the constant-gradient fiber integrals of `v` in terms of `P` and `M`.
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hSv0
  set γ := ‖fderiv ℝ v x₀‖; have hγ : 0 < γ := hSv_pos x₀ hx₀
  set ν_h := μH.restrict S_h; have : Fact (μH S_h < ∞) := ⟨hSh_fin⟩
  set P := (μH S_v).toReal; set M := (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH).toReal
  have hP_pos : 0 < P := ENNReal.toReal_pos hSv0 hSv_fin.ne
  have hM_eq : M = P / γ := by
    have hm : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH) = ENNReal.ofReal γ⁻¹ * μH S_v :=
      (setLIntegral_const _ _).symm ▸ setLIntegral_congr_fun hSv_m fun x hx ↦ by
        rw [← ofReal_norm, hconst x hx x₀ hx₀, ENNReal.ofReal_inv_of_pos hγ]
    simp [M, P, hm, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), inv_mul_eq_div]
  have hlhs_eq : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
      ENNReal.ofReal (M * Φ (P / M)) := by
    have hc : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
        ENNReal.ofReal (Φ γ / γ) * μH S_v :=
      (setLIntegral_const _ _).symm ▸ setLIntegral_congr_fun hSv_m fun x hx ↦ by
        rw [hconst x hx x₀ hx₀]
    have hPM : P / M = γ := by rw [hM_eq, div_div_cancel₀ hP_pos.ne']
    rw [hc, hPM, hM_eq, ← ENNReal.ofReal_toReal hSv_fin.ne,
      ← ENNReal.ofReal_mul (div_nonneg (hΦ_nn γ hγ.le) hγ.le)]
    congr 1; ring
  -- Stage 3: Pass to Bochner integrals on `S_h` and apply reciprocal-weighted Jensen.
  have hg_pos : ∀ᵐ x ∂ν_h, 0 < ‖fderiv ℝ h x‖ := (ae_restrict_mem hSh_m).mono hSh_pos
  have hinv_int : Integrable (fun x ↦ ‖fderiv ℝ h x‖⁻¹) ν_h :=
    ⟨(measurable_fderiv ℝ h).norm.inv.aestronglyMeasurable,
      (lintegral_congr_ae <| hg_pos.mono fun _ hx ↦ by
        rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.2 hx.le),
          ENNReal.ofReal_inv_of_pos hx]).trans_lt (hinv.trans_lt hinv_fin)⟩
  have hΦ_int : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ν_h :=
    ⟨((TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm) h).div
        (measurable_fderiv ℝ h).norm).aestronglyMeasurable,
      (lintegral_congr_ae <| hg_pos.mono fun _ hx ↦ by
        rw [← ofReal_norm, Real.norm_of_nonneg (div_nonneg (hΦ_nn _ hx.le) hx.le)]).trans_lt hΦ_fin⟩
  have hM_bound : (∫ x, ‖fderiv ℝ h x‖⁻¹ ∂ν_h) ≤ M := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hinv_fin.ne,
      ofReal_integral_eq_lintegral_ofReal hinv_int (hg_pos.mono fun _ hx ↦ inv_nonneg.2 hx.le)]
    exact (setLIntegral_congr_fun hSh_m fun x hx ↦ by
      rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos (hSh_pos x hx)]).le.trans hinv
  have hPν : P ≤ ν_h.real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]; exact ENNReal.toReal_mono hSh_fin.ne hperim
  rw [hlhs_eq, ← ofReal_integral_eq_lintegral_ofReal hΦ_int
    (hg_pos.mono fun _ hx ↦ div_nonneg (hΦ_nn _ hx.le) hx.le)]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg_pos hinv_int hΦ_int hP_pos.le hPν hM_bound)

private theorem ae_fiber_bounds_toReal_schwarzRearrangement
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    let v : E → ℝ := fun x ↦
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal
    ∀ᵐ t : ℝ, 0 < t →
      t ∉ v '' {z | fderiv ℝ v z = 0} ∧
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) ≤
        μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) ∧
      (∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
        (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ∧
      (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hv_ne_top := schwarzRearrangement_ofReal_ne_top volume hh zero_le_one (hfin 1 zero_lt_one)
  have hv_level {t : ℝ} (ht : 0 < t) :
      {x | t < v x} = {x | ENNReal.ofReal t < schwarzRearrangement volume f x} :=
    Set.ext fun x ↦ (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hv_ne_top x)).symm
  have hh_level {t : ℝ} (ht : 0 < t) : {x | ENNReal.ofReal t < f x} = {x | t < h x} :=
    Set.ext fun _ ↦ ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  have hcrit := hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume
  filter_upwards [compl_mem_ae_iff.2 hcrit, hh.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hv_lip.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hh.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤,
    hv_lip.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure ⊤,
    ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin]
    with t hcritt hregh hregv hperh hperv hdisth hdistv ht
  rw [finrank_self, univ_inter, univ_inter,
    TauCeti.setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero h] at hregh
  rw [finrank_self, univ_inter, univ_inter,
    TauCeti.setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero v] at hregv
  refine ⟨hcritt, ?_, hdistv ht ▸ hdisth ht, (hdistv ht) ▸ ENNReal.ofReal_lt_top⟩
  have hmeas_v : μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (v ⁻¹' {t}) := by
    simpa only [Measure.restrict_apply_univ] using congrArg (fun ν : Measure E ↦ ν univ) hregv.symm
  have hmeas_h : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (h ⁻¹' {t}) := by
    simpa only [Measure.restrict_apply_univ] using congrArg (fun ν : Measure E ↦ ν univ) hregh.symm
  simp only [TopologicalSpace.Opens.coe_top, univ_inter] at hperh hperv
  rw [hmeas_v, hmeas_h, ← hperv, ← hperh, hv_level ht, ← hh_level ht]
  have hm : MeasurableSet {x | ENNReal.ofReal t < f x} :=
    measurableSet_lt measurable_const hh.continuous.measurable.ennreal_ofReal
  exact hm.nullMeasurableSet.perimeter_setOf_lt_schwarzRearrangement_le

private theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h) (hh0 : ∀ x, 0 ≤ h x)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  by_cases htop : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) = ∞
  · exact htop ▸ le_top
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hv_ne_top := schwarzRearrangement_ofReal_ne_top volume hh zero_le_one (hfin 1 zero_lt_one)
  have hΦ_cont : ContinuousOn Φ (Ici 0) := hΦ.continuousOn_Ici_of_monotoneOn hΦm
  have hco_h := lintegral_map_norm_fderiv_eq_setLIntegral_Ioi hh0
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) hΦ_cont h) hΦ0
  rw [lintegral_map_norm_fderiv_eq_setLIntegral_Ioi (fun _ ↦ ENNReal.toReal_nonneg)
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) hΦ_cont v) hΦ0, hco_h]
  set R_v := {x : E | fderiv ℝ v x ≠ 0}; set R_h := {x : E | fderiv ℝ h x ≠ 0}
  have hRv_m : MeasurableSet R_v :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ v)
  have hRh_m : MeasurableSet R_h :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hΦ_ae_fin : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) →
      (∫⁻ x in R_h ∩ h ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
    have hmeas := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume
      hRh_m.nullMeasurableSet
      (fun _ hx ↦ (differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
      (ENNReal.measurable_ofReal.comp
        ((TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) hΦ_cont h).div (measurable_fderiv ℝ h).norm))
    rw [finrank_self] at hmeas
    exact (ae_restrict_iff' measurableSet_Ioi).1 (ae_lt_top' hmeas.restrict (hco_h ▸ htop))
  have hrad (x y : E) (hxy : ‖x‖ = ‖y‖) : v x = v y :=
    congrArg ENNReal.toReal (schwarzRearrangement_eq_of_norm_eq volume f hxy)
  have hanti (x y : E) (hxy : ‖x‖ ≤ ‖y‖) : v y ≤ v x :=
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume f hxy)
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [hΦ_ae_fin, ae_fiber_bounds_toReal_schwarzRearrangement hh hfin]
    with t hΦt hfib ht
  obtain ⟨hcritt, hperim_le, hinv_le, hinv_fin⟩ := hfib ht
  exact setLIntegral_fiber_le_of_const_norm_fderiv hΦ hΦm hΦ0
    (hRv_m.inter (isClosed_singleton.preimage hv_lip.continuous).measurableSet)
    (hRh_m.inter (isClosed_singleton.preimage hh.continuous).measurableSet)
    (fun _ hx ↦ norm_pos_iff.2 hx.1) (fun _ hx ↦ norm_pos_iff.2 hx.1)
    (fun _ _ ↦ norm_fderiv_le_of_lipschitz ℝ hh)
    (fun _ hx _ hy ↦ norm_fderiv_eq_of_norm_eq hrad
      (TauCeti.norm_eq_of_notMem_image_fderiv_eq_zero hanti hcritt hx.2 hy.2))
    hperim_le hinv_le hinv_fin (hΦt ht)

omit [Nontrivial E] in
private theorem integrable_and_integral_le_of_lintegral_le {v u : E → ℝ} {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hle : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖))
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ v x‖) volume ∧
      ∫ x, Φ ‖fderiv ℝ v x‖ ≤ ∫ x, Φ ‖fderiv ℝ u x‖ := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have heq (w : E → ℝ) : (∫⁻ x, ‖Φ ‖fderiv ℝ w x‖‖ₑ) =
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) :=
    lintegral_congr fun _ ↦ by rw [← ofReal_norm, Real.norm_of_nonneg (hΦ_nn _ (norm_nonneg _))]
  have hint_v : Integrable (fun x ↦ Φ ‖fderiv ℝ v x‖) volume :=
    ⟨(TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm)
        v).aestronglyMeasurable,
      by rw [HasFiniteIntegral, heq v]; exact hle.trans_lt (heq u ▸ hint.hasFiniteIntegral)⟩
  refine ⟨hint_v, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint_v (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))]
  exact hle

end PrivateHelpers

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The convex-integrand Pólya–Szegő inequality for Lipschitz functions.** -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  let hpos : E → ℝ := fun x ↦ max (h x) 0
  have hhpos_lip : LipschitzWith K hpos := hh.max_const 0
  have hhpos_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hpos x} ≠ ∞ := by
    convert hfin t ht using 2; ext x; simp [hpos, lt_max_iff, ht.not_gt]
  have hofReal : (fun y ↦ ENNReal.ofReal (h y)) = fun y ↦ ENNReal.ofReal (hpos y) := funext fun y ↦
    (le_total 0 (h y)).elim (fun hy ↦ by simp [hpos, max_eq_left hy])
      (fun hy ↦ by simp [hpos, max_eq_right hy, ENNReal.ofReal_of_nonpos hy])
  rw [hofReal]
  refine (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg hhpos_lip
    (fun x ↦ le_max_right (h x) 0) hhpos_fin hΦ hΦm hΦ0).trans (lintegral_mono_ae ?_)
  filter_upwards [hh.ae_differentiableAt (μ := volume)] with x hx
  refine ENNReal.ofReal_le_ofReal (hΦm (norm_nonneg _) (norm_nonneg _) ?_)
  simpa only [NNReal.coe_one, one_mul, id_eq, Function.comp_def] using
    (LipschitzWith.id.max_const (0 : ℝ)).norm_fderiv_comp_le hx

/-- **Signed convex-integrand Pólya–Szegő inequality for Lipschitz functions.** -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) := by
  have hu_norm : LipschitzWith K (fun x ↦ ‖u x‖) := by
    simpa only [one_mul, Function.comp_def] using
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hu
  refine (hu_norm.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin hΦ hΦm hΦ0).trans
    (lintegral_mono_ae ?_)
  filter_upwards [hu.ae_differentiableAt (μ := volume)] with x hx
  refine ENNReal.ofReal_le_ofReal (hΦm (norm_nonneg _) (norm_nonneg _) ?_)
  simpa only [NNReal.coe_one, one_mul, Function.comp_def] using
    lipschitzWith_one_norm.norm_fderiv_comp_le hx

/-- Integrability of `Φ ‖Dh*‖` when `Φ ‖Dh‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖)
      volume :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin hΦ hΦm hΦ0) hint).1

/-- **Bochner-integral Pólya–Szegő inequality** for the positive-part Schwarz rearrangement. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin hΦ hΦm hΦ0) hint).2

/-- Integrability of `Φ ‖D(|u|*)‖` when `Φ ‖Du‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖)
      volume :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (hu.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin hΦ hΦm hΦ0) hint).1

/-- **Signed Bochner-integral Pólya–Szegő inequality** for `‖u ·‖`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ u x‖ :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (hu.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin hΦ hΦm hΦ0) hint).2

/-- **`Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)** for the positive part. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_rpow_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ h x‖ ^ p) :=
  hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)**. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x‖ ^ p) :=
  hu.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- Integrability of `‖D(|u|*)‖ ^ p` (`1 ≤ p`) when `‖Du‖ ^ p` is integrable. -/
theorem integrable_norm_fderiv_toReal_schwarzRearrangement_norm_rpow {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    Integrable (fun x ↦ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p)
      volume :=
  hu.integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, Bochner-integral form)**. -/
theorem integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    ∫ x, ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p ≤
      ∫ x, ‖fderiv ℝ u x‖ ^ p :=
  hu.integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

end LipschitzWith
