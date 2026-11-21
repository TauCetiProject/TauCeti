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
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Convex.Continuous
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Integral.Bochner.Basic
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
  have hreg_eq (w : E → ℝ) :
      {x | DifferentiableAt ℝ w x ∧ Surjective (fderiv ℝ w x)} = {x | fderiv ℝ w x ≠ 0} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq,
      surjective_fderiv_iff_ne_zero_of_finrank_eq_one (finrank_self ℝ)]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨differentiableAt_of_fderiv_ne_zero h, h⟩⟩
  rw [finrank_self, univ_inter, univ_inter, hreg_eq h] at hregh
  rw [finrank_self, univ_inter, univ_inter, hreg_eq v] at hregv
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
  have hrad (x y : E) (hxy : ‖x‖ = ‖y‖) : v x = v y :=
    congrArg ENNReal.toReal (schwarzRearrangement_eq_of_norm_eq volume f hxy)
  have hanti (x y : E) (hxy : ‖x‖ ≤ ‖y‖) : v y ≤ v x :=
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume f hxy)
  set μH : Measure E := μHE[finrank ℝ E - 1]
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [ae_fiber_bounds_toReal_schwarzRearrangement hh hfin] with t hfib ht
  obtain ⟨hcritt, hperim_le, hinv_le, hinv_fin⟩ := hfib ht
  set S_v := R_v ∩ v ⁻¹' {t}; set S_h := R_h ∩ h ⁻¹' {t}
  have hSv_m : MeasurableSet S_v :=
    hRv_m.inter (isClosed_singleton.preimage hv_lip.continuous).measurableSet
  have hSh_m : MeasurableSet S_h :=
    hRh_m.inter (isClosed_singleton.preimage hh.continuous).measurableSet
  have hSh_fin : μH S_h < ∞ :=
    calc μH S_h = ∫⁻ _ in S_h, 1 ∂μH := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in S_h, (K : ℝ≥0∞) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          setLIntegral_mono ((measurable_fderiv ℝ h).eNorm.inv.const_mul _) fun x hx ↦ by
            have hne0 : ‖fderiv ℝ h x‖ₑ ≠ 0 := by
              rw [← ofReal_norm]; exact (ENNReal.ofReal_pos.2 (norm_pos_iff.2 hx.1)).ne'
            rw [← ENNReal.mul_inv_cancel hne0 (by simp [← ofReal_norm])]
            gcongr; rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ hh)
      _ = (K : ℝ≥0∞) * ∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          lintegral_const_mul _ (measurable_fderiv ℝ h).eNorm.inv
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hinv_le.trans_lt hinv_fin)
  have : IsFiniteMeasure (μH.restrict S_h) := ⟨by simpa using hSh_fin⟩
  have hg₁_const : ∃ γ : ℝ, ∀ᵐ x ∂μH.restrict S_v, ‖fderiv ℝ v x‖ = γ := by
    rcases S_v.eq_empty_or_nonempty with hSv_empty | ⟨x₀, hx₀⟩
    · exact ⟨0, by simp [hSv_empty]⟩
    · exact ⟨‖fderiv ℝ v x₀‖, (ae_restrict_mem hSv_m).mono fun x hx ↦
        norm_fderiv_eq_of_norm_eq hrad
          (TauCeti.norm_eq_of_notMem_image_fderiv_eq_zero hanti hcritt hx.2 hx₀.2)⟩
  have hinv_congr (w : E → ℝ) {S : Set E} (hS : MeasurableSet S)
      (hpos : ∀ x ∈ S, 0 < ‖fderiv ℝ w x‖) :
      (∫⁻ x in S, ENNReal.ofReal ‖fderiv ℝ w x‖⁻¹ ∂μH) =
        ∫⁻ x in S, ‖fderiv ℝ w x‖ₑ⁻¹ ∂μH :=
    setLIntegral_congr_fun hS fun x hx ↦ by
      rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos (hpos x hx)]
  have hSv_eq := hinv_congr v hSv_m fun _ hx ↦ norm_pos_iff.2 hx.1
  have hSh_eq := hinv_congr h hSh_m fun _ hx ↦ norm_pos_iff.2 hx.1
  exact hΦ.lintegral_ofReal_div_le_of_ae_eq_const hΦm hΦ0
    ((ae_restrict_mem hSv_m).mono fun _ hx ↦ norm_pos_iff.2 hx.1) hg₁_const
    (measurable_fderiv ℝ h).norm.aemeasurable
    ((ae_restrict_mem hSh_m).mono fun _ hx ↦ norm_pos_iff.2 hx.1)
    (by simpa using hperim_le) (hSh_eq ▸ hSv_eq ▸ hinv_le) (hSv_eq ▸ hinv_fin)

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
      volume := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  let E : ℝ≥0 := ⟨∫ x, Φ ‖fderiv ℝ h x‖, integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)⟩
  have hE : (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)) = E :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))).symm.trans (ENNReal.ofReal_coe_nnreal (p := E))
  exact (MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm)
      _).aestronglyMeasurable
    (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)) (E := E)
    ((hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin hΦ hΦm hΦ0).trans_eq hE)).1

/-- **Bochner-integral Pólya–Szegő inequality** for the positive-part Schwarz rearrangement. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  let E : ℝ≥0 := ⟨∫ x, Φ ‖fderiv ℝ h x‖, integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)⟩
  have hE : (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)) = E :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))).symm.trans (ENNReal.ofReal_coe_nnreal (p := E))
  exact (MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm)
      _).aestronglyMeasurable
    (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)) (E := E)
    ((hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin hΦ hΦm hΦ0).trans_eq hE)).2

/-- Integrability of `Φ ‖D(|u|*)‖` when `Φ ‖Du‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖)
      volume := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  let E : ℝ≥0 := ⟨∫ x, Φ ‖fderiv ℝ u x‖, integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)⟩
  have hE : (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖)) = E :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))).symm.trans (ENNReal.ofReal_coe_nnreal (p := E))
  exact (MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm)
      _).aestronglyMeasurable
    (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)) (E := E)
    ((hu.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin hΦ hΦm hΦ0).trans_eq
      hE)).1

/-- **Signed Bochner-integral Pólya–Szegő inequality** for `‖u ·‖`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ u x‖ := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  let E : ℝ≥0 := ⟨∫ x, Φ ‖fderiv ℝ u x‖, integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)⟩
  have hE : (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖)) = E :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))).symm.trans (ENNReal.ofReal_coe_nnreal (p := E))
  exact (MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    (TauCeti.measurable_map_norm_fderiv (𝕜 := ℝ) (hΦ.continuousOn_Ici_of_monotoneOn hΦm)
      _).aestronglyMeasurable
    (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)) (E := E)
    ((hu.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hfin hΦ hΦm hΦ0).trans_eq
      hE)).2

/-- **`Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)** for the positive part. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_rpow_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ h x‖ ^ p) :=
  hh.lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- Integrability of `‖Dh*‖ ^ p` (`1 ≤ p`) when `‖Dh‖ ^ p` is integrable. -/
theorem integrable_norm_fderiv_toReal_schwarzRearrangement_rpow {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ h x‖ ^ p) volume) :
    Integrable (fun x ↦ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p)
      volume :=
  hh.integrable_map_norm_fderiv_toReal_schwarzRearrangement hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

/-- **`Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, Bochner-integral form)** for the positive
part. -/
theorem integral_norm_fderiv_toReal_schwarzRearrangement_rpow_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ h x‖ ^ p) volume) :
    ∫ x, ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p ≤
      ∫ x, ‖fderiv ℝ h x‖ ^ p :=
  hh.integral_map_norm_fderiv_toReal_schwarzRearrangement_le hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

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
