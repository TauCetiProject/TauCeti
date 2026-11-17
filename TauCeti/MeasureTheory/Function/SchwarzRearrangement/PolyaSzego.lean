/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.BoundedVariation.LevelSet
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Convex.Monotone
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Integral
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.MeasureTheory.Function.Monotone
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# Convex-integrand Pólya–Szegő inequality for Lipschitz functions

Let `E` be a finite-dimensional real inner product space equipped with an additive Haar measure `μ`.
For every `K`-Lipschitz function `h : E → ℝ` and every `Φ : ℝ → ℝ` convex on `[0, ∞)` with
`Φ 0 ≤ 0`, the real Schwarz rearrangement `h*` of the positive part of `h` satisfies
`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ`
(`LipschitzWith.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le`), with no sign,
decay, monotonicity, or positive-dimension restrictions.

For Lebesgue `volume` in positive dimension, the scalar coarea formula decomposes both integrals
over positive levels `t > 0` into `∫_{{w = t} ∩ {Dw ≠ 0}} Φ(‖Dw‖) / ‖Dw‖ dH^{n-1}`. At almost every
level `t > 0`:
* `t` is not a critical value of `h*`, so `‖Dh*‖` is constant and nonzero along `{h* = t}` by
  `TauCeti.norm_eq_of_eq_of_forall_fderiv_ne_zero` and `TauCeti.norm_fderiv_eq_of_norm_eq`;
* the Euclidean Hausdorff measures `μHE[finrank ℝ E - 1]` of `{h* = t}` and `{h = t}` agree with
  their superlevel perimeters
  (`LipschitzWith.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage`), which satisfy
  `P({h* > t}) ≤ P({h > t})` by the sharp Euclidean isoperimetric inequality;
* the reciprocal-gradient level integrals satisfy `m_{h*}(t) = -μ_h'(t) ≥ m_h(t)` by the
  reciprocal-weight coarea identities in
  `TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues` and
  `TauCeti.MeasureTheory.Function.Coarea.DistributionFunction`;
* reciprocal-weighted Jensen and perspective monotonicity (`ConvexOn.mul_map_div_le_integral_div`)
  compare the two level integrals.

Subtracting the infimum of nonnegative levels of finite superlevel volume removes any decay
assumption on `h`, truncating `Φ` at zero (`ConvexOn.monotoneOn_max_const`) removes monotonicity of
`Φ`, and Haar uniqueness (`Measure.isAddLeftInvariant_eq_smul`) transfers the inequality from
`volume` to any additive Haar measure `μ`.

## Main declarations

* `LipschitzWith.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le`: extended
  convex-integrand Pólya–Szegő inequality for arbitrary Lipschitz functions and additive Haar
  measures.
* `LipschitzWith.integrable_map_norm_fderiv_toReal_schwarzRearrangement` and
  `LipschitzWith.integral_map_norm_fderiv_toReal_schwarzRearrangement_le`: Bochner integrability and
  integral comparison for convex nondecreasing `Φ` with `Φ 0 = 0`.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, J. Funct. Anal. **287** (2024), Theorem 5.8.
* J. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  **384** (1988), 153–179.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., AMS, 2001, Theorem 7.17 and Lemma 7.17.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace Metric Module ContinuousLinearMap
open scoped ENNReal NNReal Topology

namespace LipschitzWith

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Extended-real wrapper around `ConvexOn.mul_map_div_le_integral_div` on the level subset
`{x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}`. -/
private theorem ofReal_mul_map_div_le_setLIntegral_fiber {h : E → ℝ}
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {t P M : ℝ} (hP : 0 ≤ P) (hM0 : 0 ≤ M)
    (hPv : ENNReal.ofReal P ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}))
    (hPh_fin : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) < ∞)
    (hmh : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] ≤ ENNReal.ofReal M)
    (hΦh_fin : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞) :
    ENNReal.ofReal (M * Φ (P / M)) ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  have hSm : MeasurableSet ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [inter_comm]
    exact TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
  set S := {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}
  set ν := μHE[finrank ℝ E - 1].restrict S
  have : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hPh_fin⟩
  have hg : ∀ᵐ x ∂ν, 0 < ‖fderiv ℝ h x‖ :=
    (ae_restrict_mem hSm).mono fun x hx ↦ norm_pos_iff.2 hx.1
  have hinv_eq : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ h x‖⁻¹ ∂ν = ∫⁻ x, ‖fderiv ℝ h x‖ₑ⁻¹ ∂ν :=
    lintegral_congr_ae (hg.mono fun x hpos ↦ by
      dsimp only
      rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos hpos])
  have hi : Integrable (fun x ↦ ‖fderiv ℝ h x‖⁻¹) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_fderiv ℝ h).norm.inv.aestronglyMeasurable
      (ae_of_all _ fun x ↦ inv_nonneg.2 (norm_nonneg _))).1
      (hinv_eq.symm ▸ (hmh.trans_lt ENNReal.ofReal_lt_top).ne)
  have hΦ_nonneg (x : E) : 0 ≤ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖ :=
    div_nonneg (hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hΦm_meas : Measurable fun x : E ↦ Φ ‖fderiv ℝ h x‖ :=
    hΦm.measurable_comp (measurable_fderiv ℝ h).norm fun _ ↦ norm_nonneg _
  have hΦi : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hΦm_meas.div (measurable_fderiv ℝ h).norm).aestronglyMeasurable
      (ae_of_all _ hΦ_nonneg)).1 hΦh_fin.ne
  have hPν : P ≤ ν.real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ, ← ENNReal.toReal_ofReal hP]
    exact ENNReal.toReal_mono hPh_fin.ne hPv
  have hM_int : ∫ x, ‖fderiv ℝ h x‖⁻¹ ∂ν ≤ M := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ inv_nonneg.2 (norm_nonneg _))
      hi.aestronglyMeasurable, hinv_eq, ← ENNReal.toReal_ofReal hM0]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmh
  rw [← ofReal_integral_eq_lintegral_ofReal hΦi (ae_of_all _ hΦ_nonneg)]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg hi hΦi hP hPν hM_int)

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Single-level comparison between a radially nonincreasing map `v` along a level set on which
`fderiv ℝ v` never vanishes and a map `h` whose noncritical level set has at least the Hausdorff
measure of `v ⁻¹' {t}` and no smaller reciprocal-gradient bound `μ'`. -/
private theorem fiber_le_of_level_bounds {v h : E → ℝ} (hvm : Measurable v)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {t μ' : ℝ} (hrad : ∀ z w : E, ‖z‖ ≤ ‖w‖ → v w ≤ v z)
    (hreg : ∀ z : E, v z = t → fderiv ℝ v z ≠ 0)
    (hPv : μHE[finrank ℝ E - 1] (v ⁻¹' {t}) ≤
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}))
    (hPh_fin : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) < ∞)
    (hmv : ∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] = ENNReal.ofReal μ')
    (hmh : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] ≤ ENNReal.ofReal μ')
    (hΦh_fin : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞) :
    ∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μHE[finrank ℝ E - 1] ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  have hv_inter : {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t} = v ⁻¹' {t} :=
    inter_eq_right.mpr fun x hx ↦ hreg x hx
  rw [hv_inter] at hmv ⊢
  rcases eq_or_ne (μHE[finrank ℝ E - 1] (v ⁻¹' {t})) 0 with hPv0 | hPv0
  · simp [Measure.restrict_eq_zero.2 hPv0]
  obtain ⟨x₀, hx₀ : v x₀ = t⟩ := nonempty_of_measure_ne_zero hPv0
  have hPv_fin : μHE[finrank ℝ E - 1] (v ⁻¹' {t}) < ∞ := hPv.trans_lt hPh_fin
  have hvt_m : MeasurableSet (v ⁻¹' {t}) := hvm (measurableSet_singleton t)
  have hcst (x : E) (hx : x ∈ v ⁻¹' {t}) : ‖fderiv ℝ v x‖ = ‖fderiv ℝ v x₀‖ :=
    TauCeti.norm_fderiv_eq_of_norm_eq
      (fun z w hzw ↦ le_antisymm (hrad w z hzw.symm.le) (hrad z w hzw.le))
      (TauCeti.norm_eq_of_eq_of_forall_fderiv_ne_zero hrad
        (fun z hz ↦ hreg z (hz.trans hx₀)) (hx₀.trans hx.symm)).symm
  set γ := ‖fderiv ℝ v x₀‖
  have hγ : 0 < γ := norm_pos_iff.2 (hreg x₀ hx₀)
  set P := μHE[finrank ℝ E - 1].real (v ⁻¹' {t})
  have hP : 0 < P := ENNReal.toReal_pos hPv0 hPv_fin.ne
  set M := max μ' 0
  have hM_eq : ENNReal.ofReal M = ENNReal.ofReal μ' := by simp [M]
  have hmv_eval : ENNReal.ofReal γ⁻¹ * μHE[finrank ℝ E - 1] (v ⁻¹' {t}) = ENNReal.ofReal M := by
    rw [hM_eq, ← hmv, ← setLIntegral_const]
    refine setLIntegral_congr_fun hvt_m fun x hx ↦ ?_
    rw [← ofReal_norm, hcst x hx, ENNReal.ofReal_inv_of_pos hγ]
  have hM_val : M = γ⁻¹ * P := by
    have htr := congrArg ENNReal.toReal hmv_eval
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le),
      ENNReal.toReal_ofReal (le_max_right _ _), eq_comm] at htr
  have hPM : P / M = γ := by rw [hM_val]; field_simp
  have hP_ofReal : ENNReal.ofReal P = μHE[finrank ℝ E - 1] (v ⁻¹' {t}) := by
    dsimp only [P]
    rw [measureReal_def, ENNReal.ofReal_toReal hPv_fin.ne]
  have hlhs_eval : ∫⁻ x in v ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖)
        ∂μHE[finrank ℝ E - 1] = ENNReal.ofReal (M * Φ (P / M)) := by
    have hΦγ : 0 ≤ Φ γ / γ := div_nonneg (hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hγ.le hγ.le) hγ.le
    calc ∫⁻ x in v ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖)
            ∂μHE[finrank ℝ E - 1]
        = ENNReal.ofReal (Φ γ / γ) * ENNReal.ofReal P := by
          rw [setLIntegral_congr_fun hvt_m fun x hx ↦ by rw [hcst x hx],
            setLIntegral_const, hP_ofReal]
      _ = ENNReal.ofReal (M * Φ (P / M)) := by
          rw [← ENNReal.ofReal_mul hΦγ, hPM, hM_val]
          congr 1
          ring
  rw [hlhs_eval]
  exact ofReal_mul_map_div_le_setLIntegral_fiber hΦ hΦm hΦ0 hP.le (le_max_right _ _)
    (hP_ofReal.trans_le hPv) hPh_fin (hM_eq ▸ hmh) hΦh_fin

variable [FiniteDimensional ℝ E]

/-- Almost-every-level finiteness and critical-value exclusion needed in the Lipschitz Pólya–Szegő
coarea comparison. -/
private theorem ae_level_conditions_of_lipschitzWith {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {Φ : ℝ → ℝ} (hΦm : MonotoneOn Φ (Ici 0))
    (hInt : ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] ≠ ∞) :
    ∀ᵐ t : ℝ, 0 < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞ ∧
      μHE[finrank ℝ E - 1] (h ⁻¹' {t}) < ∞ ∧
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) = 0 ∧
      ∀ z : E, (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal = t →
        fderiv ℝ (fun w ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) w).toReal) z ≠ 0 := by
  have hRh : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hm := MeasureTheory.aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt (F := ℝ) volume
    hRh.nullMeasurableSet
    (fun x hx ↦ (TauCeti.differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
    (ENNReal.measurable_ofReal.comp
      ((hΦm.measurable_comp (measurable_fderiv ℝ h).norm fun _ ↦ norm_nonneg _).div
        (measurable_fderiv ℝ h).norm))
  rw [finrank_self] at hm
  have hae_Φfin := (ae_restrict_iff' measurableSet_Ioi).1 (ae_lt_top' hm.restrict hInt)
  have hae_Hfin : ∀ᵐ t : ℝ, 0 < t → μHE[finrank ℝ E - 1] (h ⁻¹' {t}) < ∞ := by
    have hk (k : ℕ) : ∀ᵐ t : ℝ,
        μHE[finrank ℝ E - 1] ({x | 1 / ((k : ℝ) + 1) < h x} ∩ h ⁻¹' {t}) < ∞ := by
      have hSk : NullMeasurableSet {x | 1 / ((k : ℝ) + 1) < h x} :=
        (isOpen_lt continuous_const hh.continuous).measurableSet.nullMeasurableSet
      simpa [finrank_self] using
        hh.ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn hSk
          (hh.integrableOn_normDet_adjoint_fderiv (hfin _ (Nat.one_div_pos_of_nat (n := k))))
    filter_upwards [ae_all_iff.2 hk] with t ht htpos
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
    have heq : {x | 1 / ((k : ℝ) + 1) < h x} ∩ h ⁻¹' {t} = h ⁻¹' {t} :=
      inter_eq_right.mpr fun x (hx : h x = t) ↦ by rwa [mem_ofPred_eq, hx]
    rw [← heq]
    exact ht k
  have hae_crit_h : ∀ᵐ t : ℝ, μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) = 0 := by
    simpa [finrank_self, ContinuousLinearMap.normDet_adjoint_eq_norm] using
      hh.ae_euclideanHausdorffMeasure_setOf_normDet_adjoint_fderiv_eq_zero_inter_preimage_eq_zero
  have hae_reg_v : ∀ᵐ t : ℝ, ∀ z : E,
      (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal = t →
        fderiv ℝ (fun w ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) w).toReal) z ≠ 0 := by
    rw [eventually_iff, mem_ae_iff]
    refine measure_mono_null (fun t ht ↦ ?_)
      (hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume)
    rw [mem_compl_iff, mem_ofPred_eq] at ht
    push Not at ht
    obtain ⟨z, hzt, hfz⟩ := ht
    exact ⟨z, hfz, hzt⟩
  filter_upwards [hae_Φfin, hae_Hfin, hae_crit_h, hae_reg_v] with t h1 h2 h3 h4 htpos
  exact ⟨h1 htpos, h2 htpos, h3, h4⟩

/-- Core Lipschitz Pólya–Szegő inequality on a nontrivial space for nonnegative `h` whose positive
superlevel sets have finite volume, and `Φ` convex and monotone on `[0, ∞)` with `Φ 0 = 0`. -/
private theorem lintegral_ofReal_map_norm_fderiv_le_core [Nontrivial E] {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (h0 : ∀ x, 0 ≤ h x) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)) ∞ with htop | hInt_ne
  · exact htop ▸ le_top
  have hv : LipschitzWith K (fun z ↦
      (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) :=
    TauCeti.lipschitzWith_toReal_schwarzRearrangement volume hh
  have hne := TauCeti.schwarzRearrangement_ofReal_ne_top volume hh (hfin 1 one_pos)
  have hco (w : E → ℝ) (hw : ∀ x, 0 ≤ w x) :=
    MeasureTheory.lintegral_ofReal_eq_setLIntegral_Ioi_fiber (w := w) hw
      (hΦm.measurable_comp (measurable_fderiv ℝ w).norm fun _ ↦ norm_nonneg _)
      (ae_of_all _ fun _ h0 ↦ by simp [h0, hΦ0])
  rw [hco h h0] at hInt_ne
  rw [hco _ (fun _ ↦ ENNReal.toReal_nonneg), hco h h0]
  have hRh : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [ae_level_conditions_of_lipschitzWith hh hfin hΦm hInt_ne,
    hh.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hv.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin,
    MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin]
    with t hlev hperh hperv hmv hmh (htpos : 0 < t)
  obtain ⟨hΦt, hHt, hcrith, hregv⟩ := hlev htpos
  have hRh_eq : μHE[finrank ℝ E - 1] (h ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [← measure_inter_add_sdiff (h ⁻¹' {t}) hRh, inter_comm (h ⁻¹' {t})]
    have hdiff : h ⁻¹' {t} \ {x | fderiv ℝ h x ≠ 0} = {x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t} := by
      ext x; simp [and_comm]
    rw [hdiff, hcrith, add_zero]
  have hPv_le : μHE[finrank ℝ E - 1] ((fun z ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t}) ≤
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [← hRh_eq, ← hperv, ← hperh]
    have hvset : {x | t < (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) x).toReal} =
        {x | ENNReal.ofReal t < TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) x} := by
      ext x; exact (ENNReal.ofReal_lt_iff_lt_toReal htpos.le (hne x)).symm
    have hhset : {x | t < h x} = {x | ENNReal.ofReal t < ENNReal.ofReal (h x)} := by
      ext x; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg htpos.le).symm
    have hnm : NullMeasurableSet {x | ENNReal.ofReal t < ENNReal.ofReal (h x)} := by
      rw [← hhset]
      exact (isOpen_lt continuous_const hh.continuous).measurableSet.nullMeasurableSet
    rw [hvset, hhset]
    exact hnm.perimeter_setOf_lt_schwarzRearrangement_le
  exact fiber_le_of_level_bounds hv.continuous.measurable hΦ hΦm hΦ0
    (fun z w hzw ↦ ENNReal.toReal_mono (hne z)
      (TauCeti.schwarzRearrangement_le_of_norm_le volume _ hzw))
    hregv hPv_le (hRh_eq ▸ hHt) (hmv htpos) (hmh htpos) hΦt

/-- For `S = {s ≥ 0 | volume {h > s} ≠ ∞}` and `c = sInf S`, shifting `h` at `c` commutes with
extended Schwarz rearrangement up to `+ ENNReal.ofReal c`. -/
private theorem schwarzRearrangement_ofReal_eq_add_sInf [Nontrivial E] (h : E → ℝ) (x : E) :
    TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x =
      TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (max (h y - sInf {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}) 0))
        x + ENNReal.ofReal (sInf {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}) := by
  set S : Set ℝ := {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}
  set c := sInf S
  have hSbdd : BddBelow S := ⟨0, fun _ hs ↦ hs.1⟩
  have hc0 : 0 ≤ c := Real.sInf_nonneg fun _ hs ↦ hs.1
  rw [← congrFun (TauCeti.schwarzRearrangement_add_const volume _ _) x]
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [TauCeti.lt_schwarzRearrangement_iff, TauCeti.lt_schwarzRearrangement_iff]
  rcases lt_or_ge t (ENNReal.ofReal c) with htc | hct
  · have ht_fin : t ≠ ∞ := (lt_trans htc ENNReal.ofReal_lt_top).ne
    have htr_not : t.toReal ∉ S := notMem_of_lt_csInf (ENNReal.toReal_lt_of_lt_ofReal htc) hSbdd
    have hvol : volume {y | t < ENNReal.ofReal (h y)} = ∞ := by
      have hvol' : volume {y | t.toReal < h y} = ∞ := by
        by_contra hne
        exact htr_not ⟨ENNReal.toReal_nonneg, hne⟩
      convert hvol' using 2
      ext y
      conv_lhs => rw [← ENNReal.ofReal_toReal ht_fin]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg
    have huniv : {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} = univ :=
      eq_univ_of_forall fun _ ↦ htc.trans_le le_add_self
    rw [hvol, huniv, measure_univ_of_isAddLeftInvariant]
  · rcases eq_or_ne t ∞ with rfl | ht_fin
    · simp
    · suffices {y | t < ENNReal.ofReal (h y)} =
          {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} by rw [this]
      ext y
      simp only [mem_ofPred_eq]
      rw [← ENNReal.ofReal_add (le_max_right _ _) hc0, ← ENNReal.ofReal_toReal ht_fin]
      have hcs : c ≤ t.toReal := (ENNReal.ofReal_le_iff_le_toReal ht_fin).1 hct
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      grind

/-- Removing the finite-superlevel-measure and sign hypotheses for convex nondecreasing `Φ` with
`Φ 0 = 0` by shifting `h` at the infimum `c` of nonnegative levels with finite superlevel volume
(or noting `h* = 0` when all nonnegative superlevel volumes are `∞`). -/
private theorem lintegral_ofReal_map_norm_fderiv_le_of_monotoneOn [Nontrivial E] {K : ℝ≥0}
    {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  let S : Set ℝ := {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}
  rcases S.eq_empty_or_nonempty with hSempty | hSne
  · have htop_all (x : E) :
        TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x = ∞ := by
      by_contra hne
      have hlt : TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x <
          TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x := by
        rw [TauCeti.lt_schwarzRearrangement_iff]
        set r := (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal
        have hvol' : volume {y | r < h y} = ∞ := by
          by_contra hfin
          exact (hSempty ▸ notMem_empty r) ⟨ENNReal.toReal_nonneg, hfin⟩
        have hset : {y | TauCeti.schwarzRearrangement volume (fun z ↦ ENNReal.ofReal (h z)) x <
            ENNReal.ofReal (h y)} = {y | r < h y} := by
          ext y
          conv_lhs => rw [← ENNReal.ofReal_toReal hne]
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg
        rw [hset, hvol']
        exact measure_ball_lt_top
      exact lt_irrefl _ hlt
    simp [htop_all, hΦ0]
  · set c := sInf S
    have hSbdd : BddBelow S := ⟨0, fun _ hs ↦ hs.1⟩
    have hc0 : 0 ≤ c := Real.sInf_nonneg fun _ hs ↦ hs.1
    let hc_fun : E → ℝ := fun x ↦ max (h x - c) 0
    have hhc_lip : LipschitzWith K hc_fun :=
      (LipschitzWith.of_dist_le_mul fun x y ↦ by
        simpa [dist_sub_right] using hh.dist_le_mul x y).max_const 0
    have hhc_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hc_fun x} ≠ ∞ := by
      obtain ⟨s, hsS, hsc⟩ := (csInf_lt_iff hSbdd hSne).1 (lt_add_of_pos_right c ht)
      refine ne_top_of_le_ne_top hsS.2 (measure_mono fun x hx ↦ ?_)
      simp only [hc_fun, mem_ofPred_eq] at hx ⊢
      grind
    have hhc_ne := TauCeti.schwarzRearrangement_ofReal_ne_top volume hhc_lip (hhc_fin 1 one_pos)
    have hval_eq : (fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) =
        fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (hc_fun y)) z).toReal + c := by
      ext z
      rw [schwarzRearrangement_ofReal_eq_add_sInf h z,
        ENNReal.toReal_add (hhc_ne z) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc0]
    simp_rw [hval_eq, fderiv_add_const]
    refine (lintegral_ofReal_map_norm_fderiv_le_core hhc_lip (fun _ ↦ le_max_right _ _)
      hhc_fin hΦ hΦm hΦ0).trans (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (hΦm (norm_nonneg _) (norm_nonneg _) ?_))
    simp only [hc_fun]
    rw [TauCeti.fderiv_max_const_eq_indicator]
    refine (norm_indicator_le_norm_self _ x).trans_eq ?_
    rw [fderiv_sub_const]

/-- Lebesgue-`volume` form of the Lipschitz convex-integrand Pólya–Szegő inequality. -/
private theorem lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_volume_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine le_of_eq (lintegral_congr fun x ↦ ?_)
    rw [@Subsingleton.elim (E →L[ℝ] ℝ) (by infer_instance) (fderiv ℝ _ x) 0,
      @Subsingleton.elim (E →L[ℝ] ℝ) (by infer_instance) (fderiv ℝ h x) 0]
  let Ψ : ℝ → ℝ := fun s ↦ max (Φ s) 0
  have hΨ_ofReal (r : ℝ) : ENNReal.ofReal (Φ r) = ENNReal.ofReal (Ψ r) := by
    simp [Ψ, ENNReal.ofReal_max]
  have hΨ0 : Ψ 0 = 0 := max_eq_right hΦ0
  have hΨ_conv : ConvexOn ℝ (Ici 0) Ψ := hΦ.sup (convexOn_const 0 (convex_Ici 0))
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := by
    simpa only [inter_self] using hΦ.monotoneOn_max_const (mem_Ici.2 le_rfl) hΦ0
  simp_rw [hΨ_ofReal]
  exact lintegral_ofReal_map_norm_fderiv_le_of_monotoneOn hh hΨ_conv hΨ_mono hΨ0

/-- **Convex-integrand Pólya–Szegő inequality for Lipschitz functions.** For any additive Haar
measure `μ` on `E`, any `K`-Lipschitz function `h : E → ℝ`, and any `Φ : ℝ → ℝ` convex on `[0, ∞)`
with `Φ 0 ≤ 0`, the real Schwarz rearrangement `h*` of the positive part of `h` satisfies
`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ`. -/
theorem lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le
    (μ : Measure E) [μ.IsAddHaarMeasure] {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) ∂μ := by
  have hc₀ : (Measure.addHaarScalarFactor μ volume : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hrearr : TauCeti.schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) =
      TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) := by
    rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def,
      TauCeti.schwarzRearrangement_smul_measure volume hc₀ ENNReal.coe_ne_top]
  rw [hrearr]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def]
  conv_rhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume, ENNReal.smul_def]
  rw [lintegral_smul_measure, lintegral_smul_measure]
  exact mul_le_mul_right
    (lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_volume_le hh hΦ hΦ0) _

/-- **Integrability in the Lipschitz convex-integrand Pólya–Szegő inequality.** For any additive
Haar measure `μ`, if `h` is `K`-Lipschitz and `Φ` is convex and nondecreasing on `[0, ∞)` with
`Φ 0 = 0`, integrability of `x ↦ Φ ‖fderiv ℝ h x‖` under `μ` implies integrability of
`x ↦ Φ ‖fderiv ℝ h* x‖` under `μ`, where `h*` is the real Schwarz rearrangement of the positive part
of `h`. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement
    {μ : Measure E} [μ.IsAddHaarMeasure] {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) μ) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ (fun z ↦
      (TauCeti.schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) μ := by
  have hnonneg (w : E → ℝ) (x : E) : 0 ≤ Φ ‖fderiv ℝ w x‖ :=
    hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)
  refine (lintegral_ofReal_ne_top_iff_integrable
    (hΦm.measurable_comp (measurable_fderiv ℝ _).norm
      fun _ ↦ norm_nonneg _).aestronglyMeasurable
    (ae_of_all _ (hnonneg _))).1 ?_
  refine ne_top_of_le_ne_top ((lintegral_ofReal_ne_top_iff_integrable
    hint.aestronglyMeasurable (ae_of_all _ (hnonneg h))).2 hint) ?_
  exact hh.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le μ hΦ hΦ0.le

/-- **Bochner-integral Pólya–Szegő inequality for Lipschitz functions.** For any additive Haar
measure `μ`, `K`-Lipschitz `h`, and convex nondecreasing `Φ` on `[0, ∞)` with `Φ 0 = 0`, if
`x ↦ Φ ‖fderiv ℝ h x‖` is `μ`-integrable and `h*` denotes the real Schwarz rearrangement of the
positive part of `h`, then `∫ x, Φ ‖fderiv ℝ h* x‖ ∂μ ≤ ∫ x, Φ ‖fderiv ℝ h x‖ ∂μ`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le
    {μ : Measure E} [μ.IsAddHaarMeasure] {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) μ) :
    ∫ x, Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement μ (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ∂μ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ ∂μ := by
  have hnonneg (w : E → ℝ) (x : E) : 0 ≤ Φ ‖fderiv ℝ w x‖ :=
    hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)
  have hint' := hh.integrable_map_norm_fderiv_toReal_schwarzRearrangement hΦ hΦm hΦ0 hint
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnonneg _)) hint'.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnonneg h)) hint.aestronglyMeasurable]
  exact ENNReal.toReal_mono
    ((lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable
      (ae_of_all _ (hnonneg h))).2 hint)
    (hh.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le μ hΦ hΦ0.le)

end LipschitzWith
