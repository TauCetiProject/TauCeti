/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Subgraph

/-!
# Equality in Steiner's perimeter inequality

Let `s` be a Lebesgue-measurable set of finite volume in a finite-dimensional real inner product
space `E`, and let `e` be a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`. Write
`D = {y ∈ H | 0 < |s_y|}` for the transverse projection of positive-length line sections
`s_y = {t ∈ ℝ | y + t • e ∈ s}`, and `v(y) = |s_y|` for the real section length. For any
null-measurable family `A ⊆ H` of noninterval sections (sections that do not agree almost
everywhere with any interval), the perimeter deficit between `s` and its Steiner symmetral `S s`
controls `|A|²`:

`(2 |D| + |Dv|) P(S s) + 4 |A|² ≤ (2 |D| + |Dv|) P(s)`

(`MeasureTheory.NullMeasurableSet.mul_perimeter_steinerSymmetrization_add_four_mul_sq_le`), and in
the coordinate-free form using `2 |D| + |Dv| ≤ 2 P(s)`,

`P(s) P(S s) + 2 |A|² ≤ P(s)²`

(`MeasureTheory.NullMeasurableSet.perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le`).
Both inequalities hold for finite or infinite ambient perimeter and in every positive dimension.
Consequently, if `s` has finite perimeter and `P(S s) = P(s)`, then almost every line section of
`s` along `e` agrees almost everywhere with an interval
(`NullMeasurableSet.ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq`).
Finite ambient perimeter is necessary for the equality conclusion: a set of infinite perimeter whose
noninterval sections still give a symmetral of infinite perimeter satisfies `P(S s) = P(s)`.

## Strategy

For a shrinking family of radial smooth mollifiers `κ_j` on `H`, put `w_j = κ_j ⋆ v`,
`d_j = κ_j ⋆ (2 · 1_D)`, and `a_j = κ_j ⋆ 1_A`. By the mollified slicing excess inequality
(`MeasureTheory.NullMeasurableSet.mul_integral_sqrt_normed_convolution_add_two_mul_sq_le`),

`M ∫ √(d_j² + ‖∇w_j‖²) + 2 (∫ a_j √d_j)² ≤ M P(s)`,

where `M = 2 |D| + |Dv|`. On the other hand, the smooth symmetric subgraph perimeter upper bound
(`TauCeti.perimeter_setOf_abs_inner_lt_div_two_le`) applied to `w_j - ε` bounds the perimeter of
`{|⟪e, x⟫| < (w_j(y) - ε) / 2}` above by `∫_{w_j > ε} √(4 + ‖∇w_j‖²)`, which compares with
`∫ √(d_j² + ‖∇w_j‖²)` up to the `L¹` error `∫ |2 · 1_{w_j > ε} - d_j|`. Passing to a subsequence
along which `{w_j > ε} → {v > ε}` in measure for almost every `ε > 0`
(`MeasureTheory.Measure.exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt`), taking `j → ∞`
and then `ε → 0⁺`, lower semicontinuity of the perimeter concludes.

## References

* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), §1.2 and Theorem 1.1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
-/

public section

noncomputable section

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Set TauCeti
  TopologicalSpace
open scoped Convolution ENNReal RealInnerProductSpace Topology symmDiff

namespace MeasureTheory.NullMeasurableSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Quantitative Steiner perimeter excess inequality.** Let `s` be a Lebesgue-measurable set of
finite volume, `e` a unit vector with orthogonal hyperplane `H = (ℝ ∙ e)ᗮ`, and `A ⊆ H` a
null-measurable family of noninterval line sections of `s`. Writing
`D = {y ∈ H | 0 < |s_y|}` and `v(y) = |s_y|`, we have

`(2 |D| + |Dv|) P(S_e s) + 4 |A|² ≤ (2 |D| + |Dv|) P(s)`,

whether the ambient perimeter `P(s)` is finite or infinite. -/
theorem mul_perimeter_steinerSymmetrization_add_four_mul_sq_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    (2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) *
        perimeter volume ⊤ (steinerSymmetrization e he s) + 4 * volume A ^ 2 ≤
      (2 * volume {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} +
        totalVariationOn volume ⊤
          (fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s})) *
        perimeter volume ⊤ s := by
  let H := (ℝ ∙ e)ᗮ
  let D : Set H := {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  let v : H → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let fD : H → ℝ := D.indicator (fun _ ↦ 2)
  let fA : H → ℝ := A.indicator (fun _ ↦ 1)
  -- Handle infinite ambient perimeter: then `volume s ≠ 0`, so `volume D ≠ 0` and RHS = ∞.
  by_cases hP : perimeter volume ⊤ s = ∞
  · have hD0 : volume D ≠ 0 := fun hD0 ↦ by
      have hs0 : volume s = 0 := by
        rw [volume_eq_lintegral_volume_lineSection e he hs,
          lintegral_eq_zero_iff' (aemeasurable_volume_lineSection e he hs)]
        have hD0' : ∀ᵐ y : H ∂volume, ¬0 < volume {t : ℝ | (y : E) + t • e ∈ s} :=
          ae_iff.2 (by simpa only [not_not] using hD0)
        filter_upwards [hD0'] with y hy
        exact nonpos_iff_eq_zero.1 (not_lt.1 hy)
      rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 hs0)), perimeter_empty] at hP
      exact ENNReal.zero_ne_top hP
    rw [hP, ENNReal.mul_top fun h0 ↦
      hD0 ((mul_eq_zero.1 (add_eq_zero.1 h0).1).resolve_left (by norm_num))]
    exact le_top
  -- Finite ambient perimeter: set up `D`, `A`, `v`, and a shrinking mollifier subsequence.
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_le := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_self_add.trans hDA_le)
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_add_self.trans hDA_le)
  have hv_tv_fin : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hv_int : Integrable v volume :=
    ⟨(aemeasurable_volume_lineSection e he hs).ennreal_toReal.aestronglyMeasurable,
      (lintegral_mono fun y ↦ by
        rw [Real.eNorm_of_nonneg measureReal_nonneg, measureReal_def]
        exact ENNReal.ofReal_toReal_le).trans_lt
        ((volume_eq_lintegral_volume_lineSection e he hs).symm ▸ hfin.lt_top)⟩
  have hD_ind_int : Integrable fD volume := (integrableOn_const hDfin).integrable_indicator₀ hD
  have hAD : ∀ᵐ y : H ∂volume, y ∈ A → y ∈ D := by
    filter_upwards [hbad] with y hy hyA
    by_contra hyD
    exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
  let M : ℝ := 2 * volume.real D + (totalVariationOn volume ⊤ v).toReal
  have hM_nonneg : 0 ≤ M := by positivity
  have hM_ofReal : ENNReal.ofReal M = 2 * volume D + totalVariationOn volume ⊤ v := by
    rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat, ofReal_measureReal hDfin, ENNReal.ofReal_toReal hv_tv_fin]
  have hA_ofReal : ENNReal.ofReal (4 * volume.real A ^ 2) = 4 * volume A ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal hAfin]
  have hq_qmp : QuasiMeasurePreserving
      (fun x : E ↦ ((orthogonalLineEquiv e he).symm x).1) volume volume :=
    Measure.quasiMeasurePreserving_fst.comp
      (MeasurePreserving.symm (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv
        (measurePreserving_orthogonalLineEquiv e he)).quasiMeasurePreserving
  let S_trunc : ℝ → Set E := fun ε ↦
    {x : E | |⟪e, x⟫_ℝ| < (v ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
  have hS_trunc_nm (ε : ℝ) : NullMeasurableSet (S_trunc ε) volume :=
    nullMeasurableSet_lt (continuous_const.inner continuous_id).abs.measurable.aemeasurable
      (((hv_int.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hq_qmp).sub
        aemeasurable_const).div_const 2)
  have hlsc {t : ℕ → Set E} {u : Set E} (ht : ∀ k, NullMeasurableSet (t k) volume)
      (hu : NullMeasurableSet u volume)
      (hlim : Tendsto (fun k ↦ volume (t k ∆ u)) atTop (𝓝 0)) :
      perimeter volume ⊤ u ≤ liminf (fun k ↦ perimeter volume ⊤ (t k)) atTop :=
    perimeter_le_liminf (.of_forall ht) hu fun _ _ _ ↦
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
        fun _ ↦ measure_mono inter_subset_left
  have hlim_mul_add {m p c l : ℝ≥0∞} {u vseq r : ℕ → ℝ≥0∞}
      (hp : p ≤ liminf u atTop) (hc : c ≤ liminf vseq atTop)
      (hle : ∀ k, m * u k + vseq k ≤ r k) (hr : Tendsto r atTop (𝓝 l)) : m * p + c ≤ l :=
    calc m * p + c ≤ m * liminf u atTop + c := by gcongr
      _ ≤ liminf (fun k ↦ m * u k) atTop + liminf vseq atTop := by
          refine add_le_add ?_ hc
          simpa only [liminf_const, Pi.mul_def] using
            ENNReal.le_liminf_mul (u := fun _ : ℕ ↦ m) (v := u) (f := atTop)
      _ ≤ liminf (fun k ↦ m * u k + vseq k) atTop := ENNReal.le_liminf_add _ _
      _ ≤ liminf r atTop := liminf_le_liminf (.of_forall hle)
      _ = l := hr.liminf_eq
  -- Pass to a shrinking subsequence along which `{w j > ε} → {v > ε}` in measure for a.e. `ε`.
  let ρ₀ : ℕ → ContDiffBump (0 : H) := ContDiffBump.shrinking one_pos
  have hρ₀_lim : Tendsto (fun j ↦ (ρ₀ j).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  obtain ⟨ns, hns, hlevel_ae⟩ :=
    volume.exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt
      (f := fun j ↦ (ρ₀ j).normed volume ⋆[lsmul ℝ ℝ, volume] v)
      (fun j ↦ ((ρ₀ j).integrable_normed.integrable_convolution _
        hv_int).aestronglyMeasurable.aemeasurable)
      hv_int.aestronglyMeasurable.aemeasurable
      (tendsto_lintegral_enorm_normed_convolution_sub hρ₀_lim hv_int)
  let ρ : ℕ → ContDiffBump (0 : H) := fun j ↦ ρ₀ (ns j)
  have hρ_lim : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0) := hρ₀_lim.comp hns.tendsto_atTop
  -- Step 1: For any `ε > 0` with `{w j > ε} → {v > ε}` in measure, pass to `j → ∞`.
  have hstep_eps {ε : ℝ} (hε : 0 < ε)
      (hEj_lim : Tendsto (fun j ↦ volume ({y : H | ε < ((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] v)
          y} ∆ {y : H | ε < v y})) atTop (𝓝 0)) :
      ENNReal.ofReal M * perimeter volume ⊤ (S_trunc ε) + 4 * volume A ^ 2 ≤
        ENNReal.ofReal M * perimeter volume ⊤ s +
          ENNReal.ofReal (M * (2 * volume.real (D \ {y : H | ε < v y}))) := by
    let d : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fD
    let w : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] v
    let a : ℕ → H → ℝ := fun j ↦ (ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] fA
    let Sj : ℕ → Set E := fun j ↦
      {x : E | |⟪e, x⟫_ℝ| < (w j ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
    let Ej : ℕ → Set H := fun j ↦ {y : H | ε < w j y}
    let Eε : Set H := {y : H | ε < v y}
    let fEj : ℕ → H → ℝ := fun j ↦ (Ej j).indicator (fun _ ↦ 2)
    let fEε : H → ℝ := Eε.indicator (fun _ ↦ 2)
    have hw_smooth (j : ℕ) : ContDiff ℝ 1 (w j) :=
      (ρ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        ((ρ j).contDiff_normed (n := 1)) hv_int.locallyIntegrable
    have hw_int (j : ℕ) : Integrable (w j) volume :=
      (ρ j).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hv_int
    have hd_int (j : ℕ) : Integrable (d j) volume :=
      (ρ j).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hD_ind_int
    have hd_mem (j : ℕ) (y : H) : d j y ∈ Icc (0 : ℝ) 2 :=
      (ρ j).normed_convolution_mem_Icc hD_ind_int.locallyIntegrable
        (fun z ↦ by by_cases hz : z ∈ D <;> simp [fD, hz]) y
    have hEj_m (j : ℕ) : MeasurableSet (Ej j) :=
      measurableSet_lt measurable_const (hw_smooth j).continuous.measurable
    have hEε_nm : NullMeasurableSet Eε volume :=
      nullMeasurableSet_lt aemeasurable_const hv_int.aestronglyMeasurable.aemeasurable
    have hEj_fin (j : ℕ) : volume (Ej j) ≠ ∞ :=
      ne_top_of_le_ne_top ((hw_int j).measure_ge_lt_top hε).ne <|
        measure_mono fun _ (hy : ε < w j _) ↦ hy.le
    have hSj_nm (j : ℕ) : NullMeasurableSet (Sj j) volume :=
      (measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
        ((((hw_smooth j).continuous.comp (continuous_fst.comp
          (orthogonalLineEquiv e he).symm.continuous)).sub continuous_const).div_const
          2).measurable).nullMeasurableSet
    -- Combine the smooth subgraph bound and the mollified slicing excess bound for each `j`.
    have hper_j (j : ℕ) :
        ENNReal.ofReal M * perimeter volume ⊤ (Sj j) +
            ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2) ≤
          ENNReal.ofReal M * perimeter volume ⊤ s +
            ENNReal.ofReal (M * ∫ y : H, |fEj j y - d j y|) := by
      have hgrad_int : Integrable (fun y : H ↦ ‖fderiv ℝ (w j) y‖) volume :=
        (ρ j).integrable_norm_fderiv_normed_convolution hv_int.locallyIntegrable hv_tv_fin
      have hsqrt_int : Integrable (fun y : H ↦ √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2)) volume := by
        refine ((hd_int j).add hgrad_int).mono'
          (Real.continuous_sqrt.comp ((((ρ j).hasCompactSupport_normed.continuous_convolution_left
            (lsmul ℝ ℝ) (ρ j).continuous_normed hD_ind_int.locallyIntegrable).pow 2).add
              (((hw_smooth j).continuous_fderiv one_ne_zero).norm.pow 2))).aestronglyMeasurable
          (.of_forall fun y ↦ ?_)
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact (Real.sqrt_le_left (add_nonneg (hd_mem j y).1 (opNorm_nonneg _))).2
          (by nlinarith [mul_nonneg (hd_mem j y).1 (opNorm_nonneg (fderiv ℝ (w j) y))])
      have hdiff_int : Integrable (fun y : H ↦ |fEj j y - d j y|) volume :=
        (((integrableOn_const (hEj_fin j)).integrable_indicator (hEj_m j)).sub (hd_int j)).abs
      have hsum_int : Integrable (fun y : H ↦ √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) +
          |fEj j y - d j y|) volume := hsqrt_int.add hdiff_int
      set I_sq := ∫ y : H, √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2)
      set I_err := ∫ y : H, |fEj j y - d j y|
      have hper_upper : perimeter volume ⊤ (Sj j) ≤ ENNReal.ofReal (I_sq + I_err) := by
        calc perimeter volume ⊤ (Sj j)
            ≤ ∫⁻ y in Ej j, ENNReal.ofReal √(4 + ‖fderiv ℝ (w j) y‖ ^ 2) := by
              have hsub := perimeter_setOf_abs_inner_lt_div_two_le e he
                ((hw_smooth j).sub (contDiff_const (c := ε)))
              simpa only [Ej, sub_pos,
                show ∀ y, fderiv ℝ (fun x ↦ w j x - ε) y = fderiv ℝ (w j) y from
                  fun _ ↦ fderiv_sub_const ε] using hsub
          _ ≤ ∫⁻ y : H, ENNReal.ofReal
                (√(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) + |fEj j y - d j y|) := by
              rw [← lintegral_indicator (hEj_m j)]
              refine lintegral_mono fun y ↦ ?_
              by_cases hy : y ∈ Ej j
              · rw [indicator_of_mem hy]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [show fEj j y = 2 from indicator_of_mem hy _,
                  Real.sqrt_le_left (by positivity)]
                have hsq : √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) ^ 2 =
                    d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2 := Real.sq_sqrt (by positivity)
                have hble : d j y ≤ √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) :=
                  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
                have hcross : d j y * (2 - d j y) ≤
                    |2 - d j y| * √(d j y ^ 2 + ‖fderiv ℝ (w j) y‖ ^ 2) :=
                  (mul_le_mul_of_nonneg_left (le_abs_self _) (hd_mem j y).1).trans <|
                    (mul_comm (d j y) _).le.trans
                      (mul_le_mul_of_nonneg_left hble (abs_nonneg _))
                nlinarith [hsq, (sq_abs (2 - d j y)).symm, hcross]
              · rw [indicator_of_notMem hy]; exact zero_le
          _ = ENNReal.ofReal (I_sq + I_err) := by
              rw [← integral_add hsqrt_int hdiff_int, ofReal_integral_eq_lintegral_ofReal hsum_int
                (.of_forall fun _ ↦ add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
      have hmoll := hs.mul_integral_sqrt_normed_convolution_add_two_mul_sq_le hfin hP e he hA
        hbad (ρ j)
      calc ENNReal.ofReal M * perimeter volume ⊤ (Sj j) +
              ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2)
          ≤ ENNReal.ofReal M * ENNReal.ofReal (I_sq + I_err) +
              ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2) := by gcongr
        _ = ENNReal.ofReal (M * I_sq + 2 * (∫ y : H, a j y * √(d j y)) ^ 2 + M * I_err) := by
            rw [← ENNReal.ofReal_mul hM_nonneg, ← ENNReal.ofReal_add
              (mul_nonneg hM_nonneg (add_nonneg (integral_nonneg fun _ ↦ Real.sqrt_nonneg _)
                (integral_nonneg fun _ ↦ abs_nonneg _))) (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (M * (perimeter volume ⊤ s).toReal + M * I_err) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal M * perimeter volume ⊤ s + ENNReal.ofReal (M * I_err) := by
            rw [ENNReal.ofReal_add (mul_nonneg hM_nonneg ENNReal.toReal_nonneg)
                (mul_nonneg hM_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)),
              ENNReal.ofReal_mul hM_nonneg, ENNReal.ofReal_toReal hP]
    -- Limit 1: `Sj j → S_trunc ε` in `L¹`, so `P(S_trunc ε) ≤ liminf P(Sj j)`.
    have hSj_lim : Tendsto (fun j ↦ volume (Sj j ∆ S_trunc ε)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_lintegral_enorm_normed_convolution_sub hρ_lim hv_int) (fun _ ↦ zero_le) fun j ↦ ?_
      rw [volume_eq_lintegral_volume_lineSection e he ((hSj_nm j).symmDiff (hS_trunc_nm ε))]
      refine lintegral_mono fun y ↦ ?_
      have hsymm_sec : {t : ℝ | (y : E) + t • e ∈ Sj j ∆ S_trunc ε} =
          Metric.eball (0 : ℝ) (ENNReal.ofReal (w j y - ε) / 2) ∆
            Metric.eball (0 : ℝ) (ENNReal.ofReal (v y - ε) / 2) := by
        rw [← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ w j z - ε) y,
          ← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ v z - ε) y]
        ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq, Sj, S_trunc]
      rw [hsymm_sec]
      refine (volume_eball_ofReal_symmDiff_le (w j y - ε) (v y - ε)).trans_eq ?_
      rw [sub_sub_sub_cancel_right, Real.eNorm_eq_ofReal_abs]
    -- Limit 2: `2 (∫ a j √(d j))² → 4 |A|²`.
    have ha_sq_lim : Tendsto (fun j ↦ ENNReal.ofReal (2 * (∫ y : H, a j y * √(d j y)) ^ 2))
        atTop (𝓝 (4 * volume A ^ 2)) := by
      have hreal : Tendsto (fun j ↦ 2 * (∫ y : H, a j y * √(d j y)) ^ 2) atTop
          (𝓝 (4 * volume.real A ^ 2)) := by
        have := ((tendsto_integral_mul_sqrt_normed_convolution hρ_lim hA hD hAfin hDfin hAD).pow
          2).const_mul 2
        rwa [show 2 * (√2 * volume.real A) ^ 2 = 4 * volume.real A ^ 2 by
          rw [mul_pow, Real.sq_sqrt zero_le_two]; ring] at this
      simpa only [hA_ofReal] using ENNReal.tendsto_ofReal hreal
    -- Limit 3: `limsup ∫ |2 · 1_{Ej j} - d j| ≤ 2 |D \ Eε|`.
    have hEε_sub_D : Eε ⊆ D := fun y (hy : ε < v y) ↦ by
      dsimp only [D, mem_ofPred_eq]
      exact pos_iff_ne_zero.2 fun h0 ↦ (hε.trans hy).ne' (by simp [v, measureReal_def, h0])
    have herr_upper (j : ℕ) :
        ∫ y : H, |fEj j y - d j y| ≤
          2 * volume.real (Ej j ∆ Eε) + 2 * volume.real (D \ Eε) + ∫ y : H, |fD y - d j y| := by
      have hfEj_int : Integrable (fEj j) volume :=
        (integrableOn_const (hEj_fin j)).integrable_indicator (hEj_m j)
      have hfEε_int : Integrable fEε volume :=
        (integrableOn_const (ne_top_of_le_ne_top hDfin
          (measure_mono hEε_sub_D))).integrable_indicator₀ hEε_nm
      have hi1 : Integrable (fun y : H ↦ |fEj j y - fEε y|) volume := (hfEj_int.sub hfEε_int).abs
      have hi2 : Integrable (fun y : H ↦ |fEε y - fD y|) volume := (hfEε_int.sub hD_ind_int).abs
      have hi12 : Integrable (fun y : H ↦ |fEj j y - fEε y| + |fEε y - fD y|) volume := hi1.add hi2
      have hi3 : Integrable (fun y : H ↦ |fD y - d j y|) volume := (hD_ind_int.sub (hd_int j)).abs
      have hI1 : ∫ y : H, |fEj j y - fEε y| = 2 * volume.real (Ej j ∆ Eε) := by
        rw [show (fun y : H ↦ |fEj j y - fEε y|) = (Ej j ∆ Eε).indicator (fun _ ↦ (2 : ℝ)) from
            funext fun y ↦ by by_cases h1 : y ∈ Ej j <;> by_cases h2 : y ∈ Eε <;>
              simp [fEj, fEε, Set.mem_symmDiff, h1, h2],
          integral_indicator₀ ((hEj_m j).nullMeasurableSet.symmDiff hEε_nm),
          setIntegral_const, smul_eq_mul, mul_comm]
      have hI2 : ∫ y : H, |fEε y - fD y| = 2 * volume.real (D \ Eε) := by
        rw [show (fun y : H ↦ |fEε y - fD y|) = (D \ Eε).indicator (fun _ ↦ (2 : ℝ)) from
            funext fun y ↦ by by_cases h1 : y ∈ Eε <;> by_cases h2 : y ∈ D <;>
              first | exact absurd (hEε_sub_D h1) h2 | simp [fEε, fD, h1, h2],
          integral_indicator₀ (hD.diff hEε_nm), setIntegral_const, smul_eq_mul, mul_comm]
      calc ∫ y : H, |fEj j y - d j y|
          ≤ ∫ y : H, (|fEj j y - fEε y| + |fEε y - fD y| + |fD y - d j y|) :=
            integral_mono (hfEj_int.sub (hd_int j)).abs (hi12.add hi3) fun y ↦ by
              linarith [abs_sub_le (fEj j y) (fEε y) (d j y), abs_sub_le (fEε y) (fD y) (d j y)]
        _ = _ := by rw [integral_add hi12 hi3, integral_add hi1 hi2, hI1, hI2]
    have herr_lim : Tendsto (fun j ↦ ENNReal.ofReal (M * (2 * volume.real (Ej j ∆ Eε) +
        2 * volume.real (D \ Eε) + ∫ y : H, |fD y - d j y|)))
        atTop (𝓝 (ENNReal.ofReal (M * (2 * volume.real (D \ Eε))))) := by
      have hsymm_real : Tendsto (fun j ↦ volume.real (Ej j ∆ Eε)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEj_lim
      have hd_L1 : Tendsto (fun j ↦ ∫ y : H, |fD y - d j y|) atTop (𝓝 0) :=
        (tendsto_integral_abs_normed_convolution_sub hρ_lim hD_ind_int).congr
          fun j ↦ integral_congr_ae (.of_forall fun _ ↦ abs_sub_comm _ _)
      refine ENNReal.tendsto_ofReal (Tendsto.const_mul M ?_)
      simpa only [mul_zero, zero_add, add_zero] using
        ((hsymm_real.const_mul 2).add tendsto_const_nhds).add hd_L1
    exact hlim_mul_add (hlsc hSj_nm (hS_trunc_nm ε) hSj_lim) ha_sq_lim.liminf_eq.ge
      (fun j ↦ (hper_j j).trans (by gcongr; exact herr_upper j)) (herr_lim.const_add _)
  -- Step 2: Choose `ε k ∈ (0, 1 / (k + 1))` where `{w j > ε k} → {v > ε k}` and let `k → ∞`.
  have hex_eps (k : ℕ) : ∃ ε ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)),
      Tendsto (fun j ↦ volume ({y : H | ε < ((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] v) y} ∆
        {y : H | ε < v y})) atTop (𝓝 0) := by
    let bad : Set ℝ := {ε : ℝ | ¬Tendsto (fun j ↦ volume
      ({y : H | ε < ((ρ j).normed volume ⋆[lsmul ℝ ℝ, volume] v) y} ∆
        {y : H | ε < v y})) atTop (𝓝 0)}
    have hbad0 : volume bad = 0 := ae_iff.1 hlevel_ae
    obtain ⟨ε, hεI, hεgood⟩ : (Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) \ bad).Nonempty :=
      Set.nonempty_iff_ne_empty.2 fun hempty ↦ by
        have h0 := measure_mono_null (Set.sdiff_eq_empty.1 hempty) hbad0
        rw [Real.volume_Ioo, sub_zero] at h0
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne' h0
    exact ⟨ε, hεI, not_not.1 hεgood⟩
  choose ε hε_mem hε_level using hex_eps
  have hε_lim : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hε_mem k).1.le) (fun k ↦ (hε_mem k).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hS_lim : Tendsto (fun k ↦ volume (S_trunc (ε k) ∆ steinerSymmetrization e he s))
      atTop (𝓝 0) := by
    have hdom : Tendsto (fun k ↦ ∫⁻ y : H, ENNReal.ofReal (min (v y) (ε k))) atTop (𝓝 0) := by
      rw [← lintegral_zero (μ := (volume : Measure H))]
      refine tendsto_lintegral_of_dominated_convergence' (fun y ↦ ENNReal.ofReal (v y))
        (fun k ↦ (hv_int.aestronglyMeasurable.aemeasurable.min aemeasurable_const).ennreal_ofReal)
        (fun k ↦ .of_forall fun y ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))
        (ne_top_of_le_ne_top hv_int.2.ne (lintegral_mono fun y ↦ by
          rw [Real.eNorm_of_nonneg measureReal_nonneg]))
        (.of_forall fun y ↦ by
          simpa only [ENNReal.ofReal_zero,
            min_eq_right (show (0 : ℝ) ≤ v y from measureReal_nonneg)] using
            ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := v y)).min hε_lim))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom (fun _ ↦ zero_le)
      fun k ↦ ?_
    rw [volume_eq_lintegral_volume_lineSection e he
      ((hS_trunc_nm (ε k)).symmDiff (nullMeasurableSet_steinerSymmetrization e he hs))]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin
    have hsymm_sec : {t : ℝ | (y : E) + t • e ∈ S_trunc (ε k) ∆ steinerSymmetrization e he s} =
        Metric.eball (0 : ℝ) (ENNReal.ofReal (max (v y - ε k) 0) / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal (v y) / 2) := by
      have hofmax : ENNReal.ofReal (v y - ε k) = ENNReal.ofReal (max (v y - ε k) 0) := by
        rcases le_or_gt (v y - ε k) 0 with hle | hgt
        · rw [max_eq_right hle, ENNReal.ofReal_of_nonpos hle, ENNReal.ofReal_zero]
        · rw [max_eq_left hgt.le]
      rw [← hofmax, ← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ v z - ε k) y,
        show ENNReal.ofReal (v y) = volume {t : ℝ | (y : E) + t • e ∈ s} from
          ofReal_measureReal hyfin.ne, ← lineSection_steinerSymmetrization e he]
      ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq, S_trunc]
    rw [hsymm_sec]
    refine (volume_eball_ofReal_symmDiff_le (max (v y - ε k) 0) (v y)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rcases le_total (v y) (ε k) with hle | hge
    · rw [max_eq_right (sub_nonpos.2 hle), zero_sub, abs_neg, abs_of_nonneg measureReal_nonneg,
        min_eq_left hle]
    · rw [max_eq_left (sub_nonneg.2 hge), sub_sub_cancel_left, abs_neg,
        abs_of_pos (hε_mem k).1, min_eq_right hge]
  have hDdiff_lim : Tendsto (fun k ↦ volume (D \ {y : H | ε k < v y})) atTop (𝓝 0) := by
    let G : ℕ → Set H := fun k ↦ {y : H | 0 < v y ∧ v y ≤ 1 / ((k : ℝ) + 1)}
    have hGm (k : ℕ) : NullMeasurableSet (G k) volume :=
      (nullMeasurableSet_lt aemeasurable_const hv_int.aestronglyMeasurable.aemeasurable).inter
        (nullMeasurableSet_le hv_int.aestronglyMeasurable.aemeasurable aemeasurable_const)
    have hGanti : Antitone G := fun m n hmn _ hy ↦
      ⟨hy.1, hy.2.trans (one_div_le_one_div_of_le (by positivity) (by gcongr))⟩
    have hGfin : volume (G 0) ≠ ∞ :=
      ne_top_of_le_ne_top hDfin <| measure_mono fun y (hy : y ∈ G 0) ↦ by
        dsimp only [D, mem_ofPred_eq]
        exact pos_iff_ne_zero.2 fun h0 ↦ hy.1.ne' (by simp [v, measureReal_def, h0])
    have hGinter : (⋂ k, G k) = ∅ := eq_empty_of_forall_notMem fun y hy ↦ by
      simp only [mem_iInter, mem_ofPred_eq, G] at hy
      exact (hy 0).1.not_ge
        (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun k ↦ (hy k).2)
    have hGlim : Tendsto (fun k : ℕ ↦ volume (G k)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hGinter, measure_empty] using
        tendsto_measure_iInter_atTop hGm hGanti ⟨0, hGfin⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim
      (fun _ ↦ zero_le) fun k ↦ measure_mono_ae ?_
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin ⟨hyD, hnot⟩
    exact ⟨ENNReal.toReal_pos hyD.ne' hyfin.ne, (not_lt.1 hnot).trans (hε_mem k).2.le⟩
  have hDdiff_rhs : Tendsto (fun k ↦ ENNReal.ofReal M * perimeter volume ⊤ s +
      ENNReal.ofReal (M * (2 * volume.real (D \ {y : H | ε k < v y}))))
      atTop (𝓝 (ENNReal.ofReal M * perimeter volume ⊤ s)) := by
    have hreal : Tendsto (fun k ↦ volume.real (D \ {y : H | ε k < v y})) atTop (𝓝 0) := by
      simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDdiff_lim
    simpa only [mul_zero, ENNReal.ofReal_zero, add_zero] using
      (ENNReal.tendsto_ofReal ((hreal.const_mul 2).const_mul M)).const_add
        (ENNReal.ofReal M * perimeter volume ⊤ s)
  rw [← hM_ofReal]
  exact hlim_mul_add
    (hlsc (fun k ↦ hS_trunc_nm (ε k)) (nullMeasurableSet_steinerSymmetrization e he hs) hS_lim)
    (liminf_const _).ge (fun k ↦ hstep_eps (hε_mem k).1 (hε_level k)) hDdiff_rhs

/-- **Coordinate-free quantitative Steiner perimeter excess inequality.** For a Lebesgue-measurable
set `s` of finite volume, a unit vector `e`, and a null-measurable family `A ⊆ (ℝ ∙ e)ᗮ` of
noninterval line sections of `s`,

`P(s) P(S_e s) + 2 |A|² ≤ P(s)²`.

This holds whether `P(s)` is finite or infinite, in every positive dimension. -/
theorem perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ s * perimeter volume ⊤ (steinerSymmetrization e he s) +
        2 * volume A ^ 2 ≤
      perimeter volume ⊤ s ^ 2 := by
  by_cases hP : perimeter volume ⊤ s = ∞
  · rw [hP, ENNReal.top_pow two_ne_zero]; exact le_top
  set P := perimeter volume ⊤ s
  set PS := perimeter volume ⊤ (steinerSymmetrization e he s)
  set D : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  set v : (ℝ ∙ e)ᗮ → ℝ := fun y ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}
  set M := 2 * volume D + totalVariationOn volume ⊤ v
  have hDA_le := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hM_le : M ≤ 2 * P := by
    rw [two_mul]
    exact add_le_add (le_self_add.trans hDA_le)
      (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hM_fin : M ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hP) hM_le
  have hPS_le : PS ≤ P := perimeter_steinerSymmetrization_le e he hs hfin
  have hPS_fin : PS ≠ ∞ := ne_top_of_le_ne_top hP hPS_le
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top hP <|
    (le_self_add.trans_eq (two_mul _).symm).trans (le_add_self.trans hDA_le)
  have hreal : M.toReal * PS.toReal + 4 * volume.real A ^ 2 ≤ M.toReal * P.toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hM_fin hP)
      (hs.mul_perimeter_steinerSymmetrization_add_four_mul_sq_le hfin e he hA hbad)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top hM_fin hPS_fin)
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hAfin)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_pow] at h1
  have hM_le_real : M.toReal ≤ 2 * P.toReal := by
    simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hP) hM_le
  have hPS_le_real : PS.toReal ≤ P.toReal := ENNReal.toReal_mono hP hPS_le
  have hfinal_real : P.toReal * PS.toReal + 2 * volume.real A ^ 2 ≤ P.toReal ^ 2 := by
    nlinarith [ENNReal.toReal_nonneg (a := P), ENNReal.toReal_nonneg (a := PS),
      ENNReal.toReal_nonneg (a := M)]
  calc P * PS + 2 * volume A ^ 2
      = ENNReal.ofReal (P.toReal * PS.toReal + 2 * volume.real A ^ 2) := by
        rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (by positivity),
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hP,
          ENNReal.ofReal_toReal hPS_fin, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
          ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal hAfin]
    _ ≤ ENNReal.ofReal (P.toReal ^ 2) := ENNReal.ofReal_le_ofReal hfinal_real
    _ = P ^ 2 := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hP]

/-- **Equality in Steiner's perimeter inequality forces interval sections.** Let `s` be a
Lebesgue-measurable set of finite volume and finite perimeter, and let `e` be a unit vector. If
the Steiner symmetral of `s` along `e` has the same perimeter as `s`, then almost every line
section of `s` parallel to `e` agrees almost everywhere with an interval. -/
theorem ae_exists_ordConnected_lineSection_of_perimeter_steinerSymmetrization_eq
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  let A : Set (ℝ ∙ e)ᗮ := {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
    ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  have hineq := hs.perimeter_mul_perimeter_steinerSymmetrization_add_two_mul_sq_le
    hfin e he (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ ↦ id)
  rw [heq, ← sq] at hineq
  have hzero : 2 * volume A ^ 2 = 0 := nonpos_iff_eq_zero.1 <|
    WithTop.le_of_add_le_add_left (ENNReal.pow_ne_top hP) (hineq.trans_eq (add_zero _).symm)
  have hA0 : volume A = 0 := by
    simpa [sq] using (mul_eq_zero.1 hzero).resolve_left (by norm_num)
  rw [ae_iff]
  simpa [A] using hA0

end MeasureTheory.NullMeasurableSet

end
