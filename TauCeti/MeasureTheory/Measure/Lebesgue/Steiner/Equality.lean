/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.BoundedVariation.Slicing.MollifiedExcess
import TauCeti.Analysis.BoundedVariation.Subgraph
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.Analysis.Real.Sqrt
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.Continuity
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Perimeter

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
`s` along `e` agrees almost everywhere with an interval; see
`NullMeasurableSet.ae_exists_ordConnected_ae_eq_lineSection_of_perimeter_steinerSymmetrization_eq`.
Finite ambient perimeter is necessary for the equality conclusion: a set of infinite perimeter whose
noninterval sections still give a symmetral of infinite perimeter satisfies `P(S s) = P(s)`.

## Strategy

For a shrinking family of radial smooth mollifiers `κ_j` on `H`, put `w_j = κ_j ⋆ v`,
`d_j = κ_j ⋆ (2 · 1_D)`, and `a_j = κ_j ⋆ 1_A`. By the mollified slicing excess inequality
(`MeasureTheory.NullMeasurableSet.mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le`),

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

private noncomputable abbrev steinD {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (e : E) : Set (ℝ ∙ e)ᗮ :=
  {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}

private noncomputable abbrev steinV {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (e : E) : (ℝ ∙ e)ᗮ → ℝ :=
  fun y : (ℝ ∙ e)ᗮ ↦ volume.real {t : ℝ | (y : E) + t • e ∈ s}

private noncomputable abbrev steinFD {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (e : E) : (ℝ ∙ e)ᗮ → ℝ :=
  (steinD s e).indicator (fun _ ↦ (2 : ℝ))

private noncomputable abbrev steinM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : Set E) (e : E) : ℝ :=
  2 * volume.real (steinD s e) + (totalVariationOn volume ⊤ (steinV s e)).toReal

private noncomputable abbrev steinSTrunc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set E) (e : E) (he : ‖e‖ = 1) (ε : ℝ) : Set E :=
  {x : E | |⟪e, x⟫_ℝ| < (steinV s e ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}

private theorem nullMeasurableSet_steinSTrunc {s : Set E} {e : E} {he : ‖e‖ = 1}
    {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A) (ε : ℝ) :
    NullMeasurableSet (steinSTrunc s e he ε) volume :=
  have hq : QuasiMeasurePreserving
      (fun x : E ↦ ((orthogonalLineEquiv e he).symm x).1) volume volume :=
    Measure.quasiMeasurePreserving_fst.comp
      (MeasurePreserving.symm (orthogonalLineEquiv e he).toHomeomorph.toMeasurableEquiv
        (measurePreserving_orthogonalLineEquiv e he)).quasiMeasurePreserving
  nullMeasurableSet_lt (continuous_const.inner continuous_id).abs.measurable.aemeasurable
    (((S.hv_int.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hq).sub
      aemeasurable_const).div_const 2)

/-- Area-formula comparison bounding the perimeter of the mollified truncated subgraph
`{|⟪e, x⟫| < (mollW s e ρ y - ε) / 2}` by `∫ √(d² + ‖∇w‖²) + ∫ |2 · 1_{w > ε} - d|`. -/
private theorem perimeter_trunc_mollified_le {s : Set E} {e : E} {he : ‖e‖ = 1}
    {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    {ε : ℝ} (hε : 0 < ε) :
    perimeter volume ⊤
        {x : E | |⟪e, x⟫_ℝ| < (mollW s e ρ ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} ≤
      ENNReal.ofReal
        ((∫ y : (ℝ ∙ e)ᗮ, √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2)) +
          ∫ y : (ℝ ∙ e)ᗮ, |({y : (ℝ ∙ e)ᗮ | ε < mollW s e ρ y}.indicator
            (fun _ ↦ (2 : ℝ))) y - mollD s e ρ y|) := by
  let H := (ℝ ∙ e)ᗮ
  let Eε : Set H := {y : H | ε < mollW s e ρ y}
  have hw_smooth : ContDiff ℝ 1 (mollW s e ρ) := (S.w_smooth ρ).of_le (by simp)
  have hEε_m : MeasurableSet Eε := measurableSet_lt measurable_const hw_smooth.continuous.measurable
  have hEε_fin : volume Eε ≠ ∞ := ((S.w_int ρ).measure_gt_lt_top hε).ne
  have hgrad_int := S.gradW_int ρ
  -- Integrability of the mollified gradient integrand and the `L¹` indicator error.
  have hsqrt_int : Integrable
      (fun y : H ↦ √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2)) volume := by
    refine ((S.d_int ρ).add hgrad_int).mono'
      (Real.continuous_sqrt.comp (((S.d_smooth ρ).continuous.pow 2).add
        ((hw_smooth.continuous_fderiv one_ne_zero).norm.pow 2))).aestronglyMeasurable
      (.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hle := Real.sqrt_sq_add_sq_le (mollD s e ρ y) ‖fderiv ℝ (mollW s e ρ) y‖
    rw [abs_of_nonneg (S.d_mem ρ y).1, abs_of_nonneg (opNorm_nonneg _)] at hle
    exact hle
  have hdiff_int : Integrable (fun y : H ↦ |Eε.indicator (fun _ ↦ (2 : ℝ)) y - mollD s e ρ y|)
      volume :=
    (((integrableOn_const hEε_fin).integrable_indicator hEε_m).sub (S.d_int ρ)).abs
  have hsum_int : Integrable
      (fun y : H ↦ √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) +
        |Eε.indicator (fun _ ↦ (2 : ℝ)) y - mollD s e ρ y|) volume := hsqrt_int.add hdiff_int
  -- Bound the truncated subgraph perimeter by the area integral and compare pointwise.
  calc perimeter volume ⊤
          {x : E | |⟪e, x⟫_ℝ| < (mollW s e ρ ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
      ≤ ∫⁻ y in Eε, ENNReal.ofReal √(4 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) := by
        have hsub := perimeter_setOf_abs_inner_lt_div_two_le e he
          (hw_smooth.sub (contDiff_const (c := ε)))
        have hfderiv (y : H) :
            fderiv ℝ (fun x ↦ mollW s e ρ x - ε) y = fderiv ℝ (mollW s e ρ) y :=
          fderiv_sub_const ε
        simpa only [Eε, sub_pos, hfderiv] using hsub
    _ ≤ ∫⁻ y : H, ENNReal.ofReal
          (√(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2) +
            |Eε.indicator (fun _ ↦ (2 : ℝ)) y - mollD s e ρ y|) := by
        rw [← lintegral_indicator hEε_m]
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ Eε
        · rw [indicator_of_mem hy]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [indicator_of_mem hy]
          have hlip := Real.abs_sqrt_sq_add_sq_sub_sqrt_sq_add_sq_le 2 (mollD s e ρ y)
            ‖fderiv ℝ (mollW s e ρ) y‖
          norm_num only at hlip
          exact sub_le_iff_le_add'.1 ((le_abs_self _).trans hlip)
        · rw [indicator_of_notMem hy]; exact zero_le
    _ = ENNReal.ofReal
          ((∫ y : H, √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2)) +
            ∫ y : H, |Eε.indicator (fun _ ↦ (2 : ℝ)) y - mollD s e ρ y|) := by
        rw [← integral_add hsqrt_int hdiff_int, ofReal_integral_eq_lintegral_ofReal hsum_int
          (.of_forall fun _ ↦ add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]

/-- Single-bump combination of the smooth symmetric subgraph perimeter bound and the mollified
slicing excess inequality at positive threshold `ε`. -/
private theorem mul_perimeter_subgraph_mollified_add_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {e : E} {he : ‖e‖ = 1}
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (S : MollifiedSetup s e A) (ρ : ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (steinM s e) *
        perimeter volume ⊤
          {x : E | |⟪e, x⟫_ℝ| < (mollW s e ρ ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} +
        ENNReal.ofReal (2 * (∫ y : (ℝ ∙ e)ᗮ, mollA e A ρ y * √(mollD s e ρ y)) ^ 2) ≤
      ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s +
        ENNReal.ofReal (steinM s e *
          ∫ y : (ℝ ∙ e)ᗮ, |({y : (ℝ ∙ e)ᗮ | ε < mollW s e ρ y}.indicator
            (fun _ ↦ (2 : ℝ))) y - mollD s e ρ y|) := by
  let H := (ℝ ∙ e)ᗮ
  let Eε : Set H := {y : H | ε < mollW s e ρ y}
  set I_sq := ∫ y : H, √(mollD s e ρ y ^ 2 + ‖fderiv ℝ (mollW s e ρ) y‖ ^ 2)
  set I_err := ∫ y : H, |Eε.indicator (fun _ ↦ (2 : ℝ)) y - mollD s e ρ y|
  have hM_nonneg : 0 ≤ steinM s e := by positivity
  -- Step 1: Bound the truncated subgraph perimeter via the area formula and `L¹` error.
  have hper_upper :
      perimeter volume ⊤
          {x : E | |⟪e, x⟫_ℝ| < (mollW s e ρ ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} ≤
        ENNReal.ofReal (I_sq + I_err) :=
    perimeter_trunc_mollified_le (he := he) S ρ hε
  -- Step 2: Apply the mollified slicing excess inequality and convert to `ℝ≥0∞`.
  have hmoll :
      steinM s e * I_sq + 2 * (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2 ≤
        steinM s e * (perimeter volume ⊤ s).toReal :=
    hs.mul_integral_sqrt_sq_add_norm_fderiv_sq_add_two_mul_sq_le hfin hP e he hA hbad ρ
  calc ENNReal.ofReal (steinM s e) *
          perimeter volume ⊤
            {x : E | |⟪e, x⟫_ℝ| <
              (mollW s e ρ ((orthogonalLineEquiv e he).symm x).1 - ε) / 2} +
          ENNReal.ofReal (2 * (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2)
      ≤ ENNReal.ofReal (steinM s e) * ENNReal.ofReal (I_sq + I_err) +
          ENNReal.ofReal (2 * (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2) := by
        gcongr
    _ = ENNReal.ofReal
          (steinM s e * I_sq + 2 * (∫ y : H, mollA e A ρ y * √(mollD s e ρ y)) ^ 2 +
            steinM s e * I_err) := by
        rw [← ENNReal.ofReal_mul hM_nonneg, ← ENNReal.ofReal_add
          (mul_nonneg hM_nonneg (add_nonneg (integral_nonneg fun _ ↦ Real.sqrt_nonneg _)
            (integral_nonneg fun _ ↦ abs_nonneg _))) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (steinM s e * (perimeter volume ⊤ s).toReal + steinM s e * I_err) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s +
        ENNReal.ofReal (steinM s e * I_err) := by
        rw [ENNReal.ofReal_add (mul_nonneg hM_nonneg ENNReal.toReal_nonneg)
            (mul_nonneg hM_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)),
          ENNReal.ofReal_mul hM_nonneg, ENNReal.ofReal_toReal hP]

/-- Fixed-threshold limit (`j → ∞`) along a shrinking bump subsequence for any `ε > 0` at which
the superlevel sets `{w_j > ε}` converge in measure to `{v > ε}`. -/
private theorem step_eps_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) {e : E} {he : ‖e‖ = 1}
    {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I)
    (S : MollifiedSetup s e A) {ρ : ℕ → ContDiffBump (0 : (ℝ ∙ e)ᗮ)}
    (hρ_lim : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (hEj_lim : Tendsto (fun j ↦ volume ({y : (ℝ ∙ e)ᗮ | ε < mollW s e (ρ j) y} ∆
      {y : (ℝ ∙ e)ᗮ | ε < steinV s e y})) atTop (𝓝 0)) :
    ENNReal.ofReal (steinM s e) * perimeter volume ⊤ (steinSTrunc s e he ε) + 4 * volume A ^ 2 ≤
      ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s +
        ENNReal.ofReal
          (steinM s e * (2 * volume.real (steinD s e \ {y : (ℝ ∙ e)ᗮ | ε < steinV s e y}))) := by
  let H := (ℝ ∙ e)ᗮ
  let Sj : ℕ → Set E := fun j ↦
    {x : E | |⟪e, x⟫_ℝ| < (mollW s e (ρ j) ((orthogonalLineEquiv e he).symm x).1 - ε) / 2}
  let Ej : ℕ → Set H := fun j ↦ {y : H | ε < mollW s e (ρ j) y}
  let Eε : Set H := {y : H | ε < steinV s e y}
  let fEj : ℕ → H → ℝ := fun j ↦ (Ej j).indicator (fun _ ↦ 2)
  let fEε : H → ℝ := Eε.indicator (fun _ ↦ 2)
  have hEj_m (j : ℕ) : MeasurableSet (Ej j) :=
    measurableSet_lt measurable_const (S.w_smooth (ρ j)).continuous.measurable
  have hEε_nm : NullMeasurableSet Eε volume :=
    nullMeasurableSet_lt aemeasurable_const S.hv_int.aestronglyMeasurable.aemeasurable
  have hEj_fin (j : ℕ) : volume (Ej j) ≠ ∞ := ((S.w_int (ρ j)).measure_gt_lt_top hε).ne
  have hSj_nm (j : ℕ) : NullMeasurableSet (Sj j) volume :=
    (measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
      ((((S.w_smooth (ρ j)).continuous.comp (continuous_fst.comp
        (orthogonalLineEquiv e he).symm.continuous)).sub continuous_const).div_const
        2).measurable).nullMeasurableSet
  -- Combine the smooth subgraph bound and the mollified slicing excess bound for each `j`.
  have hper_j (j : ℕ) :
      ENNReal.ofReal (steinM s e) * perimeter volume ⊤ (Sj j) +
          ENNReal.ofReal (2 * (∫ y : H, mollA e A (ρ j) y * √(mollD s e (ρ j) y)) ^ 2) ≤
        ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s +
          ENNReal.ofReal (steinM s e * ∫ y : H, |fEj j y - mollD s e (ρ j) y|) :=
    mul_perimeter_subgraph_mollified_add_le hs hfin hP hA hbad S (ρ j) hε
  -- Limit 1: `Sj j → steinSTrunc s e he ε` in `L¹`, so `P(steinSTrunc ε) ≤ liminf P(Sj j)`.
  have hSj_lim : Tendsto (fun j ↦ volume (Sj j ∆ steinSTrunc s e he ε)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_enorm_normed_convolution_sub hρ_lim S.hv_int) (fun _ ↦ zero_le) fun j ↦ ?_
    rw [volume_eq_lintegral_volume_lineSection e he
      ((hSj_nm j).symmDiff (nullMeasurableSet_steinSTrunc S ε))]
    refine lintegral_mono fun y ↦ ?_
    have hsymm_sec : {t : ℝ | (y : E) + t • e ∈ Sj j ∆ steinSTrunc s e he ε} =
        Metric.eball (0 : ℝ) (ENNReal.ofReal (mollW s e (ρ j) y - ε) / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal (steinV s e y - ε) / 2) := by
      rw [← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ mollW s e (ρ j) z - ε) y,
        ← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ steinV s e z - ε) y]
      ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq, Sj]
    rw [hsymm_sec]
    refine (volume_eball_ofReal_symmDiff_le (mollW s e (ρ j) y - ε)
      (steinV s e y - ε)).trans_eq ?_
    rw [sub_sub_sub_cancel_right, Real.eNorm_eq_ofReal_abs]
  -- Limit 2: `2 (∫ a_j √d_j)² → 4 |A|²`.
  have ha_sq_lim :
      Tendsto (fun j ↦
          ENNReal.ofReal (2 * (∫ y : H, mollA e A (ρ j) y * √(mollD s e (ρ j) y)) ^ 2))
        atTop (𝓝 (4 * volume A ^ 2)) := by
    have hA_ofReal : ENNReal.ofReal (4 * volume.real A ^ 2) = 4 * volume A ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal S.hAfin]
    have hreal :
        Tendsto (fun j ↦ 2 * (∫ y : H, mollA e A (ρ j) y * √(mollD s e (ρ j) y)) ^ 2)
          atTop (𝓝 (4 * volume.real A ^ 2)) := by
      have hlim := ((tendsto_integral_normed_convolution_mul_sqrt_normed_convolution_indicator
        hρ_lim hA S.hD S.hAfin S.hDfin S.hAD zero_le_two).pow 2).const_mul 2
      have hlim_eq : 2 * (√2 * volume.real A) ^ 2 = 4 * volume.real A ^ 2 := by
        rw [mul_pow, Real.sq_sqrt zero_le_two]; ring
      rwa [hlim_eq] at hlim
    simpa only [hA_ofReal] using ENNReal.tendsto_ofReal hreal
  -- Limit 3: `limsup ∫ |2 · 1_{Ej j} - d_j| ≤ 2 |D \ Eε|`.
  have hEε_sub_D : Eε ⊆ steinD s e := fun y (hy : ε < steinV s e y) ↦ by
    rw [mem_ofPred_eq]
    exact pos_iff_ne_zero.2 fun h0 ↦ (hε.trans hy).ne' (by simp [measureReal_def, h0])
  have herr_upper (j : ℕ) :
      ∫ y : H, |fEj j y - mollD s e (ρ j) y| ≤
        2 * volume.real (Ej j ∆ Eε) + 2 * volume.real (steinD s e \ Eε) +
          ∫ y : H, |steinFD s e y - mollD s e (ρ j) y| := by
    have hfEj_int : Integrable (fEj j) volume :=
      (integrableOn_const (hEj_fin j)).integrable_indicator (hEj_m j)
    have hfEε_int : Integrable fEε volume :=
      (integrableOn_const (ne_top_of_le_ne_top S.hDfin
        (measure_mono hEε_sub_D))).integrable_indicator₀ hEε_nm
    have hi1 : Integrable (fun y : H ↦ |fEj j y - fEε y|) volume := (hfEj_int.sub hfEε_int).abs
    have hi2 : Integrable (fun y : H ↦ |fEε y - steinFD s e y|) volume :=
      (hfEε_int.sub S.hD_ind_int).abs
    have hi12 : Integrable (fun y : H ↦ |fEj j y - fEε y| + |fEε y - steinFD s e y|) volume :=
      hi1.add hi2
    have hi3 : Integrable (fun y : H ↦ |steinFD s e y - mollD s e (ρ j) y|) volume :=
      (S.hD_ind_int.sub (S.d_int (ρ j))).abs
    have hI1 : ∫ y : H, |fEj j y - fEε y| = 2 * volume.real (Ej j ∆ Eε) :=
      integral_abs_indicator_sub_indicator (hEj_m j).nullMeasurableSet hEε_nm zero_le_two
    have hI2 : ∫ y : H, |fEε y - steinFD s e y| = 2 * volume.real (steinD s e \ Eε) := by
      rw [integral_abs_indicator_sub_indicator hEε_nm S.hD zero_le_two, symmDiff_of_le hEε_sub_D]
    calc ∫ y : H, |fEj j y - mollD s e (ρ j) y|
        ≤ ∫ y : H, (|fEj j y - fEε y| + |fEε y - steinFD s e y| +
            |steinFD s e y - mollD s e (ρ j) y|) :=
          integral_mono (hfEj_int.sub (S.d_int (ρ j))).abs (hi12.add hi3) fun y ↦ by
            linarith [abs_sub_le (fEj j y) (fEε y) (mollD s e (ρ j) y),
              abs_sub_le (fEε y) (steinFD s e y) (mollD s e (ρ j) y)]
      _ = _ := by rw [integral_add hi12 hi3, integral_add hi1 hi2, hI1, hI2]
  have herr_lim : Tendsto (fun j ↦ ENNReal.ofReal (steinM s e * (2 * volume.real (Ej j ∆ Eε) +
      2 * volume.real (steinD s e \ Eε) + ∫ y : H, |steinFD s e y - mollD s e (ρ j) y|)))
      atTop (𝓝 (ENNReal.ofReal (steinM s e * (2 * volume.real (steinD s e \ Eε))))) := by
    have hsymm_real := (volume : Measure H).tendsto_measureReal_zero_of_tendsto_measure_zero hEj_lim
    have hd_L1 : Tendsto (fun j ↦ ∫ y : H, |steinFD s e y - mollD s e (ρ j) y|) atTop (𝓝 0) :=
      (tendsto_integral_abs_normed_convolution_sub hρ_lim S.hD_ind_int).congr
        fun j ↦ integral_congr_ae (.of_forall fun _ ↦ abs_sub_comm _ _)
    refine ENNReal.tendsto_ofReal (Tendsto.const_mul (steinM s e) ?_)
    simpa only [mul_zero, zero_add, add_zero] using
      ((hsymm_real.const_mul 2).add tendsto_const_nhds).add hd_L1
  exact ENNReal.mul_add_le_of_le_liminf_of_tendsto
    (perimeter_le_liminf_of_tendsto_measure_symmDiff (.of_forall hSj_nm)
      (nullMeasurableSet_steinSTrunc S ε) hSj_lim)
    ha_sq_lim.liminf_eq.ge
    (.of_forall fun j ↦ (hper_j j).trans (by gcongr; exact herr_upper j))
    (herr_lim.const_add _)

/-- As `ε k → 0⁺`, the truncated symmetric subgraphs `steinSTrunc s e he (ε k)` converge in measure
to the Steiner symmetral `S_e s`. -/
private theorem tendsto_measure_symmDiff_trunc_steinerSymmetrization
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    {e : E} {he : ‖e‖ = 1} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
    {ε : ℕ → ℝ} (hε_pos : ∀ k, 0 < ε k) (hε_lim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k ↦ volume (steinSTrunc s e he (ε k) ∆ steinerSymmetrization e he s))
      atTop (𝓝 0) := by
  let H := (ℝ ∙ e)ᗮ
  have hv_nonneg (y : H) : 0 ≤ steinV s e y := measureReal_nonneg
  have hdom : Tendsto (fun k ↦ ∫⁻ y : H, ENNReal.ofReal (min (steinV s e y) (ε k)))
      atTop (𝓝 0) := by
    rw [← lintegral_zero (μ := (volume : Measure H))]
    refine tendsto_lintegral_of_dominated_convergence' (fun y ↦ ENNReal.ofReal (steinV s e y))
      (fun k ↦ (S.hv_int.aestronglyMeasurable.aemeasurable.min aemeasurable_const).ennreal_ofReal)
      (fun k ↦ .of_forall fun y ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))
      (ne_top_of_le_ne_top S.hv_int.2.ne (lintegral_mono fun y ↦ by
        rw [Real.eNorm_of_nonneg (hv_nonneg y)]))
      (.of_forall fun y ↦ by
        simpa only [ENNReal.ofReal_zero, min_eq_right (hv_nonneg y)] using
          ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := steinV s e y)).min hε_lim))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom (fun _ ↦ zero_le)
    fun k ↦ ?_
  rw [volume_eq_lintegral_volume_lineSection e he
    ((nullMeasurableSet_steinSTrunc S (ε k)).symmDiff
      (nullMeasurableSet_steinerSymmetrization e he hs))]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin
  have hsymm_sec :
      {t : ℝ | (y : E) + t • e ∈ steinSTrunc s e he (ε k) ∆ steinerSymmetrization e he s} =
        Metric.eball (0 : ℝ) (ENNReal.ofReal (max (steinV s e y - ε k) 0) / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal (steinV s e y) / 2) := by
    have hvol_eq : ENNReal.ofReal (steinV s e y) = volume {t : ℝ | (y : E) + t • e ∈ s} :=
      ofReal_measureReal hyfin.ne
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le,
      ← lineSection_setOf_abs_inner_lt_div_two e he (fun z ↦ steinV s e z - ε k) y,
      hvol_eq, ← lineSection_steinerSymmetrization e he]
    ext t; simp only [Set.mem_symmDiff, mem_ofPred_eq]
  rw [hsymm_sec]
  refine (volume_eball_ofReal_symmDiff_le (max (steinV s e y - ε k) 0) (steinV s e y)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rcases le_total (steinV s e y) (ε k) with hle | hge
  · rw [max_eq_right (sub_nonpos.2 hle), zero_sub, abs_neg, abs_of_nonneg (hv_nonneg y),
      min_eq_left hle]
  · rw [max_eq_left (sub_nonneg.2 hge), sub_sub_cancel_left, abs_neg,
      abs_of_pos (hε_pos k), min_eq_right hge]

/-- As `ε k ≤ 1 / (k + 1) → 0⁺`, the residual slice `{0 < |s_y| ≤ ε k}` vanishes in measure. -/
private theorem tendsto_measure_sdiff_pos_lineSection
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    {e : E} {he : ‖e‖ = 1} {A : Set (ℝ ∙ e)ᗮ} (S : MollifiedSetup s e A)
    {ε : ℕ → ℝ} (hε_upper : ∀ k, ε k ≤ 1 / ((k : ℝ) + 1)) :
    Tendsto (fun k ↦ volume (steinD s e \ {y : (ℝ ∙ e)ᗮ | ε k < steinV s e y})) atTop (𝓝 0) := by
  have hGlim : Tendsto
      (fun k : ℕ ↦
        volume ({y : (ℝ ∙ e)ᗮ | 0 < steinV s e y ∧ steinV s e y ≤ 1 / ((k : ℝ) + 1)} ∩ steinD s e))
      atTop (𝓝 0) :=
    S.hv_int.aestronglyMeasurable.aemeasurable.tendsto_measure_setOf_pos_lt_le_inter S.hD S.hDfin
      (fun _ _ hmn ↦ one_div_le_one_div_of_le (by positivity) (by gcongr))
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim
    (fun _ ↦ zero_le) fun k ↦ measure_mono_ae ?_
  filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin ⟨hyD, hnot⟩
  have hvy_pos : 0 < steinV s e y := ENNReal.toReal_pos hyD.ne' hyfin.ne
  exact ⟨⟨hvy_pos, (not_lt.1 hnot).trans (hε_upper k)⟩, hyD⟩

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
  -- Handle infinite ambient perimeter: then `volume s ≠ 0`, so `volume D ≠ 0` and RHS = ∞.
  by_cases hP : perimeter volume ⊤ s = ∞
  · have hD0 : volume {y : H | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} ≠ 0 := fun hD0 ↦ by
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
  -- Finite ambient perimeter: choose a subsequence of bumps with a.e. level-set convergence.
  have S := hs.mkMollifiedSetup hfin hP he hA hbad
  let ρ₀ : ℕ → ContDiffBump (0 : H) := ContDiffBump.shrinking one_pos
  have hρ₀_lim : Tendsto (fun j ↦ (ρ₀ j).rOut) atTop (𝓝 0) :=
    ContDiffBump.tendsto_rOut_shrinking one_pos
  obtain ⟨ns, hns, hlevel_ae⟩ :=
    volume.exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt
      (f := fun j ↦ mollW s e (ρ₀ j))
      (fun j ↦ (S.w_int (ρ₀ j)).aestronglyMeasurable.aemeasurable)
      S.hv_int.aestronglyMeasurable.aemeasurable
      (tendsto_lintegral_enorm_normed_convolution_sub hρ₀_lim S.hv_int)
  let ρ : ℕ → ContDiffBump (0 : H) := fun j ↦ ρ₀ (ns j)
  have hρ_lim : Tendsto (fun j ↦ (ρ j).rOut) atTop (𝓝 0) := hρ₀_lim.comp hns.tendsto_atTop
  have hex_eps (k : ℕ) : ∃ ε ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)),
      Tendsto (fun j ↦ volume ({y : H | ε < mollW s e (ρ j) y} ∆
        {y : H | ε < steinV s e y})) atTop (𝓝 0) := by
    let bad : Set ℝ := {ε : ℝ | ¬Tendsto (fun j ↦ volume
      ({y : H | ε < mollW s e (ρ j) y} ∆ {y : H | ε < steinV s e y})) atTop (𝓝 0)}
    obtain ⟨ε, hεI, hεgood⟩ : (Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) \ bad).Nonempty :=
      Set.ne_empty_iff_nonempty.1 fun hempty ↦ by
        have h0 := measure_mono_null (Set.sdiff_eq_empty.1 hempty) (ae_iff.1 hlevel_ae)
        rw [Real.volume_Ioo, sub_zero] at h0
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne' h0
    exact ⟨ε, hεI, not_not.1 hεgood⟩
  choose ε hε_mem hε_level using hex_eps
  have hε_lim : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hε_mem k).1.le) (fun k ↦ (hε_mem k).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hDdiff_rhs : Tendsto (fun k ↦ ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s +
      ENNReal.ofReal (steinM s e * (2 * volume.real (steinD s e \ {y : H | ε k < steinV s e y}))))
      atTop (𝓝 (ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s)) := by
    have hreal := (volume : Measure H).tendsto_measureReal_zero_of_tendsto_measure_zero <|
      tendsto_measure_sdiff_pos_lineSection hs hfin (he := he) S fun k ↦ (hε_mem k).2.le
    simpa only [mul_zero, ENNReal.ofReal_zero, add_zero] using
      (ENNReal.tendsto_ofReal ((hreal.const_mul 2).const_mul (steinM s e))).const_add
        (ENNReal.ofReal (steinM s e) * perimeter volume ⊤ s)
  have hM_ofReal : ENNReal.ofReal (steinM s e) =
      2 * volume (steinD s e) + totalVariationOn volume ⊤ (steinV s e) := by
    dsimp only [steinM]
    rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat, ofReal_measureReal S.hDfin, ENNReal.ofReal_toReal S.hv_tv_fin]
  rw [← hM_ofReal]
  exact ENNReal.mul_add_le_of_le_liminf_of_tendsto
    (perimeter_le_liminf_of_tendsto_measure_symmDiff
      (.of_forall fun k ↦ nullMeasurableSet_steinSTrunc S (ε k))
      (nullMeasurableSet_steinerSymmetrization e he hs)
      (tendsto_measure_symmDiff_trunc_steinerSymmetrization hs hfin S (fun k ↦ (hε_mem k).1)
        hε_lim))
    (liminf_const _).ge
    (.of_forall fun k ↦ step_eps_le hs hfin hP hA hbad S hρ_lim (hε_mem k).1 (hε_level k))
    hDdiff_rhs

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
  have hAfin : volume A ≠ ∞ := hs.volume_ne_top_of_noninterval_lineSection hfin hP e he hA hbad
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
theorem ae_exists_ordConnected_ae_eq_lineSection_of_perimeter_steinerSymmetrization_eq
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
  have hA0 : volume A = 0 :=
    mul_self_eq_zero.1 <| pow_two (volume A) ▸ (mul_eq_zero.1 hzero).resolve_left (by norm_num)
  rw [ae_iff]
  exact measure_mono_null (t := A) (fun y hy I hI heq ↦ hy ⟨I, hI, heq⟩) hA0

end MeasureTheory.NullMeasurableSet

end
