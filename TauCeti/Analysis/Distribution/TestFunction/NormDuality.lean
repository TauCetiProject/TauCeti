/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# The local `L¹` norm by duality with test vector fields

Let `Ω` be an open set of a finite-dimensional real normed space `E`, let `F` be a real Hilbert
space, and let `G : E → F →L[ℝ] ℝ` be a field of continuous linear functionals that is locally
integrable on `Ω` for a measure `μ`. Then

`∫⁻ x in Ω, ‖G x‖ₑ ∂μ = ⨆ { ∫ G x (φ x) ∂μ | φ ∈ 𝓓(Ω, F), ‖φ x‖ ≤ 1 for all x }`

(`MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`), with
both sides possibly infinite. The measure is arbitrary: it may be a Haar measure, or a measure
such as the `k`-dimensional Hausdorff measure, which is not locally finite. The bound of each
pairing by `∫_Ω ‖G‖` holds for every real normed space `F`
(`TestFunction.enorm_integral_apply_le_setLIntegral_enorm`). For a complete normed space `F`, the
duality holds as soon as a measurable field `σ` with `‖σ x‖ ≤ 1` attains the norms,
`G x (σ x) = ‖G x‖`
(`MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming`);
for a Hilbert space the normalized Riesz representatives of `G` form such a field.

This duality identifies a supremum over test vector fields, such as the total variation of a
function on `Ω` or the mass of a current, with the integral of a pointwise norm.

For the reverse inequality, fix a compact `K ⊆ Ω` and a compact neighbourhood `L ⊆ Ω` of `K`.
All errors are measured in `L¹` of the finite measure `ρ = ‖G‖ μ` on `L`, which controls the
pairings with `G`. The field `σ` on `K`, extended by zero, is approximated in `L¹(ρ)` by a
continuous function of compact support (finite measures on `E` are regular). Cut off to a
neighbourhood of `K` and rescaled into the closed unit ball, this stays an approximation, at most
doubling the error. Its mollifications with normalized bumps of shrinking support are test vector
fields of norm at most one which converge to it everywhere, hence in `L¹(ρ)` by dominated
convergence (`MeasureTheory.LocallyIntegrableOn.exists_contDiff_enorm_integral_sub_setIntegral_le`).
An exhaustion of `Ω` by compact sets concludes.

## Main declarations

* `TestFunction.enorm_integral_apply_le_setLIntegral_enorm`: `|∫ G φ| ≤ ∫_Ω ‖G‖` for a test vector
  field `φ` on `Ω` with `‖φ‖ ≤ 1`.
* `MeasureTheory.LocallyIntegrableOn.exists_contDiff_lt_ofReal_integral_apply`: given a norming
  field, every `c < ∫_W ‖G‖` is exceeded by the pairing with a smooth field of compact support in
  the open set `W`, of norm at most one.
* `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming`,
  `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`: the
  supremum of the pairings is `∫_Ω ‖G‖`, given a norming field, or for a Hilbert space `F`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1 (the variation of a Sobolev function).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Metric Set
open scoped ENNReal Distributions Topology Convolution ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {Ω : Opens E}

namespace TestFunction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pairing a field of continuous linear functionals `G` with a test vector field on `Ω` of norm
at most one gives at most `∫_Ω ‖G‖`. -/
theorem enorm_integral_apply_le_setLIntegral_enorm (φ : 𝓓(Ω, F))
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (G : E → F →L[ℝ] ℝ) :
    ‖∫ x, G x (φ x) ∂μ‖ₑ ≤ ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans
    ((lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ _))
  by_cases hx : x ∈ (Ω : Set E)
  · rw [Set.indicator_of_mem hx, eNorm_le_iff_norm_le]
    exact ((G x).le_opNorm (φ x)).trans (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
  · simp [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]

end TestFunction

namespace MeasureTheory.LocallyIntegrableOn

variable [FiniteDimensional ℝ E] [BorelSpace E] {W : Set E}

/-- Rescaling `v` into the closed unit ball moves it by at most `‖v - w‖` more than `v` is from a
vector `w` of the closed unit ball. -/
private theorem norm_inv_max_smul_sub_le [NormedAddCommGroup F] [NormedSpace ℝ F] {v w : F}
    (hw : ‖w‖ ≤ 1) : ‖(max 1 ‖v‖)⁻¹ • v - w‖ ≤ 2 * ‖v - w‖ := by
  rcases le_total ‖v‖ 1 with hv | hv
  · rw [max_eq_left hv, inv_one, one_smul]
    linarith [norm_nonneg (v - w)]
  · rw [max_eq_right hv]
    have hinv : ‖v‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hv
    have hvv : ‖‖v‖⁻¹ • v - v‖ = ‖v‖ - 1 := by
      rw [show ‖v‖⁻¹ • v - v = (‖v‖⁻¹ - 1) • v by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonpos (by linarith)]
      field_simp
      ring
    calc ‖‖v‖⁻¹ • v - w‖ ≤ ‖‖v‖⁻¹ • v - v‖ + ‖v - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖v - w‖ := by
        rw [hvv]
        linarith [norm_sub_norm_le v w]

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : E → F →L[ℝ] ℝ}

omit [CompleteSpace F] in
/-- In `L¹` of a finite measure, a field `s` with `‖s x‖ ≤ 1` vanishing outside a compact set `K`
is approximated by continuous fields with `‖h x‖ ≤ 1` vanishing outside a neighbourhood `U` of
`K`: approximate by a continuous function, rescale it into the closed unit ball and cut it off. -/
private theorem exists_continuous_lintegral_sub_le {ρ : Measure E} [IsFiniteMeasure ρ]
    {s : E → F} (hsi : Integrable s ρ) (hs1 : ∀ x, ‖s x‖ ≤ 1) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hsK : ∀ x ∉ K, s x = 0) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ h : E → F, Continuous h ∧ (∀ x, ‖h x‖ ≤ 1) ∧ (∀ x, h x ≠ 0 → x ∈ U) ∧
      ∫⁻ x, ‖h x - s x‖ₑ ∂ρ ≤ 2 * ε := by
  obtain ⟨f, -, hfs, hfc, -⟩ := hsi.exists_hasCompactSupport_lintegral_sub_le hε
  obtain ⟨χ, hχK, hχ0, -, hχ01⟩ := exists_continuous_one_zero_of_isCompact hK
    hU.isClosed_compl (disjoint_compl_right_iff_subset.2 hKU)
  set h : E → F := fun x => χ x • (max 1 ‖f x‖)⁻¹ • f x with hh_def
  have hr1 (x : E) : ‖(max 1 ‖f x‖)⁻¹ • f x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (by positivity)
  have hχh (x : E) : ‖h x‖ ≤ ‖(max 1 ‖f x‖)⁻¹ • f x‖ := by
    rw [hh_def, norm_smul _ ((max 1 ‖f x‖)⁻¹ • f x), Real.norm_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 x).2
  have hhs (x : E) : ‖h x - s x‖ₑ ≤ 2 * ‖s x - f x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), norm_sub_rev (s x)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hx : x ∈ K
    · simpa [hh_def, hχK hx] using norm_inv_max_smul_sub_le (v := f x) (hs1 x)
    · rw [hsK x hx, sub_zero, sub_zero]
      exact (hχh x).trans (by simpa using norm_inv_max_smul_sub_le (v := f x) (w := 0) (by simp))
  refine ⟨h, χ.continuous.smul ((continuous_const.max hfc.norm).inv₀
    (fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne') |>.smul hfc),
    fun x => (hχh x).trans (hr1 x), fun x hx => ?_, ?_⟩
  · by_contra hxU
    exact hx (by simp [hh_def, hχ0 hxU])
  · calc ∫⁻ x, ‖h x - s x‖ₑ ∂ρ ≤ ∫⁻ x, 2 * ‖s x - f x‖ₑ ∂ρ := lintegral_mono hhs
      _ ≤ 2 * ε := by
        rw [lintegral_const_mul' _ _ (by simp)]
        gcongr

/-- In `L¹` of a finite measure, a continuous field `h` with `‖h x‖ ≤ 1` vanishing outside the
`r`-thickening of `K` is approximated by smooth fields with `‖ψ x‖ ≤ 1` supported in the closed
`2r`-thickening of `K`: its mollifications with normalized bumps of shrinking support converge to
it everywhere, hence in `L¹` by dominated convergence. -/
private theorem exists_contDiff_lintegral_sub_le {ρ : Measure E} [IsFiniteMeasure ρ]
    {h : E → F} (hhc : Continuous h) (hh1 : ∀ x, ‖h x‖ ≤ 1) {K : Set E} {r : ℝ} (hr : 0 < r)
    (hhK : ∀ x, h x ≠ 0 → x ∈ thickening r K) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧ tsupport ψ ⊆ cthickening (2 * r) K ∧
      ∫⁻ x, ‖ψ x - h x‖ₑ ∂ρ ≤ ε := by
  have he (v : F) (hv : ‖v‖ ≤ 1) : ‖v‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 hv
  let ν : Measure E := Measure.addHaar
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨r / 2 / ((n + 1 : ℕ) : ℝ), r / ((n + 1 : ℕ) : ℝ), by positivity,
      div_lt_div_of_pos_right (by linarith) (by positivity)⟩
  set ψ : ℕ → E → F := fun n => (φ n).normed ν ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] h
  have hψd (n : ℕ) : ContDiff ℝ ∞ (ψ n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hhc.locallyIntegrable
  have hψs (n : ℕ) : tsupport (ψ n) ⊆ cthickening (2 * r) K := by
    have hsupp : Function.support (ψ n) ⊆ thickening (2 * r) K := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      rw [(φ n).support_normed_eq, mem_ball_zero_iff] at ha
      obtain ⟨y, hy, hby⟩ := mem_thickening_iff.1 (hhK b hb)
      refine mem_thickening_iff.2 ⟨y, hy, ?_⟩
      have ha' : ‖a‖ < r := ha.trans_le (div_le_self hr.le (by simp))
      rw [dist_eq_norm, add_sub_assoc]
      rw [dist_eq_norm] at hby
      linarith [norm_add_le a (b - y)]
    exact (closure_mono hsupp).trans (closure_thickening_subset_cthickening _ _)
  have hψ1 (n : ℕ) (x : E) : ‖ψ n x‖ ≤ 1 :=
    norm_convolution_lsmul_le_of_forall_norm_le (φ n).support_normed_eq.subset
      (φ n).nonneg_normed (φ n).integral_normed fun y _ => hh1 y
  have hψt (x : E) : Tendsto (fun n => ψ n x) atTop (𝓝 (h x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      ((tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 1)) hhc x
  have hlim : Tendsto (fun n => ∫⁻ x, ‖ψ n x - h x‖ₑ ∂ρ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := ρ) (fun _ => (2 : ℝ≥0∞))
      (f := fun _ => 0) (fun n => ((hψd n).continuous.sub hhc).eNorm.measurable)
      (fun n => ae_of_all _ fun x => (eNorm_sub_le).trans (by
        simpa [one_add_one_eq_two] using add_le_add (he _ (hψ1 n x)) (he _ (hh1 x))))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
      (ae_of_all _ fun x => by simpa using ((hψt x).sub_const (h x)).eNorm)
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  exact ⟨ψ n, hψd n, hψ1 n, hψs n, hn.le⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [CompleteSpace F] in
/-- The pairings of `G` on `L` with two fields of norm at most one differ by at most the distance
of the fields in `L¹` of the measure `‖G‖ μ` on `L`. -/
private theorem enorm_setIntegral_sub_le {L : Set E} (hGL : IntegrableOn G L μ) {g₁ g₂ : E → F}
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ) (h₁ : ∀ x, ‖g₁ x‖ ≤ 1)
    (h₂ : ∀ x, ‖g₂ x‖ ≤ 1) :
    ‖∫ x in L, G x (g₁ x) ∂μ - ∫ x in L, G x (g₂ x) ∂μ‖ₑ ≤
      ∫⁻ x, ‖g₁ x - g₂ x‖ₑ ∂(μ.restrict L).withDensity fun x => ‖G x‖ₑ := by
  have hGg (g : E → F) (hg : AEStronglyMeasurable g μ) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
      IntegrableOn (fun x => G x (g x)) L μ :=
    hGL.norm.mono' (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : F →L[ℝ] ℝ) v => L v)
      (by fun_prop) hGL.aestronglyMeasurable hg.restrict)
      (ae_of_all _ fun x => ((G x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hg1 x)))
  rw [← integral_sub (hGg _ hg₁ h₁) (hGg _ hg₂ h₂)]
  simp_rw [← map_sub]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀ (g := fun x => ‖g₁ x - g₂ x‖ₑ)
    hGL.aestronglyMeasurable.eNorm (hg₁.restrict.sub hg₂.restrict).eNorm]
  exact lintegral_mono fun x => (G x).le_opENorm _

/-- **Smooth approximation of a bounded field.** Let `G` be locally integrable on an open set `W`
and `σ` a measurable field with `‖σ x‖ ≤ 1`. For a compact `K ⊆ W`, the pairing `∫_K G σ` is
approximated by pairings `∫ G ψ` with smooth fields `ψ` of compact support in `W` and with
`‖ψ x‖ ≤ 1`. The measure `μ` is arbitrary. -/
theorem exists_contDiff_enorm_integral_sub_setIntegral_le (hG : LocallyIntegrableOn G W μ)
    (hW : IsOpen W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) {σ : E → F}
    (hσm : AEStronglyMeasurable σ (μ.restrict K)) (hσ : ∀ x, ‖σ x‖ ≤ 1) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧
      ‖∫ x, G x (ψ x) ∂μ - ∫ x in K, G x (σ x) ∂μ‖ₑ ≤ ε := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  set L := cthickening δ K
  have hGL : IntegrableOn G L μ := hG.integrableOn_compact_subset hδW hK.cthickening
  -- The finite measure `ρ = ‖G‖ μ` on `L` controls the pairings with `G`.
  set ρ : Measure E := (μ.restrict L).withDensity fun x => ‖G x‖ₑ
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity hGL.2.ne
  have hρμ : ρ ≪ μ := (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  -- Approximate `σ` on `K`, extended by zero, in `L¹(ρ)` by a smooth field `ψ` supported in `L`.
  set s : E → F := K.indicator σ with hs_def
  have hs1 (x : E) : ‖s x‖ ≤ 1 := by
    by_cases hx : x ∈ K <;> simp [hs_def, hx, hσ x]
  have hsμ : AEStronglyMeasurable s μ :=
    (aestronglyMeasurable_indicator_iff hK.measurableSet).2 hσm
  obtain ⟨h, hhc, hh1, hhK, hhs⟩ := exists_continuous_lintegral_sub_le
    (Integrable.of_bound (hsμ.mono_ac hρμ) 1 (ae_of_all _ hs1)) hs1 hK isOpen_thickening
    (self_subset_thickening (half_pos hδ) K) (fun x hx => by simp [hs_def, hx])
    (ε := ε / 3) (ENNReal.div_pos hε (by simp)).ne'
  obtain ⟨ψ, hψd, hψ1, hψs, hψh⟩ := exists_contDiff_lintegral_sub_le (ρ := ρ) hhc hh1
    (half_pos hδ) hhK (ε := ε / 3) (ENNReal.div_pos hε (by simp)).ne'
  rw [mul_div_cancel₀ _ two_ne_zero] at hψs
  have hψn : ∫⁻ x, ‖ψ x - s x‖ₑ ∂ρ ≤ ε :=
    calc ∫⁻ x, ‖ψ x - s x‖ₑ ∂ρ ≤ ∫⁻ x, ‖ψ x - h x‖ₑ + ‖h x - s x‖ₑ ∂ρ :=
          lintegral_mono fun x => by
            rw [← sub_add_sub_cancel (ψ x) (h x) (s x)]
            exact eNorm_add_le _ _
      _ ≤ ε / 3 + 2 * (ε / 3) := by
          rw [lintegral_add_left (f := fun x => ‖ψ x - h x‖ₑ)
            (hψd.continuous.sub hhc).eNorm.measurable]
          gcongr
      _ = ε := by
          rw [show ε / 3 + 2 * (ε / 3) = 3 * (ε / 3) by ring]
          exact ENNReal.mul_div_cancel (by simp) (by simp)
  refine ⟨ψ, hψd, hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hψs, hψs.trans hδW,
    hψ1, ?_⟩
  -- The pairing with `G` is controlled by the distance in `L¹(ρ)`.
  have h1 : ∫ x, G x (ψ x) ∂μ = ∫ x in L, G x (ψ x) ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hψs h), map_zero]).symm
  have h2 : ∫ x in K, G x (σ x) ∂μ = ∫ x in L, G x (s x) ∂μ := by
    have hGs (x : E) : G x (s x) = K.indicator (fun x => G x (σ x)) x := by
      by_cases hx : x ∈ K <;> simp [hs_def, hx]
    simp_rw [hGs, setIntegral_indicator hK.measurableSet,
      inter_eq_right.mpr (show K ⊆ L from self_subset_cthickening K)]
  rw [h1, h2]
  exact (enorm_setIntegral_sub_le hGL hψd.continuous.aestronglyMeasurable hsμ hψ1 hs1).trans hψn

/-- **The local `L¹` norm by duality, with a norming field.** Let `G` be locally integrable on an
open set `W`, and let `σ` be a measurable field with `‖σ x‖ ≤ 1` and `G x (σ x) = ‖G x‖` for
almost every `x ∈ W`. Every `c < ∫_W ‖G‖` is exceeded by some pairing `∫ G ψ` with a smooth field
`ψ` of compact support in `W` and with `‖ψ x‖ ≤ 1`. The measure `μ` is arbitrary. -/
theorem exists_contDiff_lt_ofReal_integral_apply (hG : LocallyIntegrableOn G W μ) (hW : IsOpen W)
    {σ : E → F} (hσm : AEStronglyMeasurable σ (μ.restrict W)) (hσ : ∀ x, ‖σ x‖ ≤ 1)
    (hGσ : ∀ᵐ x ∂μ, x ∈ W → G x (σ x) = ‖G x‖) {c : ℝ≥0∞}
    (hc : c < ∫⁻ x in W, ‖G x‖ₑ ∂μ) :
    ∃ ψ : E → F, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, ‖ψ x‖ ≤ 1) ∧
      c < ENNReal.ofReal (∫ x, G x (ψ x) ∂μ) := by
  -- Exhaust `W` by compact sets, and pick one carrying more than `c` of `∫_W ‖G‖`.
  obtain ⟨V, hKc, hKW, hVm, hVU, -⟩ := Opens.exists_monotone_isCompact_closure_iUnion_eq ⟨W, hW⟩
  set K : ℕ → Set E := fun n => closure (V n)
  have hKm : Monotone K := fun m n h => closure_mono (hVm h)
  have hKU : ⋃ n, K n = W := Subset.antisymm (iUnion_subset hKW)
    (hVU.symm.subset.trans (iUnion_mono fun n => subset_closure))
  rw [← hKU, setLIntegral_iUnion_of_directed _ hKm.directed_le, lt_iSup_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have hGK : IntegrableOn G (K n) μ := hG.integrableOn_compact_subset (hKW n) (hKc n)
  set a := ∫ x in K n, G x (σ x) ∂μ
  have ha : ∫⁻ x in K n, ‖G x‖ₑ ∂μ = ENNReal.ofReal a := by
    rw [← ofReal_integral_norm_eq_lintegral_eNorm hGK]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' (hKc n).measurableSet).2
      (hGσ.mono fun x hx hxK => hx (hKW n hxK))] with x hx
    exact hx.symm
  rw [ha] at hn
  have hct : c ≠ ⊤ := ne_top_of_lt hn
  have hca : c.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hn
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ := hG.exists_contDiff_enorm_integral_sub_setIntegral_le hW
    (hKc n) (hKW n) (hσm.mono_measure (Measure.restrict_mono (hKW n) le_rfl)) hσ
    (ε := ENNReal.ofReal ((a - c.toReal) / 2)) (by simp [hca])
  refine ⟨ψ, hψd, hψc, hψW, hψ1, (ENNReal.lt_ofReal_iff_toReal_lt hct).2 ?_⟩
  rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hψ
  linarith [neg_abs_le (∫ x, G x (ψ x) ∂μ - a)]

/-- **The local `L¹` norm by duality, with a norming field.** For a field `G` of continuous linear
functionals on a real normed space `F`, locally integrable on `Ω`, and a measurable field `σ` with
`‖σ x‖ ≤ 1` attaining the norm, `G x (σ x) = ‖G x‖` for almost every `x ∈ Ω`, the integral
`∫_Ω ‖G‖` is the supremum of `∫ G x (φ x)` over test vector fields `φ ∈ 𝓓(Ω, F)` with
`‖φ x‖ ≤ 1`. The measure `μ` is arbitrary, and both sides may be infinite. -/
theorem iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming {Ω : Opens E}
    (hG : LocallyIntegrableOn G Ω μ) {σ : E → F} (hσm : AEStronglyMeasurable σ (μ.restrict Ω))
    (hσ : ∀ x, ‖σ x‖ ≤ 1) (hGσ : ∀ᵐ x ∂μ, x ∈ Ω → G x (σ x) = ‖G x‖) :
    ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) =
      ∫⁻ x in Ω, ‖G x‖ₑ ∂μ  := by
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) (le_of_forall_lt fun c hc => ?_)
  · exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans <|
      (Real.eNorm_eq_ofReal_abs _).symm.trans_le (φ.enorm_integral_apply_le_setLIntegral_enorm hφ G)
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ :=
    hG.exists_contDiff_lt_ofReal_integral_apply Ω.isOpen hσm hσ hGσ hc
  exact hψ.trans_le (le_iSup₂ (f := fun (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x, G x (φ x) ∂μ)) ⟨ψ, hψd, hψc, hψW⟩ hψ1)

end MeasureTheory.LocallyIntegrableOn

namespace MeasureTheory.LocallyIntegrableOn

variable [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {G : E → F →L[ℝ] ℝ}

/-- **The local `L¹` norm by duality.** For a field `G` of continuous linear functionals on a real
Hilbert space `F` that is locally integrable on `Ω`, `∫_Ω ‖G‖` is the supremum of `∫ G x (φ x)`
over test vector fields `φ ∈ 𝓓(Ω, F)` with `‖φ x‖ ≤ 1`. The measure `μ` is arbitrary, and both
sides may be infinite. -/
theorem iSup_ofReal_integral_apply_eq_setLIntegral_enorm (hG : LocallyIntegrableOn G Ω μ) :
    ⨆ (φ : 𝓓(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (φ x) ∂μ) =
      ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  -- The unit field along the Riesz representative `g` of `G` attains the norm of `G`.
  set g : E → F := fun x => (InnerProductSpace.toDual ℝ F).symm (G x)
  have hgm : AEStronglyMeasurable g (μ.restrict Ω) :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable
      hG.aestronglyMeasurable
  refine hG.iSup_ofReal_integral_apply_eq_setLIntegral_enorm_of_norming
    (σ := fun x => ‖g x‖⁻¹ • g x) (hgm.norm.aemeasurable.inv.aestronglyMeasurable.smul hgm)
    (fun x => ?_) (ae_of_all _ fun x _ => ?_)
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one
  · have hgG : ‖g x‖ = ‖G x‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map (G x)
    have hGg : G x (g x) = ‖g x‖ ^ 2 := by
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq]
    rw [map_smul, hGg, ← hgG, smul_eq_mul]
    rcases eq_or_ne ‖g x‖ 0 with h0 | h0
    · simp [h0]
    · field_simp

end MeasureTheory.LocallyIntegrableOn
