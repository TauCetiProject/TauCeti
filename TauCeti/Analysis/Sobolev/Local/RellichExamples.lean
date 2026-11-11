/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Oscillation
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Examples for local Rellich compactness on discs and half-discs

Local Rellich compactness says that a sequence bounded in `W^{k+1,p}` on compact subsets of a
planar domain or half-disc has a subsequence converging in `W^{k,p}` on compact subsets. This file
records three examples showing what the hypothesis and the conclusion do and do not say.

* `TauCeti.RellichExamples.sineWave m z = sin (m * z.re)` is bounded by `1`, so it is bounded in
  every `Lᵖ` on compact sets, but no subsequence converges in `Lᵖ` on the unit disc
  (`not_tendsto_eLpNorm_sineWave_sub`); its derivatives are unbounded in every `Lᵖ` with
  `1 ≤ p` (`tendsto_eLpNorm_fderiv_sineWave`). So boundedness in `Lᵖ` alone gives no
  compactness, and the sequence is not bounded in `W^{1,p}`.
* The powers `z ^ m` converge to `0`, together with every real iterated derivative, uniformly
  on each compact subset of the unit disc (`tendstoUniformlyOn_iteratedFDeriv_pow`), hence in
  `Lᵖ` on each such compact set (`tendsto_eLpNorm_iteratedFDeriv_pow`). In particular they are
  bounded in every `Cᵏ`, hence in every `W^{k,p}`, on compact subsets, as Rellich predicts.
* On the half-disc `halfDisc = {z | ‖z‖ < 1 ∧ 0 ≤ z.im}`, `halfSine m z = m⁻¹ sin (m * z.im)`
  is bounded in `W^{1,p}` on compact sets reaching the real axis
  (`eLpNorm_halfSine_le`, `eLpNorm_fderiv_halfSine_le`) and converges uniformly to `0`
  (`tendstoUniformly_halfSine`), while its derivatives `cos (m * z.im) • imCLM` have no
  subsequence converging in `Lᵖ` on the half-disc (`not_tendsto_eLpNorm_fderiv_halfSine_sub`).
  So the conclusion of Rellich is convergence in `W^{k,p}`, not in `W^{k+1,p}`.

The non-convergence statements quantify over every strictly increasing reindexing and every
candidate limit, for every exponent `1 ≤ p ≤ ∞`. They reduce to `L¹` separation
(`TauCeti.MeasureTheory.not_tendsto_eLpNorm_sub_of_separated`) on the square `[-1/2, 1/2]²`, or
the rectangle `[-1/2, 1/2] × [0, 1/2]` on the half-disc, which follows from the oscillatory
integrals of `TauCeti.eventually_integral_sin_sub_sin_sq_ge`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and Rellich compactness).
-/

public noncomputable section

open MeasureTheory Filter Metric Real Set Topology
open scoped ENNReal

namespace TauCeti.RellichExamples

/-! ### Rectangles in the unit disc -/

/-- The square `[-1/2, 1/2]²` used to bound integrals over the unit disc from below. -/
private abbrev centralSquare : Set ℂ := Icc (-1 / 2 : ℝ) (1 / 2) ×ℂ Icc (-1 / 2 : ℝ) (1 / 2)

/-- The central square lies in the open unit disc. -/
private theorem centralSquare_subset_ball : centralSquare ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  rw [mem_ball_zero_iff]
  have hsq : ‖z‖ ^ 2 < 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 zero_le_one hsq

/-- `[-1/2, 1/2]` has length one. -/
private theorem volume_Icc_neg_half_half : volume (Icc (-1 / 2 : ℝ) (1 / 2)) = 1 := by
  rw [Real.volume_Icc]
  norm_num

/-! ### Oscillation in the interior -/

/-- The oscillating sequence `sin (m * z.re)`, bounded by `1`, with derivatives of size `m`. -/
def sineWave (m : ℕ) (z : ℂ) : ℝ := sin (m * z.re)

/-- Evaluation of the oscillating sequence `sineWave`. -/
theorem sineWave_apply (m : ℕ) (z : ℂ) : sineWave m z = sin (m * z.re) := by
  rw [sineWave]

/-- Each `sin (m * z.re)` is continuous. -/
theorem continuous_sineWave (m : ℕ) : Continuous (sineWave m) := by
  unfold sineWave
  fun_prop

/-- The oscillating sequence is bounded by `1`. -/
theorem abs_sineWave_le (m : ℕ) (z : ℂ) : |sineWave m z| ≤ 1 := abs_sin_le_one _

/-- The oscillating sequence is bounded in `Lᵖ` on every set `K` of finite measure, uniformly in
`m`, by `volume K ^ (1 / p)`; for `p = ∞` the bound is `1` on every set. -/
theorem eLpNorm_sineWave_le (m : ℕ) (p : ℝ≥0∞) (K : Set ℂ) :
    eLpNorm (sineWave m) p (volume.restrict K) ≤ volume K ^ p.toReal⁻¹ := by
  simpa using eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p) (C := 1)
    (continuous_sineWave m).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using abs_sineWave_le m z)

/-- Distinct members of the oscillating sequence stay a definite `L¹` distance apart on the
central square. -/
private theorem eventually_le_eLpNorm_sineWave_sub (m : ℕ) :
    ∀ᶠ n in atTop, ENNReal.ofReal (1 / 8) ≤
      eLpNorm (sineWave m - sineWave n) 1 (volume.restrict centralSquare) := by
  filter_upwards [eventually_integral_sin_sub_sin_sq_ge (a := -1 / 2) (b := 1 / 2)
    (by norm_num) 0 m] with n hn
  rw [eLpNorm_one_eq_lintegral_enorm
    ((continuous_sineWave m).sub (continuous_sineWave n)).aestronglyMeasurable]
  have hF : Measurable fun x : ℝ => ‖sin (m * x) - sin (n * x)‖ₑ := by fun_prop
  have := Complex.setLIntegral_reProdIm_comp_re (Icc (-1 / 2 : ℝ) (1 / 2))
    (Icc (-1 / 2 : ℝ) (1 / 2)) hF
  simp only [volume_Icc_neg_half_half, one_mul] at this
  simp only [Pi.sub_apply, sineWave]
  rw [this]
  refine le_trans ?_ (MeasureTheory.ofReal_integral_sq_div_le_lintegral_enorm (C := 2)
    (ae_of_all _ fun x => ?_))
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [add_zero] at hn
    linarith
  · calc |sin (m * x) - sin (n * x)| ≤ |sin (m * x)| + |sin (n * x)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (abs_sin_le_one _) (abs_sin_le_one _)
      _ = 2 := by norm_num

/-- No subsequence of `sin (m * z.re)` converges in `Lᵖ` on the unit disc, for any `1 ≤ p ≤ ∞`
and any candidate limit. -/
theorem not_tendsto_eLpNorm_sineWave_sub {p : ℝ≥0∞} (hp : 1 ≤ p) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {g : ℂ → ℝ} :
    ¬ Tendsto (fun k => eLpNorm (sineWave (φ k) - g) p (volume.restrict (ball 0 1)))
      atTop (𝓝 0) := by
  intro h
  have hμ : volume.restrict centralSquare ≤ volume.restrict (ball (0 : ℂ) 1) :=
    Measure.restrict_mono centralSquare_subset_ball le_rfl
  have : IsFiniteMeasure (volume.restrict centralSquare) :=
    isFiniteMeasure_restrict.2
      ((measure_mono centralSquare_subset_ball).trans_lt measure_ball_lt_top).ne
  refine MeasureTheory.not_tendsto_eLpNorm_sub_of_separated (g := g)
    (ENNReal.ofReal_pos.2 (by norm_num)) (Eventually.of_forall eventually_le_eLpNorm_sineWave_sub)
    hp hφ ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun _ => eLpNorm_mono_measure _ hμ)

/-- `sin (m * z.re)` has derivative `m cos (m * z.re) • reCLM`. -/
theorem hasFDerivAt_sineWave (m : ℕ) (z : ℂ) :
    HasFDerivAt (sineWave m) (((m : ℝ) * cos (m * z.re)) • Complex.reCLM) z := by
  refine (((Complex.reCLM.hasFDerivAt (x := z)).const_mul (m : ℝ)).sin).congr_fderiv ?_
  simp [smul_smul, mul_comm]

/-- The derivative of `sin (m * z.re)` as a function. -/
theorem fderiv_sineWave (m : ℕ) :
    fderiv ℝ (sineWave m) = fun z => ((m : ℝ) * cos (m * z.re)) • Complex.reCLM :=
  funext fun z => (hasFDerivAt_sineWave m z).fderiv

/-- The `L¹` norm of the derivative of `sin (m * z.re)` on the central square grows linearly. -/
private theorem eventually_le_eLpNorm_fderiv_sineWave :
    ∀ᶠ m : ℕ in atTop, (m : ℝ≥0∞) * ENNReal.ofReal (1 / 8) ≤
      eLpNorm (fderiv ℝ (sineWave m)) 1 (volume.restrict centralSquare) := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  rw [fderiv_sineWave, eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
  simp_rw [enorm_smul, Complex.reCLM_enorm, mul_one]
  rw [Complex.setLIntegral_reProdIm_comp_re _ _ (F := fun x => ‖(m : ℝ) * cos (m * x)‖ₑ)
      (by fun_prop),
    volume_Icc_neg_half_half, one_mul]
  simp_rw [enorm_mul, enorm_natCast]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m)]
  gcongr
  have key := MeasureTheory.ofReal_integral_sq_div_le_lintegral_enorm
    (μ := volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2))) (h := fun x : ℝ => sin (m * x + π / 2))
    (C := 2) (ae_of_all _ fun x => (abs_sin_le_one _).trans (by norm_num))
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at key
  have hint := integral_sin_mul_add_sq_ge (by positivity : (0 : ℝ) < m) (a := -1 / 2) (b := 1 / 2)
    (π / 2)
  simp only [sin_add_pi_div_two] at key hint
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) key
  have : 1 / (m : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hm'
  linarith

/-- The derivatives of `sin (m * z.re)` are unbounded in `Lᵖ` on the unit disc, for every
`1 ≤ p ≤ ∞`, so the sequence is not bounded in `W^{1,p}`. -/
theorem tendsto_eLpNorm_fderiv_sineWave {p : ℝ≥0∞} (hp : 1 ≤ p) :
    Tendsto (fun m => eLpNorm (fderiv ℝ (sineWave m)) p (volume.restrict (ball (0 : ℂ) 1)))
      atTop (𝓝 ∞) := by
  set μ := volume.restrict (ball (0 : ℂ) 1)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set C := μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (MeasureTheory.sub_one_div_toReal_nonneg hp)
    (measure_ne_top μ univ)
  have hC0 : C ≠ 0 := by
    refine (ENNReal.rpow_pos ?_ (measure_ne_top μ univ)).ne'
    simpa [μ] using measure_ball_pos volume (0 : ℂ) one_pos
  have hμ : volume.restrict centralSquare ≤ μ :=
    Measure.restrict_mono centralSquare_subset_ball le_rfl
  have hlow : Tendsto (fun m : ℕ => (m : ℝ≥0∞) * ENNReal.ofReal (1 / 8)) atTop (𝓝 ∞) := by
    have h := ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top
      (Or.inr (ENNReal.ofReal_ne_top (r := 1 / 8)))
    rwa [ENNReal.top_mul (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 1 / 8)).ne'] at h
  have h1 : Tendsto (fun m => eLpNorm (fderiv ℝ (sineWave m)) p μ * C) atTop (𝓝 ∞) := by
    refine tendsto_nhds_top_mono hlow ?_
    filter_upwards [eventually_le_eLpNorm_fderiv_sineWave] with m hm
    refine hm.trans ((eLpNorm_mono_measure _ hμ).trans ?_)
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp
      (by rw [fderiv_sineWave]; fun_prop : Continuous _).aestronglyMeasurable
  have h2 := ENNReal.Tendsto.div_const h1 (Or.inr hC0)
  simpa [ENNReal.mul_div_cancel_right hC0 hC, ENNReal.top_div_of_ne_top hC] using h2

/-! ### Powers on the unit disc -/

/-- On a compact subset of the unit disc the `k`-th real derivatives of `z ^ m` are eventually
bounded by a sequence tending to `0`. -/
theorem exists_tendsto_zero_norm_iteratedFDeriv_pow_le (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ ball 0 1) : ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ m in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z‖ ≤ b m := by
  obtain ⟨r, ⟨hr0, hr1⟩, hKr⟩ := exists_pos_lt_subset_ball one_pos hK.isClosed hKD
  refine ⟨fun m => (m : ℝ) ^ k * r ^ m / r ^ k, ?_, ?_⟩
  · simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
      (by rwa [abs_of_pos hr0])).div_const (r ^ k)
  filter_upwards [eventually_ge_atTop k] with m hm z hz
  rw [Complex.norm_iteratedFDeriv_pow]
  have hz' : ‖z‖ < r := mem_ball_zero_iff.1 (hKr hz)
  calc (m.descFactorial k : ℝ) * ‖z‖ ^ (m - k) ≤ (m : ℝ) ^ k * r ^ (m - k) :=
        mul_le_mul (by exact_mod_cast Nat.descFactorial_le_pow m k)
          (pow_le_pow_left₀ (norm_nonneg _) hz'.le _) (by positivity) (by positivity)
    _ = (m : ℝ) ^ k * r ^ m / r ^ k := by
        rw [pow_sub₀ r hr0.ne' hm]
        ring

/-- The powers `z ^ m` are smooth, hence lie in every local Sobolev class on the unit disc. -/
theorem memWkpLoc_pow (p : ℝ≥0∞) (k m : ℕ) :
    MemWkpLoc p (ball (0 : ℂ) 1) k (fun w : ℂ => w ^ m) :=
  (show ContDiff ℝ k (fun w : ℂ => w ^ m) by fun_prop).contDiffOn.memWkpLoc (Ω := ⊤) (by simp)

/-- The powers `z ^ m` converge to `0` with every real derivative, uniformly on each compact subset
of the unit disc. In particular they are bounded in every `Cᵏ` on such sets. -/
theorem tendstoUniformlyOn_iteratedFDeriv_pow (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ ball 0 1) :
    TendstoUniformlyOn (fun m z => iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z) 0 atTop K := by
  obtain ⟨b, hb, hle⟩ := exists_tendsto_zero_norm_iteratedFDeriv_pow_le k hK hKD
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [hle, hb.eventually (gt_mem_nhds hε)] with m h1 h2 z hz
  simpa [dist_zero_left] using (h1 z hz).trans_lt h2

/-- The powers `z ^ m` converge to `0` in `Lᵖ` with every real derivative on each compact subset
of the unit disc, for every exponent, as local Rellich compactness predicts. -/
theorem tendsto_eLpNorm_iteratedFDeriv_pow (p : ℝ≥0∞) (k : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ ball 0 1) :
    Tendsto (fun m => eLpNorm (iteratedFDeriv ℝ k (fun w : ℂ => w ^ m)) p (volume.restrict K))
      atTop (𝓝 0) := by
  obtain ⟨b, hb, hle⟩ := exists_tendsto_zero_norm_iteratedFDeriv_pow_le k hK hKD
  have hC : volume K ^ p.toReal⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hK.measure_lt_top.ne
  have h0 : Tendsto (fun m => volume K ^ p.toReal⁻¹ * ENNReal.ofReal (b m)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hb) (Or.inr hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hle] with m hm
  have hcont : Continuous (iteratedFDeriv ℝ k (fun w : ℂ => w ^ m)) :=
    (show ContDiff ℝ k (fun w : ℂ => w ^ m) by fun_prop).continuous_iteratedFDeriv le_rfl
  simpa using eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p) (C := b m)
    hcont.aestronglyMeasurable ((ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ hm))

/-! ### Oscillation on the half-disc -/

/-- The half-disc `D⁺₁ = {z | ‖z‖ < 1 ∧ 0 ≤ z.im}`, which contains part of the real axis. -/
def halfDisc : Set ℂ := ball 0 1 ∩ {z | 0 ≤ z.im}

/-- The half-disc is the intersection of the unit disc with the closed upper half-plane. -/
theorem halfDisc_def : halfDisc = ball 0 1 ∩ {z | 0 ≤ z.im} := by
  rw [halfDisc]

/-- A point lies in the half-disc when it has norm less than `1` and nonnegative imaginary part. -/
@[simp]
theorem mem_halfDisc {z : ℂ} : z ∈ halfDisc ↔ ‖z‖ < 1 ∧ 0 ≤ z.im := by
  rw [halfDisc_def, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq]

/-- The sequence `m⁻¹ sin (m * z.im)`, small in `C⁰` with derivatives of size one. -/
def halfSine (m : ℕ) (z : ℂ) : ℝ := (m : ℝ)⁻¹ * sin (m * z.im)

/-- Evaluation of the sequence `halfSine`. -/
theorem halfSine_apply (m : ℕ) (z : ℂ) : halfSine m z = (m : ℝ)⁻¹ * sin (m * z.im) := by
  rw [halfSine]

/-- Each `m⁻¹ sin (m * z.im)` is smooth. -/
theorem contDiff_halfSine (m : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (halfSine m) :=
  contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul Complex.imCLM.contDiff))

/-- The sequence `m⁻¹ sin (m * z.im)` is bounded by `m⁻¹`. -/
theorem abs_halfSine_le (m : ℕ) (z : ℂ) : |halfSine m z| ≤ (m : ℝ)⁻¹ := by
  rw [halfSine, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg m))]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg m)) (abs_sin_le_one _)

/-- Each `m⁻¹ sin (m * z.im)` lies in every local Sobolev class on the half-disc, with bounds
reaching the real axis. -/
theorem memWkpLoc_halfSine (p : ℝ≥0∞) (k m : ℕ) : MemWkpLoc p halfDisc k (halfSine m) :=
  (contDiff_halfSine m).contDiffOn.memWkpLoc (Ω := ⊤) (by simp)

/-- The sequence `m⁻¹ sin (m * z.im)` converges uniformly to `0`. -/
theorem tendstoUniformly_halfSine : TendstoUniformly halfSine 0 atTop := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  filter_upwards [tendsto_inv_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)] with m hm z
  simpa [Real.dist_eq] using (abs_halfSine_le m z).trans_lt hm

/-- For `m ≠ 0`, `m⁻¹ sin (m * z.im)` has derivative `cos (m * z.im) • imCLM`. -/
theorem hasFDerivAt_halfSine {m : ℕ} (hm : m ≠ 0) (z : ℂ) :
    HasFDerivAt (halfSine m) (cos (m * z.im) • Complex.imCLM) z := by
  refine ((((Complex.imCLM.hasFDerivAt (x := z)).const_mul (m : ℝ)).sin).const_mul
    ((m : ℝ)⁻¹)).congr_fderiv ?_
  rw [smul_smul, smul_smul]
  congr 1
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  simp only [Complex.imCLM_apply]
  field_simp

/-- For `m ≠ 0`, the derivative of `m⁻¹ sin (m * z.im)` as a function. -/
theorem fderiv_halfSine {m : ℕ} (hm : m ≠ 0) :
    fderiv ℝ (halfSine m) = fun z => cos (m * z.im) • Complex.imCLM :=
  funext fun z => (hasFDerivAt_halfSine hm z).fderiv

/-- The derivatives of `m⁻¹ sin (m * z.im)` have operator norm at most one. -/
theorem norm_fderiv_halfSine_le (m : ℕ) (z : ℂ) : ‖fderiv ℝ (halfSine m) z‖ ≤ 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : halfSine 0 = fun _ => 0 := funext fun _ => by simp [halfSine]
    simp [this]
  · rw [fderiv_halfSine hm, norm_smul, Complex.imCLM_norm, mul_one, Real.norm_eq_abs]
    exact abs_cos_le_one _

/-- On every set `K`, including sets reaching the real axis, `m⁻¹ sin (m * z.im)` has `Lᵖ` norm at
most `volume K ^ (1 / p) * m⁻¹`; for `p = ∞` the bound is `m⁻¹`. -/
theorem eLpNorm_halfSine_le (m : ℕ) (p : ℝ≥0∞) (K : Set ℂ) :
    eLpNorm (halfSine m) p (volume.restrict K) ≤
      volume K ^ p.toReal⁻¹ * ENNReal.ofReal (m : ℝ)⁻¹ := by
  simpa using eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p) (C := (m : ℝ)⁻¹)
    (contDiff_halfSine m (n := 0)).continuous.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using abs_halfSine_le m z)

/-- The derivatives of `m⁻¹ sin (m * z.im)` are bounded in `Lᵖ` on every set `K` of finite
measure, uniformly in `m`, by `volume K ^ (1 / p)` (by `1` for `p = ∞`), so the sequence is
bounded in `W^{1,p}` up to the real axis. -/
theorem eLpNorm_fderiv_halfSine_le (m : ℕ) (p : ℝ≥0∞) (K : Set ℂ) :
    eLpNorm (fderiv ℝ (halfSine m)) p (volume.restrict K) ≤ volume K ^ p.toReal⁻¹ := by
  simpa using eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p) (C := 1)
    ((contDiff_halfSine m (n := 1)).continuous_fderiv one_ne_zero).aestronglyMeasurable
    (ae_of_all _ fun z => norm_fderiv_halfSine_le m z)

/-- The rectangle `[-1/2, 1/2] × [0, 1/2]` inside the half-disc. -/
private abbrev halfRectangle : Set ℂ := Icc (-1 / 2 : ℝ) (1 / 2) ×ℂ Icc (0 : ℝ) (1 / 2)

/-- The half rectangle lies in the half-disc. -/
private theorem halfRectangle_subset_halfDisc : halfRectangle ⊆ halfDisc := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  refine ⟨centralSquare_subset_ball ⟨⟨h1, h2⟩, by linarith, h4⟩, h3⟩

/-- The derivatives of `m⁻¹ sin (m * z.im)` stay a definite `L¹` distance apart on the half
rectangle. -/
private theorem eventually_le_eLpNorm_fderiv_halfSine_sub :
    ∀ᶠ m in atTop, ∀ᶠ n in atTop, ENNReal.ofReal (1 / 16) ≤
      eLpNorm (fderiv ℝ (halfSine m) - fderiv ℝ (halfSine n)) 1
        (volume.restrict halfRectangle) := by
  filter_upwards [eventually_ne_atTop 0] with m hm
  filter_upwards [eventually_ne_atTop 0, eventually_integral_sin_sub_sin_sq_ge (a := 0)
    (b := 1 / 2) (by norm_num) (π / 2) m] with n hn hint
  rw [fderiv_halfSine hm, fderiv_halfSine hn, eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
  have hpt : ∀ x : ℂ, ‖cos (m * x.im) • Complex.imCLM - cos (n * x.im) • Complex.imCLM‖ₑ =
      ‖cos (m * x.im) - cos (n * x.im)‖ₑ := fun x => by
    have : cos (m * x.im) • Complex.imCLM - cos (n * x.im) • Complex.imCLM =
        (cos (m * x.im) - cos (n * x.im)) • Complex.imCLM := (sub_smul _ _ _).symm
    rw [this, enorm_smul, Complex.imCLM_enorm, mul_one]
  simp only [Pi.sub_apply, hpt]
  rw [Complex.setLIntegral_reProdIm_comp_im _ _ (F := fun y => ‖cos (m * y) - cos (n * y)‖ₑ)
    (by fun_prop), volume_Icc_neg_half_half, one_mul]
  have key := MeasureTheory.ofReal_integral_sq_div_le_lintegral_enorm
    (μ := volume.restrict (Icc (0 : ℝ) (1 / 2)))
    (h := fun y : ℝ => sin (m * y + π / 2) - sin (n * y + π / 2)) (C := 2)
    (ae_of_all _ fun y => (abs_sub _ _).trans ((add_le_add (abs_sin_le_one _)
      (abs_sin_le_one _)).trans (by norm_num)))
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at key
  simp only [sin_add_pi_div_two] at key hint
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) key
  linarith

/-- The derivatives `cos (m * z.im) • imCLM` of `m⁻¹ sin (m * z.im)` have no subsequence
converging in `Lᵖ` on the half-disc, for any `1 ≤ p ≤ ∞` and any candidate limit. -/
theorem not_tendsto_eLpNorm_fderiv_halfSine_sub {p : ℝ≥0∞} (hp : 1 ≤ p) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {G : ℂ → ℂ →L[ℝ] ℝ} :
    ¬ Tendsto (fun k => eLpNorm (fderiv ℝ (halfSine (φ k)) - G) p (volume.restrict halfDisc))
      atTop (𝓝 0) := by
  intro h
  have hμ : volume.restrict halfRectangle ≤ volume.restrict halfDisc :=
    Measure.restrict_mono halfRectangle_subset_halfDisc le_rfl
  have : IsFiniteMeasure (volume.restrict halfRectangle) :=
    isFiniteMeasure_restrict.2 ((measure_mono (halfRectangle_subset_halfDisc.trans
      inter_subset_left)).trans_lt measure_ball_lt_top).ne
  refine MeasureTheory.not_tendsto_eLpNorm_sub_of_separated (g := G)
    (ENNReal.ofReal_pos.2 (by norm_num)) eventually_le_eLpNorm_fderiv_halfSine_sub hp hφ ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun _ => eLpNorm_mono_measure _ hμ)

end TauCeti.RellichExamples
