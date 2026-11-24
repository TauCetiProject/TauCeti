/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic
import TauCeti.MeasureTheory.Function.SimpleFunc.Lp

/-!
# Complex interpolation of Lebesgue spaces: `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ`

For `1 ≤ p₀, p₁ ≤ ∞`, `0 ≤ θ ≤ 1` and the interpolated exponent
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, every `f ∈ Lᵖ(μ; E)` lies in the complex
interpolation space `[L^{p₀}, L^{p₁}]_θ` of the Lebesgue couple, with
`‖f‖_{[L^{p₀}, L^{p₁}]_θ} ≤ ‖f‖_{Lᵖ}`. This is one of the two inclusions of the identity
`[L^{p₀}, L^{p₁}]_θ = Lᵖ` (Bergh–Löfström, Theorem 5.1.1), the base case of the complex
interpolation of Bessel-potential spaces `[H^{s₀,p₀}, H^{s₁,p₁}]_θ = H^{s_θ,p_θ}`.

The coefficients `E` are an arbitrary complex Banach space.

## Main declarations

* `TauCeti.CompatibleCouple.lpToLebesgueComplexMethod`: the inclusion
  `Lᵖ → [L^{p₀}, L^{p₁}]_θ`, a continuous linear map of norm at most one
  (`TauCeti.CompatibleCouple.norm_lpToLebesgueComplexMethod_le`). It lies over the embedding
  `Lᵖ → L¹ + L^∞` (`TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_lpToLebesgueComplexMethod`),
  and over `TauCeti.CompatibleCouple.lpToLebesgueSum` when `p₀ ≤ p ≤ p₁`.
* `TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le`: the inclusion with
  its norm bound as an existence statement, which also covers `p = p₀ = p₁ = ∞`, and its
  `0 < θ < 1` form `..._of_mem_Ioo`, valid for every `p`.

## The argument

For a simple function `f` with finite-measure support, put `s = (1/p₁ - 1/p₀) p` and
`f_z = ‖f‖ ^ ((z - θ) s) f`. Then `f_θ = f`, and pointwise `‖f_z‖ = ‖f‖ ^ (1 + (re z - θ) s)`,
where the exponent is `p / p₀` on the line `re z = 0` and `p / p₁` on the line `re z = 1`. Hence
`‖f_{i t}‖_{p₀} ≤ ‖f‖_p ^ (p / p₀)` and `‖f_{1 + i t}‖_{p₁} ≤ ‖f‖_p ^ (p / p₁)`, and the geometric
mean of these bounds with weights `1 - θ`, `θ` is `‖f‖_p`. Since `f` takes finitely many values,
`f_z` is a finite sum of entire functions of `z` times fixed elements of `L^{p₀} ∩ L^{p₁}`.
We let `λ ↦ λ f_z` be a bounded analytic family of operators from the trivial couple `(ℂ, ℂ)` to
the Lebesgue couple, and Stein's interpolation theorem
(`TauCeti.CompatibleCouple.ComplexMethodSpace.norm_analyticFamilyMap_le`) applied to `1 ∈ [ℂ, ℂ]_θ`
bounds `‖f‖_θ` by `‖f‖_p`. Simple functions are dense in `Lᵖ` for `p < ∞`, so the inclusion
extends by continuity.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.1).
-/

public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

open Complex.HadamardThreeLines

/-! ### The analytic family `‖v‖ ^ ((z - θ) s) v` -/

section Family

variable {E : Type*} [NormedAddCommGroup E] {θ s : ℝ}

/-- The scalar `‖v‖ ^ ((z - θ) s)`, written as an exponential so that it is entire in `z` for
every `v`. -/
private def coeff (θ s : ℝ) (v : E) (z : ℂ) : ℂ :=
  exp ((z - θ) * ((s * Real.log ‖v‖ : ℝ) : ℂ))

private theorem coeff_self (v : E) : coeff θ s v θ = 1 := by
  simp [coeff]

private theorem differentiable_coeff (v : E) : Differentiable ℂ (coeff θ s v) := by
  unfold coeff
  fun_prop

private theorem norm_coeff (v : E) (z : ℂ) :
    ‖coeff θ s v z‖ = Real.exp ((z.re - θ) * (s * Real.log ‖v‖)) := by
  simp [coeff, norm_exp]

/-- On the closed strip, `‖v‖ ^ ((z - θ) s)` is bounded uniformly in `z`. -/
private theorem norm_coeff_le (hθ : θ ∈ Icc (0 : ℝ) 1) (v : E) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖coeff θ s v z‖ ≤ Real.exp |s * Real.log ‖v‖| := by
  rw [norm_coeff]
  have hz' := mem_verticalClosedStrip_iff.1 hz
  have h1 : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith [hz'.1, hθ.2], by linarith [hz'.2, hθ.1]⟩
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) h1

variable [NormedSpace ℂ E]

/-- The member `‖v‖ ^ ((z - θ) s) v` of the analytic family through `v`. -/
private def famSMul (θ s : ℝ) (z : ℂ) (v : E) : E :=
  coeff θ s v z • v

private theorem famSMul_self (v : E) : famSMul θ s θ v = v := by
  simp [famSMul, coeff_self]

private theorem famSMul_zero (z : ℂ) : famSMul θ s z (0 : E) = 0 := by
  simp [famSMul]

/-- The pointwise size of the analytic family: `‖‖v‖ ^ ((z - θ) s) v‖ ≤ ‖v‖ ^ (1 + (re z - θ) s)`,
with equality for `v ≠ 0`. -/
private theorem norm_famSMul_le (z : ℂ) (v : E) :
    ‖famSMul θ s z v‖ ≤ ‖v‖ ^ (1 + (z.re - θ) * s) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa [famSMul_zero] using Real.rpow_nonneg le_rfl _
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine le_of_eq ?_
    simp only [famSMul, norm_smul, norm_coeff, Real.rpow_add hpos, Real.rpow_def_of_pos hpos,
      mul_one, Real.exp_log hpos]
    ring_nf

end Family

/-! ### Bounded analytic families out of the trivial couple -/

section SumFamily

variable {X₀ X₁ V : Type*} [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁]
  [NormedSpace ℂ X₁] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V]
  [T1Space V] (C : CompatibleCouple ℂ X₀ X₁ V) {ι : Type*} (S : Finset ι) (φ : ι → ℂ → ℂ)
  (x : ι → C.inter)

/-- The family `λ ↦ λ ∑ i, φ i z • x i` of operators from the trivial couple `(ℂ, ℂ)` to `C`. -/
private def sumFamily (z : ℂ) : (refl ℂ ℂ).SumSpace →L[ℂ] C.SumSpace :=
  (refl ℂ ℂ).sumSpaceEmbed.smulRight (∑ i ∈ S, φ i z • C.fstToSum (C.interFst (x i)))

omit [T1Space V] in
private theorem sumFamily_apply_fstToSum (z : ℂ) (c : ℂ) :
    sumFamily C S φ x z ((refl ℂ ℂ).fstToSum c) =
      c • ∑ i ∈ S, φ i z • C.fstToSum (C.interFst (x i)) := by
  simp [sumFamily, sumSpaceEmbed_fstToSum]

/-- If the coefficients `φ i` are entire and bounded on the closed strip, `sumFamily` is a bounded
analytic family, with boundary operators `λ ↦ λ ∑ i, φ i (i t) • x i` into `X₀` and
`λ ↦ λ ∑ i, φ i (1 + i t) • x i` into `X₁`. -/
private theorem isBoundedAnalyticFamily_sumFamily (hφ : ∀ i, Differentiable ℂ (φ i))
    (hb : ∀ i, ∃ K, ∀ z ∈ verticalClosedStrip 0 1, ‖φ i z‖ ≤ K) :
    IsBoundedAnalyticFamily (sumFamily C S φ x)
      (fun t => ContinuousLinearMap.toSpanSingleton ℂ
        (∑ i ∈ S, φ i (t * I) • C.interFst (x i)))
      (fun t => ContinuousLinearMap.toSpanSingleton ℂ
        (∑ i ∈ S, φ i (1 + t * I) • C.interSnd (x i))) := by
  choose K hK using hb
  have hF : Differentiable ℂ fun z => ∑ i ∈ S, φ i z • C.fstToSum (C.interFst (x i)) :=
    Differentiable.fun_sum fun i _ => (hφ i).smul_const _
  have hdiff : Differentiable ℂ (sumFamily C S φ x) := by
    have h := (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (refl ℂ ℂ).SumSpace C.SumSpace
      (refl ℂ ℂ).sumSpaceEmbed).differentiable.comp hF
    convert h using 1
    funext z
    simp only [Function.comp_apply, ContinuousLinearMap.smulRightL_apply_apply, sumFamily]
  have hline₀ : Continuous fun t : ℝ => ∑ i ∈ S, φ i (t * I) • C.interFst (x i) :=
    continuous_finsetSum _ fun i _ => ((hφ i).continuous.comp (by fun_prop)).smul
      continuous_const
  have hline₁ : Continuous fun t : ℝ => ∑ i ∈ S, φ i (1 + t * I) • C.interSnd (x i) :=
    continuous_finsetSum _ fun i _ => ((hφ i).continuous.comp (by fun_prop)).smul
      continuous_const
  refine
    { differentiableOn := hdiff.differentiableOn
      continuousOn_apply := fun u => (hdiff.continuous.clm_apply continuous_const).continuousOn
      exists_norm_le := ⟨‖(refl ℂ ℂ).sumSpaceEmbed‖ *
          ∑ i ∈ S, K i * ‖C.fstToSum (C.interFst (x i))‖, fun z hz => ?_⟩
      continuous_fst := fun c => by
        simp only [ContinuousLinearMap.toSpanSingleton_apply]
        exact continuous_const.smul hline₀
      continuous_snd := fun c => by
        simp only [ContinuousLinearMap.toSpanSingleton_apply]
        exact continuous_const.smul hline₁
      exists_norm_fst_le := ⟨∑ i ∈ S, K i * ‖C.interFst (x i)‖, fun t => ?_⟩
      exists_norm_snd_le := ⟨∑ i ∈ S, K i * ‖C.interSnd (x i)‖, fun t => ?_⟩
      apply_mul_I := fun t c => ?_
      apply_one_add_mul_I := fun t c => ?_ }
  · rw [sumFamily, ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_left (norm_sum_le_of_le S fun i _ => (norm_smul _ _).trans_le
      (mul_le_mul_of_nonneg_right (hK i z hz) (norm_nonneg _))) (norm_nonneg _)
  · rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact norm_sum_le_of_le S fun i _ => (norm_smul _ _).trans_le
      (mul_le_mul_of_nonneg_right (hK i _ (by simp)) (norm_nonneg _))
  · rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact norm_sum_le_of_le S fun i _ => (norm_smul _ _).trans_le
      (mul_le_mul_of_nonneg_right (hK i _ (by simp)) (norm_nonneg _))
  · simp [sumFamily_apply_fstToSum, map_sum, map_smul]
  · have hc : (refl ℂ ℂ).sndToSum c = (refl ℂ ℂ).fstToSum c :=
      sumSpace_ext _ (by simp [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum])
    rw [hc, sumFamily_apply_fstToSum]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, map_smul, map_sum, fstToSum_interFst]

end SumFamily

/-! ### Simple functions -/

section SimpleFunc

variable {E : Type*} [NormedAddCommGroup E] {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The restriction `c 𝟙_{f = c}` of a simple function `f` to its fibre over `c`. -/
private def fiber (f : SimpleFunc α E) (c : E) : SimpleFunc α E :=
  (SimpleFunc.const α c).restrict (f ⁻¹' {c})

variable [NormedSpace ℂ E]

/-- An element of `L^q` given as a combination of fibres of `f` agrees almost everywhere with the
analytic family through `f`. -/
private theorem coeFn_sum_coeff_smul_toLp {θ s : ℝ} (f : SimpleFunc α E) {q : ℝ≥0∞}
    (h : ∀ c, MemLp (fiber f c) q μ) (z : ℂ) :
    ⇑(∑ c ∈ f.range, coeff θ s c z • (h c).toLp (fiber f c)) =ᵐ[μ]
      fun x => famSMul θ s z (f x) :=
  Lp.coeFn_sum_smul_restrict_const f (fun c => coeff θ s c z) (fun c => (h c).toLp (fiber f c))
    fun c => (h c).coeFn_toLp

end SimpleFunc

/-! ### The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` -/

section Inclusion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α : Type*} {mα : MeasurableSpace α}
  {μ : Measure α} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] {θ : ℝ}

/-- The fibre of a simple function `f ∈ Lᵖ`, `p < ∞`, over `c` as an element of
`L^{p₀} ∩ L^{p₁}`. -/
private def fiberInter {f : SimpleFunc α E} (hf : MemLp f p μ) (hp_top : p ≠ ∞) (c : E) :
    (lebesgue ℂ E μ p₀ p₁).inter :=
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have h₀ : MemLp (fiber f c) p₀ μ :=
    SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf hp0 hp_top p₀ c
  have h₁ : MemLp (fiber f c) p₁ μ :=
    SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf hp0 hp_top p₁ c
  ⟨(h₀.toLp _, h₁.toLp _), mem_lebesgue_inter_iff.2 (h₀.coeFn_toLp.trans h₁.coeFn_toLp.symm)⟩

private theorem interFst_fiberInter {f : SimpleFunc α E} (hf : MemLp f p μ) (hp_top : p ≠ ∞)
    (c : E) : (lebesgue ℂ E μ p₀ p₁).interFst (fiberInter hf hp_top c) =
      (SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf (zero_lt_one.trans_le Fact.out).ne'
        hp_top p₀ c).toLp (fiber f c) := by
  rw [interFst_apply]
  rfl

private theorem interSnd_fiberInter {f : SimpleFunc α E} (hf : MemLp f p μ) (hp_top : p ≠ ∞)
    (c : E) : (lebesgue ℂ E μ p₀ p₁).interSnd (fiberInter hf hp_top c) =
      (SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf (zero_lt_one.trans_le Fact.out).ne'
        hp_top p₁ c).toLp (fiber f c) := by
  rw [interSnd_apply]
  rfl

omit [Fact (1 ≤ p)] in
/-- The boundary operators of the analytic family through a simple function `f`: on a line where
`1 + (re z - θ) s = r` and `1 / q = r / p`, the operator `λ ↦ λ f_z` into `L^q` has norm at most
`‖f‖_p ^ r`. -/
private theorem norm_toSpanSingleton_sum_coeff_smul_le {θ s : ℝ} (f : SimpleFunc α E)
    (hf : MemLp f p μ) {q : ℝ≥0∞} [Fact (1 ≤ q)] (h : ∀ c, MemLp (fiber f c) q μ) {z : ℂ}
    (hr : 0 ≤ 1 + (z.re - θ) * s) (hq : q⁻¹ = ENNReal.ofReal (1 + (z.re - θ) * s) * p⁻¹)
    (c : ℂ) :
    ‖ContinuousLinearMap.toSpanSingleton ℂ
        (∑ e ∈ f.range, coeff θ s e z • (h e).toLp (fiber f e)) c‖ ≤
      (eLpNorm f p μ).toReal ^ (1 + (z.re - θ) * s) * ‖c‖ := by
  rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg c)
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_sum_coeff_smul_toLp f h z), ENNReal.toReal_rpow]
  refine ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hr hf.eLpNorm_ne_top)
    (eLpNorm_le_eLpNorm_rpow hr (f.map (famSMul θ s z)).aestronglyMeasurable hq
      (ae_of_all _ fun x => norm_famSMul_le z (f x)))

/-- At `z = θ` the analytic family `λ ↦ λ f_z` through a simple function `f` sends `1` to `f`. -/
private theorem sumSpaceEmbed_sumFamily_self {s : ℝ} (f : SimpleFunc α E) (hf : MemLp f p μ)
    (hp_top : p ≠ ∞) (g : Lp E p μ) (hfg : ⇑g =ᵐ[μ] f) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (sumFamily (lebesgue ℂ E μ p₀ p₁) f.range (coeff θ s)
      (fiberInter hf hp_top) θ ((refl ℂ ℂ).fstToSum 1)) = L1AddLinfty.ofLp g := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have h₀ : ∀ c, MemLp (fiber f c) p₀ μ :=
    SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf hp0 hp_top p₀
  have hG : (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (sumFamily (lebesgue ℂ E μ p₀ p₁) f.range
      (coeff θ s) (fiberInter hf hp_top) θ ((refl ℂ ℂ).fstToSum 1)) =
        L1AddLinfty.ofLp (∑ c ∈ f.range, coeff θ s c θ • (h₀ c).toLp (fiber f c)) := by
    rw [sumFamily_apply_fstToSum, one_smul]
    simp only [interFst_fiberInter]
    simp [map_sum, map_smul, sumSpaceEmbed_fstToSum]
  rw [hG]
  refine L1AddLinfty.ofLp_eq_ofLp_iff.2
    ((coeFn_sum_coeff_smul_toLp f h₀ (θ : ℂ)).trans ?_)
  filter_upwards [hfg] with y hy
  rw [famSMul_self, hy]

/-- **The bound for simple functions.** A simple function `f ∈ Lᵖ` lies in
`[L^{p₀}, L^{p₁}]_θ` with norm at most `‖f‖_p`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (f : SimpleFunc α E) (g : Lp E p μ) (hfg : ⇑g =ᵐ[μ] f) :
    ∃ v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) = L1AddLinfty.ofLp g ∧
        ‖v‖ ≤ ‖g‖ := by
  have hf : MemLp f p μ := (Lp.memLp g).ae_eq hfg
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  obtain ⟨s, hr₀, hr₁, hq₀, hq₁⟩ := exists_inv_eq_ofReal_mul_inv_of_inv_eq
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
    hp_top hθ hp
  -- the exponent `1 + (re z - θ) s` on the line `re z = 0`
  have hexp₀ : 1 - θ * s = 1 + (0 - θ) * s := by ring
  rw [hexp₀] at hr₀ hq₀
  -- the bounded analytic family `λ ↦ λ f_z` with `f_z = ‖f‖ ^ ((z - θ) s) f`
  have hT := isBoundedAnalyticFamily_sumFamily (lebesgue ℂ E μ p₀ p₁) f.range (coeff θ s)
    (fiberInter hf hp_top) (fun c => differentiable_coeff c)
    (fun c => ⟨_, fun z hz => norm_coeff_le hθ c hz⟩)
  set N := (eLpNorm f p μ).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hre₀ (t : ℝ) : (t * I : ℂ).re = 0 := by simp
  have hre₁ (t : ℝ) : (1 + t * I : ℂ).re = 1 := by simp
  have h₀ (t : ℝ) := norm_toSpanSingleton_sum_coeff_smul_le (z := t * I) f hf (q := p₀)
    (SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf hp0 hp_top p₀)
    (by rwa [hre₀]) (by rwa [hre₀])
  have h₁ (t : ℝ) := norm_toSpanSingleton_sum_coeff_smul_le (z := 1 + t * I) f hf (q := p₁)
    (SimpleFunc.memLp_restrict_const_fiber eNorm_zero hf hp0 hp_top p₁)
    (by rwa [hre₁]) (by rwa [hre₁])
  simp only [hre₀, hre₁] at h₀ h₁
  -- Stein's theorem applied to `1 ∈ [ℂ, ℂ]_θ`
  set one : (refl ℂ ℂ).inter := ⟨(1, 1), by simp [mem_inter_iff]⟩
  refine ⟨ComplexMethodSpace.analyticFamilyMap θ hT (ComplexMethodSpace.ofInter θ one), ?_, ?_⟩
  · have hone₁ : (refl ℂ ℂ).interFst one = 1 := by rw [interFst_apply]
    rw [ComplexMethodSpace.toSum_analyticFamilyMap, ComplexMethodSpace.toSum_ofInter hθ, hone₁]
    exact sumSpaceEmbed_sumFamily_self f hf hp_top g hfg
  · refine (ComplexMethodSpace.norm_analyticFamilyMap_le hT hθ (M₀ := N ^ (1 + (0 - θ) * s))
      (M₁ := N ^ (1 + (1 - θ) * s)) (by positivity) (by positivity)
      (fun t c => by simpa only [interFst_fiberInter] using h₀ t c)
      (fun t c => by simpa only [interSnd_fiberInter] using h₁ t c) _).trans ?_
    have hone : ‖ComplexMethodSpace.ofInter θ one‖ ≤ 1 :=
      (ComplexMethodSpace.norm_ofInter_le hθ one).trans (by simp [one])
    calc (N ^ (1 + (0 - θ) * s)) ^ (1 - θ) * (N ^ (1 + (1 - θ) * s)) ^ θ *
          ‖ComplexMethodSpace.ofInter θ one‖
        ≤ (N ^ (1 + (0 - θ) * s)) ^ (1 - θ) * (N ^ (1 + (1 - θ) * s)) ^ θ * 1 :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = N := by
          have hexp : (1 + (0 - θ) * s) * (1 - θ) + (1 + (1 - θ) * s) * θ = 1 := by ring
          rw [mul_one, Real.rpow_rpow_mul_rpow_rpow_of_add_eq hN one_ne_zero hexp,
            Real.rpow_one]
      _ = ‖g‖ := by rw [Lp.norm_def, eLpNorm_congr_ae hfg]

attribute [local instance] Lp.simpleFunc.module

/-- `exists_sumSpaceEmbed_toSum_eq_and_norm_le` for the simple functions of `Lᵖ`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_simpleFunc (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (g : Lp.simpleFunc E p μ) :
    ∃ v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        L1AddLinfty.ofLp (g : Lp E p μ) ∧ ‖v‖ ≤ ‖(g : Lp E p μ)‖ :=
  exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hp hp_top (Lp.simpleFunc.toSimpleFunc g)
    (g : Lp E p μ) (Lp.simpleFunc.toSimpleFunc_eq_toFun g).symm

/-- The element of `[L^{p₀}, L^{p₁}]_θ` chosen for a simple function of `Lᵖ` is that function. -/
private theorem sumSpaceEmbed_toSum_choose (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (g : Lp.simpleFunc E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum
        (exists_sumSpaceEmbed_toSum_eq_and_norm_le_simpleFunc hθ hp hp_top g).choose) =
      L1AddLinfty.ofLp (g : Lp E p μ) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le_simpleFunc hθ hp hp_top g).choose_spec.1

omit [Fact (1 ≤ p)] in
/-- Elements of `[L^{p₀}, L^{p₁}]_θ` are determined by their images in `L¹ + L^∞`. -/
private theorem eq_of_sumSpaceEmbed_toSum_eq {u v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ}
    (h : (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) =
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v)) : u = v :=
  ComplexMethodSpace.toSum_injective ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective h)

/-- The inclusion of the simple functions of `Lᵖ` into `[L^{p₀}, L^{p₁}]_θ`. -/
private def simpleFuncToComplexMethod (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞) :
    Lp.simpleFunc E p μ →ₗ[ℂ] (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ where
  toFun g := (exists_sumSpaceEmbed_toSum_eq_and_norm_le_simpleFunc hθ hp hp_top g).choose
  map_add' g h := eq_of_sumSpaceEmbed_toSum_eq <| by
    rw [sumSpaceEmbed_toSum_choose hθ hp hp_top]
    simp [sumSpaceEmbed_toSum_choose hθ hp hp_top, map_add]
  map_smul' c g := eq_of_sumSpaceEmbed_toSum_eq <| by
    rw [sumSpaceEmbed_toSum_choose hθ hp hp_top]
    simp [sumSpaceEmbed_toSum_choose hθ hp hp_top, map_smul]

private theorem sumSpaceEmbed_toSum_simpleFuncToComplexMethod (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (g : Lp.simpleFunc E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum (simpleFuncToComplexMethod hθ hp hp_top g)) =
      L1AddLinfty.ofLp (g : Lp E p μ) :=
  sumSpaceEmbed_toSum_choose hθ hp hp_top g

private theorem norm_simpleFuncToComplexMethod_le (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (g : Lp.simpleFunc E p μ) :
    ‖simpleFuncToComplexMethod hθ hp hp_top g‖ ≤ 1 * ‖Lp.simpleFunc.coeToLp α E ℂ g‖ := by
  simp only [simpleFuncToComplexMethod, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
  exact (exists_sumSpaceEmbed_toSum_eq_and_norm_le_simpleFunc hθ hp hp_top g).choose_spec.2

variable [CompleteSpace E]

/-- **Complex interpolation of Lebesgue spaces, `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ`.** For `0 ≤ θ ≤ 1` and
the interpolated exponent `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, the inclusion of `Lᵖ`
into the complex interpolation space of the Lebesgue couple `(L^{p₀}, L^{p₁})`. It lies over the
embedding of `Lᵖ` into `L¹ + L^∞` (`sumSpaceEmbed_toSum_lpToLebesgueComplexMethod`) and has norm
at most one (`norm_lpToLebesgueComplexMethod_le`). -/
def lpToLebesgueComplexMethod (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞) :
    Lp E p μ →L[ℂ] (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ :=
  (simpleFuncToComplexMethod hθ hp hp_top).extendOfNorm
    (Lp.simpleFunc.coeToLp α E ℂ : Lp.simpleFunc E p μ →L[ℂ] Lp E p μ).toLinearMap

variable (hθ : θ ∈ Icc (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` lies over the embedding of `Lᵖ` into `L¹ + L^∞`:
the element of `[L^{p₀}, L^{p₁}]_θ` it produces is `f` itself. -/
@[simp]
theorem sumSpaceEmbed_toSum_lpToLebesgueComplexMethod (f : Lp E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum (lpToLebesgueComplexMethod hθ hp hp_top f)) =
      L1AddLinfty.ofLp f := by
  refine congrFun ((Lp.simpleFunc.denseRange hp_top).equalizer
    ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed.comp
      (ComplexMethodSpace.toSum.comp (lpToLebesgueComplexMethod hθ hp hp_top))).continuous
    (L1AddLinfty.ofLp : Lp E p μ →L[ℂ] L1AddLinfty ℂ E μ).continuous (funext fun g => ?_)) f
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
  rw [← sumSpaceEmbed_toSum_simpleFuncToComplexMethod hθ hp hp_top g, lpToLebesgueComplexMethod]
  congr 2
  exact LinearMap.extendOfNorm_eq (Lp.simpleFunc.denseRange hp_top)
    ⟨1, norm_simpleFuncToComplexMethod_le hθ hp hp_top⟩ g

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` does not increase norms:
`‖f‖_{[L^{p₀}, L^{p₁}]_θ} ≤ ‖f‖_{Lᵖ}`. -/
theorem norm_lpToLebesgueComplexMethod_le (f : Lp E p μ) :
    ‖lpToLebesgueComplexMethod hθ hp hp_top f‖ ≤ ‖f‖ := by
  rw [lpToLebesgueComplexMethod]
  simpa using LinearMap.norm_extendOfNorm_apply_le (Lp.simpleFunc.denseRange hp_top) 1
    (norm_simpleFuncToComplexMethod_le hθ hp hp_top) f

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` has operator norm at most one. -/
theorem opNorm_lpToLebesgueComplexMethod_le :
    ‖(lpToLebesgueComplexMethod hθ hp hp_top :
      Lp E p μ →L[ℂ] (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_lpToLebesgueComplexMethod_le hθ hp hp_top f

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` is injective. -/
theorem lpToLebesgueComplexMethod_injective :
    Function.Injective (lpToLebesgueComplexMethod hθ hp hp_top :
      Lp E p μ → (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) := fun f g h => by
  have := congrArg (fun u => (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u)) h
  simpa using L1AddLinfty.ofLp_injective (by simpa using this)

/-- For `p₀ ≤ p ≤ p₁`, the inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` lies over the inclusion
`Lᵖ → L^{p₀} + L^{p₁}`. -/
theorem toSum_lpToLebesgueComplexMethod (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    ComplexMethodSpace.toSum (lpToLebesgueComplexMethod hθ hp hp_top f) =
      lpToLebesgueSum h₀ h₁ f :=
  sumSpace_ext _ (by simp)

/-- **`Lᵖ` lies in the complex interpolation space of the Lebesgue couple.** Let `0 ≤ θ ≤ 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁`, with `p < ∞` unless `p₀ = p₁ = ∞`. Every `f ∈ Lᵖ(μ; E)` is an
element of `[L^{p₀}, L^{p₁}]_θ`, of norm at most `‖f‖_p`: there is `u ∈ [L^{p₀}, L^{p₁}]_θ` whose
image in `L¹ + L^∞` is `f` and with `‖u‖_θ ≤ ‖f‖_p`. For `p < ∞` this is
`lpToLebesgueComplexMethod`; when `p₀ = p₁ = ∞`, `f` lies in the intersection. -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hp_top : p = ∞ → p₀ = ∞ ∧ p₁ = ∞) (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ := by
  by_cases hp_top' : p = ∞
  · obtain ⟨rfl, rfl⟩ := hp_top hp_top'
    subst hp_top'
    refine ⟨ComplexMethodSpace.ofInter θ ⟨(f, f), mem_lebesgue_inter_iff.2 .rfl⟩, ?_,
      (ComplexMethodSpace.norm_ofInter_le hθ _).trans (by simp)⟩
    simp [ComplexMethodSpace.toSum_ofInter hθ]
  exact ⟨lpToLebesgueComplexMethod hθ hp hp_top' f,
    sumSpaceEmbed_toSum_lpToLebesgueComplexMethod hθ hp hp_top' f,
    norm_lpToLebesgueComplexMethod_le hθ hp hp_top' f⟩

/-- **`Lᵖ` lies in the complex interpolation space of the Lebesgue couple**, for `0 < θ < 1`:
`exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le`, since for `0 < θ < 1` the only infinite `p`
is `p₀ = p₁ = ∞`. -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le_of_mem_Ioo (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ :=
  exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le (Ioo_subset_Icc_self hθ) hp
    (eq_top_iff_of_inv_eq hθ hp).1 f

end Inclusion

end TauCeti.CompatibleCouple
