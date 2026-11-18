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
import TauCeti.Analysis.Calculus.DiffContOnCl
import TauCeti.Analysis.Complex.InterpolatedExponent
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic

/-!
# Complex interpolation of Lebesgue spaces

For `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the interpolated exponent
`1 / p = (1 - θ) / p₀ + θ / p₁`, the complex interpolation space of the Lebesgue couple
`(L^{p₀}, L^{p₁})` (`TauCeti.CompatibleCouple.lebesgue`) is `Lᵖ`, with equal norms:

`[L^{p₀}, L^{p₁}]_θ = Lᵖ`,

for functions on a σ-finite measure space with values in a complex Hilbert space
(Bergh–Löfström, Theorems 5.1.1 and 5.1.2). This is the base case of the complex interpolation of
Bessel-potential spaces `[H^{s₀,p₀}, H^{s₁,p₁}]_θ = H^{s_θ,p_θ}`.

## Main declarations

* `TauCeti.CompatibleCouple.lpToLebesgueComplexMethod`: the inclusion
  `Lᵖ → [L^{p₀}, L^{p₁}]_θ` for `0 ≤ θ ≤ 1` and `p < ∞`, a continuous linear map of norm at most
  one (`TauCeti.CompatibleCouple.norm_lpToLebesgueComplexMethod_le`), for any complex Banach space
  of values and any measure. It lies over the embedding `Lᵖ → L¹ + L^∞`
  (`TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_lpToLebesgueComplexMethod`), and over
  `TauCeti.CompatibleCouple.lpToLebesgueSum` when `p₀ ≤ p ≤ p₁`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.exists_ofLp_eq_sumSpaceEmbed_toSum`: the reverse
  inclusion `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ` with `‖f‖_p ≤ ‖f‖_θ`, for values in a complex inner product
  space and a σ-finite measure.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.lebesgueEquiv`: the isometric isomorphism
  `[L^{p₀}, L^{p₁}]_θ ≃ₗᵢ[ℂ] Lᵖ`, matching the elements with the same class in `L¹ + L^∞`. It
  sends a decomposition `f₀ + f₁ ∈ L^{p₀} + L^{p₁}` to the function `f₀ + f₁`
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.coeFn_lebesgueEquiv_ae_eq_add_iff`) and an element
  of the intersection to its function
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.coeFn_lebesgueEquiv_ofInter`); for `p < ∞` its
  inverse is `lpToLebesgueComplexMethod`.

## The argument

* `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ`. For a simple function `f` with finite-measure support, put
  `s = (1/p₁ - 1/p₀) p` and `f_z = ‖f‖ ^ ((z - θ) s) f`. Then `f_θ = f`, and pointwise
  `‖f_z‖ = ‖f‖ ^ (1 + (re z - θ) s)`, where the exponent is `p / p₀` on the line `re z = 0` and
  `p / p₁` on the line `re z = 1`. Hence `‖f_{i t}‖_{p₀} ≤ ‖f‖_p ^ (p / p₀)` and
  `‖f_{1 + i t}‖_{p₁} ≤ ‖f‖_p ^ (p / p₁)`, and the geometric mean of these bounds with weights
  `1 - θ`, `θ` is `‖f‖_p`. Since `f` takes finitely many values, `f_z` is a finite sum of entire
  functions of `z` times fixed elements of `L^{p₀} ∩ L^{p₁}`. We let `λ ↦ λ f_z` be a bounded
  analytic family of operators from the trivial couple `(ℂ, ℂ)` to the Lebesgue couple, and Stein's
  interpolation theorem (`TauCeti.CompatibleCouple.ComplexMethodSpace.norm_analyticFamilyMap_le`)
  applied to `1 ∈ [ℂ, ℂ]_θ` bounds `‖f‖_θ` by `‖f‖_p`. Simple functions are dense in `Lᵖ` for
  `p < ∞`, so the inclusion extends by continuity. For `p = ∞` both endpoints are `L^∞`.
* `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ`. Let `F` be an admissible function with `F θ = f`. Pair `F` with the
  dual analytic family `z ↦ ‖g‖ ^ P'(z) ‖g‖⁻¹ g` of a test function `g`, where
  `P'(z) = 1 + (z - θ) (b₁ - b₀) / b` (`TauCeti.interpExponent`) for the conjugate exponents
  `b_j = 1 - 1 / p_j` and `b = 1 - 1 / p`. Hadamard's three-lines theorem then bounds `|∫ ⟪g, f⟫|`
  by the norm of the traces of `F` times `‖g‖_{p'}`. This pairing is a finite sum of holomorphic
  functions when `‖g‖` is simple. Approximating `‖g‖` from below by simple functions extends the
  bound to bounded `g` of finite-measure support, and duality
  (`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_norm_integral_inner_le`) bounds
  `‖f‖_p`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorems 5.1.1 and 5.1.2).
-/

public noncomputable section

open MeasureTheory Complex Set Filter Topology Complex.HadamardThreeLines
open scoped ENNReal InnerProductSpace ComplexConjugate ZeroAtInfty

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
    have h := (ContinuousLinearMap.smulRightL ℂ (refl ℂ ℂ).SumSpace C.SumSpace
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

/-- The analytic family through a simple function is a finite combination of its fibres. -/
private theorem sum_coeff_smul_fiber_apply {θ s : ℝ} (f : SimpleFunc α E) (z : ℂ) (x : α) :
    ∑ c ∈ f.range, coeff θ s c z • fiber f c x = famSMul θ s z (f x) := by
  rw [← SimpleFunc.map_apply (famSMul θ s z) f x, SimpleFunc.map_apply_eq_sum_restrict_const]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [fiber, SimpleFunc.restrict_apply _ (f.measurableSet_fiber c), SimpleFunc.coe_const,
    famSMul]
  by_cases hx : x ∈ f ⁻¹' {c} <;> simp [hx]

/-- An element of `L^q` given as a combination of fibres of `f` agrees almost everywhere with the
analytic family through `f`. -/
private theorem coeFn_sum_coeff_smul_toLp {θ s : ℝ} (f : SimpleFunc α E) {q : ℝ≥0∞}
    (h : ∀ c, MemLp (fiber f c) q μ) (z : ℂ) :
    ⇑(∑ c ∈ f.range, coeff θ s c z • (h c).toLp (fiber f c)) =ᵐ[μ]
      fun x => famSMul θ s z (f x) := by
  have hc : ∀ c ∈ f.range, ⇑(coeff θ s c z • (h c).toLp (fiber f c)) =ᵐ[μ]
      fun x => coeff θ s c z • fiber f c x := fun c _ =>
    (Lp.coeFn_smul _ _).trans ((h c).coeFn_toLp.mono fun x hx => by simp [hx])
  filter_upwards [Lp.coeFn_finsetSum f.range fun c => coeff θ s c z • (h c).toLp (fiber f c),
    (Filter.eventually_all_finset f.range).2 hc] with x hsum hall
  rw [hsum, Finset.sum_apply, ← sum_coeff_smul_fiber_apply]
  exact Finset.sum_congr rfl hall

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
  have h₀ : MemLp (fiber f c) p₀ μ := SimpleFunc.memLp_restrict_const_fiber hf hp0 hp_top p₀ c
  have h₁ : MemLp (fiber f c) p₁ μ := SimpleFunc.memLp_restrict_const_fiber hf hp0 hp_top p₁ c
  ⟨(h₀.toLp _, h₁.toLp _), mem_lebesgue_inter_iff.2 (h₀.coeFn_toLp.trans h₁.coeFn_toLp.symm)⟩

private theorem interFst_fiberInter {f : SimpleFunc α E} (hf : MemLp f p μ) (hp_top : p ≠ ∞)
    (c : E) : (lebesgue ℂ E μ p₀ p₁).interFst (fiberInter hf hp_top c) =
      (SimpleFunc.memLp_restrict_const_fiber hf (zero_lt_one.trans_le Fact.out).ne' hp_top p₀
        c).toLp (fiber f c) := by
  rw [interFst_apply]
  rfl

private theorem interSnd_fiberInter {f : SimpleFunc α E} (hf : MemLp f p μ) (hp_top : p ≠ ∞)
    (c : E) : (lebesgue ℂ E μ p₀ p₁).interSnd (fiberInter hf hp_top c) =
      (SimpleFunc.memLp_restrict_const_fiber hf (zero_lt_one.trans_le Fact.out).ne' hp_top p₁
        c).toLp (fiber f c) := by
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
  have h₀ : ∀ c, MemLp (fiber f c) p₀ μ := SimpleFunc.memLp_restrict_const_fiber hf hp0 hp_top p₀
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
    (SimpleFunc.memLp_restrict_const_fiber hf hp0 hp_top p₀)
    (by rwa [hre₀]) (by rwa [hre₀])
  have h₁ (t : ℝ) := norm_toSpanSingleton_sum_coeff_smul_le (z := 1 + t * I) f hf (q := p₁)
    (SimpleFunc.memLp_restrict_const_fiber hf hp0 hp_top p₁)
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
          rw [mul_one, ← Real.rpow_mul hN, ← Real.rpow_mul hN,
            ← Real.rpow_add' hN (by rw [hexp]; exact one_ne_zero), hexp, Real.rpow_one]
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

end Inclusion

/-! ### The case `p = ∞` -/

section Top

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α : Type*} {mα : MeasurableSpace α}
  {μ : Measure α} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-- For `p₀ = p₁ = ∞` every element of the complex interpolation space is a function of `L^∞` of
no larger norm, because the sum space is then `L^∞` itself. -/
private theorem exists_ofLp_eq_sumSpaceEmbed_toSum_top
    (u : (lebesgue ℂ E μ ∞ ∞).ComplexMethodSpace θ) :
    ∃ f : Lp E ∞ μ, L1AddLinfty.ofLp f =
      (lebesgue ℂ E μ ∞ ∞).sumSpaceEmbed (ComplexMethodSpace.toSum u) ∧ ‖f‖ ≤ ‖u‖ := by
  have key (f₀ f₁ : Lp E ∞ μ) (h : (lebesgue ℂ E μ ∞ ∞).fstToSum f₀ +
      (lebesgue ℂ E μ ∞ ∞).sndToSum f₁ = ComplexMethodSpace.toSum u) :
      L1AddLinfty.ofLp (f₀ + f₁) =
        (lebesgue ℂ E μ ∞ ∞).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
    rw [← h]
    exact ofLp_eq_lebesgue_sumSpaceEmbed_iff.2 (Lp.coeFn_add f₀ f₁)
  obtain ⟨f₀, f₁, h⟩ := (lebesgue ℂ E μ ∞ ∞).exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum u)
  refine ⟨f₀ + f₁, key f₀ f₁ h, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨g₀, g₁, hg, hgn⟩ := (lebesgue ℂ E μ ∞ ∞).norm_sumSpace_lt_iff.1
    (lt_add_of_le_of_pos (ComplexMethodSpace.norm_toSum_le u) hε)
  rw [L1AddLinfty.ofLp_injective ((key f₀ f₁ h).trans (key g₀ g₁ hg).symm)]
  exact (norm_add_le _ _).trans_lt hgn

/-- `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p` for `0 < θ < 1`, including `p = ∞`: for
`p < ∞` this is `lpToLebesgueComplexMethod`, and for `p = ∞` both endpoints are `L^∞`, so `f`
lies in their intersection. -/
private theorem exists_sumSpaceEmbed_toSum_eq_ofLp [CompleteSpace E] [Fact (1 ≤ p)]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 rfl
    have hx : (f, f) ∈ (lebesgue ℂ E μ ∞ ∞).inter := mem_lebesgue_inter_iff.2 EventuallyEq.rfl
    refine ⟨ComplexMethodSpace.ofInter θ ⟨(f, f), hx⟩, ?_,
      (ComplexMethodSpace.norm_ofInter_le (Ioo_subset_Icc_self hθ) _).trans ?_⟩
    · rw [ComplexMethodSpace.toSum_ofInter (Ioo_subset_Icc_self hθ), sumSpaceEmbed_fstToSum,
        lebesgue_embed₀, interFst_apply]
    · simp
  · exact ⟨lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f,
      sumSpaceEmbed_toSum_lpToLebesgueComplexMethod _ hp hp_top f,
      norm_lpToLebesgueComplexMethod_le _ hp hp_top f⟩

end Top

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {α : Type*}
  {mα : MeasurableSpace α} {μ : Measure α}
  {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-! ### Pairing with bounded functions of finite-measure support -/

/-- The pairing `f ↦ ∫ ⟪ψ, f⟫` of `Lʳ` with a function `ψ ∈ L¹ ∩ L^∞`: the Hölder pairing with
`x ↦ ⟪ψ x, ·⟫`, which lies in the dual exponent space `L^{r'}`. -/
private def innerCLM (r : ℝ≥0∞) [Fact (1 ≤ r)] {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) : Lp E r μ →L[ℂ] ℂ :=
  haveI : Fact (1 ≤ r.conjExponent) := ⟨ENNReal.HolderConjugate.one_le r.conjExponent r⟩
  (ContinuousLinearMap.id ℂ (E →L[ℂ] ℂ)).lpPairing μ r.conjExponent r
    (((innerSL ℂ).comp_memLp' (h₁.of_le_of_le htop one_ne_zero
      (ENNReal.HolderConjugate.one_le r.conjExponent r) le_top)).toLp _)

private theorem innerCLM_apply (r : ℝ≥0∞) [Fact (1 ≤ r)] {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) (f : Lp E r μ) : innerCLM r h₁ htop f = ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ := by
  have hψ : MemLp (innerSL ℂ ∘ ψ) r.conjExponent μ := (innerSL ℂ).comp_memLp'
    (h₁.of_le_of_le htop one_ne_zero (ENNReal.HolderConjugate.one_le r.conjExponent r) le_top)
  rw [innerCLM, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hψ.coeFn_toLp] with x hx
  simp [hx]

/-- The pairing `f₀ + f₁ ↦ ∫ ⟪ψ, f₀ + f₁⟫` of `L^{p₀} + L^{p₁}` with `ψ ∈ L¹ ∩ L^∞`. -/
private def sumInnerCLM {ψ : α → E} (h₁ : MemLp ψ 1 μ) (htop : MemLp ψ ∞ μ) :
    (lebesgue ℂ E μ p₀ p₁).SumSpace →L[ℂ] ℂ :=
  (lebesgue ℂ E μ p₀ p₁).sumLift (innerCLM p₀ h₁ htop) (innerCLM p₁ h₁ htop) fun x => by
    rw [innerCLM_apply, innerCLM_apply]
    exact integral_congr_ae ((mem_lebesgue_inter_iff.1 x.2).mono fun y hy => by
      simp only [interFst_apply, interSnd_apply]
      rw [hy])

private theorem sumInnerCLM_fstToSum {ψ : α → E} (h₁ : MemLp ψ 1 μ) (htop : MemLp ψ ∞ μ)
    (f : Lp E p₀ μ) :
    sumInnerCLM (p₁ := p₁) h₁ htop ((lebesgue ℂ E μ p₀ p₁).fstToSum f) = ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ :=
  (sumLift_fstToSum _ _ _ _ f).trans (innerCLM_apply p₀ h₁ htop f)

private theorem sumInnerCLM_sndToSum {ψ : α → E} (h₁ : MemLp ψ 1 μ) (htop : MemLp ψ ∞ μ)
    (f : Lp E p₁ μ) :
    sumInnerCLM (p₀ := p₀) h₁ htop ((lebesgue ℂ E μ p₀ p₁).sndToSum f) = ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ :=
  (sumLift_sndToSum _ _ _ _ f).trans (innerCLM_apply p₁ h₁ htop f)

private theorem sumInnerCLM_fstToSum_add_sndToSum {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) (f₀ : Lp E p₀ μ) (f₁ : Lp E p₁ μ) :
    sumInnerCLM h₁ htop ((lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁) =
      ∫ x, ⟪ψ x, f₀ x + f₁ x⟫_ℂ ∂μ := by
  -- `ψ ∈ L¹ ∩ L^∞` lies in the dual exponent spaces, so Hölder's inequality applies
  have hint (t : ℝ≥0∞) [Fact (1 ≤ t)] (f : Lp E t μ) : Integrable (fun x => ⟪ψ x, f x⟫_ℂ) μ :=
    ((innerSL ℂ).comp_memLp' (h₁.of_le_of_le htop one_ne_zero
      (ENNReal.HolderConjugate.one_le t.conjExponent t) le_top)).integrable_apply (Lp.memLp f)
  rw [map_add, sumInnerCLM_fstToSum, sumInnerCLM_sndToSum,
    ← integral_add (hint p₀ f₀) (hint p₁ f₁)]
  simp_rw [inner_add_right]

/-- Finite combinations of pairings are pairings with the conjugate combination. -/
private theorem sum_mul_integral_inner {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ψ : ι → α → E)
    {f : α → E} (hint : ∀ i ∈ s, Integrable (fun x => ⟪ψ i x, f x⟫_ℂ) μ) :
    ∑ i ∈ s, c i * ∫ x, ⟪ψ i x, f x⟫_ℂ ∂μ =
      ∫ x, ⟪∑ i ∈ s, (starRingEnd ℂ) (c i) • ψ i x, f x⟫_ℂ ∂μ := by
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum s fun i hi => (hint i hi).const_mul (c i)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [sum_inner, inner_smul_left]

/-! ### The three-lines estimate against an analytic family of test functions -/

/-- The piece `x ↦ ‖g x‖⁻¹ g x` of the direction of `g` on the level set `r = ρ` of a simple
function `r`. -/
private def levelPiece (g : α → E) (r : SimpleFunc α ℝ) (ρ : ℝ) : α → E :=
  (r ⁻¹' {ρ}).indicator fun x => ((‖g x‖⁻¹ : ℝ) : ℂ) • g x

private theorem norm_levelPiece_le (g : α → E) (r : SimpleFunc α ℝ) (ρ : ℝ) (x : α) :
    ‖levelPiece g r ρ x‖ ≤ 1 := by
  unfold levelPiece
  by_cases hx : x ∈ r ⁻¹' {ρ}
  · rw [Set.indicator_of_mem hx, Complex.coe_smul, ← one_div]
    exact norm_div_norm_smul_le (g x) zero_le_one
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact zero_le_one

private theorem levelPiece_of_eq_zero (g : α → E) (r : SimpleFunc α ℝ) (ρ : ℝ) {x : α}
    (hx : g x = 0) : levelPiece g r ρ x = 0 := by
  simp [levelPiece, hx]

private theorem memLp_levelPiece {g : α → E} (hg : StronglyMeasurable g) {s : Set α}
    (hs : μ s ≠ ∞) (hgs : ∀ x ∉ s, g x = 0) (r : SimpleFunc α ℝ) (ρ : ℝ) (q : ℝ≥0∞) :
    MemLp (levelPiece g r ρ) q μ :=
  (memLp_top_of_bound ((((Complex.measurable_ofReal.comp
    hg.norm.measurable.inv).stronglyMeasurable.smul hg).indicator
      (r.measurableSet_fiber ρ)).aestronglyMeasurable) 1
    (ae_of_all _ (norm_levelPiece_le g r ρ))).mono_exponent_of_measure_support_ne_top
    (fun x hx => levelPiece_of_eq_zero g r ρ (hgs x hx)) hs le_top

/-- The coefficient `ρ ^ P(z) = exp (P(z) log ρ)` of the level set `r = ρ` in the analytic
family of test functions, set to `0` on the level set `r = 0`. -/
private def levelCoeff (P : ℂ → ℂ) (z : ℂ) (ρ : ℝ) : ℂ :=
  if ρ = 0 then 0 else exp (P z * Real.log ρ)

private theorem differentiable_levelCoeff {P : ℂ → ℂ} (hP : Differentiable ℂ P) (ρ : ℝ) :
    Differentiable ℂ fun z => levelCoeff P z ρ := by
  unfold levelCoeff
  split_ifs
  · exact differentiable_const 0
  · fun_prop

private theorem norm_levelCoeff (P : ℂ → ℂ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖levelCoeff P z ρ‖ = ρ ^ (P z).re := by
  rw [levelCoeff, ite_eq_right hρ.ne', norm_exp, Real.rpow_def_of_pos hρ, mul_comm]
  simp

private theorem norm_levelCoeff_le (P : ℂ → ℂ) (z : ℂ) (ρ : ℝ) {B : ℝ} (hB : |(P z).re| ≤ B) :
    ‖levelCoeff P z ρ‖ ≤ Real.exp (B * |Real.log ρ|) := by
  unfold levelCoeff
  split_ifs
  · simpa using (Real.exp_pos _).le
  · rw [norm_exp]
    refine Real.exp_le_exp.2 ?_
    calc (P z * Real.log ρ).re = (P z).re * Real.log ρ := by simp
      _ ≤ |(P z).re| * |Real.log ρ| := (le_abs_self _).trans (abs_mul _ _).le
      _ ≤ B * |Real.log ρ| := by gcongr

/-- A finite combination `z ↦ ∑ ρ, ρ ^ P(z) L_ρ (F z)` of continuous linear images of a function
`F` bounded on the closed strip is bounded there, as long as `Re P` is. -/
private theorem bddAbove_norm_sum_levelCoeff_mul {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {P : ℂ → ℂ} {B : ℝ} (hP : ∀ z ∈ verticalClosedStrip 0 1, |(P z).re| ≤ B)
    (S : Finset ℝ) (L : ℝ → V →L[ℂ] ℂ) {F : ℂ → V} {M : ℝ}
    (hF : ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M) :
    BddAbove ((norm ∘ fun z => ∑ ρ ∈ S, levelCoeff P z ρ * L ρ (F z)) ''
      verticalClosedStrip 0 1) := by
  refine ⟨∑ ρ ∈ S, Real.exp (B * |Real.log ρ|) * (‖L ρ‖ * M), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_levelCoeff_le P z ρ (hP z hz)) ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (hF z hz) (norm_nonneg _))) (norm_nonneg _) (Real.exp_pos _).le

/-- The analytic family of test functions `‖r‖ ^ P(z) ‖g‖⁻¹ g`, conjugated so that pairing with
it is complex-linear in `z`. -/
private def testFamily (P : ℂ → ℂ) (g : α → E) (r : SimpleFunc α ℝ) (z : ℂ) (x : α) : E :=
  ∑ ρ ∈ r.range, conj (levelCoeff P z ρ) • levelPiece g r ρ x

private theorem testFamily_apply (P : ℂ → ℂ) (g : α → E) (r : SimpleFunc α ℝ) (z : ℂ) (x : α) :
    testFamily P g r z x = conj (levelCoeff P z (r x)) • ((‖g x‖⁻¹ : ℝ) : ℂ) • g x := by
  rw [testFamily, Finset.sum_eq_single (r x)]
  · simp [levelPiece]
  · intro ρ _ hρ
    simp [levelPiece, Ne.symm hρ]
  · exact fun h => absurd (r.mem_range_self x) h

private theorem norm_testFamily_le (P : ℂ → ℂ) (g : α → E) {r : SimpleFunc α ℝ}
    (hr : ∀ x, 0 ≤ r x) (z : ℂ) (x : α) : ‖testFamily P g r z x‖ ≤ ‖r x‖ ^ (P z).re := by
  rw [Real.norm_of_nonneg (hr x)]
  rcases (hr x).eq_or_lt with h | h
  · rw [testFamily_apply, ← h]
    simpa [levelCoeff] using Real.rpow_nonneg le_rfl _
  · rw [testFamily_apply, norm_smul, Complex.norm_conj, norm_levelCoeff P z h, Complex.coe_smul,
      ← one_div]
    exact mul_le_of_le_one_right (Real.rpow_nonneg h.le _) (norm_div_norm_smul_le (g x) zero_le_one)

private theorem testFamily_of_eq_one {P : ℂ → ℂ} {z : ℂ} (hPz : P z = 1) (g : α → E)
    {r : SimpleFunc α ℝ} (hr : ∀ x, 0 ≤ r x) (x : α) :
    testFamily P g r z x = ((r x * ‖g x‖⁻¹ : ℝ) : ℂ) • g x := by
  rw [testFamily_apply, levelCoeff, hPz, smul_smul]
  congr 1
  rcases (hr x).eq_or_lt with h | h
  · simp [← h]
  · rw [ite_eq_right h.ne', one_mul, ← ofReal_exp, Real.exp_log h, conj_ofReal, ← ofReal_mul]

/-- On a boundary line, where `1 / t' = Re P(z) / q` for the conjugate exponent `t'` of `t`, the
pairing of `f ∈ Lᵗ` with the test function at `z` is bounded by `‖f‖_t`, when `‖r‖_q ≤ 1`. -/
private theorem norm_sum_levelCoeff_mul_integral_le {P : ℂ → ℂ} {z : ℂ} (hPz : 0 ≤ (P z).re)
    {t q : ℝ≥0∞} [Fact (1 ≤ t)] (hq : t.conjExponent⁻¹ = ENNReal.ofReal (P z).re * q⁻¹)
    {g : α → E} (hg : StronglyMeasurable g) {s : Set α} (hs : μ s ≠ ∞) (hgs : ∀ x ∉ s, g x = 0)
    {r : SimpleFunc α ℝ} (hr : ∀ x, 0 ≤ r x) (hrn : eLpNorm r q μ ≤ 1) (f : Lp E t μ) :
    ‖∑ ρ ∈ r.range, levelCoeff P z ρ * ∫ x, ⟪levelPiece g r ρ x, f x⟫_ℂ ∂μ‖ ≤ ‖f‖ := by
  rw [sum_mul_integral_inner _ _ _ fun ρ _ => ((innerSL ℂ).comp_memLp'
    (memLp_levelPiece hg hs hgs r ρ t.conjExponent)).integrable_apply (Lp.memLp f)]
  have hmeas : AEStronglyMeasurable (testFamily P g r z) μ :=
    (Finset.aestronglyMeasurable_fun_sum _ fun ρ _ =>
      (memLp_levelPiece hg hs hgs r ρ ⊤).aestronglyMeasurable.const_smul _)
  have htest : eLpNorm (testFamily P g r z) t.conjExponent μ ≤ 1 :=
    (eLpNorm_le_eLpNorm_rpow hPz hmeas hq
      (ae_of_all _ (norm_testFamily_le P g hr z))).trans (ENNReal.rpow_le_one hrn hPz)
  rw [← toReal_eNorm, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    ((enorm_integral_inner_le (p := t.conjExponent) (q := t) (u := testFamily P g r z)).trans ?_)
  simpa using mul_le_mul_of_nonneg_right htest (zero_le : 0 ≤ eLpNorm f t μ)

/-- **The three-lines estimate.** Let `F` be an admissible function for the Lebesgue couple with
traces `g`, and `F θ = f₀ + f₁`. For a function `g` vanishing off a set of finite measure and a
nonnegative simple function `r` of `L^{p'}` norm at most one, the pairing of `f₀ + f₁` with
`r ‖g‖⁻¹ g` is bounded by the norm of the traces. It is the value at `θ` of the pairing of `F` with
the analytic family of test functions `‖r‖ ^ P(z) ‖g‖⁻¹ g`, which on the line `Re z = j` lies in
the unit ball of the dual space of `L^{p_j}`. -/
private theorem norm_integral_inner_le_of_isStripFunction (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    {F : ℂ → (lebesgue ℂ E μ p₀ p₁).SumSpace} {tr : C₀(ℝ, Lp E p₀ μ) × C₀(ℝ, Lp E p₁ μ)}
    (hF : (lebesgue ℂ E μ p₀ p₁).IsStripFunction F tr) {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ}
    (hFθ : F θ = (lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁)
    {g : α → E} (hg : StronglyMeasurable g) {s : Set α} (hs : μ s ≠ ∞) (hgs : ∀ x ∉ s, g x = 0)
    {r : SimpleFunc α ℝ} (hr : ∀ x, 0 ≤ r x) (hrn : eLpNorm r p.conjExponent μ ≤ 1) :
    ‖∫ x, ⟪((r x * ‖g x‖⁻¹ : ℝ) : ℂ) • g x, f₀ x + f₁ x⟫_ℂ ∂μ‖ ≤ ‖tr‖ := by
  have hθ' := Ioo_subset_Icc_self hθ
  have hq₀ : p₀.conjExponent ≠ 0 := ENNReal.HolderConjugate.ne_zero _ p₀
  have hq₁ : p₁.conjExponent ≠ 0 := ENNReal.HolderConjugate.ne_zero _ p₁
  have hq := inv_conjExponent_eq_of_inv_eq (Fact.out : 1 ≤ p₀) (Fact.out : 1 ≤ p₁) hθ' hp
  set P := interpExponent (p₀.conjExponent⁻¹).toReal (p₁.conjExponent⁻¹).toReal θ
  have hPnn {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) : 0 ≤ (P z).re :=
    re_interpExponent_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hθ' hz
  have h₁ (ρ : ℝ) := memLp_levelPiece hg hs hgs r ρ 1
  have htop (ρ : ℝ) := memLp_levelPiece hg hs hgs r ρ ⊤
  -- the pairing of `F` with the analytic family of test functions
  set Ψ : ℂ → ℂ := fun z => ∑ ρ ∈ r.range, levelCoeff P z ρ *
    sumInnerCLM (p₀ := p₀) (p₁ := p₁) (h₁ ρ) (htop ρ) (F z) with hΨ
  have hd : DiffContOnCl ℂ Ψ (verticalStrip 0 1) := DiffContOnCl.fun_sum fun ρ _ =>
    ((differentiable_levelCoeff (differentiable_interpExponent _ _ _) ρ).diffContOnCl).smul
      ((ContinuousLinearMap.differentiable _).comp_diffContOnCl hF.diffContOnCl)
  have hB : BddAbove ((norm ∘ Ψ) '' verticalClosedStrip 0 1) :=
    bddAbove_norm_sum_levelCoeff_mul (F := F) (P := P) (fun z hz => abs_re_interpExponent_le hθ'
      (Complex.HadamardThreeLines.mem_verticalClosedStrip_iff.1 hz)) r.range
      (fun ρ => sumInnerCLM (μ := μ) (E := E) (p₀ := p₀) (p₁ := p₁) (h₁ ρ) (htop ρ))
      fun z hz => hF.norm_le hz
  -- on the two boundary lines the pairing is bounded by the norm of the traces
  have ha : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖Ψ z‖ ≤ ‖tr‖ := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff] at hz
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = t * I := ⟨z.im, by simp [Complex.ext_iff, hz]⟩
    simp only [hΨ, hF.apply_mul_I, sumInnerCLM_fstToSum]
    exact (norm_sum_levelCoeff_mul_integral_le (hPnn (by simp))
      (ofReal_re_interpExponent_mul_inv_of_re_eq_zero hq₀ hq₁ hθ hq (by simp)).symm hg hs hgs hr
      hrn _).trans ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_fst_le tr))
  have hb : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖Ψ z‖ ≤ ‖tr‖ := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff] at hz
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = 1 + t * I := ⟨z.im, by simp [Complex.ext_iff, hz]⟩
    simp only [hΨ, hF.apply_one_add_mul_I, sumInnerCLM_sndToSum]
    exact (norm_sum_levelCoeff_mul_integral_le (hPnn (by simp))
      (ofReal_re_interpExponent_mul_inv_of_re_eq_one hq₀ hq₁ hθ hq (by simp)).symm hg hs hgs hr
      hrn _).trans ((ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_snd_le tr))
  have key := norm_le_interp_of_mem_verticalClosedStrip₀₁' Ψ (z := (θ : ℂ))
    (by simp [hθ.1.le, hθ.2.le]) hd hB ha hb
  rw [← Real.rpow_add' (norm_nonneg _) (by simp), ofReal_re, sub_add_cancel, Real.rpow_one] at key
  -- at `θ` the exponent is one and the test function is `r ‖g‖⁻¹ g`
  refine le_of_eq_of_le ?_ key
  simp only [hΨ, hFθ, sumInnerCLM_fstToSum_add_sndToSum]
  rw [sum_mul_integral_inner _ _ _ fun ρ _ => (((innerSL ℂ).comp_memLp'
    (memLp_levelPiece hg hs hgs r ρ p₀.conjExponent)).integrable_apply (Lp.memLp f₀)).add
    (((innerSL ℂ).comp_memLp' (memLp_levelPiece hg hs hgs r ρ p₁.conjExponent)).integrable_apply
      (Lp.memLp f₁)) |>.congr (ae_of_all _ fun x => (inner_add_right _ _ _).symm)]
  congr 2
  funext x
  rw [← testFamily, testFamily_of_eq_one (interpExponent_self _ _ _) g hr x]

/-- `norm_integral_inner_le_of_isStripFunction` for every test function `g` of `L^{p'}` norm at
most one, by approximating `‖g‖` from below by nonnegative simple functions. -/
private theorem norm_integral_inner_le_of_isStripFunction_of_eLpNorm_le_one
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    {F : ℂ → (lebesgue ℂ E μ p₀ p₁).SumSpace} {tr : C₀(ℝ, Lp E p₀ μ) × C₀(ℝ, Lp E p₁ μ)}
    (hF : (lebesgue ℂ E μ p₀ p₁).IsStripFunction F tr) {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ}
    (hFθ : F θ = (lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁)
    {g : α → E} (hg : StronglyMeasurable g) {s : Set α} (hs : μ s ≠ ∞) (hgs : ∀ x ∉ s, g x = 0)
    (hgtop : MemLp g ∞ μ) (hgn : eLpNorm g p.conjExponent μ ≤ 1) :
    ‖∫ x, ⟪g x, f₀ x + f₁ x⟫_ℂ ∂μ‖ ≤ ‖tr‖ := by
  -- the simple functions `r n` increase to `‖g‖`
  have hmeas : Measurable fun x => ENNReal.ofReal ‖g x‖ := hg.norm.measurable.ennreal_ofReal
  set r : ℕ → SimpleFunc α ℝ := fun n =>
    (SimpleFunc.eapprox (fun x => ENNReal.ofReal ‖g x‖) n).map ENNReal.toReal with hr_def
  have hr0 (n : ℕ) (x : α) : 0 ≤ r n x := ENNReal.toReal_nonneg
  have hle (n : ℕ) (x : α) : r n x ≤ ‖g x‖ := by
    have h : SimpleFunc.eapprox (fun x => ENNReal.ofReal ‖g x‖) n x ≤ ENNReal.ofReal ‖g x‖ := by
      rw [← SimpleFunc.iSup_eapprox_apply hmeas x]
      exact le_iSup (fun n => SimpleFunc.eapprox (fun x => ENNReal.ofReal ‖g x‖) n x) n
    simpa [hr_def] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hlim (x : α) : Tendsto (fun n => r n x) atTop (𝓝 ‖g x‖) := by
    have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
      (SimpleFunc.tendsto_eapprox hmeas x)
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at h
    exact h
  have hbound (n : ℕ) := norm_integral_inner_le_of_isStripFunction hθ hp hF hFθ hg hs hgs (hr0 n)
    ((eLpNorm_mono (r n).aestronglyMeasurable fun x => by
      simpa [abs_of_nonneg (hr0 n x)] using hle n x).trans hgn)
  -- dominated convergence along the approximations `r n ‖g‖⁻¹ g → g`
  have hdom : Integrable (fun x => ‖g x‖ * ‖f₀ x‖ + ‖g x‖ * ‖f₁ x‖) μ :=
    ((hgtop.mono_exponent_of_measure_support_ne_top (p := p₀.conjExponent) hgs hs
      le_top).norm.integrable_mul (Lp.memLp f₀).norm).add
      ((hgtop.mono_exponent_of_measure_support_ne_top (p := p₁.conjExponent) hgs hs
        le_top).norm.integrable_mul (Lp.memLp f₁).norm)
  have htend : Tendsto (fun n => ∫ x, ⟪((r n x * ‖g x‖⁻¹ : ℝ) : ℂ) • g x, f₀ x + f₁ x⟫_ℂ ∂μ)
      atTop (𝓝 (∫ x, ⟪g x, f₀ x + f₁ x⟫_ℂ ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hdom (fun n => ?_)
      (ae_of_all _ fun x => ?_)
    · exact ((Complex.measurable_ofReal.comp ((r n).measurable.mul
        hg.norm.measurable.inv)).aestronglyMeasurable.smul hg.aestronglyMeasurable).inner
        ((Lp.aestronglyMeasurable f₀).add (Lp.aestronglyMeasurable f₁))
    · refine ae_of_all _ fun x => (norm_inner_le_norm _ _).trans ?_
      rw [← mul_add, Complex.coe_smul, ← div_eq_mul_inv]
      exact mul_le_mul ((norm_div_norm_smul_le (g x) (hr0 n x)).trans (hle n x))
        (norm_add_le _ _) (norm_nonneg _) (norm_nonneg _)
    · refine Tendsto.inner ?_ tendsto_const_nhds
      rcases eq_or_ne (g x) 0 with h | h
      · simp [h]
      · have h' : ‖g x‖ * ‖g x‖⁻¹ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.2 h)
        simpa [h'] using ((continuous_ofReal.tendsto _).comp
          ((hlim x).mul_const ‖g x‖⁻¹)).smul_const (g x)
  exact le_of_tendsto' htend.norm hbound

/-- `ComplexMethodSpace.exists_ofLp_eq_sumSpaceEmbed_toSum` for `p < ∞`: by the three-lines
estimate, `f₀ + f₁ = u` pairs with every bounded test function `g` of finite-measure support to at
most `‖u‖_θ ‖g‖_{p'}`, and duality bounds its `Lᵖ` norm. -/
private theorem exists_ofLp_eq_sumSpaceEmbed_toSum_of_ne_top [SigmaFinite μ] [Fact (1 ≤ p)]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hp_top : p ≠ ∞) (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    ∃ f : Lp E p μ, L1AddLinfty.ofLp f =
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) ∧ ‖f‖ ≤ ‖u‖ := by
  obtain ⟨f₀, f₁, hdec⟩ := (lebesgue ℂ E μ p₀ p₁).exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum u)
  have hh : AEStronglyMeasurable (fun x => f₀ x + f₁ x) μ :=
    (Lp.aestronglyMeasurable f₀).add (Lp.aestronglyMeasurable f₁)
  -- every representative of `u` bounds the pairings with normalized test functions
  have hle := hh.eLpNorm_le_of_forall_norm_integral_inner_le (𝕜 := ℂ) (C := ‖u‖) hp_top
    fun g s hg hs hgs hgtop hgn => le_of_forall_pos_lt_add fun ε hε => by
      obtain ⟨tr, rfl, htr⟩ := ComplexMethodSpace.norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hε)
      exact (norm_integral_inner_le_of_isStripFunction_of_eLpNorm_le_one hθ hp
        ((lebesgue ℂ E μ p₀ p₁).isStripFunction_stripFunction tr)
        (by rw [← stripEval_apply, ← ComplexMethodSpace.toSum_mk, hdec]) hg hs hgs hgtop
        hgn).trans_lt htr
  have hmem : MemLp (fun x => f₀ x + f₁ x) p μ := memLp_iff.2 (hle.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hmem.toLp _, ?_, ?_⟩
  · rw [← hdec]
    exact ofLp_eq_lebesgue_sumSpaceEmbed_iff.2 hmem.coeFn_toLp
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hle

namespace ComplexMethodSpace

/-- **`[L^{p₀}, L^{p₁}]_θ` embeds in `Lᵖ`.** For `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the
interpolated exponent `1 / p = (1 - θ) / p₀ + θ / p₁`, every element `u` of the complex
interpolation space of the Lebesgue couple, with values in a complex inner product space and over a
σ-finite measure, is the class in `L¹ + L^∞` of a function `f ∈ Lᵖ` with `‖f‖_p ≤ ‖u‖_θ`. -/
theorem exists_ofLp_eq_sumSpaceEmbed_toSum [SigmaFinite μ] [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    ∃ f : Lp E p μ,
      L1AddLinfty.ofLp f = (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u) ∧ ‖f‖ ≤ ‖u‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 rfl
    exact exists_ofLp_eq_sumSpaceEmbed_toSum_top u
  · exact exists_ofLp_eq_sumSpaceEmbed_toSum_of_ne_top hθ hp hp_top u

variable [SigmaFinite μ] [Fact (1 ≤ p)]

/-- The function of `Lᵖ` with the class of `u` in `L¹ + L^∞`. -/
private def toLpFun (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) : Lp E p μ :=
  (exists_ofLp_eq_sumSpaceEmbed_toSum hθ hp u).choose

private theorem ofLp_toLpFun (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    L1AddLinfty.ofLp (toLpFun hθ hp u) = (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u) :=
  (exists_ofLp_eq_sumSpaceEmbed_toSum hθ hp u).choose_spec.1

private theorem norm_toLpFun [CompleteSpace E] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) : ‖toLpFun hθ hp u‖ = ‖u‖ := by
  refine le_antisymm (exists_ofLp_eq_sumSpaceEmbed_toSum hθ hp u).choose_spec.2 ?_
  obtain ⟨v, hv, hvn⟩ := exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp (toLpFun hθ hp u)
  rwa [((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective.comp toSum_injective)
    (hv.trans (ofLp_toLpFun hθ hp u))] at hvn

private theorem toLpFun_add (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    toLpFun hθ hp (u + v) = toLpFun hθ hp u + toLpFun hθ hp v := by
  refine L1AddLinfty.ofLp_injective (𝕜 := ℂ) ?_
  rw [map_add (L1AddLinfty.ofLp (𝕜 := ℂ)), ofLp_toLpFun, ofLp_toLpFun, ofLp_toLpFun,
    map_add toSum, map_add]

private theorem toLpFun_smul (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (c : ℂ)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    toLpFun hθ hp (c • u) = c • toLpFun hθ hp u := by
  refine L1AddLinfty.ofLp_injective (𝕜 := ℂ) ?_
  rw [map_smul (L1AddLinfty.ofLp (𝕜 := ℂ)), ofLp_toLpFun, ofLp_toLpFun, map_smul toSum,
    map_smul]

/-- `toLpFun` as a linear isometry. -/
private def toLpLinearIsometry [CompleteSpace E] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ →ₗᵢ[ℂ] Lp E p μ where
  toFun := toLpFun hθ hp
  map_add' := toLpFun_add hθ hp
  map_smul' := toLpFun_smul hθ hp
  norm_map' := norm_toLpFun hθ hp

/-- **Complex interpolation of Lebesgue spaces**, `[L^{p₀}, L^{p₁}]_θ = Lᵖ` with equal norms, for
`1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁`, for functions on a σ-finite
measure space with values in a complex Hilbert space: the isometric isomorphism sending `u` to the
function of `Lᵖ` with the same class in `L¹ + L^∞` (`ComplexMethodSpace.ofLp_lebesgueEquiv`). -/
def lebesgueEquiv [CompleteSpace E] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] Lp E p μ :=
  LinearIsometryEquiv.ofSurjective (toLpLinearIsometry hθ hp) fun f => by
    obtain ⟨v, hv, -⟩ := exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp f
    exact ⟨v, (L1AddLinfty.ofLp_injective (𝕜 := ℂ)) ((ofLp_toLpFun hθ hp v).trans hv)⟩

variable [CompleteSpace E] (hθ : θ ∈ Ioo 0 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)

/-- `lebesgueEquiv` sends `u ∈ [L^{p₀}, L^{p₁}]_θ` to the function of `Lᵖ` with the same class in
`L¹ + L^∞`. -/
@[simp]
theorem ofLp_lebesgueEquiv (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    L1AddLinfty.ofLp (lebesgueEquiv hθ hp u) = (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u) :=
  ofLp_toLpFun hθ hp u

/-- The inverse of `lebesgueEquiv` sends `f ∈ Lᵖ` to the element of `[L^{p₀}, L^{p₁}]_θ` with the
same class in `L¹ + L^∞`. -/
@[simp]
theorem sumSpaceEmbed_toSum_lebesgueEquiv_symm (f : Lp E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum ((lebesgueEquiv hθ hp).symm f)) =
      L1AddLinfty.ofLp f := by
  rw [← ofLp_lebesgueEquiv hθ hp, LinearIsometryEquiv.apply_symm_apply]

/-- `lebesgueEquiv` sends `u` with `toSum u = f₀ + f₁` in `L^{p₀} + L^{p₁}` to the function
`f₀ + f₁`. -/
theorem coeFn_lebesgueEquiv_ae_eq_add_iff (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ)
    {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ} :
    ⇑(lebesgueEquiv hθ hp u) =ᵐ[μ] ⇑f₀ + ⇑f₁ ↔
      toSum u = (lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁ := by
  rw [← (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective.eq_iff, ← ofLp_lebesgueEquiv hθ hp,
    ofLp_eq_lebesgue_sumSpaceEmbed_iff]

/-- `lebesgueEquiv` sends the class of an element of the intersection `L^{p₀} ∩ L^{p₁}` to its
function. -/
theorem coeFn_lebesgueEquiv_ofInter (x : (lebesgue ℂ E μ p₀ p₁).inter) :
    ⇑(lebesgueEquiv hθ hp (ofInter θ x)) =ᵐ[μ] ⇑(x : Lp E p₀ μ × Lp E p₁ μ).1 := by
  rw [← L1AddLinfty.ofLp_eq_ofLp_iff (𝕜 := ℂ), ofLp_lebesgueEquiv,
    toSum_ofInter (Ioo_subset_Icc_self hθ), sumSpaceEmbed_fstToSum, lebesgue_embed₀,
    interFst_apply]

/-- For `p₀ ≤ p ≤ p₁`, `lebesgueEquiv` restricts on the intersection to the inclusion
`L^{p₀} ∩ L^{p₁} → Lᵖ`. -/
theorem lebesgueEquiv_ofInter (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (x : (lebesgue ℂ E μ p₀ p₁).inter) :
    lebesgueEquiv hθ hp (ofInter θ x) = lebesgueInterToLp h₀ h₁ x :=
  Lp.ext ((coeFn_lebesgueEquiv_ofInter hθ hp x).trans (coeFn_lebesgueInterToLp h₀ h₁ x).symm)

/-- For `p₀ ≤ p ≤ p₁`, the inverse of `lebesgueEquiv` lies over the inclusion
`Lᵖ → L^{p₀} + L^{p₁}`. -/
theorem toSum_lebesgueEquiv_symm (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    toSum ((lebesgueEquiv hθ hp).symm f) = lpToLebesgueSum h₀ h₁ f :=
  (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective <| by
    rw [sumSpaceEmbed_toSum_lebesgueEquiv_symm, sumSpaceEmbed_lpToLebesgueSum]

/-- For `p < ∞`, the inverse of `lebesgueEquiv` is the inclusion `lpToLebesgueComplexMethod`. -/
theorem lebesgueEquiv_symm_eq_lpToLebesgueComplexMethod (hp_top : p ≠ ∞) (f : Lp E p μ) :
    (lebesgueEquiv hθ hp).symm f =
      lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f :=
  toSum_injective <| (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective <| by
    rw [sumSpaceEmbed_toSum_lebesgueEquiv_symm, sumSpaceEmbed_toSum_lpToLebesgueComplexMethod]

end ComplexMethodSpace

end Inner

end TauCeti.CompatibleCouple
