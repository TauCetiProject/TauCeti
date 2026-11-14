/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import TauCeti.Analysis.Complex.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Complex interpolation of Lebesgue spaces

For `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the interpolated exponent
`1 / p = (1 - θ) / p₀ + θ / p₁`, the complex interpolation space of the Lebesgue couple
`(L^{p₀}, L^{p₁})` (`TauCeti.CompatibleCouple.lebesgue`) is `Lᵖ`, with equal norms:

`[L^{p₀}, L^{p₁}]_θ = Lᵖ`.

Both spaces sit in `L¹ + L^∞`, and the identification matches the elements with the same class
there (`TauCeti.CompatibleCouple.ComplexMethodSpace.lebesgueEquiv`). Transported along the Bessel
potential isomorphisms `H^{s,q} ≃ L^q` by the retract theorems of the complex method, it gives the
interpolation identity `[H^{s,p₀}, H^{s,p₁}]_θ = H^{s,p}` for Bessel-potential spaces of a common
order `s`.

## The two inclusions

* `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p`
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.exists_sumSpaceEmbed_toSum_eq_ofLp`), for any
  complex Banach space of values and any measure. A simple function `f` of norm one is the value at
  `θ` of the analytic family `z ↦ ‖f‖ ^ (P(z) - 1) f`, where `P(z) = 1 + (z - θ) (a₁ - a₀) / a`
  (`TauCeti.interpExponent`) with `a_j = 1 / p_j` and `a = 1 / p`. On the line `Re z = j` its
  norm is `‖f‖ ^ (p / p_j)`, in the unit ball of `L^{p_j}`. Such a family need not vanish at
  infinity on the boundary lines, but its values still lie in the interpolation space
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.exists_toSum_eq_and_norm_le`). Simple functions are
  dense in `Lᵖ` for `p < ∞`, and for `p = ∞` both endpoints are `L^∞`.
* `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ` with `‖f‖_p ≤ ‖f‖_θ`
  (`TauCeti.CompatibleCouple.ComplexMethodSpace.exists_ofLp_eq_sumSpaceEmbed_toSum`), for values in
  a complex inner product space and a σ-finite measure. Let `F` be an admissible function with
  `F θ = f`. Pair `F` with the dual analytic family `z ↦ ‖g‖ ^ P'(z) ‖g‖⁻¹ g` of a test function
  `g`, with the conjugate exponents in place of the exponents. Hadamard's three-lines theorem then
  bounds `|∫ ⟪g, f⟫|` by the norm of the traces of `F` times `‖g‖_{p'}`. This pairing is a finite
  sum of holomorphic functions when `‖g‖` is simple. Approximating `‖g‖` from below by simple
  functions extends the bound to bounded `g` of finite-measure support, and duality
  (`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`) bounds
  `‖f‖_p`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, Theorems 5.1.1 and 5.1.2.
-/

public noncomputable section

open MeasureTheory Complex Set Filter Topology Complex.HadamardThreeLines
open scoped ENNReal InnerProductSpace ComplexConjugate ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section Embedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The analytic family through a simple function -/

/-- The vector `‖v‖ ^ (w - 1) v`, written `exp ((w - 1) log ‖v‖) v`, of norm `‖v‖ ^ re w`. -/
private def powSmul (w : ℂ) (v : E) : E :=
  exp ((w - 1) * Real.log ‖v‖) • v

private theorem powSmul_one (v : E) : powSmul 1 v = v := by
  simp [powSmul]

private theorem norm_powSmul_le (w : ℂ) (v : E) : ‖powSmul w v‖ ≤ ‖v‖ ^ w.re := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [powSmul, smul_zero, norm_zero]
    exact Real.rpow_nonneg le_rfl _
  · have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hre : ((w - 1) * (Real.log ‖v‖ : ℂ)).re = (w.re - 1) * Real.log ‖v‖ := by simp
    rw [powSmul, norm_smul, norm_exp, hre, mul_comm (w.re - 1), ← Real.rpow_def_of_pos hr,
      Real.rpow_sub_one hr.ne', div_mul_cancel₀ _ hr.ne']

/-- The indicator of the fibre `f ⁻¹' {c}` of a simple function, with value `c` on it. -/
private def fiber (f : SimpleFunc α E) (c : E) : α → E :=
  (f ⁻¹' {c}).indicator fun _ => c

omit [NormedSpace ℂ E] in
private theorem norm_fiber_le (f : SimpleFunc α E) (c : E) (x : α) : ‖fiber f c x‖ ≤ ‖f x‖ := by
  by_cases hx : f x = c <;> simp [fiber, hx]

omit [NormedSpace ℂ E] in
private theorem memLp_fiber {r : ℝ≥0∞} {f : SimpleFunc α E} (hf : MemLp f r μ) (c : E) :
    MemLp (fiber f c) r μ :=
  hf.of_le ((stronglyMeasurable_const.indicator
    (f.measurableSet_fiber c)).aestronglyMeasurable) (ae_of_all _ (norm_fiber_le f c))

private theorem sum_smul_fiber (f : SimpleFunc α E) (a : E → ℂ) (x : α) :
    ∑ c ∈ f.range, a c • fiber f c x = a (f x) • f x := by
  rw [Finset.sum_eq_single (f x)]
  · simp [fiber]
  · intro c _ hc
    simp [fiber, Ne.symm hc]
  · exact fun h => absurd (f.mem_range_self x) h

/-- The member `x ↦ ‖f x‖ ^ (w - 1) f x` of the analytic family through the simple function `f`,
as an element of `Lʳ`: a finite combination of the fibre indicators of `f` with coefficients
entire in `w`. -/
private def famLp (r : ℝ≥0∞) {f : SimpleFunc α E} (hf : MemLp f r μ) (w : ℂ) :
    Lp E r μ :=
  ∑ c ∈ f.range, exp ((w - 1) * Real.log ‖c‖) • (memLp_fiber hf c).toLp (fiber f c)

private theorem coeFn_famLp {r : ℝ≥0∞} {f : SimpleFunc α E} (hf : MemLp f r μ)
    (w : ℂ) :
    famLp r hf w =ᵐ[μ] fun x => powSmul w (f x) := by
  have h : ∀ᵐ x ∂μ, ∀ c ∈ f.range,
      (exp ((w - 1) * Real.log ‖c‖) • (memLp_fiber hf c).toLp (fiber f c) : Lp E r μ) x =
        exp ((w - 1) * Real.log ‖c‖) • fiber f c x := by
    refine (Filter.eventually_all_finset _).2 fun c _ => ?_
    filter_upwards [Lp.coeFn_smul (exp ((w - 1) * Real.log ‖c‖))
      ((memLp_fiber hf c).toLp (fiber f c)), (memLp_fiber hf c).coeFn_toLp] with x h₁ h₂
    rw [h₁, Pi.smul_apply, h₂]
  filter_upwards [Lp.coeFn_finsetSum f.range fun c =>
    exp ((w - 1) * Real.log ‖c‖) • (memLp_fiber hf c).toLp (fiber f c), h] with x hx hx'
  rw [famLp, hx, Finset.sum_apply, Finset.sum_congr rfl hx',
    sum_smul_fiber f (fun c => exp ((w - 1) * Real.log ‖c‖)) x, powSmul]

private theorem famLp_one {r : ℝ≥0∞} {f : SimpleFunc α E} (hf : MemLp f r μ) :
    famLp r hf 1 = hf.toLp f :=
  Lp.ext <| (coeFn_famLp hf 1).trans <| by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, powSmul_one]

private theorem differentiable_famLp {r : ℝ≥0∞} [Fact (1 ≤ r)] {f : SimpleFunc α E}
    (hf : MemLp f r μ) : Differentiable ℂ (famLp r hf) := by
  unfold famLp
  exact Differentiable.fun_sum fun c _ => (by fun_prop : Differentiable ℂ fun w : ℂ =>
    exp ((w - 1) * Real.log ‖c‖)).smul_const _

/-- The members of the analytic family through `f` are bounded in `Lʳ` as long as the real part
of the exponent stays bounded. -/
private theorem exists_norm_famLp_le {r : ℝ≥0∞} [Fact (1 ≤ r)] {f : SimpleFunc α E}
    (hf : MemLp f r μ) (B : ℝ) :
    ∃ K, ∀ w : ℂ, |w.re - 1| ≤ B → ‖famLp r hf w‖ ≤ K := by
  refine ⟨∑ c ∈ f.range, Real.exp (B * |Real.log ‖c‖|) * ‖(memLp_fiber hf c).toLp (fiber f c)‖,
    fun w hw => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)⟩
  rw [norm_smul, norm_exp]
  gcongr
  calc ((w - 1) * Real.log ‖c‖).re = (w.re - 1) * Real.log ‖c‖ := by simp
    _ ≤ |w.re - 1| * |Real.log ‖c‖| := (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ B * |Real.log ‖c‖| := by gcongr

/-- The member of the analytic family through `f` whose exponent has real part `t ≥ 0` has
`Lˢ` norm at most `‖f‖_p ^ t`, where `1 / s = t / p`. -/
private theorem eLpNorm_famLp_le {r p s : ℝ≥0∞} {f : SimpleFunc α E}
    (hf : MemLp f r μ)
    {w : ℂ} (hw : 0 ≤ w.re) (hs : s⁻¹ = ENNReal.ofReal w.re * p⁻¹) :
    eLpNorm (famLp r hf w) s μ ≤ eLpNorm f p μ ^ w.re := by
  rw [eLpNorm_congr_ae (coeFn_famLp hf w)]
  exact eLpNorm_le_eLpNorm_rpow hw ((Lp.aestronglyMeasurable _).congr (coeFn_famLp hf w)) hs
    (ae_of_all _ fun x => norm_powSmul_le w (f x))

/-! ### Elements of the Lebesgue couple -/

variable {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

private theorem lebesgue_fstToSum_eq_sndToSum_iff {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ} :
    (lebesgue ℂ E μ p₀ p₁).fstToSum f₀ = (lebesgue ℂ E μ p₀ p₁).sndToSum f₁ ↔ ⇑f₀ =ᵐ[μ] ⇑f₁ := by
  rw [← (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective.eq_iff, sumSpaceEmbed_fstToSum,
    sumSpaceEmbed_sndToSum, lebesgue_embed₀, lebesgue_embed₁, L1AddLinfty.ofLp_eq_ofLp_iff]

/-! ### `Lᵖ` embeds in the complex interpolation space -/

/-- A simple function of `Lᵖ` norm at most one, in both endpoint spaces, lies in
`[L^{p₀}, L^{p₁}]_θ` with norm at most one: it is the value at `θ` of the analytic family
`z ↦ ‖f‖ ^ (P(z) - 1) f`, which lies in the unit ball of `L^{p_j}` on the line `Re z = j`. -/
private theorem exists_toSum_eq_fstToSum_of_eLpNorm_le_one (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {f : SimpleFunc α E}
    (hf₀ : MemLp f p₀ μ) (hf₁ : MemLp f p₁ μ) (hf : eLpNorm f p μ ≤ 1) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      ComplexMethodSpace.toSum u = (lebesgue ℂ E μ p₀ p₁).fstToSum (hf₀.toLp f) ∧ ‖u‖ ≤ 1 := by
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  set P := interpExponent (p₀⁻¹).toReal (p₁⁻¹).toReal θ with hP
  have hPd : Differentiable ℂ P := differentiable_interpExponent _ _ _
  -- on the closed strip the real part of `P` is nonnegative and bounded
  have hPnn {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) : 0 ≤ (P z).re :=
    re_interpExponent_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hθ hz
  obtain ⟨K, hK⟩ := exists_norm_famLp_le hf₀ (2 + |interpSlope (p₀⁻¹).toReal (p₁⁻¹).toReal θ|)
  -- on the line `Re z = j` the family lies in the unit ball of `L^{p_j}`
  have hbd {r : ℝ≥0∞} [Fact (1 ≤ r)] (hfr : MemLp f r μ) {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1)
      (hr : r⁻¹ = ENNReal.ofReal (P z).re * p⁻¹) : ‖famLp r hfr (P z)‖ ≤ 1 := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one <| by
      simpa using (eLpNorm_famLp_le hfr (hPnn hz) hr).trans (ENNReal.rpow_le_one hf (hPnn hz))
  obtain ⟨u, hu, hnorm⟩ := ComplexMethodSpace.exists_toSum_eq_and_norm_le
    (C := lebesgue ℂ E μ p₀ p₁) (Ioo_subset_Icc_self hθ)
    (F := fun z => (lebesgue ℂ E μ p₀ p₁).fstToSum (famLp p₀ hf₀ (P z)))
    (G₀ := fun t : ℝ => famLp p₀ hf₀ (P (t * I)))
    (G₁ := fun t : ℝ => famLp p₁ hf₁ (P (1 + t * I)))
    ((ContinuousLinearMap.differentiable _).comp ((differentiable_famLp hf₀).comp hPd)).diffContOnCl
    (isBounded_iff_forall_norm_le.2 ⟨K, by
      rintro _ ⟨z, hz, rfl⟩
      refine ((lebesgue ℂ E μ p₀ p₁).norm_fstToSum_le _).trans (hK _ ?_)
      have := abs_re_interpExponent_le (a₀ := (p₀⁻¹).toReal) (a₁ := (p₁⁻¹).toReal) hθ hz
      exact (abs_sub _ _).trans (by simp only [abs_one]; linarith)⟩)
    ((differentiable_famLp hf₀).continuous.comp (hPd.continuous.comp (by fun_prop)))
    ((differentiable_famLp hf₁).continuous.comp (hPd.continuous.comp (by fun_prop)))
    (fun t => rfl)
    (fun t => lebesgue_fstToSum_eq_sndToSum_iff.2 <|
      (coeFn_famLp hf₀ _).trans (coeFn_famLp hf₁ _).symm)
    (fun t => hbd hf₀ (by simp) (ofReal_re_interpExponent_mul_inv_of_re_eq_zero hp₀ hp₁ hθ hp
      (by simp)).symm)
    (fun t => hbd hf₁ (by simp) (ofReal_re_interpExponent_mul_inv_of_re_eq_one hp₀ hp₁ hθ hp
      (by simp)).symm)
  refine ⟨u, ?_, hnorm⟩
  rw [hu, hP, interpExponent_self, famLp_one]

/-- Every simple function `f` of `Lᵖ`, `p < ∞`, lies in `[L^{p₀}, L^{p₁}]_θ`, with norm at most
`‖f‖_p`. -/
private theorem exists_toSum_simpleFunc [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    {f : SimpleFunc α E} (hf : MemLp f p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) =
        L1AddLinfty.ofLp (hf.toLp f) ∧ ‖u‖ ≤ ‖hf.toLp f‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  -- the fibres of nonzero values have finite measure, so every multiple of `f` is in every `Lʳ`
  have hfin := SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hp_top f hf
  rcases (norm_nonneg (hf.toLp f)).eq_or_lt with hN0 | hNpos
  · refine ⟨0, ?_, by rw [norm_zero, ← hN0]⟩
    rw [norm_eq_zero.1 hN0.symm]
    simp
  set N := ‖hf.toLp f‖ with hN
  have hNc : (N : ℂ) ≠ 0 := ofReal_ne_zero.2 hNpos.ne'
  set g : SimpleFunc α E := (N⁻¹ : ℂ) • f with hg
  have hgfin : ∀ y, y ≠ 0 → μ (g ⁻¹' {y}) < ∞ := fun y hy => by
    refine (measure_mono fun x hx => ?_).trans_lt (hfin ((N : ℂ) • y) (smul_ne_zero
      (ofReal_ne_zero.2 hNpos.ne') hy))
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hg, FunLike.coe_smul,
      Pi.smul_apply] at hx ⊢
    rw [← hx, smul_smul, mul_inv_cancel₀ hNc, one_smul]
  have hg₀ := SimpleFunc.memLp_of_finite_measure_preimage p₀ hgfin
  have hgnorm : eLpNorm g p μ ≤ 1 := by
    rw [hg, FunLike.coe_smul, eLpNorm_const_smul, ← ofReal_norm, norm_inv,
      norm_real, Real.norm_of_nonneg hNpos.le, hN, Lp.norm_toLp,
      ENNReal.ofReal_inv_of_pos (by simpa [hN, Lp.norm_toLp] using hNpos),
      ENNReal.ofReal_toReal (hf.eLpNorm_lt_top.ne)]
    exact ENNReal.inv_mul_le_one _
  obtain ⟨u, hu, hun⟩ := exists_toSum_eq_fstToSum_of_eLpNorm_le_one hθ hp hg₀
    (SimpleFunc.memLp_of_finite_measure_preimage p₁ hgfin) hgnorm
  refine ⟨(N : ℂ) • u, ?_, ?_⟩
  · rw [map_smul, map_smul, hu, sumSpaceEmbed_fstToSum, lebesgue_embed₀, ← map_smul,
      L1AddLinfty.ofLp_eq_ofLp_iff]
    filter_upwards [Lp.coeFn_smul (N : ℂ) (hg₀.toLp g), hg₀.coeFn_toLp, hf.coeFn_toLp]
      with x h₁ h₂ h₃
    rw [h₁, Pi.smul_apply, h₂, h₃, hg, FunLike.coe_smul, Pi.smul_apply, smul_smul,
      mul_inv_cancel₀ hNc, one_smul]
  · rw [norm_smul, norm_real, Real.norm_of_nonneg hNpos.le]
    exact mul_le_of_le_one_right hNpos.le hun

/-- `ComplexMethodSpace.exists_sumSpaceEmbed_toSum_eq_ofLp` for `p < ∞`, by density of the simple
functions in `Lᵖ`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_ofLp_of_ne_top [CompleteSpace E] [Fact (1 ≤ p)]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hp_top : p ≠ ∞) (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ := by
  -- approximate `f` by simple functions `g n`, with `‖f - g n‖_p < 1 / (n + 1)`
  have happrox (n : ℕ) : ∃ g : SimpleFunc α E,
      eLpNorm (⇑f - ⇑g) p μ < ENNReal.ofReal (1 / (n + 1)) ∧ MemLp g p μ :=
    (Lp.memLp f).exists_simpleFunc_eLpNorm_sub_lt hp_top
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose g hg hgm using happrox
  set F : ℕ → Lp E p μ := fun n => (hgm n).toLp (g n)
  have hF : Tendsto F atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev, Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
      ((EventuallyEq.refl _ ⇑f).sub (hgm n).coeFn_toLp))]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hg n).le
  choose u hu hun using fun n => exists_toSum_simpleFunc hθ hp hp_top (hgm n)
  have hu' (n : ℕ) : (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum (u n)) =
      L1AddLinfty.ofLp (F n) := hu n
  have hinj : Function.Injective fun v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ =>
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) :=
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective.comp ComplexMethodSpace.toSum_injective
  -- the classes `u n` of the simple functions form a Cauchy sequence, since `g m - g n` is simple
  have hdist (m n : ℕ) : ‖u m - u n‖ ≤ ‖F m - F n‖ := by
    have hgmn : MemLp ⇑(g m - g n) p μ := by simpa using (hgm m).sub (hgm n)
    obtain ⟨v, hv, hvn⟩ := exists_toSum_simpleFunc hθ hp hp_top hgmn
    have hsub : hgmn.toLp ⇑(g m - g n) = F m - F n := by
      refine Lp.ext ?_
      filter_upwards [hgmn.coeFn_toLp, Lp.coeFn_sub (F m) (F n), (hgm m).coeFn_toLp,
        (hgm n).coeFn_toLp] with x h₁ h₂ h₃ h₄
      rw [h₁, h₂, Pi.sub_apply]
      exact (congrArg₂ (· - ·) h₃ h₄).symm
    rw [hsub] at hv hvn
    have : v = u m - u n := hinj <| by simp only [map_sub, hv, hu']
    rwa [this] at hvn
  have hC : CauchySeq u := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hF.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm]
      exact (hdist m n).trans_lt (by rw [← dist_eq_norm]; exact hN m hm n hn)⟩
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨v, tendsto_nhds_unique (((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed.continuous.comp
    ComplexMethodSpace.toSum.continuous).tendsto v |>.comp hv) ?_,
    le_of_tendsto_of_tendsto' hv.norm hF.norm hun⟩
  simpa only [Function.comp_def, hu'] using (L1AddLinfty.ofLp.continuous.tendsto f).comp hF

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
    rw [← h, map_add, map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀,
      lebesgue_embed₁]
  obtain ⟨f₀, f₁, h⟩ := (lebesgue ℂ E μ ∞ ∞).exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum u)
  refine ⟨f₀ + f₁, key f₀ f₁ h, le_of_forall_pos_lt_add fun ε hε => ?_⟩
  obtain ⟨g₀, g₁, hg, hgn⟩ := (lebesgue ℂ E μ ∞ ∞).norm_sumSpace_lt_iff.1
    (lt_add_of_le_of_pos (ComplexMethodSpace.norm_toSum_le u) hε)
  rw [L1AddLinfty.ofLp_injective ((key f₀ f₁ h).trans (key g₀ g₁ hg).symm)]
  exact (norm_add_le _ _).trans_lt hgn

namespace ComplexMethodSpace

/-- **`Lᵖ` embeds in `[L^{p₀}, L^{p₁}]_θ`.** For `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the
interpolated exponent `1 / p = (1 - θ) / p₀ + θ / p₁`, every `f ∈ Lᵖ` lies in the complex
interpolation space of the Lebesgue couple, with `‖f‖_θ ≤ ‖f‖_p`: some `u` in it is the class of
`f` in `L¹ + L^∞`. Together with `exists_ofLp_eq_sumSpaceEmbed_toSum` this identifies the two
spaces isometrically (`ComplexMethodSpace.lebesgueEquiv`). -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp [CompleteSpace E] [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u) = L1AddLinfty.ofLp f ∧ ‖u‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- for `p = ∞` both endpoints are `L^∞`, and `f` lies in their intersection
    obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 rfl
    have hx : (f, f) ∈ (lebesgue ℂ E μ ∞ ∞).inter := mem_lebesgue_inter_iff.2 EventuallyEq.rfl
    refine ⟨ofInter θ ⟨(f, f), hx⟩, ?_, (norm_ofInter_le (Ioo_subset_Icc_self hθ) _).trans ?_⟩
    · rw [toSum_ofInter (Ioo_subset_Icc_self hθ), sumSpaceEmbed_fstToSum, lebesgue_embed₀,
        interFst_apply]
    · simp
  · exact exists_sumSpaceEmbed_toSum_eq_ofLp_of_ne_top hθ hp hp_top f

end ComplexMethodSpace

end Embedding

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-! ### Pairing with bounded functions of finite-measure support -/

/-- Hölder's inequality makes `⟪ψ, f⟫` integrable for `ψ ∈ L^{r'}` and `f ∈ Lʳ`. -/
private theorem integrable_inner_of_memLp {r r' : ℝ≥0∞} [r'.HolderConjugate r] {ψ f : α → E}
    (hψ : MemLp ψ r' μ) (hf : MemLp f r μ) : Integrable (fun x => ⟪ψ x, f x⟫_ℂ) μ :=
  (hψ.norm.integrable_mul hf.norm).mono (hψ.aestronglyMeasurable.inner hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by simpa using norm_inner_le_norm (ψ x) (f x))

omit [InnerProductSpace ℂ E] in
/-- A function in `L¹ ∩ L^∞` is in the dual space of every `Lʳ`. -/
private theorem memLp_conjExponent {r : ℝ≥0∞} [Fact (1 ≤ r)] {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) : MemLp ψ r.conjExponent μ :=
  h₁.of_le_of_le htop one_ne_zero (ENNReal.HolderConjugate.one_le r.conjExponent r) le_top

/-- The pairing `f ↦ ∫ ⟪ψ, f⟫` of `Lʳ` with a function `ψ ∈ L¹ ∩ L^∞`. -/
private def innerCLM (r : ℝ≥0∞) [Fact (1 ≤ r)] {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) : Lp E r μ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ
      map_add' f g := by
        rw [← integral_add
          (integrable_inner_of_memLp (memLp_conjExponent (r := r) h₁ htop) (Lp.memLp f))
          (integrable_inner_of_memLp (memLp_conjExponent (r := r) h₁ htop) (Lp.memLp g))]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, inner_add_right]
      map_smul' c f := by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, inner_smul_right] }
    (eLpNorm ψ r.conjExponent μ).toReal fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_def, ← ENNReal.toReal_mul, ← toReal_eNorm]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top
        (memLp_conjExponent (r := r) h₁ htop).eLpNorm_ne_top (Lp.eLpNorm_ne_top f))
        enorm_integral_inner_le

private theorem innerCLM_apply (r : ℝ≥0∞) [Fact (1 ≤ r)] {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) (f : Lp E r μ) : innerCLM r h₁ htop f = ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ :=
  rfl

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
  sumLift_fstToSum _ _ _ _ f

private theorem sumInnerCLM_sndToSum {ψ : α → E} (h₁ : MemLp ψ 1 μ) (htop : MemLp ψ ∞ μ)
    (f : Lp E p₁ μ) :
    sumInnerCLM (p₀ := p₀) h₁ htop ((lebesgue ℂ E μ p₀ p₁).sndToSum f) = ∫ x, ⟪ψ x, f x⟫_ℂ ∂μ :=
  sumLift_sndToSum _ _ _ _ f

private theorem sumInnerCLM_fstToSum_add_sndToSum {ψ : α → E} (h₁ : MemLp ψ 1 μ)
    (htop : MemLp ψ ∞ μ) (f₀ : Lp E p₀ μ) (f₁ : Lp E p₁ μ) :
    sumInnerCLM h₁ htop ((lebesgue ℂ E μ p₀ p₁).fstToSum f₀ + (lebesgue ℂ E μ p₀ p₁).sndToSum f₁) =
      ∫ x, ⟪ψ x, f₀ x + f₁ x⟫_ℂ ∂μ := by
  rw [map_add, sumInnerCLM_fstToSum, sumInnerCLM_sndToSum,
    ← integral_add (integrable_inner_of_memLp (memLp_conjExponent (r := p₀) h₁ htop) (Lp.memLp f₀))
      (integrable_inner_of_memLp (memLp_conjExponent (r := p₁) h₁ htop) (Lp.memLp f₁))]
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

private theorem norm_inv_norm_smul_le (v : E) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ ≤ 1 := by
  rw [norm_smul, norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
  rcases eq_or_ne ‖v‖ 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

private theorem norm_levelPiece_le (g : α → E) (r : SimpleFunc α ℝ) (ρ : ℝ) (x : α) :
    ‖levelPiece g r ρ x‖ ≤ 1 := by
  unfold levelPiece
  by_cases hx : x ∈ r ⁻¹' {ρ}
  · rw [Set.indicator_of_mem hx]
    exact norm_inv_norm_smul_le (g x)
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
  · rw [testFamily_apply, norm_smul, Complex.norm_conj, norm_levelCoeff P z h]
    exact mul_le_of_le_one_right (Real.rpow_nonneg h.le _) (norm_inv_norm_smul_le (g x))

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
  rw [sum_mul_integral_inner _ _ _ fun ρ _ => integrable_inner_of_memLp
    (memLp_levelPiece hg hs hgs r ρ t.conjExponent) (Lp.memLp f)]
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
  have hq₀ : p₀.conjExponent ≠ 0 := ENNReal.HolderConjugate.ne_zero _ p₀
  have hq₁ : p₁.conjExponent ≠ 0 := ENNReal.HolderConjugate.ne_zero _ p₁
  have hq := inv_conjExponent_eq_of_inv_eq (Fact.out : 1 ≤ p₀) (Fact.out : 1 ≤ p₁)
    (Ioo_subset_Icc_self hθ) hp
  set P := interpExponent (p₀.conjExponent⁻¹).toReal (p₁.conjExponent⁻¹).toReal θ
  have hPnn {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) : 0 ≤ (P z).re :=
    re_interpExponent_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hθ hz
  have h₁ (ρ : ℝ) := memLp_levelPiece hg hs hgs r ρ 1
  have htop (ρ : ℝ) := memLp_levelPiece hg hs hgs r ρ ⊤
  -- the pairing of `F` with the analytic family of test functions
  set Ψ : ℂ → ℂ := fun z => ∑ ρ ∈ r.range, levelCoeff P z ρ *
    sumInnerCLM (p₀ := p₀) (p₁ := p₁) (h₁ ρ) (htop ρ) (F z) with hΨ
  have hd : DiffContOnCl ℂ Ψ (verticalStrip 0 1) := by
    have key : ∀ S : Finset ℝ, DiffContOnCl ℂ (fun z => ∑ ρ ∈ S, levelCoeff P z ρ *
        sumInnerCLM (p₀ := p₀) (p₁ := p₁) (h₁ ρ) (htop ρ) (F z)) (verticalStrip 0 1) := by
      intro S
      induction S using Finset.cons_induction with
      | empty => simpa using diffContOnCl_const (c := (0 : ℂ))
      | cons a S ha ih =>
        simp only [Finset.sum_cons]
        exact (((differentiable_levelCoeff (differentiable_interpExponent _ _ _)
          a).diffContOnCl).smul ((ContinuousLinearMap.differentiable _).comp_diffContOnCl
            hF.diffContOnCl)).add ih
    exact key r.range
  have hB : BddAbove ((norm ∘ Ψ) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ ρ ∈ r.range, Real.exp ((1 + |interpSlope (p₀.conjExponent⁻¹).toReal
      (p₁.conjExponent⁻¹).toReal θ|) * |Real.log ρ|) *
        (‖sumInnerCLM (p₀ := p₀) (p₁ := p₁) (h₁ ρ) (htop ρ)‖ * ‖tr‖), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (norm_levelCoeff_le P z ρ (abs_re_interpExponent_le hθ hz))
      (((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hF.norm_le hz)
        (norm_nonneg _)))) (norm_nonneg _) (Real.exp_pos _).le
  -- on the two boundary lines the pairing is bounded by the norm of the traces
  have ha : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖Ψ z‖ ≤ ‖tr‖ := by
    intro z hz
    have hz' : z = (z.im : ℂ) * I := by
      rw [← re_add_im z, show z.re = 0 from hz]
      simp
    simp only [hΨ]
    rw [hz', hF.apply_mul_I]
    simp only [sumInnerCLM_fstToSum]
    rw [← hz']
    refine (norm_sum_levelCoeff_mul_integral_le (hPnn (by simp [show z.re = 0 from hz]))
      (ofReal_re_interpExponent_mul_inv_of_re_eq_zero hq₀ hq₁ hθ hq hz).symm hg hs hgs hr hrn
      _).trans ?_
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_fst_le tr)
  have hb : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖Ψ z‖ ≤ ‖tr‖ := by
    intro z hz
    have hz' : z = 1 + (z.im : ℂ) * I := by
      rw [← re_add_im z, show z.re = 1 from hz]
      simp
    simp only [hΨ]
    rw [hz', hF.apply_one_add_mul_I]
    simp only [sumInnerCLM_sndToSum]
    rw [← hz']
    refine (norm_sum_levelCoeff_mul_integral_le (hPnn (by simp [show z.re = 1 from hz]))
      (ofReal_re_interpExponent_mul_inv_of_re_eq_one hq₀ hq₁ hθ hq hz).symm hg hs hgs hr hrn
      _).trans ?_
    exact (ZeroAtInftyContinuousMap.norm_coe_le_norm _ _).trans (norm_snd_le tr)
  have key := norm_le_interp_of_mem_verticalClosedStrip₀₁' Ψ (z := (θ : ℂ))
    (by simp [hθ.1.le, hθ.2.le]) hd hB ha hb
  rw [← Real.rpow_add' (norm_nonneg _) (by simp), ofReal_re, sub_add_cancel, Real.rpow_one] at key
  -- at `θ` the exponent is one and the test function is `r ‖g‖⁻¹ g`
  refine le_of_eq_of_le ?_ key
  simp only [hΨ, hFθ, sumInnerCLM_fstToSum_add_sndToSum]
  rw [sum_mul_integral_inner _ _ _ fun ρ _ => ((integrable_inner_of_memLp
    (memLp_levelPiece hg hs hgs r ρ p₀.conjExponent) (Lp.memLp f₀)).add
    (integrable_inner_of_memLp (memLp_levelPiece hg hs hgs r ρ p₁.conjExponent)
      (Lp.memLp f₁))).congr (ae_of_all _ fun x => (inner_add_right _ _ _).symm)]
  congr 2
  funext x
  rw [← testFamily, testFamily_of_eq_one (interpExponent_self _ _ _) g hr x]

private theorem norm_ofReal_mul_inv_norm_smul_le {ρ : ℝ} (hρ : 0 ≤ ρ) (v : E) (hρv : ρ ≤ ‖v‖) :
    ‖((ρ * ‖v‖⁻¹ : ℝ) : ℂ) • v‖ ≤ ‖v‖ := by
  rw [norm_smul, norm_real, Real.norm_of_nonneg (by positivity)]
  rcases eq_or_ne ‖v‖ 0 with h | h
  · simp [h]
  · rwa [mul_assoc, inv_mul_cancel₀ h, mul_one]

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
      rw [← mul_add]
      exact mul_le_mul (norm_ofReal_mul_inv_norm_smul_le (hr0 n x) (g x) (hle n x))
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
  -- every representative of `u` bounds the pairings with normalized test functions
  have hpair₁ {g : α → E} (hg : StronglyMeasurable g) {s : Set α} (hs : μ s ≠ ∞)
      (hgs : ∀ x ∉ s, g x = 0) (hgtop : MemLp g ∞ μ) (hgn : eLpNorm g p.conjExponent μ ≤ 1) :
      ‖∫ x, ⟪g x, f₀ x + f₁ x⟫_ℂ ∂μ‖ ≤ ‖u‖ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨tr, rfl, htr⟩ := ComplexMethodSpace.norm_lt_iff.1 (lt_add_of_pos_right ‖u‖ hε)
    refine lt_of_le_of_lt ?_ htr
    exact norm_integral_inner_le_of_isStripFunction_of_eLpNorm_le_one hθ hp
      ((lebesgue ℂ E μ p₀ p₁).isStripFunction_stripFunction tr)
      (by rw [← stripEval_apply, ← ComplexMethodSpace.toSum_mk, hdec]) hg hs hgs hgtop hgn
  -- hence all bounded test functions of finite-measure support, after normalization
  have hpair (g : α → E) (s : Set α) (hs : μ s ≠ ∞) (hgs : ∀ x, x ∉ s → g x = 0)
      (hgtop : MemLp g ∞ μ) :
      ‖∫ x, ⟪f₀ x + f₁ x, g x⟫_ℂ ∂μ‖ₑ ≤ ENNReal.ofReal ‖u‖ * eLpNorm g p.conjExponent μ := by
    -- a strongly measurable version `g'` of `g`, vanishing off a measurable set of finite measure
    set s' := toMeasurable μ s
    set g' : α → E := s'.indicator (hgtop.aestronglyMeasurable.mk g) with hg'_def
    have hg' : StronglyMeasurable g' :=
      hgtop.aestronglyMeasurable.stronglyMeasurable_mk.indicator (measurableSet_toMeasurable μ s)
    have hgg' : g =ᵐ[μ] g' := by
      filter_upwards [hgtop.aestronglyMeasurable.ae_eq_mk] with x hx
      by_cases hxs : x ∈ s'
      · rw [hg'_def, Set.indicator_of_mem hxs, hx]
      · rw [hg'_def, Set.indicator_of_notMem hxs, hgs x fun h => hxs (subset_toMeasurable μ s h)]
    have hs' : μ s' ≠ ∞ := by rwa [measure_toMeasurable]
    have hg's : ∀ x ∉ s', g' x = 0 := fun x hx => Set.indicator_of_notMem hx _
    have hg'top : MemLp g' ∞ μ := hgtop.ae_eq hgg'
    have hconj : ∫ x, ⟪f₀ x + f₁ x, g x⟫_ℂ ∂μ = conj (∫ x, ⟪g' x, f₀ x + f₁ x⟫_ℂ ∂μ) := by
      rw [← integral_conj]
      exact integral_congr_ae (hgg'.mono fun x hx => by simp only [hx, inner_conj_symm])
    rw [hconj, ← ofReal_norm, RCLike.norm_conj, eLpNorm_congr_ae hgg']
    have hc : eLpNorm g' p.conjExponent μ ≠ ∞ :=
      (hg'top.mono_exponent_of_measure_support_ne_top hg's hs' le_top).eLpNorm_ne_top
    rcases eq_or_ne (eLpNorm g' p.conjExponent μ) 0 with hc0 | hc0
    · have hg'0 : g' =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff (ENNReal.HolderConjugate.ne_zero _ p)).1 hc0
      rw [integral_eq_zero_of_ae (hg'0.mono fun x hx => by simp [hx])]
      simp
    · set k : ℝ := (eLpNorm g' p.conjExponent μ).toReal with hk_def
      have hk : 0 < k := ENNReal.toReal_pos hc0 hc
      have hn : eLpNorm (((k⁻¹ : ℝ) : ℂ) • g') p.conjExponent μ ≤ 1 := by
        rw [eLpNorm_const_smul, ← ofReal_norm, norm_real, Real.norm_of_nonneg (inv_pos.2 hk).le,
          ENNReal.ofReal_inv_of_pos hk, hk_def, ENNReal.ofReal_toReal hc]
        exact ENNReal.inv_mul_le_one _
      have hb := hpair₁ (hg'.const_smul _) hs' (fun x hx => by simp [hg's x hx])
        (hg'top.const_smul _) hn
      simp_rw [Pi.smul_apply, inner_smul_left, integral_const_mul, conj_ofReal, norm_mul, norm_real,
        Real.norm_of_nonneg (inv_pos.2 hk).le] at hb
      rw [← ENNReal.ofReal_toReal hc, ← hk_def, ← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_mul_le_iff₀ hk] at hb
      linarith
  have hh : AEStronglyMeasurable (fun x => f₀ x + f₁ x) μ :=
    (Lp.aestronglyMeasurable f₀).add (Lp.aestronglyMeasurable f₁)
  have hle := hh.eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) hp_top hpair
  have hmem : MemLp (fun x => f₀ x + f₁ x) p μ := memLp_iff.2 (hle.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hmem.toLp _, ?_, ?_⟩
  · rw [← hdec, map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀,
      lebesgue_embed₁]
    refine (l1Linfty ℂ E μ).sumSpaceEmbed_injective ?_
    rw [map_add, L1AddLinfty.sumSpaceEmbed_ofLp, L1AddLinfty.sumSpaceEmbed_ofLp,
      L1AddLinfty.sumSpaceEmbed_ofLp]
    exact ((L1AddLinfty.lpToAmbient_add_lpToAmbient_eq_iff ℂ).2 hmem.coeFn_toLp.symm).symm
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

end ComplexMethodSpace

end Inner

end TauCeti.CompatibleCouple
