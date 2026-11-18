/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `Lᵖ` embeds contractively into `[L^{p₀}, L^{p₁}]_θ`

Let `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁`. For the Lebesgue couple
`(L^{p₀}(μ; E), L^{p₁}(μ; E))` of a complex Banach space `E`, every `f ∈ Lᵖ(μ; E)` lies in the
complex interpolation space `[L^{p₀}, L^{p₁}]_θ`, with `‖f‖_θ ≤ ‖f‖_p`. This is one of the two
inclusions of the identity `[L^{p₀}, L^{p₁}]_θ = Lᵖ` with equal norms (Bergh–Löfström,
Theorem 5.1.1, and Theorem 5.1.2 for vector values). The map is
`TauCeti.CompatibleCouple.ComplexMethodSpace.ofLp`, a continuous linear map
`Lᵖ(μ; E) → [L^{p₀}, L^{p₁}]_θ` of norm at most one lying over the common embedding of both spaces
into `L¹ + L^∞` (`TauCeti.CompatibleCouple.ComplexMethodSpace.sumSpaceEmbed_toSum_ofLp`); when
`p₀ ≤ p ≤ p₁` it lies over the inclusion `Lᵖ → L^{p₀} + L^{p₁}`
(`TauCeti.CompatibleCouple.ComplexMethodSpace.toSum_ofLp`).

For `p < ∞` and a simple function `f` with `‖f‖_p = N > 0`, the admissible function is the
analytic family

`F(z) = exp (δ (z - θ)²) (‖f‖ / N) ^ (r(z) - 1) f`, `r(z) = p ((1 - z) / p₀ + z / p₁)`,

with `F(θ) = f`. On the line `re z = j` the pointwise norm of `F(z)` is
`|exp (δ (z - θ)²)| N ^ (1 - p / pⱼ) ‖f‖ ^ (p / pⱼ)`, whose `L^{pⱼ}` norm is
`|exp (δ (z - θ)²)| N`; letting `δ → 0` gives `‖f‖_θ ≤ N`. The family is built by induction on
simple functions, as a sum of the families of indicator functions with disjoint supports. Simple
functions are dense in `Lᵖ` and `[L^{p₀}, L^{p₁}]_θ` is complete, so the contraction extends to
all of `Lᵖ`. For `p = ∞` both endpoints are `L^∞`, which is the intersection of the couple.

## Main declarations

* `TauCeti.CompatibleCouple.ComplexMethodSpace.ofLp`: the contractive inclusion
  `Lᵖ → [L^{p₀}, L^{p₁}]_θ`.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.sumSpaceEmbed_toSum_ofLp`,
  `TauCeti.CompatibleCouple.ComplexMethodSpace.toSum_ofLp`: it is the identity on the underlying
  functions.
* `TauCeti.CompatibleCouple.ComplexMethodSpace.norm_ofLp_le`: `‖f‖_θ ≤ ‖f‖_p`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, Theorems 5.1.1 and 5.1.2.
-/

public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines Filter Set Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-! ### The analytic family through a simple function -/

/-- The exponent `r(z) = p ((1 - z) / p₀ + z / p₁)` of the analytic family. -/
private def expo (p₀ p₁ p : ℝ≥0∞) (z : ℂ) : ℂ :=
  p.toReal * ((1 - z) * (p₀⁻¹).toReal + z * (p₁⁻¹).toReal)

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem re_expo (z : ℂ) :
    (expo p₀ p₁ p z).re = p.toReal * ((1 - z.re) * (p₀⁻¹).toReal + z.re * (p₁⁻¹).toReal) := by
  simp [expo]

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem expo_self (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0) : expo p₀ p₁ p θ = 1 := by
  have h := congrArg ENNReal.toReal (inv_eq_ofReal_of_inv_eq hp₀ hp₁ hθ hp)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by
    have := sub_nonneg.2 hθ.2
    have := hθ.1
    positivity)] at h
  have hp' : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hp0, hpt⟩
  have h2 : p.toReal * ((1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal) = 1 := by
    rw [← h, mul_inv_cancel₀ hp']
  rw [expo]
  exact_mod_cast h2

/-- On the closed strip the real part of the exponent lies in `[0, p]`. -/
private theorem re_expo_mem {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) :
    (expo p₀ p₁ p z).re ∈ Icc 0 p.toReal := by
  have h₀ : (p₀⁻¹).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using ENNReal.inv_le_one.2 (Fact.out : 1 ≤ p₀))
  have h₁ : (p₁⁻¹).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using ENNReal.inv_le_one.2 (Fact.out : 1 ≤ p₁))
  have hz1 := sub_nonneg.2 hz.2
  have hq₀ : (0 : ℝ) ≤ (p₀⁻¹).toReal := ENNReal.toReal_nonneg
  have hq₁ : (0 : ℝ) ≤ (p₁⁻¹).toReal := ENNReal.toReal_nonneg
  have hp : (0 : ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hle : (1 - z.re) * (p₀⁻¹).toReal + z.re * (p₁⁻¹).toReal ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h₀ hz1, mul_le_mul_of_nonneg_left h₁ hz.1]
  rw [re_expo]
  exact ⟨mul_nonneg hp (add_nonneg (mul_nonneg hz1 hq₀) (mul_nonneg hz.1 hq₁)),
    (mul_le_mul_of_nonneg_left hle hp).trans_eq (mul_one _)⟩

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
/-- On a line where `re r(z) = p / s`, the exponent relation `1 / s = re r(z) / p`, in the form
used by `TauCeti.eLpNorm_le_mul_eLpNorm_rpow`. -/
private theorem inv_eq_ofReal_re_expo_mul_inv {s : ℝ≥0∞} (hs : s ≠ 0) (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) {z : ℂ} (hz : (expo p₀ p₁ p z).re = p.toReal * (s⁻¹).toReal) :
    s⁻¹ = ENNReal.ofReal (expo p₀ p₁ p z).re * p⁻¹ := by
  rw [hz, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hpt,
    ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hs), mul_comm p, mul_assoc,
    ENNReal.mul_inv_cancel hp0 hpt, mul_one]

/-- The scalar coefficient `exp (δ (z - θ)²) (a / N) ^ (r(z) - 1)` of the analytic family at a
point where `‖f‖ = a`. -/
private def coeff (p₀ p₁ p : ℝ≥0∞) (δ θ N a : ℝ) (z : ℂ) : ℂ :=
  stripGaussian δ θ z * ((a / N : ℝ) : ℂ) ^ (expo p₀ p₁ p z - 1)

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem coeff_self (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0) (δ N a : ℝ) : coeff p₀ p₁ p δ θ N a θ = 1 := by
  simp [coeff, expo_self hθ hp hp0 hpt hp₀ hp₁]

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem differentiable_coeff (δ θ : ℝ) {N a : ℝ} (hN : 0 < N) (ha : 0 < a) :
    Differentiable ℂ (coeff p₀ p₁ p δ θ N a) :=
  (differentiable_stripGaussian δ θ).mul <| Differentiable.const_cpow (by unfold expo; fun_prop)
    (Or.inl (ofReal_ne_zero.2 (div_pos ha hN).ne'))

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem norm_coeff {δ θ N a : ℝ} (hN : 0 < N) (ha : 0 < a) (z : ℂ) :
    ‖coeff p₀ p₁ p δ θ N a z‖ = ‖stripGaussian δ θ z‖ * (a / N) ^ ((expo p₀ p₁ p z).re - 1) := by
  rw [coeff, norm_mul, norm_cpow_eq_rpow_re_of_pos (div_pos ha hN), sub_re, one_re]

private theorem norm_coeff_le {δ θ N a : ℝ} (hδ : 0 ≤ δ) (hN : 0 < N) (ha : 0 < a) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖coeff p₀ p₁ p δ θ N a z‖ ≤
      Real.exp (δ * (|θ| + 1) ^ 2) * ((a / N) ^ (-1 : ℝ) + (a / N) ^ (p.toReal - 1)) := by
  have hr := re_expo_mem (p₀ := p₀) (p₁ := p₁) (p := p) hz
  have hb := div_pos ha hN
  rw [norm_coeff hN ha]
  refine mul_le_mul (norm_stripGaussian_le hδ θ hz) ?_ (Real.rpow_nonneg hb.le _)
    (Real.exp_pos _).le
  -- The exponent `re r(z) - 1` lies in `[-1, p - 1]`.
  rcases le_total 1 (a / N) with hb1 | hb1
  · exact (Real.rpow_le_rpow_of_exponent_le hb1 (by linarith [hr.2])).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hb.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith [hr.1])).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hb.le _))

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
private theorem tendsto_coeff {δ θ N a : ℝ} (hδ : 0 < δ) (hN : 0 < N) (ha : 0 < a) (b : ℝ) :
    Tendsto (fun t : ℝ => coeff p₀ p₁ p δ θ N a (b + t * I)) (cocompact ℝ) (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have h := (tendsto_norm_stripGaussian hδ θ b).mul_const
    ((a / N) ^ (p.toReal * ((1 - b) * (p₀⁻¹).toReal + b * (p₁⁻¹).toReal) - 1))
  rw [zero_mul] at h
  refine h.congr fun t => ?_
  rw [norm_coeff hN ha, re_expo]
  simp

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] in
/-- The pointwise bound on the boundary values of the analytic family: on a line where
`re r(z) = ρ`, the value at a point with `f = v` has norm at most
`exp (δ (|θ| + 1)²) N ^ (1 - ρ) ‖v‖ ^ ρ`. -/
private theorem norm_coeff_smul_le {δ θ N ρ : ℝ} (hδ : 0 ≤ δ) (hN : 0 < N) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hzρ : (expo p₀ p₁ p z).re = ρ) (v : E) :
    ‖coeff p₀ p₁ p δ θ N ‖v‖ z • v‖ ≤
      Real.exp (δ * (|θ| + 1) ^ 2) * N ^ (1 - ρ) * ‖v‖ ^ ρ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [smul_zero, norm_zero]
    positivity
  have ha := norm_pos_iff.2 hv
  -- `(a / N) ^ (ρ - 1) a = N ^ (1 - ρ) a ^ ρ`.
  have h : (‖v‖ / N) ^ (ρ - 1) * ‖v‖ = N ^ (1 - ρ) * ‖v‖ ^ ρ := by
    have hNρ := (Real.rpow_pos_of_pos hN ρ).ne'
    rw [Real.div_rpow ha.le hN.le, Real.rpow_sub_one ha.ne', Real.rpow_sub hN, Real.rpow_sub hN,
      Real.rpow_one]
    field_simp [hNρ]
  rw [norm_smul, norm_coeff hN ha, hzρ, mul_assoc, h, ← mul_assoc]
  gcongr
  exact norm_stripGaussian_le hδ θ hz

variable (θ) in
/-- `f` has an admissible function `F` with `F θ = f` whose boundary traces are, almost
everywhere, the values `coeff ‖f‖ z • f` of the analytic family through `f`. -/
private def HasFamily (p₀ p₁ : ℝ≥0∞) [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (δ N : ℝ) (f : Lp E p μ) : Prop :=
  ∃ F g, (lebesgue ℂ E μ p₀ p₁).IsStripFunction F g ∧
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (F θ) = L1AddLinfty.ofLp f ∧
    (∀ t : ℝ, ⇑(g.1 t) =ᵐ[μ] fun x => coeff p₀ p₁ p δ θ N ‖f x‖ (t * I) • f x) ∧
    ∀ t : ℝ, ⇑(g.2 t) =ᵐ[μ] fun x => coeff p₀ p₁ p δ θ N ‖f x‖ (1 + t * I) • f x

/-- The indicator function of `s` with value `c` as an element of `L^{p₀} ∩ L^{p₁}`. -/
private def indicatorInter {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    (lebesgue ℂ E μ p₀ p₁).inter :=
  ⟨(indicatorConstLp p₀ hs hμs c, indicatorConstLp p₁ hs hμs c),
    mem_lebesgue_inter_iff.2 ((indicatorConstLp_coeFn (p := p₀) (hs := hs) (hμs := hμs)
      (c := c)).trans (indicatorConstLp_coeFn (p := p₁) (hs := hs) (hμs := hμs) (c := c)).symm)⟩

variable [Fact (1 ≤ p)]

private theorem hasFamily_indicatorConstLp (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpt : p ≠ ∞)
    {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : E) : HasFamily θ p₀ p₁ δ N (indicatorConstLp p hs hμs c) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hf := indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : indicatorConstLp p hs hμs (0 : E) = 0 :=
      Lp.ext ((hf.trans (Eventually.of_forall fun x => by simp)).trans (Lp.coeFn_zero E p μ).symm)
    refine ⟨0, 0, IsStripFunction.zero, by simp [h0], fun t => ?_, fun t => ?_⟩
    · filter_upwards [hf, Lp.coeFn_zero E p₀ μ] with x hx _
      simp_all
    · filter_upwards [hf, Lp.coeFn_zero E p₁ μ] with x hx _
      simp_all
  have ha := norm_pos_iff.2 hc
  set x : (lebesgue ℂ E μ p₀ p₁).inter := indicatorInter hs hμs c
  have hK (z) (hz : z ∈ verticalClosedStrip 0 1) := norm_coeff_le (p₀ := p₀) (p₁ := p₁) (p := p)
    (θ := θ) hδ.le hN ha hz
  refine ⟨_, _, (lebesgue ℂ E μ p₀ p₁).isStripFunction_smul_inter x
    (differentiable_coeff δ θ hN ha) hK (by simpa using tendsto_coeff hδ hN ha 0)
    (by simpa using tendsto_coeff hδ hN ha 1), ?_, fun t => ?_, fun t => ?_⟩
  · rw [coeff_self hθ hp hp0 hpt hp₀ hp₁, one_smul, sumSpaceEmbed_fstToSum, lebesgue_embed₀,
      interFst_apply]
    exact L1AddLinfty.ofLp_eq_ofLp_iff.2 ((indicatorConstLp_coeFn (p := p₀) (hs := hs)
      (hμs := hμs) (c := c)).trans hf.symm)
  · rw [smulInterTraces_fst_apply, interFst_apply]
    filter_upwards [Lp.coeFn_smul (coeff p₀ p₁ p δ θ N ‖c‖ (t * I))
      (indicatorConstLp p₀ hs hμs c), indicatorConstLp_coeFn (p := p₀) (hs := hs) (hμs := hμs)
      (c := c), hf] with y h h₀ hy
    by_cases hys : y ∈ s <;> simp_all [x, indicatorInter]
  · rw [smulInterTraces_snd_apply, interSnd_apply]
    filter_upwards [Lp.coeFn_smul (coeff p₀ p₁ p δ θ N ‖c‖ (1 + t * I))
      (indicatorConstLp p₁ hs hμs c), indicatorConstLp_coeFn (p := p₁) (hs := hs) (hμs := hμs)
      (c := c), hf] with y h h₁ hy
    by_cases hys : y ∈ s <;> simp_all [x, indicatorInter]

private theorem hasFamily_add {δ N : ℝ} {f g : Lp E p μ} (hf : HasFamily θ p₀ p₁ δ N f)
    (hg : HasFamily θ p₀ p₁ δ N g) (hfg : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    HasFamily θ p₀ p₁ δ N (f + g) := by
  obtain ⟨F, a, hF, hFθ, ha₀, ha₁⟩ := hf
  obtain ⟨G, b, hG, hGθ, hb₀, hb₁⟩ := hg
  refine ⟨F + G, a + b, hF.add hG, by simp [hFθ, hGθ], fun t => ?_, fun t => ?_⟩
  · filter_upwards [Lp.coeFn_add (a.1 t) (b.1 t), Lp.coeFn_add f g, ha₀ t, hb₀ t, hfg]
      with x h hx h₁ h₂ h₀
    simp only [Prod.fst_add] at h ⊢
    rcases h₀ with h₀ | h₀ <;> simp_all
  · filter_upwards [Lp.coeFn_add (a.2 t) (b.2 t), Lp.coeFn_add f g, ha₁ t, hb₁ t, hfg]
      with x h hx h₁ h₂ h₀
    simp only [Prod.snd_add] at h ⊢
    rcases h₀ with h₀ | h₀ <;> simp_all

/-- Every simple function of `Lᵖ`, `p < ∞`, has an analytic family. -/
private theorem hasFamily_simpleFunc (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpt : p ≠ ∞)
    {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) (f : Lp.simpleFunc E p μ) :
    HasFamily θ p₀ p₁ δ N (f : Lp E p μ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  induction f using Lp.simpleFunc.induction hp0 hpt with
  | indicatorConst c hs hμs => exact hasFamily_indicatorConstLp hθ hp hpt hδ hN hs hμs.ne c
  | @add f g hf hg hfg hFf hFg =>
    refine hasFamily_add hFf hFg ?_
    rw [Lp.simpleFunc.toLp_eq_toLp, Lp.simpleFunc.toLp_eq_toLp]
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂, or_iff_not_imp_left]
    exact fun h => Function.notMem_support.1 (Set.disjoint_left.1 hfg h)

/-- The boundary traces of the analytic family through `f` have `L^{pⱼ}` norm at most
`exp (δ (|θ| + 1)²) ‖f‖_p`. -/
private theorem norm_trace_le {δ : ℝ} (hδ : 0 ≤ δ) {f : Lp E p μ} (hN : 0 < ‖f‖) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) {s : ℝ≥0∞}
    (hs : s⁻¹ = ENNReal.ofReal (expo p₀ p₁ p z).re * p⁻¹) {y : Lp E s μ}
    (hy : ⇑y =ᵐ[μ] fun x => coeff p₀ p₁ p δ θ ‖f‖ ‖f x‖ z • f x) :
    ‖y‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖f‖ := by
  set ρ := (expo p₀ p₁ p z).re
  have hρ := re_expo_mem (p₀ := p₀) (p₁ := p₁) (p := p) hz
  set K := Real.exp (δ * (|θ| + 1) ^ 2) * ‖f‖ ^ (1 - ρ)
  have hK : 0 ≤ K := by positivity
  have h := eLpNorm_le_mul_eLpNorm_rpow (K := K.toNNReal) (f := f) hρ.1
    (Lp.aestronglyMeasurable y) hs (hy.mono fun x hx => by
      rw [hx, Real.coe_toNNReal _ hK]
      exact norm_coeff_smul_le hδ hN hz rfl (f x))
  have h' : eLpNorm y s μ ≤ ENNReal.ofReal (K * ‖f‖ ^ ρ) := by
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg f) hρ.1, Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
    exact h
  calc ‖y‖ ≤ K * ‖f‖ ^ ρ := ENNReal.toReal_le_of_le_ofReal (by positivity) h'
    _ = Real.exp (δ * (|θ| + 1) ^ 2) * ‖f‖ := by
      rw [mul_assoc, ← Real.rpow_add hN, sub_add_cancel, Real.rpow_one]

/-- For `p < ∞`, a simple function `f ∈ Lᵖ` lies in `[L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p`. -/
private theorem exists_of_simpleFunc (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpt : p ≠ ∞)
    (f : Lp.simpleFunc E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) =
        L1AddLinfty.ofLp (f : Lp E p μ) ∧ ‖u‖ ≤ ‖(f : Lp E p μ)‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  rcases (norm_nonneg (f : Lp E p μ)).eq_or_lt with hN | hN
  · have hf0 : (f : Lp E p μ) = 0 := norm_eq_zero.1 hN.symm
    exact ⟨0, by simp [hf0], by simp⟩
  obtain ⟨F, g, hF, hFθ, -, -⟩ := hasFamily_simpleFunc hθ hp hpt one_pos hN f
  obtain ⟨u, hu⟩ := (ComplexMethodSpace.exists_toSum_eq_iff hθ).2 ⟨F, g, hF, rfl⟩
  refine ⟨u, by rw [hu, hFθ], ?_⟩
  -- The family with the Gaussian factor `exp (δ (z - θ)²)` bounds `‖u‖` by `exp (δ c) ‖f‖_p`.
  have key (δ : ℝ) (hδ : 0 < δ) :
      ‖u‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * ‖(f : Lp E p μ)‖ := by
    obtain ⟨G, h, hG, hGθ, h₀, h₁⟩ := hasFamily_simpleFunc hθ hp hpt hδ hN f
    refine (ComplexMethodSpace.norm_le_of_toSum_eq hθ hG
      (sumSpace_ext _ (by rw [hu, hFθ, hGθ]))).trans (norm_prod_le_iff.2
        ⟨(ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_,
          (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun t => ?_⟩)
    · exact norm_trace_le hδ.le hN (by simp)
        (inv_eq_ofReal_re_expo_mul_inv hp₀ hp0 hpt (by simp [re_expo])) (h₀ t)
    · exact norm_trace_le hδ.le hN (by simp)
        (inv_eq_ofReal_re_expo_mul_inv hp₁ hp0 hpt (by simp [re_expo])) (h₁ t)
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖(f : Lp E p μ)‖) (𝓝[>] 0)
      (𝓝 ‖(f : Lp E p μ)‖) := by
    have : Continuous fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) * ‖(f : Lp E p μ)‖ := by
      fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- An element of `[L^{p₀}, L^{p₁}]_θ` is determined by the function it represents in
`L¹ + L^∞`. -/
private theorem sumSpaceEmbed_toSum_injective :
    Function.Injective fun u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ =>
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) :=
  (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective.comp ComplexMethodSpace.toSum_injective

variable [CompleteSpace E]

/-- Every `f ∈ Lᵖ` lies in `[L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_ofLp (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) =
        L1AddLinfty.ofLp f ∧ ‖u‖ ≤ ‖f‖ := by
  have hθ' := Ioo_subset_Icc_self hθ
  by_cases hpt : p = ∞
  · -- Both endpoints are `L^∞`, and `f` lies in the intersection.
    obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 hpt
    subst hpt
    refine ⟨ComplexMethodSpace.ofInter θ ⟨(f, f), mem_lebesgue_inter_iff.2 EventuallyEq.rfl⟩,
      ?_, (ComplexMethodSpace.norm_ofInter_le hθ' _).trans (by simp)⟩
    rw [ComplexMethodSpace.toSum_ofInter hθ', sumSpaceEmbed_fstToSum, lebesgue_embed₀,
      interFst_apply]
  -- For `p < ∞`, approximate `f` by simple functions `v n = g n`, whose elements `u n` of the
  -- complete space `[L^{p₀}, L^{p₁}]_θ` form a Cauchy sequence.
  have hsimple := exists_of_simpleFunc (μ := μ) (E := E) hθ' hp hpt
  obtain ⟨v, hv, hvf⟩ := mem_closure_iff_seq_limit.1
    ((Lp.simpleFunc.denseRange (E := E) (μ := μ) hpt).closure_range ▸ mem_univ f)
  choose g hg using hv
  choose u hu hun using fun n => hsimple (g n)
  have hdist (m n : ℕ) : dist (u m) (u n) ≤ dist (v m) (v n) := by
    obtain ⟨w, hw, hwn⟩ := hsimple (g m - g n)
    have huw : u m - u n = w := sumSpaceEmbed_toSum_injective (by
      simp only [map_sub, hu, hw, AddSubgroup.coe_sub])
    rw [dist_eq_norm, dist_eq_norm, huw, ← hg m, ← hg n]
    simpa using hwn
  obtain ⟨u₀, hu₀⟩ := cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε =>
    (Metric.cauchySeq_iff.1 hvf.cauchySeq ε hε).imp fun N hN m hm n hn =>
      (hdist m n).trans_lt (hN m hm n hn))
  refine ⟨u₀, tendsto_nhds_unique (((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed.continuous.comp
    ComplexMethodSpace.toSum.continuous).tendsto u₀ |>.comp hu₀) ?_,
    le_of_tendsto_of_tendsto' hu₀.norm hvf.norm fun n => (hun n).trans_eq (by rw [hg])⟩
  refine (((L1AddLinfty.ofLp (𝕜 := ℂ) (E := E) (μ := μ) (p := p)).continuous.tendsto f).comp
    hvf).congr fun n => ?_
  simp [hu, hg]

/-- The element of `[L^{p₀}, L^{p₁}]_θ` given by `f ∈ Lᵖ`. -/
private def ofLpAux (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ) :
    (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ :=
  (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp f).choose

private theorem sumSpaceEmbed_toSum_ofLpAux (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum (ofLpAux hθ hp f)) =
      L1AddLinfty.ofLp f :=
  (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp f).choose_spec.1

namespace ComplexMethodSpace

/-- **`Lᵖ` embeds contractively into `[L^{p₀}, L^{p₁}]_θ`.** For `0 < θ < 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁`, every `f ∈ Lᵖ(μ; E)` lies in the complex interpolation space of
the Lebesgue couple `(L^{p₀}(μ; E), L^{p₁}(μ; E))`, as the same function
(`CompatibleCouple.ComplexMethodSpace.sumSpaceEmbed_toSum_ofLp`), with `‖f‖_θ ≤ ‖f‖_p`
(`CompatibleCouple.ComplexMethodSpace.norm_ofLp_le`). -/
def ofLp (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    Lp E p μ →L[ℂ] (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun := ofLpAux hθ hp
      map_add' f g := sumSpaceEmbed_toSum_injective <| by
        simp only [map_add, sumSpaceEmbed_toSum_ofLpAux]
      map_smul' c f := sumSpaceEmbed_toSum_injective <| by
        simp only [map_smul, sumSpaceEmbed_toSum_ofLpAux, RingHom.id_apply] }
    1 fun f =>
      (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp f).choose_spec.2.trans_eq (one_mul _).symm

variable (hθ : θ ∈ Ioo 0 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)

/-- The element `ofLp hθ hp f` of `[L^{p₀}, L^{p₁}]_θ` is the function `f`, viewed in
`L¹ + L^∞`. -/
@[simp]
theorem sumSpaceEmbed_toSum_ofLp (f : Lp E p μ) :
    (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum (ofLp hθ hp f)) = L1AddLinfty.ofLp f :=
  sumSpaceEmbed_toSum_ofLpAux hθ hp f

/-- For `p₀ ≤ p ≤ p₁`, the inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` lies over the inclusion
`Lᵖ → L^{p₀} + L^{p₁}`. -/
theorem toSum_ofLp (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    toSum (ofLp hθ hp f) = lpToLebesgueSum h₀ h₁ f :=
  sumSpace_ext _ (by simp)

/-- **`‖f‖_θ ≤ ‖f‖_p`** for `f ∈ Lᵖ`. -/
theorem norm_ofLp_le (f : Lp E p μ) : ‖ofLp hθ hp f‖ ≤ ‖f‖ :=
  (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp f).choose_spec.2

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` has operator norm at most one. -/
theorem opNorm_ofLp_le :
    ‖(ofLp hθ hp : Lp E p μ →L[ℂ] (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by simpa using norm_ofLp_le hθ hp f

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` is injective. -/
theorem ofLp_injective :
    Function.Injective (ofLp hθ hp : Lp E p μ → (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :=
  fun f g h => L1AddLinfty.ofLp_injective (𝕜 := ℂ) <| by
    rw [← sumSpaceEmbed_toSum_ofLp hθ hp f, h, sumSpaceEmbed_toSum_ofLp]

end ComplexMethodSpace

end TauCeti.CompatibleCouple
