/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic

/-!
# `Lᵖ` lies in the complex interpolation space of `(L^{p₀}, L^{p₁})`

Let `1 ≤ p₀, p₁ ≤ ∞`, `0 ≤ θ ≤ 1` and `1 / p = (1 - θ) / p₀ + θ / p₁`. Every `f ∈ Lᵖ(μ; E)`, for a
complex Banach space `E`, lies in the complex interpolation space `[L^{p₀}, L^{p₁}]_θ` of the
Lebesgue couple `TauCeti.CompatibleCouple.lebesgue`, with norm `‖f‖_θ ≤ ‖f‖_p`
(`TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le`). This is the
inclusion `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` of the identity `[L^{p₀}, L^{p₁}]_θ = Lᵖ` with equal norms
(Bergh–Löfström, Theorem 5.1.1), the description of the complex method on the Lebesgue couple
through which the interpolation of Bessel potential spaces and of operators between `Lᵖ` spaces
is computed. The theorem holds for `p < ∞` and every `0 ≤ θ ≤ 1`; for `0 < θ < 1` the only infinite
`p` is `p₀ = p₁ = ∞`, where the couple is `(L^∞, L^∞)` and the statement is immediate
(`TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le_of_mem_Ioo`).

The proof is Thorin's analytic family. For a simple function `f` with `‖f‖_p ≤ 1` and `δ > 0`,
the function

`F z = exp (δ (z - θ)²) sgn(f) |f| ^ {w z}`, where `w z = p ((1 - z) / p₀ + z / p₁)`,

is admissible for the complex method: it is a finite combination of the fibre indicators of `f`,
which lie in `L^{p₀} ∩ L^{p₁}`, with entire scalar coefficients that decay along the boundary
lines of the strip (`TauCeti.CompatibleCouple.exists_isStripFunction_smul_inter`). Since `w θ = 1`
it takes the value `f` at `θ`. On the line `re z = j` the modulus `|f| ^ {re w z} = |f| ^ {p / pⱼ}`
has `L^{pⱼ}` norm at most `‖f‖_p ^ {p / pⱼ} ≤ 1`
(`TauCeti.eLpNorm_le_eLpNorm_rpow`), so `‖f‖_θ ≤ exp δ` for every `δ > 0`. Simple functions are
dense in `Lᵖ` for `p < ∞`, and the bound passes to all of `Lᵖ` by continuity
(`LinearMap.extendOfNorm`).

Bergh and Löfström also prove the reverse inclusion `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ`, with
`‖f‖_p ≤ ‖f‖_θ`, by duality against the same analytic families of test functions; this file
treats the inclusion of `Lᵖ`.

## Main declarations

* `TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le`: for `0 ≤ θ ≤ 1` and
  `p < ∞`, every `f ∈ Lᵖ` lies in `[L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p`.
* `TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le_of_mem_Ioo`: the same
  for `0 < θ < 1` and every `p`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.1).
-/

public section

open MeasureTheory Complex Complex.HadamardThreeLines Filter Set Topology
open scoped ENNReal ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {mα : MeasurableSpace α}
  {μ : Measure α} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-! ### The analytic family through a simple function -/

/-- `powSign w c = ‖c‖ ^ (w - 1) • c`, the value at `c` of the analytic family `sgn(f) |f| ^ w`.
The convention `Real.log 0 = 0` gives `powSign w 0 = 0`. -/
private noncomputable def powSign (w : ℂ) (c : E) : E :=
  exp ((w - 1) * Real.log ‖c‖) • c

private theorem powSign_one (c : E) : powSign 1 c = c := by
  simp [powSign]

private theorem norm_powSign_le (w : ℂ) (c : E) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign, Real.rpow_nonneg]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    refine le_of_eq ?_
    have hre : ((w - 1) * (Real.log ‖c‖ : ℂ)).re = Real.log ‖c‖ * (w.re - 1) := by
      simp [mul_comm]
    rw [powSign, norm_smul, norm_exp, hre, ← Real.rpow_def_of_pos hpos,
      Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']

/-- The exponent `w z = r ((1 - z) a₀ + z a₁)` of the analytic family; it is used with `r = p`,
`a₀ = 1 / p₀` and `a₁ = 1 / p₁`. -/
private noncomputable def expo (r a₀ a₁ : ℝ) (z : ℂ) : ℂ :=
  r * ((1 - z) * a₀ + z * a₁)

private theorem re_expo (r a₀ a₁ : ℝ) (z : ℂ) :
    (expo r a₀ a₁ z).re = r * ((1 - z.re) * a₀ + z.re * a₁) := by
  simp [expo]

private theorem re_expo_mul_I (r a₀ a₁ t : ℝ) : (expo r a₀ a₁ (t * I)).re = r * a₀ := by
  simp [re_expo]

private theorem re_expo_one_add_mul_I (r a₀ a₁ t : ℝ) :
    (expo r a₀ a₁ (1 + t * I)).re = r * a₁ := by
  simp [re_expo]

/-- The scalar coefficient `exp (δ (z - θ)²) s ^ (w z - 1)` of the fibre `f ⁻¹' {c}` in the
analytic family, where `s = ‖c‖`. -/
private noncomputable def coeff (δ θ r a₀ a₁ s : ℝ) (z : ℂ) : ℂ :=
  exp (δ * (z - θ) ^ 2) * exp ((expo r a₀ a₁ z - 1) * Real.log s)

private theorem coeff_smul (δ θ r a₀ a₁ : ℝ) (c : E) (z : ℂ) :
    coeff δ θ r a₀ a₁ ‖c‖ z • c = exp (δ * (z - θ) ^ 2) • powSign (expo r a₀ a₁ z) c := by
  rw [coeff, mul_smul, powSign]

private theorem differentiable_coeff (δ θ r a₀ a₁ s : ℝ) :
    Differentiable ℂ (coeff δ θ r a₀ a₁ s) := by
  unfold coeff expo
  fun_prop

private theorem norm_coeff (δ θ r a₀ a₁ s : ℝ) (z : ℂ) :
    ‖coeff δ θ r a₀ a₁ s z‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) *
      Real.exp ((r * ((1 - z.re) * a₀ + z.re * a₁) - 1) * Real.log s) := by
  rw [coeff, norm_mul, norm_exp, norm_exp, ← re_expo]
  congr 2
  · simp [sq]
  · simp

/-- On the closed strip, `|exp (δ (z - θ)²)| ≤ exp δ` for `0 ≤ θ ≤ 1`. -/
private theorem norm_exp_mul_sub_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ∈ Icc 0 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖exp (δ * (z - θ) ^ 2)‖ ≤ Real.exp δ := by
  have hre : (δ * (z - θ) ^ 2 : ℂ).re = δ * ((z.re - θ) ^ 2 - z.im ^ 2) := by
    simp [sq]
  rw [norm_exp, hre, Real.exp_le_exp]
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h : (z.re - θ) ^ 2 - z.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.im]
  nlinarith

private theorem tendsto_exp_mul_sub_sq {δ : ℝ} (hδ : 0 < δ) (b : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (δ * (b - t ^ 2))) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun t => by simp
  have h : Tendsto (fun t : ℝ => δ * (b - t ^ 2)) (cocompact ℝ) atBot :=
    ((tendsto_atBot_add_const_left _ b (tendsto_neg_atTop_atBot.comp hsq)).const_mul_atBot
      hδ).congr fun t => by simp [sub_eq_add_neg]
  exact Real.tendsto_exp_atBot.comp h

/-- The coefficients tend to zero along the vertical line `re z = a`. -/
private theorem tendsto_coeff {δ : ℝ} (hδ : 0 < δ) (θ r a₀ a₁ s a : ℝ) :
    Tendsto (fun t : ℝ => coeff δ θ r a₀ a₁ s (a + t * I)) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_coeff] using (tendsto_exp_mul_sub_sq hδ ((a - θ) ^ 2)).mul_const
    (Real.exp ((r * ((1 - a) * a₀ + a * a₁) - 1) * Real.log s))

/-- The coefficients are bounded on the closed strip. -/
private theorem norm_coeff_le {δ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ∈ Icc 0 1) {r a₀ a₁ : ℝ} (hr : 0 ≤ r)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (s : ℝ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖coeff δ θ r a₀ a₁ s z‖ ≤ Real.exp δ * Real.exp ((r * (a₀ + a₁) + 1) * |Real.log s|) := by
  rw [coeff, norm_mul]
  refine mul_le_mul (norm_exp_mul_sub_sq_le hδ hθ hz) ?_ (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_exp, Real.exp_le_exp]
  have hre : ((expo r a₀ a₁ z - 1) * (Real.log s : ℂ)).re =
      (r * ((1 - z.re) * a₀ + z.re * a₁) - 1) * Real.log s := by
    simp [← re_expo]
  rw [hre]
  obtain ⟨hz0, hz1⟩ := hz
  have hw0 : 0 ≤ r * ((1 - z.re) * a₀ + z.re * a₁) := by
    have : 0 ≤ 1 - z.re := by linarith
    positivity
  have hw1 : r * ((1 - z.re) * a₀ + z.re * a₁) ≤ r * (a₀ + a₁) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hr
  calc (r * ((1 - z.re) * a₀ + z.re * a₁) - 1) * Real.log s
      ≤ |r * ((1 - z.re) * a₀ + z.re * a₁) - 1| * |Real.log s| := by
        rw [← abs_mul]
        exact le_abs_self _
    _ ≤ (r * (a₀ + a₁) + 1) * |Real.log s| := by
        gcongr
        exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### Simple functions in the intersection -/

/-- The piece of a simple function `f` on its fibre `f ⁻¹' {c}`. -/
private noncomputable def piece (f : SimpleFunc α E) (c : E) : SimpleFunc α E :=
  (SimpleFunc.const α c).restrict (f ⁻¹' {c})

/-- On each point the pieces of `f`, weighted by coefficients depending on the value, sum to the
weighted value of `f`. -/
private theorem sum_smul_piece_apply (f : SimpleFunc α E) (a : E → ℂ) (x : α) :
    ∑ c ∈ f.range, a c • piece f c x = a (f x) • f x := by
  have h := SimpleFunc.map_apply_eq_sum_restrict_const f (fun c => a c • c) x
  rw [SimpleFunc.map_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [piece, SimpleFunc.restrict_apply _ (f.measurableSet_fiber c), SimpleFunc.coe_const]
  by_cases hx : x ∈ f ⁻¹' {c} <;> simp [hx]

omit [NormedSpace ℂ E] in
private theorem piece_preimage_lt_top {f : SimpleFunc α E} (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞)
    (c : E) : ∀ y, y ≠ 0 → μ (piece f c ⁻¹' {y}) < ∞ := by
  intro y hy
  refine (measure_mono fun x hx => ?_).trans_lt (hf y hy)
  simp only [piece, mem_preimage, mem_singleton_iff,
    SimpleFunc.restrict_apply _ (f.measurableSet_fiber c), SimpleFunc.coe_const] at hx ⊢
  by_cases hxc : x ∈ f ⁻¹' {c}
  · rw [indicator_of_mem hxc] at hx
    rw [mem_preimage, mem_singleton_iff] at hxc
    exact hxc.trans hx
  · rw [indicator_of_notMem hxc] at hx
    exact absurd hx.symm hy

variable (p₀ p₁) in
/-- A simple function whose nonzero fibres have finite measure, as an element of
`L^{p₀} ∩ L^{p₁}`. -/
private noncomputable def simpleInter (f : SimpleFunc α E) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    (lebesgue ℂ E μ p₀ p₁).inter :=
  ⟨((SimpleFunc.memLp_of_finite_measure_preimage p₀ hf).toLp f,
    (SimpleFunc.memLp_of_finite_measure_preimage p₁ hf).toLp f),
    mem_lebesgue_inter_iff.2 ((SimpleFunc.memLp_of_finite_measure_preimage p₀ hf).coeFn_toLp.trans
      (SimpleFunc.memLp_of_finite_measure_preimage p₁ hf).coeFn_toLp.symm)⟩

private theorem coeFn_interFst_simpleInter (f : SimpleFunc α E)
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    ⇑((lebesgue ℂ E μ p₀ p₁).interFst (simpleInter p₀ p₁ f hf)) =ᵐ[μ] f := by
  rw [interFst_apply]
  exact (SimpleFunc.memLp_of_finite_measure_preimage p₀ hf).coeFn_toLp

private theorem coeFn_interSnd_simpleInter (f : SimpleFunc α E)
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    ⇑((lebesgue ℂ E μ p₀ p₁).interSnd (simpleInter p₀ p₁ f hf)) =ᵐ[μ] f := by
  rw [interSnd_apply]
  exact (SimpleFunc.memLp_of_finite_measure_preimage p₁ hf).coeFn_toLp

/-- A combination of the pieces of `f` in `L^q`, with coefficients depending on the value, is
the class of the weighted function `x ↦ a (f x) • f x`. -/
private theorem coeFn_sum_smul_piece {q : ℝ≥0∞} (f : SimpleFunc α E) (a : E → ℂ)
    (u : E → Lp E q μ) (hu : ∀ c, ⇑(u c) =ᵐ[μ] piece f c) :
    ⇑(∑ c ∈ f.range, a c • u c) =ᵐ[μ] fun x => a (f x) • f x := by
  have h : ∀ᵐ x ∂μ, ∀ c ∈ f.range, (a c • u c) x = a c • piece f c x :=
    (eventually_all_finset f.range).2 fun c _ => by
      filter_upwards [Lp.coeFn_smul (a c) (u c), hu c] with x h₁ h₂
      rw [h₁, Pi.smul_apply, h₂]
  filter_upwards [Lp.coeFn_finsetSum f.range (fun c => a c • u c), h] with x hx hx'
  rw [hx, Finset.sum_apply, ← sum_smul_piece_apply f a x]
  exact Finset.sum_congr rfl hx'

/-- The pieces of `f` sum to `f` in `L^{p₀}`. -/
private theorem sum_interFst_simpleInter_piece (f : SimpleFunc α E)
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    ∑ c ∈ f.range, (lebesgue ℂ E μ p₀ p₁).interFst
        (simpleInter p₀ p₁ (piece f c) (piece_preimage_lt_top hf c)) =
      (lebesgue ℂ E μ p₀ p₁).interFst (simpleInter p₀ p₁ f hf) := by
  refine Lp.ext ?_
  have h := coeFn_sum_smul_piece f (fun _ => (1 : ℂ)) _ fun c => coeFn_interFst_simpleInter
    (p₀ := p₀) (p₁ := p₁) (piece f c) (piece_preimage_lt_top hf c)
  simp only [one_smul] at h
  exact h.trans (coeFn_interFst_simpleInter f hf).symm

/-! ### The bound on simple functions -/

private theorem expo_self_eq_one (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞) :
    expo p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal θ = 1 := by
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (one_le_of_inv_eq Fact.out Fact.out hθ hp)).ne'
  have hinv : p⁻¹.toReal = (1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal := by
    rw [inv_eq_ofReal_of_inv_eq hp₀ hp₁ hθ hp, ENNReal.toReal_ofReal]
    have : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2
    have : 0 ≤ θ := hθ.1
    positivity
  have h : p.toReal * ((1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal) = 1 := by
    rw [← hinv, ENNReal.toReal_inv, mul_inv_cancel₀ (ENNReal.toReal_pos hp0 hp_top).ne']
  have h' : ((p.toReal * ((1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal) : ℝ) : ℂ) = 1 := by
    rw [h, ofReal_one]
  simpa [expo] using h'

/-- The exponent `1 / q` is reached at the real part `p / q` of the family's exponent. -/
private theorem inv_eq_ofReal_mul_inv {q : ℝ≥0∞} (hq : q ≠ 0) (hp0 : p ≠ 0) (hp_top : p ≠ ∞) :
    q⁻¹ = ENNReal.ofReal (p.toReal * (q⁻¹).toReal) * p⁻¹ := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hp_top,
    ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hq), mul_right_comm,
    ENNReal.mul_inv_cancel hp0 hp_top, one_mul]

/-- On a vertical line where the exponent has real part `re w = p / q`, the member of the
analytic family through `f` with `‖f‖_p ≤ 1` has `L^q` norm at most `exp δ`. -/
private theorem norm_sum_coeff_smul_le {q : ℝ≥0∞} (hθ : θ ∈ Icc 0 1) {δ : ℝ}
    (hδ : 0 ≤ δ) {r a₀ a₁ : ℝ} (f : SimpleFunc α E) (hf1 : eLpNorm f p μ ≤ 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hw : 0 ≤ (expo r a₀ a₁ z).re)
    (hq : q⁻¹ = ENNReal.ofReal (expo r a₀ a₁ z).re * p⁻¹) (u : E → Lp E q μ)
    (hu : ∀ c, ⇑(u c) =ᵐ[μ] piece f c) :
    ‖∑ c ∈ f.range, coeff δ θ r a₀ a₁ ‖c‖ z • u c‖ ≤ Real.exp δ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_sum_smul_piece f _ u hu)]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos δ).le ?_
  have heq : (fun x => coeff δ θ r a₀ a₁ ‖f x‖ z • f x) =
      exp (δ * (z - θ) ^ 2) • ⇑(f.map (powSign (expo r a₀ a₁ z))) := by
    funext x
    simp [coeff_smul]
  rw [heq, eLpNorm_const_smul, ← mul_one (ENNReal.ofReal (Real.exp δ))]
  gcongr
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_exp_mul_sub_sq_le hδ hθ hz)
  · exact (eLpNorm_le_eLpNorm_rpow hw (f.map _).aestronglyMeasurable hq
      (ae_of_all _ fun x => by simpa using norm_powSign_le _ (f x))).trans
      (ENNReal.rpow_le_one hf1 hw)

/-- **The analytic family.** For a simple function `f` with finite-measure fibres and
`‖f‖_p ≤ 1`, the admissible function `exp (δ (z - θ)²) sgn(f) |f| ^ {w z}` shows that the class of
`f` in `[L^{p₀}, L^{p₁}]_θ` has norm at most `exp δ`. -/
private theorem norm_ofInter_simpleInter_le_exp (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (f : SimpleFunc α E) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) (hf1 : eLpNorm f p μ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖ComplexMethodSpace.ofInter θ (simpleInter p₀ p₁ f hf)‖ ≤ Real.exp δ := by
  set C := lebesgue ℂ E μ p₀ p₁
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (one_le_of_inv_eq Fact.out Fact.out hθ hp)).ne'
  have hw := expo_self_eq_one hθ hp hp_top
  set r := p.toReal
  set a₀ := (p₀⁻¹).toReal
  set a₁ := (p₁⁻¹).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  -- The family is the combination of the pieces of `f` with the entire coefficients `coeff`.
  set x := fun c => simpleInter p₀ p₁ (piece f c) (piece_preimage_lt_top hf c)
  have hstrip (c : E) : ∃ g, C.IsStripFunction
      (fun z => coeff δ θ r a₀ a₁ ‖c‖ z • C.fstToSum (C.interFst (x c))) g :=
    C.exists_isStripFunction_smul_inter (differentiable_coeff _ _ _ _ _ _).diffContOnCl
      (fun z hz => norm_coeff_le hδ.le hθ hr ENNReal.toReal_nonneg ENNReal.toReal_nonneg _ hz)
      (by simpa only [ofReal_zero, zero_add] using tendsto_coeff hδ θ r a₀ a₁ ‖c‖ 0)
      (by simpa only [ofReal_one] using tendsto_coeff hδ θ r a₀ a₁ ‖c‖ 1) (x c)
  choose g hg using hstrip
  have hF := IsStripFunction.sum f.range fun c _ => hg c
  refine (ComplexMethodSpace.norm_le_of_toSum_eq hθ hF ?_).trans ?_
  · -- At `θ` every coefficient is `1`, and the pieces of `f` sum to `f`.
    rw [ComplexMethodSpace.toSum_ofInter hθ, Finset.sum_apply, ← sum_interFst_simpleInter_piece,
      map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [coeff, hw, x]
  -- On the boundary lines the family has norm at most `exp δ`.
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (Real.exp_pos δ).le).2 fun t => ?_,
    (ZeroAtInftyContinuousMap.norm_le (Real.exp_pos δ).le).2 fun t => ?_⟩
  · have h := hF.apply_mul_I t
    rw [Finset.sum_apply] at h
    simp only [← map_smul, ← map_sum] at h
    rw [← C.fstToSum_injective h, map_sum]
    simp only [map_smul]
    refine norm_sum_coeff_smul_le (z := t * I) hθ hδ.le f hf1 (by simp)
      (by rw [re_expo_mul_I]; exact mul_nonneg hr ENNReal.toReal_nonneg)
      (by rw [re_expo_mul_I]; exact inv_eq_ofReal_mul_inv hp₀ hp0 hp_top)
      (fun c => C.interFst (x c)) fun c => coeFn_interFst_simpleInter _ _
  · have h := hF.apply_one_add_mul_I t
    rw [Finset.sum_apply] at h
    simp only [fstToSum_interFst, ← map_smul, ← map_sum] at h
    rw [← C.sndToSum_injective h, map_sum]
    simp only [map_smul]
    refine norm_sum_coeff_smul_le (z := 1 + t * I) hθ hδ.le f hf1 (by simp)
      (by rw [re_expo_one_add_mul_I]; exact mul_nonneg hr ENNReal.toReal_nonneg)
      (by rw [re_expo_one_add_mul_I]; exact inv_eq_ofReal_mul_inv hp₁ hp0 hp_top)
      (fun c => C.interSnd (x c)) fun c => coeFn_interSnd_simpleInter _ _

/-- For a simple function `f` with finite-measure fibres and `‖f‖_p ≤ 1`, the class of `f` in
`[L^{p₀}, L^{p₁}]_θ` has norm at most `1`. -/
private theorem norm_ofInter_simpleInter_le_one (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (f : SimpleFunc α E) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) (hf1 : eLpNorm f p μ ≤ 1) :
    ‖ComplexMethodSpace.ofInter θ (simpleInter p₀ p₁ f hf)‖ ≤ 1 := by
  have hlim : Tendsto Real.exp (𝓝[>] 0) (𝓝 1) := by
    simpa using (Real.continuous_exp.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ =>
    norm_ofInter_simpleInter_le_exp hθ hp hp_top f hf hf1 hδ)

/-! ### Density of simple functions -/

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module

variable [Fact (1 ≤ p)]

variable (p₀ p₁) in
/-- A simple function of `Lᵖ`, `p < ∞`, as an element of `L^{p₀} ∩ L^{p₁}`. -/
private noncomputable def ofSimpleFunc (hp_top : p ≠ ∞) (g : Lp.simpleFunc E p μ) :
    (lebesgue ℂ E μ p₀ p₁).inter :=
  simpleInter p₀ p₁ (Lp.simpleFunc.toSimpleFunc g) fun y hy =>
    SimpleFunc.measure_preimage_lt_top_of_memLp (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      hp_top _ (Lp.simpleFunc.memLp g) y hy

private theorem coeFn_interFst_ofSimpleFunc (hp_top : p ≠ ∞) (g : Lp.simpleFunc E p μ) :
    ⇑((lebesgue ℂ E μ p₀ p₁).interFst (ofSimpleFunc p₀ p₁ hp_top g)) =ᵐ[μ] ⇑(g : Lp E p μ) :=
  (coeFn_interFst_simpleInter _ _).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun g)

variable (p₀ p₁) in
/-- The inclusion of the simple functions of `Lᵖ`, `p < ∞`, into `L^{p₀} ∩ L^{p₁}`, a linear
map. -/
private noncomputable def ofSimpleFuncₗ (hp_top : p ≠ ∞) :
    Lp.simpleFunc E p μ →ₗ[ℂ] (lebesgue ℂ E μ p₀ p₁).inter where
  toFun := ofSimpleFunc p₀ p₁ hp_top
  map_add' g h := (lebesgue ℂ E μ p₀ p₁).interFst_injective <| Lp.ext <| by
    rw [map_add]
    filter_upwards [coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top (g + h),
      coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top g,
      coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top h,
      Lp.coeFn_add ((lebesgue ℂ E μ p₀ p₁).interFst (ofSimpleFunc p₀ p₁ hp_top g))
        ((lebesgue ℂ E μ p₀ p₁).interFst (ofSimpleFunc p₀ p₁ hp_top h)),
      Lp.coeFn_add (g : Lp E p μ) h] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, Pi.add_apply, h₂, h₃, AddSubgroup.coe_add, h₅, Pi.add_apply]
  map_smul' c g := (lebesgue ℂ E μ p₀ p₁).interFst_injective <| Lp.ext <| by
    rw [map_smul, RingHom.id_apply]
    filter_upwards [coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top (c • g),
      coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top g,
      Lp.coeFn_smul c ((lebesgue ℂ E μ p₀ p₁).interFst (ofSimpleFunc p₀ p₁ hp_top g)),
      Lp.coeFn_smul c (g : Lp E p μ)] with x h₁ h₂ h₃ h₄
    rw [h₁, h₃, Pi.smul_apply, h₂, Lp.simpleFunc.coe_smul, h₄, Pi.smul_apply]

/-- On the simple functions of `Lᵖ`, `p < ∞`, the class in `[L^{p₀}, L^{p₁}]_θ` has norm at most
the `Lᵖ` norm. -/
private theorem norm_ofInter_ofSimpleFuncₗ_le (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (g : Lp.simpleFunc E p μ) :
    ‖ComplexMethodSpace.ofInter θ (ofSimpleFuncₗ p₀ p₁ hp_top g)‖ ≤ ‖(g : Lp E p μ)‖ := by
  rcases eq_or_ne (g : Lp E p μ) 0 with h0 | h0
  · have : g = 0 := Subtype.ext h0
    simp [this]
  have hpos : 0 < ‖(g : Lp E p μ)‖ := norm_pos_iff.2 h0
  -- Normalize `g` to the unit sphere of `Lᵖ`.
  set c : ℂ := ((‖(g : Lp E p μ)‖⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = ‖(g : Lp E p μ)‖⁻¹ := by
    simp [c]
  have hcg : eLpNorm (Lp.simpleFunc.toSimpleFunc (c • g)) p μ ≤ 1 := by
    rw [eLpNorm_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun _),
      ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def, Lp.simpleFunc.coe_smul,
      norm_smul, hc, inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
  have h : ‖ComplexMethodSpace.ofInter θ (ofSimpleFuncₗ p₀ p₁ hp_top (c • g))‖ ≤ 1 := by
    simp only [ofSimpleFuncₗ, LinearMap.coe_mk, AddHom.coe_mk, ofSimpleFunc]
    exact norm_ofInter_simpleInter_le_one hθ hp hp_top _ _ hcg
  rwa [map_smul, map_smul, norm_smul, hc, inv_mul_le_iff₀ hpos, mul_one] at h

/-- **`Lᵖ` lies in the complex interpolation space of the Lebesgue couple.** Let `0 ≤ θ ≤ 1`
and `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`. Every `f ∈ Lᵖ(μ; E)` is an element of
`[L^{p₀}, L^{p₁}]_θ`, of norm at most `‖f‖_p`: there is `u ∈ [L^{p₀}, L^{p₁}]_θ` whose image in
`L¹ + L^∞` is `f` and with `‖u‖_θ ≤ ‖f‖_p`. -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le [CompleteSpace E] (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ := by
  -- Extend the inclusion of the simple functions by continuity.
  set T₀ := (ComplexMethodSpace.ofInter (C := lebesgue ℂ E μ p₀ p₁) θ).toLinearMap ∘ₗ
    ofSimpleFuncₗ p₀ p₁ hp_top
  let e : Lp.simpleFunc E p μ →ₗ[ℂ] Lp E p μ :=
    { toFun g := g
      map_add' := AddSubgroup.coe_add _
      map_smul' := Lp.simpleFunc.coe_smul }
  have hdense : DenseRange e := Lp.simpleFunc.denseRange hp_top
  have hbound (g : Lp.simpleFunc E p μ) : ‖T₀ g‖ ≤ 1 * ‖e g‖ := by
    simpa [T₀, e] using norm_ofInter_ofSimpleFuncₗ_le hθ hp hp_top g
  refine ⟨T₀.extendOfNorm e f, ?_, by
    simpa using LinearMap.norm_extendOfNorm_apply_le hdense 1 hbound f⟩
  refine hdense.induction_on (p := fun f => (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed
      (ComplexMethodSpace.toSum (T₀.extendOfNorm e f)) = L1AddLinfty.ofLp f) f
    (isClosed_eq (by fun_prop) (by fun_prop)) fun g => ?_
  rw [LinearMap.extendOfNorm_eq hdense ⟨1, hbound⟩ g]
  simp only [T₀, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    ComplexMethodSpace.toSum_ofInter hθ, sumSpaceEmbed_fstToSum, lebesgue_embed₀]
  exact L1AddLinfty.ofLp_eq_ofLp_iff.2 (coeFn_interFst_ofSimpleFunc hp_top g)

/-- **`Lᵖ` lies in the complex interpolation space of the Lebesgue couple**, for `0 < θ < 1`.
Let `1 / p = (1 - θ) / p₀ + θ / p₁`. Every `f ∈ Lᵖ(μ; E)` is an element of
`[L^{p₀}, L^{p₁}]_θ`, of norm at most `‖f‖_p`. For `p < ∞` this is
`TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le`; the only infinite `p`
is `p₀ = p₁ = ∞`, where `f` lies in the intersection. -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le_of_mem_Ioo [CompleteSpace E]
    (hθ : θ ∈ Ioo 0 1) (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (f : Lp E p μ) :
    ∃ u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) = L1AddLinfty.ofLp f ∧
        ‖u‖ ≤ ‖f‖ := by
  by_cases hp_top : p = ∞
  · obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 hp_top
    subst hp_top
    refine ⟨ComplexMethodSpace.ofInter θ ⟨(f, f), mem_lebesgue_inter_iff.2 .rfl⟩, ?_,
      (ComplexMethodSpace.norm_ofInter_le (Ioo_subset_Icc_self hθ) _).trans (by simp)⟩
    simp [ComplexMethodSpace.toSum_ofInter (Ioo_subset_Icc_self hθ)]
  · exact exists_sumSpaceEmbed_toSum_eq_ofLp_and_norm_le (Ioo_subset_Icc_self hθ) hp hp_top f

end TauCeti.CompatibleCouple
