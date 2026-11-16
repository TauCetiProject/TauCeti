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
import TauCeti.MeasureTheory.Function.LpSeminorm.PowSign
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

`F z = exp (δ (z - θ)²) sgn(f) |f| ^ {w z}`, where `w z = p ((1 - z) / p₀ + z / p₁)`
(`TauCeti.thorinExponent`),

is admissible for the complex method: it is a finite combination of the fibre indicators of `f`,
which lie in `L^{p₀} ∩ L^{p₁}`, with entire scalar coefficients that decay along the boundary
lines of the strip (`TauCeti.CompatibleCouple.isStripFunction_smul_inter`). Since `w θ = 1`
it takes the value `f` at `θ`. On the line `re z = j` the modulus `|f| ^ {re w z} = |f| ^ {p / pⱼ}`
has `L^{pⱼ}` norm at most `‖f‖_p ^ {p / pⱼ} ≤ 1`
(`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_le_one`), so `‖f‖_θ ≤ exp δ` for every
`δ > 0`. Simple functions are dense in `Lᵖ` for `p < ∞`, and the bound passes to all of `Lᵖ` by
continuity (`LinearMap.extendOfNorm`).

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

open Complex.HadamardThreeLines

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {mα : MeasurableSpace α}
  {μ : Measure α} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-! ### The analytic family through a simple function -/

/-- The scalar coefficient `exp (δ (z - θ)²) s ^ (w z - 1)` of the fibre `f ⁻¹' {c}` in the
analytic family, where `s = ‖c‖` and `w = thorinExponent a₀ a₁ θ`. -/
private noncomputable def coeff (δ θ a₀ a₁ s : ℝ) (z : ℂ) : ℂ :=
  gaussian δ θ z * exp ((thorinExponent a₀ a₁ θ z - 1) * Real.log s)

private theorem coeff_smul (δ θ a₀ a₁ : ℝ) (c : E) (z : ℂ) :
    coeff δ θ a₀ a₁ ‖c‖ z • c = gaussian δ θ z • powSign (thorinExponent a₀ a₁ θ z) c := by
  rw [coeff, mul_smul, powSign_def]

private theorem differentiable_coeff (δ θ a₀ a₁ s : ℝ) :
    Differentiable ℂ (coeff δ θ a₀ a₁ s) :=
  (differentiable_gaussian δ θ).mul (by simp only [thorinExponent_def]; fun_prop)

/-- The coefficients tend to zero along the vertical line `re z = a`. -/
private theorem tendsto_coeff {δ : ℝ} (hδ : 0 < δ) (θ a₀ a₁ s a : ℝ) :
    Tendsto (fun t : ℝ => coeff δ θ a₀ a₁ s (a + t * I)) (cocompact ℝ) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => ‖gaussian δ θ (a + t * I)‖ *
      Real.exp ((a - θ) * thorinSlope a₀ a₁ θ * Real.log s)) (cocompact ℝ) (𝓝 0) := by
    simpa using (tendsto_gaussian hδ θ a).norm.mul_const
      (Real.exp ((a - θ) * thorinSlope a₀ a₁ θ * Real.log s))
  refine squeeze_zero_norm (fun t => le_of_eq ?_) h
  rw [coeff, norm_mul, norm_exp]
  congr 1
  simp [thorinExponent_def]

/-- The coefficients are bounded on the closed strip. -/
private theorem norm_coeff_le {δ : ℝ} (hδ : 0 ≤ δ) (hθ : θ ∈ Icc 0 1) (a₀ a₁ s : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖coeff δ θ a₀ a₁ s z‖ ≤ Real.exp δ * Real.exp (|thorinSlope a₀ a₁ θ| * |Real.log s|) := by
  rw [coeff, norm_mul, norm_exp]
  refine mul_le_mul (norm_gaussian_le_exp hδ hθ hz) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    (Real.exp_pos _).le
  have hre : ((thorinExponent a₀ a₁ θ z - 1) * (Real.log s : ℂ)).re =
      ((thorinExponent a₀ a₁ θ z).re - 1) * Real.log s := by
    simp
  rw [hre]
  calc ((thorinExponent a₀ a₁ θ z).re - 1) * Real.log s
      ≤ |((thorinExponent a₀ a₁ θ z).re - 1) * Real.log s| := le_abs_self _
    _ = |(thorinExponent a₀ a₁ θ z).re - 1| * |Real.log s| := abs_mul _ _
    _ ≤ |thorinSlope a₀ a₁ θ| * |Real.log s| :=
        mul_le_mul_of_nonneg_right (abs_re_thorinExponent_le a₀ a₁ hθ hz) (abs_nonneg _)

/-! ### Simple functions in the intersection -/

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
    (u : E → Lp E q μ) (hu : ∀ c, ⇑(u c) =ᵐ[μ] (SimpleFunc.const α c).restrict (f ⁻¹' {c})) :
    ⇑(∑ c ∈ f.range, a c • u c) =ᵐ[μ] fun x => a (f x) • f x := by
  have h : ∀ᵐ x ∂μ, ∀ c ∈ f.range,
      (a c • u c) x = a c • (SimpleFunc.const α c).restrict (f ⁻¹' {c}) x :=
    (eventually_all_finset f.range).2 fun c _ => by
      filter_upwards [Lp.coeFn_smul (a c) (u c), hu c] with x h₁ h₂
      rw [h₁, Pi.smul_apply, h₂]
  filter_upwards [Lp.coeFn_finsetSum f.range (fun c => a c • u c), h] with x hx hx'
  rw [hx, Finset.sum_apply, ← SimpleFunc.sum_smul_restrict_const_apply f a x]
  exact Finset.sum_congr rfl hx'

/-- The pieces of `f` sum to `f` in `L^{p₀}`. -/
private theorem sum_interFst_simpleInter_piece (f : SimpleFunc α E)
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    ∑ c ∈ f.range, (lebesgue ℂ E μ p₀ p₁).interFst
        (simpleInter p₀ p₁ ((SimpleFunc.const α c).restrict (f ⁻¹' {c}))
          (f.measure_preimage_restrict_const_lt_top c hf)) =
      (lebesgue ℂ E μ p₀ p₁).interFst (simpleInter p₀ p₁ f hf) := by
  refine Lp.ext ?_
  have h := coeFn_sum_smul_piece f (fun _ => (1 : ℂ)) _ fun c => coeFn_interFst_simpleInter
    (p₀ := p₀) (p₁ := p₁) _ (f.measure_preimage_restrict_const_lt_top c hf)
  simp only [one_smul] at h
  exact h.trans (coeFn_interFst_simpleInter f hf).symm

/-! ### The bound on simple functions -/

/-- On a vertical line of the closed strip where `1 / q = (1 - re z) / p₀ + re z / p₁`, the member
of the analytic family through `f` with `‖f‖_p ≤ 1` has `L^q` norm at most `exp δ`. -/
private theorem norm_sum_coeff_smul_le {q : ℝ≥0∞} (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    {δ : ℝ} (hδ : 0 ≤ δ) (f : SimpleFunc α E) (hf1 : eLpNorm f p μ ≤ 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - z.re) * p₀⁻¹ + ENNReal.ofReal z.re * p₁⁻¹) (u : E → Lp E q μ)
    (hu : ∀ c, ⇑(u c) =ᵐ[μ] (SimpleFunc.const α c).restrict (f ⁻¹' {c})) :
    ‖∑ c ∈ f.range, coeff δ θ (p₀⁻¹).toReal (p₁⁻¹).toReal ‖c‖ z • u c‖ ≤ Real.exp δ := by
  have hw := re_thorinExponent_nonneg (z := z) (ENNReal.toReal_nonneg (a := p₀⁻¹))
    (ENNReal.toReal_nonneg (a := p₁⁻¹)) hθ hz
  have hq' : q⁻¹ = ENNReal.ofReal (thorinExponent (p₀⁻¹).toReal (p₁⁻¹).toReal θ z).re * p⁻¹ := by
    rw [ofReal_re_thorinExponent_mul_inv (zero_lt_one.trans_le Fact.out).ne'
      (zero_lt_one.trans_le Fact.out).ne' hθ hp (fun h => absurd h hp_top) hz, hq]
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_sum_smul_piece f _ u hu)]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos δ).le ?_
  have heq : (fun x => coeff δ θ (p₀⁻¹).toReal (p₁⁻¹).toReal ‖f x‖ z • f x) =
      gaussian δ θ z • ⇑(f.map (powSign (thorinExponent (p₀⁻¹).toReal (p₁⁻¹).toReal θ z))) := by
    funext x
    simp [coeff_smul]
  rw [heq, eLpNorm_const_smul, ← mul_one (ENNReal.ofReal (Real.exp δ))]
  gcongr
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_gaussian_le_exp hδ hθ hz)
  · exact f.eLpNorm_map_powSign_le_one hw hq' hf1

/-- **The analytic family.** For a simple function `f` with finite-measure fibres and
`‖f‖_p ≤ 1`, the admissible function `exp (δ (z - θ)²) sgn(f) |f| ^ {w z}` shows that the class of
`f` in `[L^{p₀}, L^{p₁}]_θ` has norm at most `exp δ`. -/
private theorem norm_ofInter_simpleInter_le_exp (hθ : θ ∈ Icc 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (f : SimpleFunc α E) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) (hf1 : eLpNorm f p μ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖ComplexMethodSpace.ofInter θ (simpleInter p₀ p₁ f hf)‖ ≤ Real.exp δ := by
  set C := lebesgue ℂ E μ p₀ p₁
  set a₀ := (p₀⁻¹).toReal
  set a₁ := (p₁⁻¹).toReal
  -- The family is the combination of the pieces of `f` with the entire coefficients `coeff`.
  set x := fun c => simpleInter p₀ p₁ ((SimpleFunc.const α c).restrict (f ⁻¹' {c}))
    (f.measure_preimage_restrict_const_lt_top c hf)
  have hF := IsStripFunction.sum f.range fun c _ =>
    C.isStripFunction_smul_inter (differentiable_coeff δ θ a₀ a₁ ‖c‖).diffContOnCl
      (fun z hz => norm_coeff_le hδ.le hθ a₀ a₁ _ hz)
      (by simpa only [ofReal_zero, zero_add] using tendsto_coeff hδ θ a₀ a₁ ‖c‖ 0)
      (by simpa only [ofReal_one] using tendsto_coeff hδ θ a₀ a₁ ‖c‖ 1) (x c)
  refine (ComplexMethodSpace.norm_le_of_toSum_eq hθ hF ?_).trans ?_
  · -- At `θ` every coefficient is `1`, and the pieces of `f` sum to `f`.
    rw [ComplexMethodSpace.toSum_ofInter hθ, Finset.sum_apply, ← sum_interFst_simpleInter_piece,
      map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [coeff, x]
  -- On the boundary lines the family has norm at most `exp δ`.
  refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le (Real.exp_pos δ).le).2 fun t => ?_,
    (ZeroAtInftyContinuousMap.norm_le (Real.exp_pos δ).le).2 fun t => ?_⟩
  · rw [Prod.fst_sum, FunLike.coe_sum, Finset.sum_apply]
    simp only [smulInterTrace_fst_apply]
    exact norm_sum_coeff_smul_le hθ hp hp_top hδ.le f hf1 (by simp) (by simp) _
      fun c => coeFn_interFst_simpleInter _ _
  · rw [Prod.snd_sum, FunLike.coe_sum, Finset.sum_apply]
    simp only [smulInterTrace_snd_apply]
    exact norm_sum_coeff_smul_le hθ hp hp_top hδ.le f hf1 (by simp) (by simp) _
      fun c => coeFn_interSnd_simpleInter _ _

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
    rw [h₁, h₄, Pi.add_apply, h₂, h₃]
    exact h₅
  map_smul' c g := (lebesgue ℂ E μ p₀ p₁).interFst_injective <| Lp.ext <| by
    rw [map_smul, RingHom.id_apply]
    filter_upwards [coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top (c • g),
      coeFn_interFst_ofSimpleFunc (p₀ := p₀) (p₁ := p₁) hp_top g,
      Lp.coeFn_smul c ((lebesgue ℂ E μ p₀ p₁).interFst (ofSimpleFunc p₀ p₁ hp_top g)),
      Lp.coeFn_smul c (g : Lp E p μ)] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄, Pi.smul_apply, Lp.simpleFunc.coe_smul]

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
  have hnorm : ‖c • (g : Lp E p μ)‖ = 1 := by
    simp [norm_smul, hc, hpos.ne']
  have hcg : eLpNorm (Lp.simpleFunc.toSimpleFunc (c • g)) p μ ≤ 1 := by
    simp [eLpNorm_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun _), ← Lp.eNorm_def,
      ← ofReal_norm, hnorm]
  have h : ‖ComplexMethodSpace.ofInter θ (ofSimpleFuncₗ p₀ p₁ hp_top (c • g))‖ ≤ 1 := by
    simp only [ofSimpleFuncₗ, LinearMap.coe_mk, AddHom.coe_mk, ofSimpleFunc]
    exact norm_ofInter_simpleInter_le_one hθ hp hp_top _ _ hcg
  simpa [norm_smul, hc, inv_mul_le_iff₀ hpos] using h

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
  let e : Lp.simpleFunc E p μ →ₗ[ℂ] Lp E p μ := (Lp.simpleFunc.coeToLp α E ℂ).toLinearMap
  have hdense : DenseRange e := Lp.simpleFunc.denseRange hp_top
  have hbound (g : Lp.simpleFunc E p μ) : ‖T₀ g‖ ≤ 1 * ‖e g‖ := by
    rw [one_mul]
    exact norm_ofInter_ofSimpleFuncₗ_le hθ hp hp_top g
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
