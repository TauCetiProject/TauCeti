/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.L1Linfty
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.Lorentz
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.Hardy

/-!
# Real interpolation of `(L¹, L^∞)` and Lorentz spaces

For the couple `(L¹(μ; E), L^∞(μ; E))`, Peetre's `K`-functional of a function `f ∈ L¹ + L^∞` is
`K(t, f) = ∫₀ᵗ ‖f‖*` (`TauCeti.CompatibleCouple.ofReal_kFunctional_lebesgue_one_top`). Combining
this identity with the monotonicity of `‖f‖*` and the weighted Hardy inequality on `dt / t`
(`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`) yields the two-sided equivalence of
the `K`-method norm with the Lorentz gauge `TauCeti.eLorentzNorm`: for `θ > 0`, `1 ≤ q ≤ ∞`, and
`1 / p = 1 - θ`,

`‖f‖_{p,q} ≤ ‖f‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}`

(`TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_lebesgue_one_top`,
`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_eLorentzNorm`), with the lower bound
holding unconditionally for all `θ : ℝ` and `q ∈ [0, ∞]`. This is the real interpolation theorem
for `(L¹, L^∞)` (Bergh–Löfström, Theorem 5.2.1): for `0 < θ < 1`, `1 ≤ q ≤ ∞`, and `1 / p = 1 - θ`,

`(L¹(μ; E), L^∞(μ; E))_{θ,q} = L^{p,q}(μ; E)`

with equivalent norms (`TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff`,
`TauCeti.CompatibleCouple.exists_mem_kMethod_lebesgue_one_top_ae_eq_iff`).

On the diagonal `q = p`, the identity `‖f‖_{p,p} = ‖f‖_p` (`TauCeti.eLorentzNorm_self`) gives a
topological isomorphism

`(L¹(μ; E), L^∞(μ; E))_{θ,p} ≃L[𝕜] Lᵖ(μ; E)`

(`TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`), with forward norm at most `1` and inverse
norm at most `θ⁻¹` (valid for all `θ > 0` and `1 ≤ p ≤ ∞` with `1 / p = 1 - θ`, including the
endpoint `θ = 1, p = ∞`).

As exact evaluations, an indicator `c 1_A` has `K`-method norm `c_{θ,q} ‖c‖ (μ A) ^ (1 - θ)` for
every `θ < 1` (`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_indicator`), and on `(0, ∞)`
with Lebesgue measure the power function `t ↦ t ^ (-(1 - θ))` represents an element of
`(L¹, L^∞)_{θ,∞}` with `K`-method norm equal to `θ⁻¹` (showing sharpness of the upper-bound
constant `θ⁻¹`) that does not lie in `(L¹, L^∞)_{θ,q}` for any finite `q ≠ 0`
(`TauCeti.CompatibleCouple.exists_mem_kMethod_top_not_mem_kMethod_rpow`).

## Main declarations

* `TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_l1Linfty`,
  `TauCeti.CompatibleCouple.eLorentzNorm_le_kMethodENorm_lebesgue_one_top`: the lower bound
  `‖f‖_{p,q} ≤ ‖f‖_{θ,q}`.
* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_le_eLorentzNorm`,
  `TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_eLorentzNorm`: the upper bound
  `‖f‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}`.
* `TauCeti.CompatibleCouple.mem_kMethod_l1Linfty_iff`,
  `TauCeti.CompatibleCouple.mem_kMethod_lebesgue_one_top_iff`,
  `TauCeti.CompatibleCouple.exists_mem_kMethod_lebesgue_one_top_ae_eq_iff`: membership in
  `(L¹, L^∞)_{θ,q}` is finiteness of the Lorentz gauge `‖f‖_{p,q}`.
* `TauCeti.CompatibleCouple.kMethodENorm_l1Linfty_indicator`,
  `TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_indicator`: exact `K`-method norm of an
  indicator `c 1_A`.
* `TauCeti.CompatibleCouple.lebesgueOneTopKMethodEquivLp`: the continuous linear equivalence
  `(L¹, L^∞)_{θ,p} ≃L[𝕜] Lᵖ(μ; E)` for `θ > 0`, `1 ≤ p ≤ ∞`, and `1 / p = 1 - θ`.
* `TauCeti.CompatibleCouple.exists_mem_kMethod_top_not_mem_kMethod_rpow`: the weak-`Lᵖ` power
  function witness in `(L¹, L^∞)_{θ,∞}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.2 (Theorem 5.2.1).
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Comparing `l1Linfty` and `lebesgue 1 ∞` -/

/-- The Lebesgue couple `(L¹, L^∞)` and `l1Linfty` have the same `K`-method norm, read through the
embedding of the sum space of the former into `L¹ + L^∞`. -/
theorem kMethodENorm_l1Linfty_sumSpaceEmbed (θ : ℝ) (q : ℝ≥0∞)
    (v : (lebesgue 𝕜 E μ 1 ∞).SumSpace) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v) =
      (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [kMethodENorm_def, kMethodENorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [kFunctional_l1Linfty_sumSpaceEmbed ht.le]

theorem mem_kMethod_l1Linfty_sumSpaceEmbed_iff {θ : ℝ} {q : ℝ≥0∞}
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} :
    (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔
      v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q := by
  simp only [mem_kMethod_iff, kMethodENorm_l1Linfty_sumSpaceEmbed]

/-! ### Two-sided equivalence with Lorentz gauges -/

/-- Pointwise lower bound `t ‖f‖*(t) ≤ K(t, u)` for `t ≥ 0`, proved directly from the definition
of `K(t, u)` without requiring real scalar multiplication on `E`. -/
private theorem mul_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty
    {u : L1AddLinfty 𝕜 E μ} {f : α → E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f)
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) := by
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hu
  -- Step 1: antitonicity of `‖f‖*` bounds `t ‖f‖*(t)` by `∫₀ᵗ ‖f‖*`
  have hle_int : ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    calc ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t
        = ∫⁻ _ in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
      _ ≤ ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s :=
          setLIntegral_mono' measurableSet_Ioc fun s hs ↦
            μ.antitone_decreasingRearrangement _ hs.2
  -- Step 2: bound `∫₀ᵗ ‖f‖*` by `‖g‖₁ + t ‖h‖_∞` over near-optimal decompositions `u = g + h`
  refine hle_int.trans (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
  obtain ⟨g, h, hgh, hlt⟩ := (kFunctional_lt_iff ht).1
    (lt_add_of_pos_right ((l1Linfty 𝕜 E μ).kFunctional t u) (NNReal.coe_pos.2 hε))
  have hgh' : ⇑g + ⇑h =ᵐ[μ] f := (L1AddLinfty.fstToSum_add_sndToSum_eq_iff.1 hgh).trans hu
  have hg_norm : ∫⁻ y, ‖g y‖ₑ ∂μ = ENNReal.ofReal ‖g‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g),
      eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable g)]
  have hh_norm : essSup (‖h ·‖ₑ) μ = ENNReal.ofReal ‖h‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top h),
      eLpNorm_exponent_top (Lp.aestronglyMeasurable h), eLpNormEssSup_eq_essSup_eNorm]
  calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ y, ‖g y‖ₑ ∂μ + ENNReal.ofReal t * essSup (‖h ·‖ₑ) μ :=
        μ.lintegral_decreasingRearrangement_le_lintegral_add_mul_essSup hf.eNorm t
          (hgh'.mono fun y hy ↦ by
            simp only [Pi.add_apply] at hy ⊢
            rw [← hy]
            exact eNorm_add_le (g y) (h y))
    _ = ENNReal.ofReal (‖g‖ + t * ‖h‖) := by
        rw [hg_norm, hh_norm, ← ENNReal.ofReal_mul ht,
          ← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
    _ ≤ ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u + ε) := ENNReal.ofReal_le_ofReal hlt.le
    _ = ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) + ε := by
        rw [ENNReal.ofReal_add (kFunctional_nonneg ht) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- **Lower bound for `(L¹, L^∞)_{θ,q}`.** For any `θ : ℝ`, `p, q ∈ [0, ∞]` with `1 / p = 1 - θ`,
and `u ∈ L¹ + L^∞` represented by `f`, the Lorentz gauge is bounded by the `K`-method norm:
`‖f‖_{p,q} ≤ ‖u‖_{θ,q}`. -/
theorem eLorentzNorm_le_kMethodENorm_l1Linfty {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p q : ℝ≥0∞}
    (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ (l1Linfty 𝕜 E μ).kMethodENorm θ q u := by
  rw [eLorentzNorm_def, kMethodENorm_def]
  have hm : Measurable fun t : ℝ ↦
      ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by fun_prop
  refine eLpNorm_mono_eNorm_ae hm.aestronglyMeasurable ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simp only [eNorm_eq_self]
  have hk0 : 0 ≤ (l1Linfty 𝕜 E μ).kFunctional t u := kFunctional_nonneg ht.le
  rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) hk0),
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  calc ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal (t ^ (-θ)) *
          (ENNReal.ofReal t * μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), hp,
          ← Real.rpow_add_one ht.ne', neg_add_eq_sub]
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal ((l1Linfty 𝕜 E μ).kFunctional t u) :=
        mul_le_mul_of_nonneg_left
          (mul_decreasingRearrangement_le_ofReal_kFunctional_l1Linfty hu ht.le) zero_le

/-- **Lower bound for the Lebesgue couple `(L¹, L^∞)_{θ,q}`.** For any `θ : ℝ`, `p, q ∈ [0, ∞]`
with `1 / p = 1 - θ`, and `v` in the sum space of `(L¹, L^∞)` represented by `f`,
`‖f‖_{p,q} ≤ ‖v‖_{θ,q}`. -/
theorem eLorentzNorm_le_kMethodENorm_lebesgue_one_top {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p q : ℝ≥0∞} (hp : p.toReal⁻¹ = 1 - θ) :
    eLorentzNorm f p q μ ≤ (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact eLorentzNorm_le_kMethodENorm_l1Linfty hv hp

/-- **Upper bound for `(L¹, L^∞)_{θ,q}`.** For `θ > 0`, `1 ≤ q ≤ ∞`, `1 / p = 1 - θ`, and
`u ∈ L¹ + L^∞` represented by `f`, Hardy's inequality on `dt / t` gives
`‖u‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}`. The constant `θ⁻¹` is sharp (attained on `t ↦ t ^ (-(1 - θ))` at
`q = ∞`). -/
theorem kMethodENorm_l1Linfty_le_eLorentzNorm [NormedSpace ℝ E] {u : L1AddLinfty 𝕜 E μ}
    {f : α → E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p q : ℝ≥0∞}
    (hθ : 0 < θ) (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  have heq : (fun t : ℝ ↦ ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) *
        ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ofReal_kFunctional_l1Linfty hu ht.le]
  calc (l1Linfty 𝕜 E μ).kMethodENorm θ q u
      = eLpNorm (fun t : ℝ ↦ ‖t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u‖ₑ) q multHaar := by
        rw [kMethodENorm_def, eLpNorm_eNorm _ (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u)]
    _ = eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) *
          ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s) q multHaar :=
        eLpNorm_congr_ae heq
    _ ≤ ENNReal.ofReal θ⁻¹ *
          eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar :=
        eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le hθ hq
    _ = ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
        rw [← hp, eLorentzNorm_def]

/-- **Upper bound for the Lebesgue couple `(L¹, L^∞)_{θ,q}`.** For `θ > 0`, `1 ≤ q ≤ ∞`,
`1 / p = 1 - θ`, and `v` in the sum space of `(L¹, L^∞)` represented by `f`,
`‖v‖_{θ,q} ≤ θ⁻¹ ‖f‖_{p,q}`. -/
theorem kMethodENorm_lebesgue_one_top_le_eLorentzNorm [NormedSpace ℝ E]
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p q : ℝ≥0∞} (hθ : 0 < θ) (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v ≤ ENNReal.ofReal θ⁻¹ * eLorentzNorm f p q μ := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_le_eLorentzNorm hv hθ hq hp

/-! ### Membership characterization -/

/-- Membership in `(L¹, L^∞)_{θ,q}` (for `l1Linfty`) is finiteness of the Lorentz gauge `‖f‖_{p,q}`,
for `θ > 0`, `1 ≤ q ≤ ∞`, and `1 / p = 1 - θ`. -/
theorem mem_kMethod_l1Linfty_iff [NormedSpace ℝ E] {u : L1AddLinfty 𝕜 E μ} {f : α → E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] f) {θ : ℝ} {p q : ℝ≥0∞}
    (hθ : 0 < θ) (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) :
    u ∈ (l1Linfty 𝕜 E μ).kMethod θ q ↔ eLorentzNorm f p q μ < ∞ := by
  rw [mem_kMethod_iff]
  exact ⟨fun h ↦ (eLorentzNorm_le_kMethodENorm_l1Linfty hu hp).trans_lt h,
    fun h ↦ (kMethodENorm_l1Linfty_le_eLorentzNorm hu hθ hq hp).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)⟩

/-- Membership in `(L¹, L^∞)_{θ,q}` (for `lebesgue 1 ∞`) is finiteness of the Lorentz gauge
`‖f‖_{p,q}`, for `θ > 0`, `1 ≤ q ≤ ∞`, and `1 / p = 1 - θ`. -/
theorem mem_kMethod_lebesgue_one_top_iff [NormedSpace ℝ E] {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace}
    {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f)
    {θ : ℝ} {p q : ℝ≥0∞} (hθ : 0 < θ) (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) :
    v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q ↔ eLorentzNorm f p q μ < ∞ := by
  rw [← mem_kMethod_l1Linfty_sumSpaceEmbed_iff]
  exact mem_kMethod_l1Linfty_iff hv hθ hq hp

/-- **Real interpolation of `(L¹, L^∞)` — function-level characterization.** For `0 < θ < 1`,
`1 ≤ q ≤ ∞`, and `1 / p = 1 - θ`, a function `f : α → E` represents an element of
`(L¹(μ; E), L^∞(μ; E))_{θ,q}` exactly when `f` is almost everywhere strongly measurable and has
finite Lorentz gauge `‖f‖_{p,q} < ∞`. -/
theorem exists_mem_kMethod_lebesgue_one_top_ae_eq_iff [NormedSpace ℝ E] {f : α → E}
    {θ : ℝ} {p q : ℝ≥0∞} (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q) (hp : p.toReal⁻¹ = 1 - θ) :
    (∃ v ∈ (lebesgue 𝕜 E μ 1 ∞).kMethod θ q,
        ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ] f) ↔
      AEStronglyMeasurable f μ ∧ eLorentzNorm f p q μ < ∞ := by
  constructor
  · rintro ⟨v, hv, hvf⟩
    exact ⟨(AEEqFun.aestronglyMeasurable _).congr hvf,
      (mem_kMethod_lebesgue_one_top_iff hvf hθ.1 hq hp).1 hv⟩
  · rintro ⟨hf, hfin⟩
    have hptop : p ≠ ∞ := fun h ↦ by simp [h] at hp; linarith [hθ.2]
    have hpr : 1 < p.toReal := by
      rw [← inv_inv p.toReal]
      exact one_lt_inv_iff₀.2 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hp₁ : 1 < p := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_toReal hptop]
      exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hpr)).2 hpr
    have hint : ∫⁻ s in Ioc 0 (1 : ℝ), μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ :=
      lintegral_decreasingRearrangement_lt_top_of_eLorentzNorm_lt_top hp₁ hptop
        (zero_lt_one.trans_le hq).ne' 1 hfin
    obtain ⟨u, hu⟩ :=
      (L1AddLinfty.exists_toAEEqFun_ae_eq_iff_lintegral_decreasingRearrangement_lt_top
        (𝕜 := 𝕜) one_pos).2 ⟨hf, hint⟩
    obtain ⟨v, rfl⟩ := lebesgue_one_top_sumSpaceEmbed_surjective (𝕜 := 𝕜) (E := E) (μ := μ) u
    exact ⟨v, (mem_kMethod_lebesgue_one_top_iff hu hθ.1 hq hp).2 hfin, hu⟩

/-! ### Exact `K`-method norm on indicators -/

/-- Exact `K`-method norm of an indicator on a set of positive finite measure, via dilation of
`multHaar`. -/
private theorem kMethodENorm_l1Linfty_indicator_of_pos_ne_top [NormedSpace ℝ E]
    {u : L1AddLinfty 𝕜 E μ} {A : Set α} {c : E}
    (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ∞) (θ : ℝ) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  set a : ℝ := (μ A).toReal
  have ha : 0 < a := ENNReal.toReal_pos hA0 hAtop
  have hmp : MeasurePreserving (a⁻¹ * ·) multHaar multHaar :=
    ⟨measurable_const_mul _, map_multHaar_mul_left (inv_pos.2 ha)⟩
  -- Pull the scaling `a = μ A` out of `t ^ (-θ) * K(t, u)` to match `s ↦ s ^ (-θ) min 1 s`
  have hfn : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar]
      (‖c‖ * a ^ (1 - θ)) • ((fun s : ℝ ↦ s ^ (-θ) * min 1 s) ∘ (a⁻¹ * ·)) := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hk : (l1Linfty 𝕜 E μ).kFunctional t u = ‖c‖ * min t a := by
      have h := ofReal_kFunctional_l1Linfty_indicator hu ht.le
      rw [← ENNReal.ofReal_toReal hAtop, ← ENNReal.ofReal_min, ← ofReal_norm,
        ← ENNReal.ofReal_mul (norm_nonneg c)] at h
      exact (ENNReal.ofReal_eq_ofReal_iff (kFunctional_nonneg ht.le)
        (mul_nonneg (norm_nonneg c) (le_min ht.le ha.le))).1 h
    rw [hk, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    have hmin : min t a = a * min 1 (a⁻¹ * t) := by
      rw [mul_min_of_nonneg _ _ ha.le, mul_one, mul_inv_cancel_left₀ ha.ne', min_comm]
    have hpow : t ^ (-θ) * a = a ^ (1 - θ) * (a⁻¹ * t) ^ (-θ) := by
      rw [Real.mul_rpow (inv_nonneg.2 ha.le) ht.le, Real.inv_rpow ha.le,
        ← Real.rpow_neg ha.le, neg_neg, ← mul_assoc, ← Real.rpow_add ha, sub_add_cancel,
        Real.rpow_one, mul_comm]
    calc t ^ (-θ) * (‖c‖ * min t a)
        = ‖c‖ * (t ^ (-θ) * a) * min 1 (a⁻¹ * t) := by rw [hmin]; ring
      _ = ‖c‖ * a ^ (1 - θ) * ((a⁻¹ * t) ^ (-θ) * min 1 (a⁻¹ * t)) := by rw [hpow]; ring
  have hphi : AEStronglyMeasurable (fun s : ℝ ↦ s ^ (-θ) * min 1 s) multHaar :=
    ((ContinuousOn.rpow_const continuousOn_id fun _ hs ↦ Or.inl (ne_of_gt hs)).mul
      (continuous_const.min continuous_id).continuousOn).aestronglyMeasurable_multHaar
  calc (l1Linfty 𝕜 E μ).kMethodENorm θ q u
      = ‖‖c‖ * a ^ (1 - θ)‖ₑ * kMethodConst θ q := by
        rw [kMethodENorm_def, eLpNorm_congr_ae hfn, eLpNorm_const_smul,
          eLpNorm_comp_measurePreserving hphi hmp, ← kMethodConst_def]
    _ = (‖c‖ₑ * μ A ^ (1 - θ)) * kMethodConst θ q := by
        rw [Real.eNorm_of_nonneg (mul_nonneg (norm_nonneg c) (Real.rpow_nonneg ha.le _)),
          ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, ← ENNReal.ofReal_rpow_of_pos ha,
          ENNReal.ofReal_toReal hAtop]
    _ = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by ring

/-- **Exact `K`-method norm of an indicator.** For `θ < 1`, any `q ∈ [0, ∞]`, and an element
`u ∈ L¹ + L^∞` represented by `c 1_A`, `‖u‖_{θ,q} = c_{θ,q} ‖c‖ (μ A) ^ (1 - θ)`. -/
theorem kMethodENorm_l1Linfty_indicator [NormedSpace ℝ E] {u : L1AddLinfty 𝕜 E μ} {A : Set α}
    {c : E} (hu : ⇑(L1AddLinfty.toAEEqFun 𝕜 u) =ᵐ[μ] A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) (q : ℝ≥0∞) :
    (l1Linfty 𝕜 E μ).kMethodENorm θ q u = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ
  have hzero_of (h : ∀ t > (0 : ℝ), ‖c‖ₑ * min (ENNReal.ofReal t) (μ A) = 0) :
      (l1Linfty 𝕜 E μ).kMethodENorm θ q u = 0 := by
    have hzero : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar] 0 := by
      filter_upwards [ae_pos_multHaar] with t ht
      have hk : (l1Linfty 𝕜 E μ).kFunctional t u = 0 := by
        have h' := ofReal_kFunctional_l1Linfty_indicator hu ht.le
        rw [h t ht, ENNReal.ofReal_eq_zero] at h'
        exact le_antisymm h' (kFunctional_nonneg ht.le)
      simp [hk]
    rw [kMethodENorm_def, eLpNorm_congr_ae hzero, eLpNorm_zero]
  -- Degenerate cases: `q = 0`, `c = 0`, or `μ A = 0`
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [kMethodENorm_def, eLpNorm_exponent_zero (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u),
      kMethodConst_def, eLpNorm_exponent_zero (by fun_prop), zero_mul, zero_mul]
  rcases eq_or_ne ‖c‖ₑ 0 with hc0 | hc0
  · rw [hzero_of (fun _ _ ↦ by simp [hc0]), hc0, mul_zero, zero_mul]
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · rw [hzero_of (fun _ _ ↦ by simp [hA0]), hA0, ENNReal.zero_rpow_of_pos h1θ, mul_zero]
  -- Infinite measure: `K(t, u) = ‖c‖ t`, so the integrand `‖c‖ t ^ (1 - θ)` has infinite norm
  rcases eq_or_ne (μ A) ∞ with hAtop | hAtop
  · have hfn : (fun t : ℝ ↦ t ^ (-θ) * (l1Linfty 𝕜 E μ).kFunctional t u) =ᵐ[multHaar]
        ‖c‖ • fun t : ℝ ↦ t ^ (1 - θ) := by
      filter_upwards [ae_pos_multHaar] with t ht
      have hk : (l1Linfty 𝕜 E μ).kFunctional t u = ‖c‖ * t := by
        have h := ofReal_kFunctional_l1Linfty_indicator hu ht.le
        rw [hAtop, min_eq_left le_top, ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg c)] at h
        exact (ENNReal.ofReal_eq_ofReal_iff (kFunctional_nonneg ht.le)
          (mul_nonneg (norm_nonneg c) ht.le)).1 h
      rw [hk, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (t ^ (-θ)), mul_assoc,
        ← Real.rpow_add_one ht.ne', neg_add_eq_sub]
    calc (l1Linfty 𝕜 E μ).kMethodENorm θ q u
        = ‖c‖ₑ * eLpNorm (fun t : ℝ ↦ t ^ (1 - θ)) q multHaar := by
          rw [kMethodENorm_def, eLpNorm_congr_ae hfn, eLpNorm_const_smul, eNorm_norm]
      _ = ∞ := by rw [eLpNorm_rpow_multHaar_eq_top h1θ.ne' hq0, ENNReal.mul_top hc0]
      _ = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
          rw [hAtop, ENNReal.top_rpow_of_pos h1θ,
            ENNReal.mul_top (mul_ne_zero (kMethodConst_ne_zero θ hq0) hc0)]
  -- Positive finite measure: scale by `μ A`
  · exact kMethodENorm_l1Linfty_indicator_of_pos_ne_top hu hA0 hAtop θ q

/-- **Exact `K`-method norm of an indicator** for the Lebesgue couple `(L¹, L^∞)`: for `θ < 1`,
`q ∈ [0, ∞]`, and `v` represented by `c 1_A`, `‖v‖_{θ,q} = c_{θ,q} ‖c‖ (μ A) ^ (1 - θ)`. -/
theorem kMethodENorm_lebesgue_one_top_indicator [NormedSpace ℝ E]
    {v : (lebesgue 𝕜 E μ 1 ∞).SumSpace} {A : Set α} {c : E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed v)) =ᵐ[μ]
      A.indicator fun _ ↦ c)
    {θ : ℝ} (hθ : θ < 1) (q : ℝ≥0∞) :
    (lebesgue 𝕜 E μ 1 ∞).kMethodENorm θ q v = kMethodConst θ q * ‖c‖ₑ * μ A ^ (1 - θ) := by
  rw [← kMethodENorm_l1Linfty_sumSpaceEmbed]
  exact kMethodENorm_l1Linfty_indicator hv hθ q

/-! ### The diagonal isomorphism `(L¹, L^∞)_{θ,p} ≃L[𝕜] Lᵖ` -/

section DiagonalEquiv

variable {θ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open KMethodSpace

/-- The canonical linear map `(L¹, L^∞)_{θ,p} →ₗ[𝕜] Lᵖ(μ; E)` sending an element of the real
interpolation space to its almost-everywhere equivalence class. -/
private def lebesgueOneTopKMethodToLp (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →ₗ[𝕜] Lp E p μ where
  toFun u :=
    ⟨L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u)), by
      rw [Lp.mem_Lp_iff_memLp, memLp_iff, ← eLorentzNorm_self (AEEqFun.aestronglyMeasurable _)]
      exact (eLorentzNorm_le_kMethodENorm_lebesgue_one_top Filter.EventuallyEq.rfl hp).trans_lt
        (mem_kMethod_iff.1 (toSumₗ_mem u))⟩
  map_add' u v := Subtype.ext (by simp)
  map_smul' c u := Subtype.ext (by simp; rfl)

private theorem norm_lebesgueOneTopKMethodToLp_le (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodToLp hp u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def, KMethodSpace.norm_def]
  refine ENNReal.toReal_mono (mem_kMethod_iff.1 (toSumₗ_mem u)).ne ?_
  rw [← eLorentzNorm_self (Lp.aestronglyMeasurable _)]
  exact eLorentzNorm_le_kMethodENorm_lebesgue_one_top Filter.EventuallyEq.rfl hp

variable [NormedSpace ℝ E]

/-- The inverse linear map `Lᵖ(μ; E) →ₗ[𝕜] (L¹, L^∞)_{θ,p}` via `lpToLebesgueSum`. -/
private def lpToLebesgueOneTopKMethod (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ) :
    Lp E p μ →ₗ[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p where
  toFun g := KMethodSpace.mk (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top g) <| by
    have hrep : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
        (lpToLebesgueSum (Fact.out : 1 ≤ p) le_top g))) =ᵐ[μ] ⇑g := by
      rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
    rw [mem_kMethod_lebesgue_one_top_iff hrep hθ (Fact.out : 1 ≤ p) hp,
      eLorentzNorm_self (Lp.aestronglyMeasurable g)]
    exact Lp.eLpNorm_lt_top g
  map_add' g h := KMethodSpace.ext (by simp)
  map_smul' c g := KMethodSpace.ext (by simp)

private theorem norm_lpToLebesgueOneTopKMethod_le (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (g : Lp E p μ) :
    ‖lpToLebesgueOneTopKMethod (𝕜 := 𝕜) hθ hp g‖ ≤ θ⁻¹ * ‖g‖ := by
  rw [KMethodSpace.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (inv_nonneg.2 hθ.le),
    ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)) ?_
  have hrep : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed
      (toSumₗ (lpToLebesgueOneTopKMethod (𝕜 := 𝕜) hθ hp g)))) =ᵐ[μ] ⇑g := by
    simp only [lpToLebesgueOneTopKMethod, LinearMap.coe_mk, AddHom.coe_mk, toSumₗ_mk,
      sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
    exact Filter.EventuallyEq.rfl
  rw [← eLorentzNorm_self (Lp.aestronglyMeasurable g)]
  exact kMethodENorm_lebesgue_one_top_le_eLorentzNorm hrep hθ (Fact.out : 1 ≤ p) hp

private def lebesgueOneTopKMethodLinearEquiv (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃ₗ[𝕜] Lp E p μ where
  toFun := lebesgueOneTopKMethodToLp hp
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := lpToLebesgueOneTopKMethod hθ hp
  left_inv u := KMethodSpace.ext <| (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed_injective <| by
    simp only [lpToLebesgueOneTopKMethod, LinearMap.coe_mk, AddHom.coe_mk, toSumₗ_mk,
      sumSpaceEmbed_lpToLebesgueSum]
    exact L1AddLinfty.toAEEqFun_injective (L1AddLinfty.toAEEqFun_ofLp _)
  right_inv g := Subtype.ext <| by
    simp only [lebesgueOneTopKMethodToLp, lpToLebesgueOneTopKMethod, LinearMap.coe_mk,
      AddHom.coe_mk, toSumₗ_mk, sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]

/-- **Real interpolation of `(L¹, L^∞)` on the diagonal `q = p`.** For `θ > 0` and `1 / p = 1 - θ`
with `1 ≤ p ≤ ∞`, the real interpolation space `(L¹(μ; E), L^∞(μ; E))_{θ,p}` is topologically
isomorphic to `Lᵖ(μ; E)`, with `‖u‖_p ≤ ‖u‖_{θ,p} ≤ θ⁻¹ ‖u‖_p`. -/
def lebesgueOneTopKMethodEquivLp (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ) :
    (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p ≃L[𝕜] Lp E p μ where
  toLinearEquiv := lebesgueOneTopKMethodLinearEquiv hθ hp
  continuous_toFun := AddMonoidHomClass.continuous_of_bound
    (lebesgueOneTopKMethodToLp (𝕜 := 𝕜) hp) 1 fun u ↦
      (norm_lebesgueOneTopKMethodToLp_le hp u).trans_eq (one_mul _).symm
  continuous_invFun := AddMonoidHomClass.continuous_of_bound
    (lpToLebesgueOneTopKMethod (𝕜 := 𝕜) hθ hp) θ⁻¹
    (norm_lpToLebesgueOneTopKMethod_le (𝕜 := 𝕜) hθ hp)

@[simp]
theorem coe_lebesgueOneTopKMethodEquivLp (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ((lebesgueOneTopKMethodEquivLp hθ hp u : Lp E p μ) : α →ₘ[μ] E) =
      L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u)) :=
  (rfl)

@[simp]
theorem ofLp_lebesgueOneTopKMethodEquivLp (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    (L1AddLinfty.ofLp (lebesgueOneTopKMethodEquivLp hθ hp u) : L1AddLinfty 𝕜 E μ) =
      (lebesgue 𝕜 E μ 1 ∞).sumSpaceEmbed (toSumₗ u) :=
  L1AddLinfty.toAEEqFun_injective (L1AddLinfty.toAEEqFun_ofLp _)

@[simp]
theorem toSumₗ_lebesgueOneTopKMethodEquivLp_symm (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (g : Lp E p μ) :
    toSumₗ ((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g) =
      lpToLebesgueSum (Fact.out : 1 ≤ p) le_top g :=
  toSumₗ_mk _ _

theorem norm_lebesgueOneTopKMethodEquivLp_le (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖lebesgueOneTopKMethodEquivLp hθ hp u‖ ≤ ‖u‖ :=
  norm_lebesgueOneTopKMethodToLp_le hp u

theorem norm_lebesgueOneTopKMethodEquivLp_symm_le (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (g : Lp E p μ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) hθ hp).symm g‖ ≤ θ⁻¹ * ‖g‖ :=
  norm_lpToLebesgueOneTopKMethod_le (𝕜 := 𝕜) hθ hp g

theorem norm_le_inv_mul_norm_lebesgueOneTopKMethodEquivLp (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ)
    (u : (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p) :
    ‖u‖ ≤ θ⁻¹ * ‖lebesgueOneTopKMethodEquivLp hθ hp u‖ := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    norm_lebesgueOneTopKMethodEquivLp_symm_le (𝕜 := 𝕜) hθ hp
      (lebesgueOneTopKMethodEquivLp hθ hp u)

theorem opNorm_lebesgueOneTopKMethodEquivLp_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ) :
    ‖(lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) (E := E) (μ := μ) hθ hp :
        (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p →L[𝕜] Lp E p μ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦
    (norm_lebesgueOneTopKMethodEquivLp_le hθ hp u).trans_eq (one_mul _).symm

theorem opNorm_lebesgueOneTopKMethodEquivLp_symm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] (hθ : 0 < θ) (hp : p.toReal⁻¹ = 1 - θ) :
    ‖((lebesgueOneTopKMethodEquivLp (𝕜 := 𝕜) (E := E) (μ := μ) hθ hp).symm :
        Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ 1 ∞).KMethodSpace θ p)‖ ≤ θ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hθ.le)
    (norm_lebesgueOneTopKMethodEquivLp_symm_le (𝕜 := 𝕜) hθ hp)

end DiagonalEquiv

/-! ### Weak-`Lᵖ` power-function witness -/

section PowerWitness

/-- On `(0, ∞)` with Lebesgue measure, the `K`-functional of `t ↦ t ^ (-(1 - θ))` equals
`θ⁻¹ t ^ θ` for every `t > 0`. -/
private theorem kFunctional_lebesgue_one_top_rpow_neg {θ : ℝ} (hθ : θ ∈ Ioo 0 1)
    {v : (lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).SumSpace}
    (hv : ⇑(L1AddLinfty.toAEEqFun ℝ
        ((lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).sumSpaceEmbed v))
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ ↦ t ^ (-(1 - θ))))
    {t : ℝ} (ht : 0 < t) :
    (lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).kFunctional t v = θ⁻¹ * t ^ θ := by
  set p : ℝ≥0∞ := ENNReal.ofReal (1 - θ)⁻¹
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hp : p.toReal⁻¹ = 1 - θ := by
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 h1θ.le), inv_inv]
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 h1θ)).ne'
  have hrearr : ∀ s ∈ Ioc 0 t,
      (volume.restrict (Ioi (0 : ℝ))).decreasingRearrangement (fun x : ℝ ↦ ‖x ^ (-(1 - θ))‖ₑ) s =
        ENNReal.ofReal (s ^ (-(1 - θ))) := fun s hs ↦ by
    have hnorm : (fun x : ℝ ↦ ‖x ^ (-(1 - θ))‖ₑ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ ↦ ENNReal.ofReal (x ^ (-p.toReal⁻¹)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
      rw [Real.eNorm_of_nonneg (Real.rpow_nonneg hx.le _), hp]
    rw [Measure.decreasingRearrangement_congr_ae _ hnorm,
      decreasingRearrangement_ofReal_rpow_neg_inv hp0 ENNReal.ofReal_ne_top hs.1, hp]
  have hK : ENNReal.ofReal
      ((lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).kFunctional t v) =
      ENNReal.ofReal (θ⁻¹ * t ^ θ) := by
    rw [ofReal_kFunctional_lebesgue_one_top hv ht.le,
      setLIntegral_congr_fun measurableSet_Ioc hrearr,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
      lintegral_ofReal_rpow_Ioo (by linarith [hθ.1]) ht.le]
    simp [div_eq_inv_mul]
  exact (ENNReal.ofReal_eq_ofReal_iff (kFunctional_nonneg ht.le)
    (mul_nonneg (inv_nonneg.2 hθ.1.le) (Real.rpow_nonneg ht.le _))).1 hK

/-- On `(0, ∞)` with Lebesgue measure and `0 < θ < 1`, the power function `t ↦ t ^ (-(1 - θ))`
represents an element `v` of `(L¹, L^∞)_{θ,∞}` whose `K`-method norm equals `θ⁻¹` (attaining
equality in `kMethodENorm_lebesgue_one_top_le_eLorentzNorm`), while `v ∉ (L¹, L^∞)_{θ,q}` for every
finite `q ≠ 0` (witnessing `Lᵖ ⊊ (L¹, L^∞)_{θ,∞}`). -/
theorem exists_mem_kMethod_top_not_mem_kMethod_rpow {θ : ℝ} (hθ : θ ∈ Ioo 0 1) :
    ∃ v : (lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).SumSpace,
      ⇑(L1AddLinfty.toAEEqFun ℝ
          ((lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).sumSpaceEmbed v)) =ᵐ[
          volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ ↦ t ^ (-(1 - θ))) ∧
      (lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).kMethodENorm θ ∞ v =
        ENNReal.ofReal θ⁻¹ ∧
      ∀ q : ℝ≥0∞, q ≠ 0 → q ≠ ∞ →
        v ∉ (lebesgue ℝ ℝ (volume.restrict (Ioi (0 : ℝ))) 1 ∞).kMethod θ q := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set p : ℝ≥0∞ := ENNReal.ofReal (1 - θ)⁻¹
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ.2
  have hp : p.toReal⁻¹ = 1 - θ := by
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 h1θ.le), inv_inv]
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 h1θ)).ne'
  set f : ℝ → ℝ := fun t ↦ t ^ (-(1 - θ))
  have hf_meas : AEStronglyMeasurable f μ :=
    (ContinuousOn.rpow_const continuousOn_id fun _ ht ↦ Or.inl (ne_of_gt ht))
      |>.aestronglyMeasurable measurableSet_Ioi
  have hf_eNorm : ∀ᵐ t ∂μ, ‖f t‖ₑ = ‖ENNReal.ofReal (t ^ (-p.toReal⁻¹))‖ₑ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [eNorm_eq_self, Real.eNorm_of_nonneg (Real.rpow_nonneg ht.le _), hp]
  -- Step 1: realize `f` as an element `v ∈ (L¹, L^∞)_{θ,∞}` via `‖f‖_{p,∞} = 1`
  have htop : eLorentzNorm f p ∞ μ = 1 := by
    rw [eLorentzNorm_congr_eNorm_ae hf_eNorm]
    exact eLorentzNorm_ofReal_rpow_neg_inv_top hp0 ENNReal.ofReal_ne_top
  obtain ⟨v, _, hvf⟩ :=
    (exists_mem_kMethod_lebesgue_one_top_ae_eq_iff (𝕜 := ℝ) (E := ℝ) (μ := μ) hθ le_top hp).2
      ⟨hf_meas, htop.symm ▸ ENNReal.one_lt_top⟩
  refine ⟨v, hvf, ?_, fun q hq0 hq hvq ↦ ?_⟩
  -- Step 2: evaluate `‖v‖_{θ,∞} = θ⁻¹` from `K(t, v) = θ⁻¹ t ^ θ`
  · have hconst : (fun t : ℝ ↦ t ^ (-θ) * (lebesgue ℝ ℝ μ 1 ∞).kFunctional t v) =ᵐ[multHaar]
        fun _ ↦ θ⁻¹ := by
      filter_upwards [ae_pos_multHaar] with t ht
      rw [kFunctional_lebesgue_one_top_rpow_neg hθ hvf ht, ← mul_assoc, mul_comm (t ^ (-θ)),
        mul_assoc, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]
    rw [kMethodENorm_def, eLpNorm_congr_ae hconst,
      eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_const _ (NeZero.ne multHaar),
      Real.eNorm_of_nonneg (inv_nonneg.2 hθ.1.le)]
  -- Step 3: rule out finite `q ≠ 0` since `‖f‖_{p,q} = ∞`
  · have hfin : eLorentzNorm f p q μ < ∞ :=
      (eLorentzNorm_le_kMethodENorm_lebesgue_one_top hvf hp).trans_lt (mem_kMethod_iff.1 hvq)
    rw [eLorentzNorm_congr_eNorm_ae hf_eNorm,
      eLorentzNorm_ofReal_rpow_neg_inv_eq_top hp0 ENNReal.ofReal_ne_top hq0 hq] at hfin
    exact lt_irrefl _ hfin

end PowerWitness

end TauCeti.CompatibleCouple
