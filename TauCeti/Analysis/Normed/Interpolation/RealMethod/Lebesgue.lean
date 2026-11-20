/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.Lorentz
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Lorentz functions in the real interpolation spaces of `(L^{p₀}, L^{p₁})`

Let `1 ≤ p₀ < p₁ ≤ ∞`, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁`, and put
`δ = 1 / p₀ - 1 / p₁`. For `1 ≤ q ≤ ∞`, every element `v` of `L^{p₀}(μ; E) + L^{p₁}(μ; E)`
represented by a function `f` satisfies

`‖v‖_{(L^{p₀}, L^{p₁})_{θ, q}} ≤ ((1 - 2^{-θδ})⁻¹ + (1 - 2^{-(1 - θ)δ})⁻¹) ‖f‖_{p, q}`

(`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_le_eLorentzNorm`), where `‖f‖_{p, q}` is the
Lorentz gauge `TauCeti.eLorentzNorm`. Since `‖f‖_{p, q} ≤ ‖f‖_p` for `q ≥ p`, the space `Lᵖ(μ; E)`
lies in `(L^{p₀}, L^{p₁})_{θ, q}` for every `q ≥ p`, with the same constant
(`TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le`,
`TauCeti.CompatibleCouple.lpToLebesgueSum_mem_kMethod`).

This is the inclusion `L^{p, q} ⊆ (L^{p₀}, L^{p₁})_{θ, q}` of the identification
`(L^{p₀}, L^{p₁})_{θ, q} = L^{p, q}` (Bergh–Löfström, Theorem 5.3.1). For the couple
`(L¹, L^∞)` the sharper constant `θ⁻¹` is
`TauCeti.CompatibleCouple.kMethodENorm_lebesgue_one_top_le_eLorentzNorm`. In Keel and Tao's proof
of the endpoint Strichartz estimate, the case `q = 2 ≥ p` for exponents `p₀ < p < p₁` close to `p`
is what places functions of `Lᵖ` in the real interpolation spaces to which bilinear real
interpolation (`TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le`) applies.

## The argument

Write `a = 1 / p`, `a₀ = 1 / p₀` and `a₁ = 1 / p₁`, so that `a₀ - a = θδ` and `a - a₁ = (1 - θ)δ`,
and let `f*` be the decreasing rearrangement of `‖f‖`. For `s > 0` cut `f` at the level `f*(s)`:
`f₀ = f 1_{‖f‖ > f*(s)}` and `f₁ = f - f₀`. Then the rearrangement of `‖f₀‖` is at most `f*` and
vanishes beyond `s`, while that of `‖f₁‖` is at most `min(f*, f*(s))`
(`MeasureTheory.Measure.decreasingRearrangement_indicator_setOf_lt_eq_zero`,
`MeasureTheory.Measure.decreasingRearrangement_indicator_compl_setOf_lt_le`). Since `f*` is
antitone it is bounded on the dyadic intervals `(2^{-(n+1)} s, 2^{-n} s]` and `[2ⁿ s, 2ⁿ⁺¹ s)` by
its values at their left endpoints, and Minkowski's inequality for series turns these step
functions into the bounds `‖f₀‖_{p₀} ≤ ∑ₙ f*(2^{-(n+1)} s) (2^{-(n+1)} s)^{a₀}` and
`‖f₁‖_{p₁} ≤ f*(s) s^{a₁} + ∑ₙ f*(2ⁿ s) (2ⁿ s)^{a₁}`
(`MeasureTheory.Measure.eLpNorm_indicator_setOf_lt_le`,
`MeasureTheory.Measure.eLpNorm_indicator_compl_setOf_lt_le`). The `K`-functional is at most
`‖f₀‖_{p₀} + t ‖f₁‖_{p₁}`
(`TauCeti.CompatibleCouple.ofReal_kFunctional_lebesgue_le_eLpNorm_add_mul`). With `t = s^δ` and
`F(u) = u^a f*(u)` this gives

`t^{-θ} K(t, v) ≤ ∑ₙ 2^{-nθδ} F(2^{-n} s) + ∑ₙ 2^{-n(1-θ)δ} F(2ⁿ s)`.

The substitution `t = s^δ` multiplies the `L^q(dt / t)` seminorm by `δ^{1 / q} ≤ 1`
(`TauCeti.eLpNorm_comp_rpow_multHaar`), Minkowski's inequality sums the two series in
`L^q(ds / s)`, and by the dilation invariance of `ds / s` (`TauCeti.eLpNorm_comp_mul_left_multHaar`)
every `F(c ·)` has `L^q(ds / s)` seminorm `‖f‖_{p, q}`. The two geometric series give the
constant. Summing over dyadic intervals replaces the weighted Hardy inequalities used for
`(L¹, L^∞)`, which for the tail would need `q ≥ p₁`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.3 (Theorem 5.3.1).
* T. Holmstedt, *Interpolation of quasi-normed spaces*, Math. Scand. **26** (1970), 177–199.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]

/-! ### The `K`-method norm -/

section KMethod

variable {θ : ℝ} {p q : ℝ≥0∞}

/-- The exponents of the interpolation: with `δ = 1 / p₀ - 1 / p₁`, `0 < δ ≤ 1`, `1 / p > 0`,
`1 / p₀ = 1 / p + θδ` and `1 / p₁ = 1 / p - (1 - θ)δ`. -/
private theorem toReal_inv_facts (hθ : θ ∈ Ioo 0 1) (hp₀₁ : p₀ < p₁)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    0 < (p₀⁻¹ - p₁⁻¹).toReal ∧ (p₀⁻¹ - p₁⁻¹).toReal ≤ 1 ∧ 0 < (p⁻¹).toReal ∧
      (p₀⁻¹).toReal = (p⁻¹).toReal + θ * (p₀⁻¹ - p₁⁻¹).toReal ∧
      (p₁⁻¹).toReal = (p⁻¹).toReal - (1 - θ) * (p₀⁻¹ - p₁⁻¹).toReal := by
  have h₀ : p₀⁻¹ ≤ 1 := ENNReal.inv_le_one.2 Fact.out
  have h₀t : p₀⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top h₀
  have h₁t : p₁⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.inv_le_one.2 Fact.out)
  have hlt : p₁⁻¹ < p₀⁻¹ := ENNReal.inv_lt_inv.2 hp₀₁
  have hδ : (p₀⁻¹ - p₁⁻¹).toReal = (p₀⁻¹).toReal - (p₁⁻¹).toReal :=
    ENNReal.toReal_sub_of_le hlt.le h₀t
  have ha : (p⁻¹).toReal = (1 - θ) * (p₀⁻¹).toReal + θ * (p₁⁻¹).toReal := by
    rw [inv_eq_ofReal_of_inv_eq (zero_lt_one.trans_le Fact.out).ne'
      (zero_lt_one.trans_le Fact.out).ne' (Ioo_subset_Icc_self hθ) hp,
      ENNReal.toReal_ofReal (add_nonneg (mul_nonneg (sub_nonneg.2 hθ.2.le) ENNReal.toReal_nonneg)
        (mul_nonneg hθ.1.le ENNReal.toReal_nonneg))]
  have hlt' : (p₁⁻¹).toReal < (p₀⁻¹).toReal := (ENNReal.toReal_lt_toReal h₁t h₀t).2 hlt
  have h₀' : (p₀⁻¹).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h₀)
  have h₁' : 0 ≤ (p₁⁻¹).toReal := ENNReal.toReal_nonneg
  refine ⟨by rw [hδ]; linarith, by rw [hδ]; linarith, ?_, by rw [hδ, ha]; ring,
    by rw [hδ, ha]; ring⟩
  rw [ha]
  nlinarith [hθ.1, hθ.2]

/-- `ofReal ((2⁻¹ ^ m) ^ x) = ofReal (2⁻¹ ^ x) ^ m`. -/
private theorem ofReal_inv_two_pow_rpow (m : ℕ) (x : ℝ) :
    ENNReal.ofReal (((2 : ℝ)⁻¹ ^ m) ^ x) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ x) ^ m := by
  rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]

/-- `ofReal ((2 ^ m) ^ (-x)) = ofReal (2⁻¹ ^ x) ^ m`. -/
private theorem ofReal_two_pow_rpow_neg (m : ℕ) (x : ℝ) :
    ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-x)) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ x) ^ m := by
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), ← inv_pow,
    ofReal_inv_two_pow_rpow]

/-- The rescaling of one dyadic term: `s ^ (-x) (c s) ^ (a + x) = c ^ x (c s) ^ a`. -/
private theorem ofReal_rpow_neg_mul_mul_ofReal_rpow {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (a x : ℝ) (y : ℝ≥0∞) :
    ENNReal.ofReal (s ^ (-x)) * (y * ENNReal.ofReal ((c * s) ^ (a + x))) =
      ENNReal.ofReal (c ^ x) * (ENNReal.ofReal ((c * s) ^ a) * y) := by
  have h : s ^ (-x) * (c * s) ^ (a + x) = c ^ x * (c * s) ^ a := by
    rw [Real.rpow_add (by positivity), Real.mul_rpow hc.le hs.le (z := x), Real.rpow_neg hs.le]
    field_simp
  calc _ = ENNReal.ofReal (s ^ (-x) * (c * s) ^ (a + x)) * y := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
    _ = _ := by
        rw [h, ENNReal.ofReal_mul (by positivity)]
        ring

/-- With `t = s ^ δ`, the integrand `t ^ (-θ) K(t, v)` of the `K`-method norm is at most
`∑ₙ 2^{-nθδ} F(2^{-n} s) + ∑ₙ 2^{-n(1-θ)δ} F(2ⁿ s)`, where `F(u) = u ^ a g*(u)`, for `v`
represented by a strongly measurable `g` and `1 / p₀ = a + θδ`, `1 / p₁ = a - (1 - θ)δ`. -/
private theorem eNorm_rpow_neg_mul_kFunctional_le {a δ : ℝ}
    (ha₀ : (p₀⁻¹).toReal = a + θ * δ) (ha₁ : (p₁⁻¹).toReal = a - (1 - θ) * δ)
    {v : (lebesgue 𝕜 E μ p₀ p₁).SumSpace} {g : α → E} (hg : StronglyMeasurable g)
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed v)) =ᵐ[μ] g)
    {s : ℝ} (hs : 0 < s) :
    ‖(s ^ δ) ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional (s ^ δ) v‖ₑ ≤
      ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ (θ * δ)) ^ n * (ENNReal.ofReal ((2⁻¹ ^ n * s) ^ a) *
          μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ ^ n * s)) +
        ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * δ)) ^ n * (ENNReal.ofReal ((2 ^ n * s) ^ a) *
          μ.decreasingRearrangement (‖g ·‖ₑ) (2 ^ n * s)) := by
  set R := μ.decreasingRearrangement (‖g ·‖ₑ)
  set A := {x | R s < ‖g x‖ₑ}
  set F : ℝ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal (u ^ a) * R u
  have hK := ofReal_kFunctional_lebesgue_le_eLpNorm_add_mul hv
    (ae_of_all _ fun x ↦ congrFun (indicator_self_add_compl A g) x) (Real.rpow_pos_of_pos hs δ)
  have h₀ := μ.eLpNorm_indicator_setOf_lt_le (r := p₀) hg.aestronglyMeasurable Fact.out hs
  have h₁ := μ.eLpNorm_indicator_compl_setOf_lt_le (r := p₁) hg.aestronglyMeasurable Fact.out hs
  rw [ha₀] at h₀
  rw [ha₁, sub_eq_add_neg] at h₁
  have e₀ : (s ^ δ) ^ (-θ) = s ^ (-(θ * δ)) := by
    rw [← Real.rpow_mul hs.le]
    ring_nf
  have e₁ : (s ^ δ) ^ (-θ) * s ^ δ = s ^ (-(-((1 - θ) * δ))) := by
    rw [e₀, ← Real.rpow_add hs]
    ring_nf
  rw [Real.eNorm_of_nonneg (mul_nonneg (by positivity) (kFunctional_nonneg (by positivity))),
    ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((s ^ δ) ^ (-θ)) *
        ENNReal.ofReal ((lebesgue 𝕜 E μ p₀ p₁).kFunctional (s ^ δ) v)
      ≤ ENNReal.ofReal (s ^ (-(θ * δ))) * eLpNorm (A.indicator g) p₀ μ +
          ENNReal.ofReal (s ^ (-(-((1 - θ) * δ)))) * eLpNorm (Aᶜ.indicator g) p₁ μ := by
        refine (mul_le_mul_right hK _).trans_eq ?_
        rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), e₁, e₀]
    _ ≤ (∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ (θ * δ)) ^ (n + 1) * F (2⁻¹ ^ (n + 1) * s)) +
          (F s + ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * δ)) ^ n * F (2 ^ n * s)) := by
        refine add_le_add ((mul_le_mul_right h₀ _).trans_eq ?_)
          ((mul_le_mul_right h₁ _).trans_eq ?_)
        · rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun n ↦ ?_
          rw [ofReal_rpow_neg_mul_mul_ofReal_rpow (by positivity) hs, ofReal_inv_two_pow_rpow]
        · rw [mul_add, ← ENNReal.tsum_mul_left]
          congr 1
          · simpa [F] using ofReal_rpow_neg_mul_mul_ofReal_rpow one_pos hs a (-((1 - θ) * δ)) (R s)
          · refine tsum_congr fun n ↦ ?_
            rw [ofReal_rpow_neg_mul_mul_ofReal_rpow (by positivity) hs, ofReal_two_pow_rpow_neg]
    _ = _ := by
        rw [tsum_eq_zero_add' (f := fun n : ℕ ↦ ENNReal.ofReal (2⁻¹ ^ (θ * δ)) ^ n *
          F (2⁻¹ ^ n * s)) CompleteLattice.summable]
        simp only [pow_zero, one_mul]
        ring

/-- **Lorentz functions lie in the real interpolation spaces of `(L^{p₀}, L^{p₁})`.** Let
`1 ≤ p₀ < p₁ ≤ ∞`, `0 < θ < 1`, `1 / p = (1 - θ) / p₀ + θ / p₁` and `1 ≤ q ≤ ∞`, and put
`δ = 1 / p₀ - 1 / p₁`. An element `v` of `L^{p₀} + L^{p₁}` represented by `f` satisfies
`‖v‖_{θ, q} ≤ ((1 - 2^{-θδ})⁻¹ + (1 - 2^{-(1 - θ)δ})⁻¹) ‖f‖_{p, q}`. -/
theorem kMethodENorm_lebesgue_le_eLorentzNorm (hθ : θ ∈ Ioo 0 1) (hp₀₁ : p₀ < p₁)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hq : 1 ≤ q)
    {v : (lebesgue 𝕜 E μ p₀ p₁).SumSpace} {f : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed v)) =ᵐ[μ] f) :
    (lebesgue 𝕜 E μ p₀ p₁).kMethodENorm θ q v ≤
      ((1 - ENNReal.ofReal (2⁻¹ ^ (θ * (p₀⁻¹ - p₁⁻¹).toReal)))⁻¹ +
        (1 - ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * (p₀⁻¹ - p₁⁻¹).toReal)))⁻¹) *
        eLorentzNorm f p q μ := by
  obtain ⟨hδ, hδ₁, ha, ha₀, ha₁⟩ := toReal_inv_facts hθ hp₀₁ hp
  set δ := (p₀⁻¹ - p₁⁻¹).toReal
  have hf : AEStronglyMeasurable f μ := (AEEqFun.aestronglyMeasurable _).congr hv
  have hg : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  rw [eLorentzNorm_congr_ae hf.ae_eq_mk, eLorentzNorm_eq_eLpNorm hg.aestronglyMeasurable
    (ENNReal.inv_ne_top.1 (ENNReal.toReal_pos_iff.1 ha).2.ne), kMethodENorm_def]
  set F : ℝ → ℝ≥0∞ := fun u ↦
    ENNReal.ofReal (u ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖hf.mk f ·‖ₑ) u
  have hF : Measurable F := μ.measurable_rpow_mul_decreasingRearrangement _ _
  have hK := (lebesgue 𝕜 E μ p₀ p₁).aestronglyMeasurable_rpow_neg_mul_kFunctional θ v
  -- Minkowski's inequality for the dyadic series, whose terms all have the norm of `F`.
  have hsum : ∀ (r : ℝ≥0∞) {c : ℝ}, 0 < c →
      eLpNorm (fun s ↦ ∑' n : ℕ, r ^ n * F (c ^ n * s)) q multHaar ≤
        (1 - r)⁻¹ * eLpNorm F q multHaar := by
    intro r c hc
    refine (eLpNorm_tsum_le (fun n ↦ ((hF.comp (measurable_const_mul _)).const_mul _).aemeasurable)
      hq).trans_eq ?_
    rw [← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    rw [eLpNorm_const_mul_ennreal_of_pos (zero_lt_one.trans_le hq)]
    exact congrArg (r ^ n * ·) (eLpNorm_comp_mul_left_multHaar F (pow_pos hc n) q)
  calc eLpNorm (fun t ↦ t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t v) q multHaar
      ≤ eLpNorm (fun s ↦ (s ^ δ) ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional (s ^ δ) v)
          q multHaar := by
        rw [eLpNorm_comp_rpow_multHaar hK hδ.ne' q]
        refine le_mul_of_one_le_left zero_le ((ENNReal.one_rpow _).symm.le.trans
          (ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg))
        rw [← ENNReal.ofReal_one, abs_of_pos (inv_pos.2 hδ)]
        exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hδ).2 hδ₁)
    _ ≤ eLpNorm (fun s ↦ ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ (θ * δ)) ^ n * F (2⁻¹ ^ n * s) +
          ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * δ)) ^ n * F (2 ^ n * s)) q multHaar := by
        refine eLpNorm_mono_eNorm_ae ?_ (ae_pos_multHaar.mono fun s hs ↦
          (eNorm_rpow_neg_mul_kFunctional_le ha₀ ha₁ hg (hv.trans hf.ae_eq_mk) hs).trans_eq
            (eNorm_eq_self _).symm)
        have hK' : AEStronglyMeasurable
            (fun t ↦ t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t v) (multHaar.map (· ^ δ)) := by
          rw [map_multHaar_rpow hδ.ne']
          exact hK.smul_measure _
        exact hK'.comp_aemeasurable (measurable_id'.pow_const δ).aemeasurable
    _ ≤ (1 - ENNReal.ofReal (2⁻¹ ^ (θ * δ)))⁻¹ * eLpNorm F q multHaar +
          (1 - ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * δ)))⁻¹ * eLpNorm F q multHaar :=
        (eLpNorm_add_le hq).trans (add_le_add (hsum _ (by norm_num)) (hsum _ two_pos))
    _ = _ := (add_mul _ _ _).symm

/-- `(1 - 2^{-x})⁻¹` is finite for `x > 0`. -/
private theorem inv_one_sub_ofReal_inv_two_rpow_lt_top {x : ℝ} (hx : 0 < x) :
    (1 - ENNReal.ofReal (2⁻¹ ^ x))⁻¹ < ∞ :=
  ENNReal.inv_lt_top.2 <| tsub_pos_of_lt <| ENNReal.ofReal_lt_one.2 <|
    Real.rpow_lt_one (by norm_num) (by norm_num) hx

variable [Fact (1 ≤ p)]

/-- **`Lᵖ` lies in the real interpolation spaces `(L^{p₀}, L^{p₁})_{θ, q}`, `q ≥ p`.** For
`1 ≤ p₀ < p₁ ≤ ∞`, `0 < θ < 1`, `1 / p = (1 - θ) / p₀ + θ / p₁` and `p ≤ q ≤ ∞`, every `f ∈ Lᵖ` has
`‖f‖_{θ, q} ≤ ((1 - 2^{-θδ})⁻¹ + (1 - 2^{-(1 - θ)δ})⁻¹) ‖f‖_p`, with `δ = 1 / p₀ - 1 / p₁`. -/
theorem kMethodENorm_lpToLebesgueSum_le (hθ : θ ∈ Ioo 0 1) (hp₀₁ : p₀ < p₁)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpq : p ≤ q)
    (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    (lebesgue 𝕜 E μ p₀ p₁).kMethodENorm θ q (lpToLebesgueSum h₀ h₁ f) ≤
      ((1 - ENNReal.ofReal (2⁻¹ ^ (θ * (p₀⁻¹ - p₁⁻¹).toReal)))⁻¹ +
        (1 - ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * (p₀⁻¹ - p₁⁻¹).toReal)))⁻¹) * eLpNorm f p μ := by
  obtain ⟨-, -, ha, -, -⟩ := toReal_inv_facts hθ hp₀₁ hp
  have hp0 : p ≠ 0 := ENNReal.inv_ne_top.1 (ENNReal.toReal_pos_iff.1 ha).2.ne
  have hptop : p ≠ ∞ := fun h ↦ hp₀₁.ne_top ((eq_top_iff_of_inv_eq hθ hp).1 h).1
  refine (kMethodENorm_lebesgue_le_eLorentzNorm hθ hp₀₁ hp ((Fact.out : 1 ≤ p).trans hpq)
    (f := f) ?_).trans ?_
  · rw [sumSpaceEmbed_lpToLebesgueSum, L1AddLinfty.toAEEqFun_ofLp]
  · gcongr
    refine (eLorentzNorm_le_of_exponent_le hp0 hptop hp0 hpq).trans_eq ?_
    rw [div_self (ENNReal.toReal_pos hp0 hptop).ne', Real.one_rpow, ENNReal.ofReal_one, one_mul,
      eLorentzNorm_self]

/-- For `1 ≤ p₀ < p₁ ≤ ∞`, `0 < θ < 1`, `1 / p = (1 - θ) / p₀ + θ / p₁` and `p ≤ q ≤ ∞`, every
`f ∈ Lᵖ` lies in the real interpolation space `(L^{p₀}, L^{p₁})_{θ, q}`. -/
theorem lpToLebesgueSum_mem_kMethod (hθ : θ ∈ Ioo 0 1) (hp₀₁ : p₀ < p₁)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpq : p ≤ q)
    (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) (f : Lp E p μ) :
    lpToLebesgueSum h₀ h₁ f ∈ (lebesgue 𝕜 E μ p₀ p₁).kMethod θ q := by
  obtain ⟨hδ, -, -, -, -⟩ := toReal_inv_facts hθ hp₀₁ hp
  refine mem_kMethod_iff.2 <| (kMethodENorm_lpToLebesgueSum_le hθ hp₀₁ hp hpq h₀ h₁ f).trans_lt <|
    ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩) (Lp.eLpNorm_lt_top f)
  · exact inv_one_sub_ofReal_inv_two_rpow_lt_top (mul_pos hθ.1 hδ)
  · exact inv_one_sub_ofReal_inv_two_rpow_lt_top (mul_pos (sub_pos.2 hθ.2) hδ)

end KMethod

end TauCeti.CompatibleCouple
