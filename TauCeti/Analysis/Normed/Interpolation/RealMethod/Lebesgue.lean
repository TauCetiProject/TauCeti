/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.Lorentz
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
vanishes beyond `s`, while that of `‖f₁‖` is at most `min(f*, f*(s))`. Since `f*` is antitone it is
bounded on the dyadic intervals `(2^{-(n+1)} s, 2^{-n} s]` and `[2ⁿ s, 2ⁿ⁺¹ s)` by its values at
their left endpoints, and Minkowski's inequality for series (`MeasureTheory.eLpNorm_tsum_le`) turns
these step functions into the bounds
`‖f₀‖_{p₀} ≤ ∑ₙ f*(2^{-(n+1)} s) (2^{-(n+1)} s)^{a₀}` and
`‖f₁‖_{p₁} ≤ f*(s) s^{a₁} + ∑ₙ f*(2ⁿ s) (2ⁿ s)^{a₁}`. With `t = s^δ` and `F(u) = u^a f*(u)` this
gives

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

/-- Any almost everywhere splitting `f₀ + f₁ = f` of a function `f` representing an element `v` of
`L^{p₀} + L^{p₁}` bounds the `K`-functional at `t > 0` by `‖f₀‖_{p₀} + t ‖f₁‖_{p₁}`. -/
theorem ofReal_kFunctional_lebesgue_le_eLpNorm_add_mul {v : (lebesgue 𝕜 E μ p₀ p₁).SumSpace}
    {f f₀ f₁ : α → E}
    (hv : ⇑(L1AddLinfty.toAEEqFun 𝕜 ((lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed v)) =ᵐ[μ] f)
    (hsum : f₀ + f₁ =ᵐ[μ] f) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ((lebesgue 𝕜 E μ p₀ p₁).kFunctional t v) ≤
      eLpNorm f₀ p₀ μ + ENNReal.ofReal t * eLpNorm f₁ p₁ μ := by
  by_cases hfin : eLpNorm f₀ p₀ μ + ENNReal.ofReal t * eLpNorm f₁ p₁ μ = ∞
  · rw [hfin]
    exact le_top
  obtain ⟨hfin₀, hfin₁⟩ := ENNReal.add_ne_top.1 hfin
  have h₀ : MemLp f₀ p₀ μ := memLp_iff.2 hfin₀.lt_top
  have h₁ : MemLp f₁ p₁ μ := memLp_iff.2 <| lt_top_iff_ne_top.2 fun htop ↦ hfin₁ <| by
    rw [htop, ENNReal.mul_top (by simpa using ht)]
  have hdec : (lebesgue 𝕜 E μ p₀ p₁).fstToSum (h₀.toLp f₀) +
      (lebesgue 𝕜 E μ p₀ p₁).sndToSum (h₁.toLp f₁) = v := by
    refine (lebesgue 𝕜 E μ p₀ p₁).sumSpaceEmbed_injective (L1AddLinfty.toAEEqFun_injective ?_)
    rw [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀, lebesgue_embed₁,
      map_add, L1AddLinfty.toAEEqFun_ofLp, L1AddLinfty.toAEEqFun_ofLp]
    refine AEEqFun.ext ?_
    filter_upwards [AEEqFun.coeFn_add (h₀.toLp f₀ : α →ₘ[μ] E) (h₁.toLp f₁), h₀.coeFn_toLp,
      h₁.coeFn_toLp, hsum, hv] with x hx hx₀ hx₁ hxs hxv
    rw [hx, Pi.add_apply, hxv, ← hxs, Pi.add_apply, ← hx₀, ← hx₁]
  calc ENNReal.ofReal ((lebesgue 𝕜 E μ p₀ p₁).kFunctional t v)
      ≤ ENNReal.ofReal (‖h₀.toLp f₀‖ + t * ‖h₁.toLp f₁‖) :=
        ENNReal.ofReal_le_ofReal (kFunctional_le ht.le hdec)
    _ = eLpNorm f₀ p₀ μ + ENNReal.ofReal t * eLpNorm f₁ p₁ μ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), ENNReal.ofReal_mul ht.le,
          Lp.norm_toLp, Lp.norm_toLp, ENNReal.ofReal_toReal hfin₀,
          ENNReal.ofReal_toReal h₁.eLpNorm_ne_top]

/-! ### Dyadic bounds for the two parts of the cut -/

section Dyadic

/-- An antitone function is bounded on `(0, s]` by its values at the left endpoints of the
dyadic intervals `(2⁻¹ ^ (n + 1) s, 2⁻¹ ^ n s]`. -/
private theorem le_tsum_indicator_Ioc {R : ℝ → ℝ≥0∞} (hR : Antitone R) {s u : ℝ} (hu : 0 < u)
    (hus : u ≤ s) :
    R u ≤ ∑' n : ℕ, (Ioc (2⁻¹ ^ (n + 1) * s) (2⁻¹ ^ n * s)).indicator
      (fun _ ↦ R (2⁻¹ ^ (n + 1) * s)) u := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near ((one_le_div hu).2 hus) one_lt_two
  have hmem : u ∈ Ioc (2⁻¹ ^ (n + 1) * s) (2⁻¹ ^ n * s) := by
    rw [inv_pow, inv_pow, ← div_eq_inv_mul, ← div_eq_inv_mul]
    rw [div_lt_iff₀ hu, mul_comm] at hn₂
    rw [le_div_iff₀ hu, mul_comm] at hn₁
    exact ⟨(div_lt_iff₀ (by positivity)).2 hn₂, (le_div_iff₀ (by positivity)).2 hn₁⟩
  refine le_trans ?_ (le_tsum _ n)
  rw [indicator_of_mem hmem]
  exact hR hmem.1.le

/-- An antitone function is bounded on `[s, ∞)` by its values at the left endpoints of the
dyadic intervals `[2 ^ n s, 2 ^ (n + 1) s)`. -/
private theorem le_tsum_indicator_Ico {R : ℝ → ℝ≥0∞} (hR : Antitone R) {s u : ℝ} (hs : 0 < s)
    (hsu : s ≤ u) :
    R u ≤ ∑' n : ℕ, (Ico (2 ^ n * s) (2 ^ (n + 1) * s)).indicator (fun _ ↦ R (2 ^ n * s)) u := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near ((one_le_div hs).2 hsu) one_lt_two
  have hmem : u ∈ Ico (2 ^ n * s) (2 ^ (n + 1) * s) :=
    ⟨(le_div_iff₀ hs).1 hn₁, (div_lt_iff₀ hs).1 hn₂⟩
  refine le_trans ?_ (le_tsum _ n)
  rw [indicator_of_mem hmem]
  exact hR hmem.1

/-- The `Lʳ` seminorm of a step function `∑ₙ cₙ 1_{Iₙ}` is at most `∑ₙ cₙ ν(Iₙ) ^ (1 / r)`. -/
private theorem eLpNorm_tsum_indicator_le {I : ℕ → Set ℝ} (hI : ∀ n, MeasurableSet (I n))
    (c : ℕ → ℝ≥0∞) {r : ℝ≥0∞} (hr : 1 ≤ r) (ν : Measure ℝ) :
    eLpNorm (fun u ↦ ∑' n, (I n).indicator (fun _ ↦ c n) u) r ν ≤
      ∑' n, c n * ν (I n) ^ (1 / r.toReal) :=
  (eLpNorm_tsum_le (fun n ↦ (measurable_const.indicator (hI n)).aemeasurable) hr).trans <|
    tsum_le_tsum fun n ↦ by
      simpa only [eNorm_eq_self] using
        eLpNorm_indicator_const_le (c n) r (hI n).nullMeasurableSet (μ := ν)

/-- A set `I ⊆ ℝ` of Lebesgue measure `ℓ` has measure at most `ℓ` for Lebesgue measure restricted
to `(0, ∞)`, so its measure raised to `1 / r` is at most `ℓ ^ (1 / r)`. -/
private theorem restrict_Ioi_rpow_le {I : Set ℝ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hI : volume I = .ofReal ℓ)
    (r : ℝ≥0∞) :
    volume.restrict (Ioi 0) I ^ (1 / r.toReal) ≤ ENNReal.ofReal (ℓ ^ (r⁻¹).toReal) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg hℓ ENNReal.toReal_nonneg, ENNReal.toReal_inv, ← one_div,
    ← hI]
  gcongr
  exact Measure.restrict_le_self

variable {g : α → E} {r : ℝ≥0∞} {s : ℝ}

/-- The part of `g` above the level `g*(s)` has `Lʳ` seminorm at most
`∑ₙ g*(2⁻¹ ^ (n + 1) s) (2⁻¹ ^ (n + 1) s) ^ (1 / r)`, where `g*` is the decreasing rearrangement of
`‖g‖`. -/
private theorem eLpNorm_indicator_lt_le (hg : StronglyMeasurable g) (hr : 1 ≤ r) (hs : 0 < s) :
    eLpNorm ({x | μ.decreasingRearrangement (‖g ·‖ₑ) s < ‖g x‖ₑ}.indicator g) r μ ≤
      ∑' n : ℕ, μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ ^ (n + 1) * s) *
        ENNReal.ofReal ((2⁻¹ ^ (n + 1) * s) ^ (r⁻¹).toReal) := by
  set R := μ.decreasingRearrangement (‖g ·‖ₑ)
  set A := {x | R s < ‖g x‖ₑ}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hg.eNorm
  have hφ : Measurable fun x ↦ ‖A.indicator g x‖ₑ := (hg.indicator hA).eNorm
  set M : ℝ → ℝ≥0∞ := fun u ↦ ∑' n : ℕ,
    (Ioc (2⁻¹ ^ (n + 1) * s) (2⁻¹ ^ n * s)).indicator (fun _ ↦ R (2⁻¹ ^ (n + 1) * s)) u
  -- The rearrangement of `‖g 1_A‖` is at most `g*` and vanishes beyond `s`.
  have hle : ∀ u, 0 < u → μ.decreasingRearrangement (fun x ↦ ‖A.indicator g x‖ₑ) u ≤ M u := by
    intro u hu
    rcases le_or_gt u s with hus | hsu
    · refine (μ.decreasingRearrangement_mono (fun x ↦ ?_) u).trans
        (le_tsum_indicator_Ioc (μ.antitone_decreasingRearrangement _) hu hus)
      rw [eNorm_indicator_eq_indicator_eNorm]
      exact indicator_le_self _ _ x
    · have hsub : {x | 0 < ‖A.indicator g x‖ₑ} ⊆ A := fun x hx ↦ by
        by_contra hxA
        simp only [mem_ofPred_eq, indicator_of_notMem hxA, eNorm_zero, lt_self_iff_false] at hx
      exact (μ.decreasingRearrangement_le_iff.2 <| (measure_mono hsub).trans <|
        (μ.measure_setOf_decreasingRearrangement_lt_le _ s).trans
          (ENNReal.ofReal_le_ofReal hsu.le)).trans zero_le
  rw [← eLpNorm_eNorm _ (hg.indicator hA).aestronglyMeasurable,
    ← μ.eLpNorm_decreasingRearrangement hφ.aemeasurable]
  refine (eLpNorm_mono_eNorm_ae (g := M)
    (μ.measurable_decreasingRearrangement _).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun u hu ↦ ?_)).trans
    ((eLpNorm_tsum_indicator_le (fun _ ↦ measurableSet_Ioc) _ hr _).trans
      (tsum_le_tsum fun n ↦ ?_))
  · simpa only [eNorm_eq_self] using hle u hu
  · gcongr
    refine restrict_Ioi_rpow_le (by positivity) ?_ r
    rw [Real.volume_Ioc, pow_succ]
    ring_nf

/-- The part of `g` at or below the level `g*(s)` has `Lʳ` seminorm at most
`g*(s) s ^ (1 / r) + ∑ₙ g*(2 ^ n s) (2 ^ n s) ^ (1 / r)`, where `g*` is the decreasing rearrangement
of `‖g‖`. -/
private theorem eLpNorm_indicator_compl_le (hg : StronglyMeasurable g) (hr : 1 ≤ r)
    (hs : 0 < s) :
    eLpNorm ({x | μ.decreasingRearrangement (‖g ·‖ₑ) s < ‖g x‖ₑ}ᶜ.indicator g) r μ ≤
      μ.decreasingRearrangement (‖g ·‖ₑ) s * ENNReal.ofReal (s ^ (r⁻¹).toReal) +
        ∑' n : ℕ, μ.decreasingRearrangement (‖g ·‖ₑ) (2 ^ n * s) *
          ENNReal.ofReal ((2 ^ n * s) ^ (r⁻¹).toReal) := by
  set R := μ.decreasingRearrangement (‖g ·‖ₑ)
  set A := {x | R s < ‖g x‖ₑ}
  have hA : MeasurableSet Aᶜ := (measurableSet_lt measurable_const hg.eNorm).compl
  have hφ : Measurable fun x ↦ ‖Aᶜ.indicator g x‖ₑ := (hg.indicator hA).eNorm
  set M₀ : ℝ → ℝ≥0∞ := (Ioc 0 s).indicator fun _ ↦ R s
  set M₁ : ℝ → ℝ≥0∞ := fun u ↦ ∑' n : ℕ,
    (Ico (2 ^ n * s) (2 ^ (n + 1) * s)).indicator (fun _ ↦ R (2 ^ n * s)) u
  -- The rearrangement of `‖g 1_{Aᶜ}‖` is at most `min (g*, g*(s))`.
  have hle : ∀ u, 0 < u →
      μ.decreasingRearrangement (fun x ↦ ‖Aᶜ.indicator g x‖ₑ) u ≤ (M₀ + M₁) u := by
    intro u hu
    rcases le_or_gt u s with hus | hsu
    · have hempty : {x | R s < ‖Aᶜ.indicator g x‖ₑ} = ∅ := by
        refine eq_empty_of_forall_notMem fun x (hx : R s < _) ↦ ?_
        by_cases hxA : x ∈ Aᶜ
        · rw [indicator_of_mem hxA] at hx
          exact hxA hx
        · simp only [indicator_of_notMem hxA, eNorm_zero, ENNReal.not_lt_zero] at hx
      refine le_add_right ((μ.decreasingRearrangement_le_iff.2 ?_).trans_eq
        (indicator_of_mem (show u ∈ Ioc 0 s from ⟨hu, hus⟩) _).symm)
      rw [hempty, measure_empty]
      exact zero_le
    · refine le_add_left ((μ.decreasingRearrangement_mono (fun x ↦ ?_) u).trans
        (le_tsum_indicator_Ico (μ.antitone_decreasingRearrangement _) hs hsu.le))
      rw [eNorm_indicator_eq_indicator_eNorm]
      exact indicator_le_self _ _ x
  rw [← eLpNorm_eNorm _ (hg.indicator hA).aestronglyMeasurable,
    ← μ.eLpNorm_decreasingRearrangement hφ.aemeasurable]
  refine (eLpNorm_mono_eNorm_ae (g := M₀ + M₁)
    (μ.measurable_decreasingRearrangement _).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun u hu ↦ ?_)).trans
    ((eLpNorm_add_le hr).trans (add_le_add ?_ ((eLpNorm_tsum_indicator_le
      (fun _ ↦ measurableSet_Ico) _ hr _).trans (tsum_le_tsum fun n ↦ ?_))))
  · simpa only [eNorm_eq_self] using hle u hu
  · refine (eLpNorm_indicator_const_le _ r measurableSet_Ioc.nullMeasurableSet).trans ?_
    rw [eNorm_eq_self]
    gcongr
    exact restrict_Ioi_rpow_le hs.le (by rw [Real.volume_Ioc, sub_zero]) r
  · gcongr
    refine restrict_Ioi_rpow_le (by positivity) ?_ r
    rw [Real.volume_Ico, pow_succ]
    ring_nf

end Dyadic

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
    rw [hp, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₀t)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁t), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.2 hθ.2.le), ENNReal.toReal_ofReal hθ.1.le]
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
  have h₀ := eLpNorm_indicator_lt_le (μ := μ) (r := p₀) hg Fact.out hs
  have h₁ := eLpNorm_indicator_compl_le (μ := μ) (r := p₁) hg Fact.out hs
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
        rw [eLpNorm_comp_rpow_multHaar hK hδ q]
        refine le_mul_of_one_le_left zero_le ((ENNReal.one_rpow _).symm.le.trans
          (ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg))
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hδ).2 hδ₁)
    _ ≤ eLpNorm (fun s ↦ ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ (θ * δ)) ^ n * F (2⁻¹ ^ n * s) +
          ∑' n : ℕ, ENNReal.ofReal (2⁻¹ ^ ((1 - θ) * δ)) ^ n * F (2 ^ n * s)) q multHaar := by
        refine eLpNorm_mono_eNorm_ae ?_ (ae_pos_multHaar.mono fun s hs ↦
          (eNorm_rpow_neg_mul_kFunctional_le ha₀ ha₁ hg (hv.trans hf.ae_eq_mk) hs).trans_eq
            (eNorm_eq_self _).symm)
        have hK' : AEStronglyMeasurable
            (fun t ↦ t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t v) (multHaar.map (· ^ δ)) := by
          rw [map_multHaar_rpow hδ]
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
  have hptop : p ≠ ∞ := ENNReal.inv_ne_zero.1 (ENNReal.toReal_pos_iff.1 ha).1.ne'
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
