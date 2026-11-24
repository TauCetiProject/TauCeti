/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
public import TauCeti.Analysis.Normed.Interpolation.RealMethod.Basic
import TauCeti.Analysis.Normed.Interpolation.RealMethod.Lebesgue
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# `Lᵖ` inside the real interpolation spaces of the Lebesgue couple

Let `1 ≤ p₀ < p < p₁ < ∞` and `0 < θ < 1` with `1 / p = (1 - θ) / p₀ + θ / p₁`. This file proves
that `Lᵖ(μ; E)` embeds continuously in the real interpolation space `(L^{p₀}, L^{p₁})_{θ,q}` of the
Lebesgue couple for every secondary exponent `p₁ ≤ q ≤ ∞`, with the explicit bound

`‖f‖_{θ,q} ≤ 2 c_{θ,q} ‖f‖_p`,

where `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` is `TauCeti.CompatibleCouple.kMethodConst θ q`
(`TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le_two_mul_kMethodConst`,
`TauCeti.CompatibleCouple.lpToLebesgueKMethod`). The measure is arbitrary.

This is half of the identification `(L^{p₀}, L^{p₁})_{θ,q} = L^{p,q}` with the Lorentz space
(Bergh–Löfström, Theorem 5.3.1), in the range `q ≥ p₁` where it has an elementary proof by
truncation. That range contains the exponent `q = 2 ≥ p₁` of Keel and Tao's proof of the endpoint
Strichartz estimate, where `L^{r'}` with `r' < 2` has to be placed in the real interpolation space
of two nearby Lebesgue spaces before the bilinear interpolation theorem
`TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le` applies. The couple `(L¹, L^∞)`, where the
identification is complete, is treated with decreasing rearrangements in
`TauCeti.Analysis.Normed.Interpolation.Lorentz`. For general Lebesgue couples,
`TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le` covers the wider range `q ≥ p` with
the constant `(1 - 2^{-θδ})⁻¹ + (1 - 2^{-(1 - θ)δ})⁻¹`, `δ = 1 / p₀ - 1 / p₁`, which blows up as
`p₀` and `p₁` approach `p`; the constant `2 c_{θ,q}` here does not depend on `p₀` and `p₁`.

## The argument

Let `N = ‖f‖_p` and `γ = -θ p₀ / (p - p₀) < 0`. For `t > 0`, split `f` at the height `N t ^ γ`:
`f = f₀ + f₁`, where `f₀` is the part of `f` where `‖f‖ > N t ^ γ` and `f₁` the rest. Then `f₀`
lies in `L^{p₀}` because `p₀ < p`, `f₁` lies in `L^{p₁}` because `p < p₁`, and

`K(t, f) ≤ (∫_{‖f‖ > N t ^ γ} ‖f‖ ^ p₀) ^ (1 / p₀) + t (∫_{‖f‖ ≤ N t ^ γ} ‖f‖ ^ p₁) ^ (1 / p₁)`.

Integrating the `q`-th power against `t ^ (-q θ) dt / t`, Minkowski's integral inequality, in the
form `TauCeti.lintegral_mul_setLIntegral_rpow_le_of_le`, moves the powers `q / p₀ ≥ 1` and
`q / p₁ ≥ 1` inside the integrals over the space, and for a fixed point `x` the integrals in `t`
are elementary (`TauCeti.lintegral_indicator_ofReal_mul_rpow_lt_le`,
`TauCeti.lintegral_indicator_le_ofReal_mul_rpow_le`); together these are the endpoint estimates
`TauCeti.lintegral_mul_setLIntegral_ofReal_mul_rpow_lt_le` and
`TauCeti.lintegral_mul_setLIntegral_le_ofReal_mul_rpow_le`. The exponent `γ` is the one that turns
both terms into multiples of `∫ ‖f‖ ^ p`: the interpolation relation gives
`γ = -θ p₀ / (p - p₀) = (1 - θ) p₁ / (p - p₁)`, and the two terms contribute
`N ^ q / (q θ)` and `N ^ q / (q (1 - θ))`. Since `(x + y) ^ q ≤ 2 ^ (q - 1) (x ^ q + y ^ q)`,

`‖f‖_{θ,q} ^ q ≤ 2 ^ (q - 1) N ^ q / (q θ (1 - θ)) ≤ 2 ^ q c_{θ,q} ^ q N ^ q`.

For `q = ∞` the same splitting bounds each term by `N t ^ θ` pointwise. Minkowski's inequality is
where `q ≥ p₁` enters; it needs an s-finite measure, and since `f` lies in `Lᵖ` the measure
restricted to `{f ≠ 0}` is σ-finite (`TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`).

## Main declarations

* `TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le_two_mul_kMethodConst`:
  `‖f‖_{θ,q} ≤ 2 c_{θ,q} ‖f‖_p`.
* `TauCeti.CompatibleCouple.lpToLebesgueKMethod`: the continuous inclusion
  `Lᵖ → (L^{p₀}, L^{p₁})_{θ,q}`, of norm at most `2 c_{θ,q}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.3 (Theorem 5.3.1).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980,
  §6.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 E : Type*} {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p₀ p p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
  {θ : ℝ}

/-! ### Splitting at a height -/

section Split

variable (f : Lp E p μ)

/-- For `f ∈ Lᵖ` with `1 ≤ p < ∞`, `∫ ‖f‖ ^ p = ‖f‖_p ^ p`, with `‖f‖_p` written as `ofReal` of
its real value. -/
private theorem lintegral_enorm_rpow_eq_ofReal [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = ENNReal.ofReal (eLpNorm f p μ).toReal ^ p.toReal := by
  rw [ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  exact lintegral_rpow_enorm_eq_eLpNorm_rpow (zero_lt_one.trans_le Fact.out).ne' hp
    (Lp.aestronglyMeasurable f)

/-- **The `K`-functional of a split.** For `p₀ < p < p₁ < ∞` and a height `0 < h < ∞`, splitting
`f ∈ Lᵖ` into its parts above and below `h` bounds the `K`-functional of `f` in
`L^{p₀} + L^{p₁}`:

`K(t, f) ≤ (∫_{‖f‖ > h} ‖f‖ ^ p₀) ^ (1 / p₀) + t (∫_{‖f‖ ≤ h} ‖f‖ ^ p₁) ^ (1 / p₁)`. -/
private theorem ofReal_kFunctional_lpToLebesgueSum_le [Fact (1 ≤ p)] (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞) {t : ℝ} (ht : 0 ≤ t) {h : ℝ≥0∞} (hh : h ≠ 0) (hh' : h ≠ ∞) :
    ENNReal.ofReal ((lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)) ≤
      (∫⁻ x in {x | h < ‖f x‖ₑ}, ‖f x‖ₑ ^ p₀.toReal ∂μ) ^ (1 / p₀.toReal) +
        ENNReal.ofReal t *
          (∫⁻ x in {x | ‖f x‖ₑ ≤ h}, ‖f x‖ₑ ^ p₁.toReal ∂μ) ^ (1 / p₁.toReal) := by
  have hp₀ : p₀ ≠ ∞ := ne_top_of_lt h₀
  have ha : 0 < p₀.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp₀
  have hb : 0 < p₁.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp₁
  have hC (e : ℝ) : h ^ e * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    rw [lintegral_enorm_rpow_eq_ofReal f (ne_top_of_lt h₁)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hh hh')
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
  -- The two parts, with their norms.
  have hS₀ : MeasurableSet {x | h < ‖f x‖ₑ} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).eNorm
  have hS₁ : MeasurableSet {x | ‖f x‖ₑ ≤ h} :=
    measurableSet_le (Lp.stronglyMeasurable f).eNorm measurable_const
  have e₀ := eLpNorm_indicator_eq_setLIntegral_rpow (Lp.aestronglyMeasurable f)
    (zero_lt_one.trans_le Fact.out).ne' hp₀ hS₀.nullMeasurableSet
  have e₁ := eLpNorm_indicator_eq_setLIntegral_rpow (Lp.aestronglyMeasurable f)
    (zero_lt_one.trans_le Fact.out).ne' hp₁ hS₁.nullMeasurableSet
  have m₀ := memLp_indicator_of_setLIntegral_rpow_ne_top (Lp.aestronglyMeasurable f)
    (zero_lt_one.trans_le Fact.out).ne' hp₀ hS₀.nullMeasurableSet
    (ne_top_of_le_ne_top (hC _) (setLIntegral_lt_enorm_rpow_le (Lp.aestronglyMeasurable f) ha
      (ENNReal.toReal_mono (ne_top_of_lt h₁) h₀.le) h))
  have m₁ := memLp_indicator_of_setLIntegral_rpow_ne_top (Lp.aestronglyMeasurable f)
    (zero_lt_one.trans_le Fact.out).ne' hp₁ hS₁.nullMeasurableSet
    (ne_top_of_le_ne_top (hC _) (setLIntegral_enorm_le_rpow_le (Lp.aestronglyMeasurable f) hb
      (ENNReal.toReal_mono hp₁ h₁.le) h))
  -- They decompose `f`.
  have hsplit : lpToLebesgueSum h₀.le h₁.le f =
      (lebesgue 𝕜 E μ p₀ p₁).fstToSum (m₀.toLp _) +
        (lebesgue 𝕜 E μ p₀ p₁).sndToSum (m₁.toLp _) := by
    refine lpToLebesgueSum_eq_fstToSum_add_sndToSum h₀.le h₁.le ?_
    filter_upwards [m₀.coeFn_toLp, m₁.coeFn_toLp] with x hx₀ hx₁
    rw [Pi.add_apply, hx₀, hx₁]
    by_cases hx : h < ‖f x‖ₑ
    · simp [hx, not_le.2 hx]
    · simp [hx, not_lt.1 hx]
  calc ENNReal.ofReal ((lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f))
      ≤ ENNReal.ofReal (‖m₀.toLp _‖ + t * ‖m₁.toLp _‖) :=
        ENNReal.ofReal_le_ofReal (kFunctional_le ht hsplit.symm)
    _ = eLpNorm ({x | h < ‖f x‖ₑ}.indicator f) p₀ μ +
          ENNReal.ofReal t * eLpNorm ({x | ‖f x‖ₑ ≤ h}.indicator f) p₁ μ := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg ht (norm_nonneg _)),
          ENNReal.ofReal_mul ht, Lp.norm_toLp, Lp.norm_toLp, ENNReal.ofReal_toReal m₀.ne,
          ENNReal.ofReal_toReal m₁.ne]
    _ = _ := by rw [e₀, e₁]

end Split

/-- The integrand of the `q`-th power of the `K`-method norm against `dt / t`, bounded by the two
truncated integrals of a split at the height `h`, with `Q = q.toReal ≥ 1`. -/
private theorem ofReal_inv_mul_enorm_rpow_le [Fact (1 ≤ p)] (f : Lp E p μ) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞) {Q : ℝ} (hQ : 1 ≤ Q) {t : ℝ} (ht : 0 < t) {h : ℝ≥0∞} (hh : h ≠ 0)
    (hh' : h ≠ ∞) :
    ENNReal.ofReal t⁻¹ * ‖t ^ (-θ) *
        (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)‖ₑ ^ Q ≤
      2 ^ (Q - 1) * (ENNReal.ofReal (t ^ (-(Q * θ) - 1)) *
          (∫⁻ x in {x | h < ‖f x‖ₑ}, ‖f x‖ₑ ^ p₀.toReal ∂μ) ^ (Q / p₀.toReal) +
        ENNReal.ofReal (t ^ (Q - Q * θ - 1)) *
          (∫⁻ x in {x | ‖f x‖ₑ ≤ h}, ‖f x‖ₑ ^ p₁.toReal ∂μ) ^ (Q / p₁.toReal)) := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  set A := ∫⁻ x in {x | h < ‖f x‖ₑ}, ‖f x‖ₑ ^ p₀.toReal ∂μ
  set B := ∫⁻ x in {x | ‖f x‖ₑ ≤ h}, ‖f x‖ₑ ^ p₁.toReal ∂μ
  set K := (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)
  have hK := ofReal_kFunctional_lpToLebesgueSum_le (𝕜 := 𝕜) f h₀ h₁ hp₁ ht.le hh hh'
  -- Powers of `t` multiply as powers of `ofReal t`.
  have hpow : ∀ x : ℝ, ENNReal.ofReal (t ^ x) ^ Q = ENNReal.ofReal (t ^ (x * Q)) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hQ0, ← Real.rpow_mul ht.le]
  have hmul : ∀ x y : ℝ, ENNReal.ofReal (t ^ x) * ENNReal.ofReal (t ^ y) =
      ENNReal.ofReal (t ^ (x + y)) := fun x y => by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
  have hinv : ENNReal.ofReal t⁻¹ = ENNReal.ofReal (t ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one]
  have hone : ENNReal.ofReal t = ENNReal.ofReal (t ^ (1 : ℝ)) := by rw [Real.rpow_one]
  have hroot : ∀ (I : ℝ≥0∞) (e : ℝ), (I ^ (1 / e)) ^ Q = I ^ (Q / e) := fun I e => by
    rw [← ENNReal.rpow_mul, one_div_mul_eq_div]
  -- The powers of `t` in front of each summand combine into a single power.
  have e₀ : ENNReal.ofReal t⁻¹ * ENNReal.ofReal (t ^ (-θ)) ^ Q =
      ENNReal.ofReal (t ^ (-(Q * θ) - 1)) := by
    rw [hinv, hpow, hmul]
    congr 2
    ring
  have e₁ : ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (-θ)) ^ Q * ENNReal.ofReal t ^ Q) =
      ENNReal.ofReal (t ^ (Q - Q * θ - 1)) := by
    rw [hinv, hone, hpow, hpow, hmul, hmul]
    congr 2
    ring
  calc ENNReal.ofReal t⁻¹ * ‖t ^ (-θ) * K‖ₑ ^ Q
      ≤ ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (-θ)) * A ^ (1 / p₀.toReal) +
          ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal t * B ^ (1 / p₁.toReal)) ^ Q := by
        rw [Real.eNorm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
          (kFunctional_nonneg ht.le)), ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
        gcongr
        calc ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal K
            ≤ ENNReal.ofReal (t ^ (-θ)) * (A ^ (1 / p₀.toReal) +
                ENNReal.ofReal t * B ^ (1 / p₁.toReal)) := by gcongr
          _ = _ := by ring
    _ ≤ ENNReal.ofReal t⁻¹ * (2 ^ (Q - 1) * ((ENNReal.ofReal (t ^ (-θ)) * A ^ (1 / p₀.toReal)) ^ Q +
          (ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal t * B ^ (1 / p₁.toReal)) ^ Q)) := by
        gcongr
        exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hQ
    _ = 2 ^ (Q - 1) * (ENNReal.ofReal t⁻¹ * ENNReal.ofReal (t ^ (-θ)) ^ Q * A ^ (Q / p₀.toReal) +
          ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (-θ)) ^ Q * ENNReal.ofReal t ^ Q) *
            B ^ (Q / p₁.toReal)) := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hQ0, hroot]
        ring
    _ = _ := by rw [e₀, e₁]

/-! ### The exponents -/

/-- The height exponent `γ = -θ a / (r - a)` satisfies `γ (a - r) / a = θ` and, by the
interpolation relation `1 / r = (1 - θ) / a + θ / b`, also `γ (b - r) / b = θ - 1`. -/
private theorem height_exponent_spec {a r b : ℝ} (ha : 0 < a) (har : a < r) (hrb : r < b)
    (hrel : r⁻¹ = (1 - θ) * a⁻¹ + θ * b⁻¹) :
    -(θ * a) / (r - a) * (a - r) / a = θ ∧ -(θ * a) / (r - a) * (b - r) / b = θ - 1 := by
  have hr : 0 < r := ha.trans har
  have hb : 0 < b := hr.trans hrb
  have hra : r - a ≠ 0 := (sub_pos.2 har).ne'
  have hab : a * b = r * ((1 - θ) * b + θ * a) := by
    field_simp at hrel
    linarith
  constructor
  · field_simp
    ring
  · field_simp
    linear_combination -hab

/-- The data of the split of `f ∈ Lᵖ` at the height `‖f‖_p t ^ γ`, for `1 ≤ p₀ < p < p₁ < ∞` with
`1 / p = (1 - θ) / p₀ + θ / p₁` and `γ = -θ p₀ / (p - p₀)`: the real exponents are positive and in
order, `γ` satisfies the two relations of `height_exponent_spec`, and `c = ‖f‖_p` is positive with
`∫ ‖f‖ ^ p = c ^ p`. -/
private theorem toReal_exponents_and_norm [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ)
    (hN : eLpNorm f p μ ≠ 0) :
    0 < p₀.toReal ∧ p₀.toReal < p.toReal ∧ p.toReal < p₁.toReal ∧
      -(θ * p₀.toReal) / (p.toReal - p₀.toReal) * (p₀.toReal - p.toReal) / p₀.toReal = θ ∧
      -(θ * p₀.toReal) / (p.toReal - p₀.toReal) * (p₁.toReal - p.toReal) / p₁.toReal = θ - 1 ∧
      0 < (eLpNorm f p μ).toReal ∧
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = ENNReal.ofReal (eLpNorm f p μ).toReal ^ p.toReal := by
  have ha : 0 < p₀.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' (ne_top_of_lt h₀)
  have har : p₀.toReal < p.toReal := ENNReal.toReal_strict_mono (ne_top_of_lt h₁) h₀
  have hrb : p.toReal < p₁.toReal := ENNReal.toReal_strict_mono hp₁ h₁
  obtain ⟨hγa, hγb⟩ := height_exponent_spec ha har hrb
    (inv_toReal_eq_of_inv_eq (zero_lt_one.trans_le Fact.out).ne'
      (zero_lt_one.trans_le Fact.out).ne' (Ioo_subset_Icc_self hθ) hp)
  exact ⟨ha, har, hrb, hγa, hγb, ENNReal.toReal_pos hN (Lp.eLpNorm_ne_top f),
    lintegral_enorm_rpow_eq_ofReal f (ne_top_of_lt h₁)⟩

/-! ### The estimate -/

/-- The constant of the two endpoints together: since
`c ^ (Q (e - r) / e) (c ^ r) ^ (Q / e) = c ^ Q` for `e = a, b`, the two terms add up to
`2 ^ (Q - 1) c ^ Q / (Q θ (1 - θ))`. -/
private theorem two_rpow_mul_add_eq {c a r b Q : ℝ} (hc : 0 < c) (ha : a ≠ 0) (hb : b ≠ 0)
    (hQ : 0 < Q) (hθ : θ ∈ Ioo 0 1) :
    2 ^ (Q - 1) * (ENNReal.ofReal (c ^ (Q * (a - r) / a) / (Q * θ)) *
          (ENNReal.ofReal c ^ r) ^ (Q / a) +
        ENNReal.ofReal (c ^ (Q * (b - r) / b) / (Q - Q * θ)) *
          (ENNReal.ofReal c ^ r) ^ (Q / b)) =
      ENNReal.ofReal (2 ^ (Q - 1) / (Q * θ * (1 - θ))) * ENNReal.ofReal c ^ Q := by
  have hD₀ : 0 < Q * θ := mul_pos hQ hθ.1
  have hD₁ : 0 < Q - Q * θ := by nlinarith [hθ.2]
  have hcQ : 0 ≤ c ^ Q := Real.rpow_nonneg hc.le Q
  -- Each term is `c ^ Q` over its denominator.
  have hterm (e D : ℝ) (he : e ≠ 0) :
      ENNReal.ofReal (c ^ (Q * (e - r) / e) / D) * (ENNReal.ofReal c ^ r) ^ (Q / e) =
        ENNReal.ofReal (c ^ Q / D) := by
    have hexp : Q * (e - r) / e + r * (Q / e) = Q := by
      field_simp
      ring
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos hc,
      ← ENNReal.ofReal_mul' (Real.rpow_nonneg hc.le _), div_mul_eq_mul_div,
      ← Real.rpow_add hc, hexp]
  calc _ = 2 ^ (Q - 1) *
        (ENNReal.ofReal (c ^ Q / (Q * θ)) + ENNReal.ofReal (c ^ Q / (Q - Q * θ))) := by
        rw [hterm a _ ha, hterm b _ hb]
    _ = ENNReal.ofReal (2 ^ (Q - 1) * (c ^ Q / (Q * θ) + c ^ Q / (Q - Q * θ))) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (div_nonneg hcQ hD₀.le) (div_nonneg hcQ hD₁.le),
          ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal (2 ^ (Q - 1) / (Q * θ * (1 - θ)) * c ^ Q) := by
        rw [show Q - Q * θ = Q * (1 - θ) by ring]
        congr 1
        field_simp [hQ.ne', hθ.1.ne', (sub_pos.2 hθ.2).ne']
        ring
    _ = _ := by
        rw [ENNReal.ofReal_mul (div_nonneg (by positivity) (mul_pos hD₀ (sub_pos.2 hθ.2)).le),
          ENNReal.ofReal_rpow_of_pos hc]

/-- **The `K`-method integral against `dt / t` of a split.** If `g` has `∫ g ^ r = c ^ r`, then the
two weighted truncated integrals of `g` at the height `c t ^ γ` add up to at most
`2 ^ (Q - 1) c ^ Q / (Q θ (1 - θ))`. Each is bounded by Minkowski's integral inequality and the
elementary integral in `t` (`TauCeti.lintegral_mul_setLIntegral_ofReal_mul_rpow_lt_le`,
`TauCeti.lintegral_mul_setLIntegral_le_ofReal_mul_rpow_le`). -/
private theorem setLIntegral_Ioi_two_mul_add_le {ν : Measure α} [SFinite ν] {g : α → ℝ≥0∞}
    (hg : Measurable g) {a r b Q γ c : ℝ} (ha : 0 < a) (har : a < r) (hrb : r < b) (hbQ : b ≤ Q)
    (hθ : θ ∈ Ioo 0 1) (hγa : γ * (a - r) / a = θ) (hγb : γ * (b - r) / b = θ - 1) (hc : 0 < c)
    (hI : ∫⁻ x, g x ^ r ∂ν = ENNReal.ofReal c ^ r) :
    ∫⁻ t in Ioi (0 : ℝ), 2 ^ (Q - 1) *
        (ENNReal.ofReal (t ^ (-(Q * θ) - 1)) *
            (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < g x}, g x ^ a ∂ν) ^ (Q / a) +
          ENNReal.ofReal (t ^ (Q - Q * θ - 1)) *
            (∫⁻ x in {x | g x ≤ ENNReal.ofReal (c * t ^ γ)}, g x ^ b ∂ν) ^ (Q / b)) ≤
      ENNReal.ofReal (2 ^ (Q - 1) / (Q * θ * (1 - θ))) * ENNReal.ofReal c ^ Q := by
  have hb : 0 < b := (ha.trans har).trans hrb
  have hQ : 0 < Q := hb.trans_le hbQ
  have hγ : γ ≠ 0 := by
    rintro rfl
    simp only [zero_mul, zero_div] at hγa
    exact hθ.1.ne hγa
  -- The weight exponents are tied to `γ` as the two endpoint estimates require.
  have hγ₀ : (-(Q * θ) - 1 + 1) / γ = Q * (r - a) / a := by
    rw [sub_add_cancel, ← hγa]
    field_simp
    ring
  have hγ₁ : (Q - Q * θ - 1 + 1) / γ = Q * (r - b) / b := by
    rw [sub_add_cancel, show Q - Q * θ = -Q * (θ - 1) by ring, ← hγb]
    field_simp
    ring
  have hb₀ := lintegral_mul_setLIntegral_ofReal_mul_rpow_lt_le (μ := ν) hg hc ha
    (har.le.trans (hrb.le.trans hbQ)) har hγ₀
  have hb₁ := lintegral_mul_setLIntegral_le_ofReal_mul_rpow_le (μ := ν) hg hc hb hbQ hrb hγ₁
  rw [hI, sub_add_cancel, abs_neg, abs_of_pos (mul_pos hQ hθ.1)] at hb₀
  rw [hI, sub_add_cancel, abs_of_pos (by nlinarith [hθ.2] : 0 < Q - Q * θ)] at hb₁
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top),
    lintegral_add_left (measurable_ofReal_rpow_mul_setLIntegral_rpow
      (measurableSet_ofReal_mul_rpow_lt hg c γ) hg.aemeasurable _ _ _),
    ← two_rpow_mul_add_eq hc ha.ne' hb.ne' hQ hθ]
  gcongr

/-- **The `K`-method integral of `f ∈ Lᵖ`.** For `p₁ ≤ Q < ∞`,
`∫ (t ^ (-θ) K(t, f)) ^ Q dt / t ≤ 2 ^ (Q - 1) ‖f‖_p ^ Q / (Q θ (1 - θ))`. The measure is reduced
to its σ-finite part `μ'` carrying `f`, where Minkowski's inequality applies. -/
private theorem lintegral_multHaar_enorm_rpow_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {Q : ℝ}
    (hbQ : p₁.toReal ≤ Q) (f : Lp E p μ) (hN : eLpNorm f p μ ≠ 0) :
    ∫⁻ t, ‖t ^ (-θ) *
        (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)‖ₑ ^ Q ∂multHaar ≤
      ENNReal.ofReal (2 ^ (Q - 1) / (Q * θ * (1 - θ))) * eLpNorm f p μ ^ Q := by
  obtain ⟨ha, har, hrb, hγa, hγb, hc, hI⟩ := toReal_exponents_and_norm hθ h₀ h₁ hp₁ hp f hN
  have hQ1 : 1 ≤ Q := le_trans (by simpa using ENNReal.toReal_mono hp₁ (Fact.out : 1 ≤ p₁)) hbQ
  set c := (eLpNorm f p μ).toReal
  have hNc : eLpNorm f p μ = ENNReal.ofReal c :=
    (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)).symm
  set g : α → ℝ≥0∞ := fun x => ‖f x‖ₑ
  have hg : Measurable g := (Lp.stronglyMeasurable f).eNorm
  have hr : 0 < p.toReal := ha.trans har
  have : SigmaFinite (μ.restrict {x | 0 < g x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hg.aemeasurable hr
      (hI ▸ ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
  rw [hNc, lintegral_multHaar_eq_setLIntegral]
  refine (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_).trans
    (setLIntegral_Ioi_two_mul_add_le (ν := μ.restrict {x | 0 < g x}) hg ha har hrb hbQ hθ hγa hγb
      hc (by rw [← hI]; exact lintegral_rpow_restrict_pos hg hr))
  simpa only [setLIntegral_rpow_restrict_pos hg ha,
    setLIntegral_rpow_restrict_pos hg (ha.trans (har.trans hrb))] using
    ofReal_inv_mul_enorm_rpow_le f h₀ h₁ hp₁ hQ1 ht
      (ENNReal.ofReal_pos.2 (mul_pos hc (Real.rpow_pos_of_pos ht _))).ne' ENNReal.ofReal_ne_top

/-- The height `c t ^ γ` raised to the power `(s - r) / s` and multiplied by `c ^ (r / s)`:
`((c t ^ γ) ^ (s - r) c ^ r) ^ (1 / s) = c t ^ (γ (s - r) / s)`. -/
private theorem rpow_sub_mul_rpow_rpow_eq {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (γ r : ℝ) {s : ℝ}
    (hs : s ≠ 0) :
    ((c * t ^ γ) ^ (s - r) * c ^ r) ^ (1 / s) = c * t ^ (γ * (s - r) / s) := by
  -- The powers of `c` combine to `c ^ s`, and the power of `t` is an `s`-th power.
  have hc' : (c * t ^ γ) ^ (s - r) * c ^ r = c ^ s * t ^ (γ * (s - r)) := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul ht.le, mul_right_comm,
      ← Real.rpow_add hc, sub_add_cancel]
  have ht' : t ^ (γ * (s - r)) = (t ^ (γ * (s - r) / s)) ^ s := by
    rw [← Real.rpow_mul ht.le, div_mul_cancel₀ _ hs]
  rw [hc', ht', ← Real.mul_rpow hc.le (by positivity), one_div,
    Real.rpow_rpow_inv (by positivity) hs]

/-- Each part of the split of `f ∈ Lᵖ` at the height `c t ^ γ`, with `c = ‖f‖_p`, has norm at
most `c t ^ (γ (s - p) / s)` in `Lˢ`. -/
private theorem setLIntegral_rpow_rpow_le {c t γ s : ℝ} (hc : 0 < c) (ht : 0 < t) (hs : 0 < s)
    {I : ℝ≥0∞}
    (hI : I ≤ ENNReal.ofReal (c * t ^ γ) ^ (s - p.toReal) * ENNReal.ofReal c ^ p.toReal) :
    I ^ (1 / s) ≤ ENNReal.ofReal (c * t ^ (γ * (s - p.toReal) / s)) := by
  have hh : 0 < c * t ^ γ := mul_pos hc (Real.rpow_pos_of_pos ht _)
  rw [← rpow_sub_mul_rpow_rpow_eq hc ht γ _ hs.ne', ← ENNReal.ofReal_rpow_of_nonneg
    (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos hh, ← ENNReal.ofReal_rpow_of_pos hc]
  gcongr

/-- **The pointwise bound behind `q = ∞`.** For `t > 0`, `t ^ (-θ) K(t, f) ≤ 2 ‖f‖_p`. -/
private theorem rpow_neg_mul_kFunctional_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (f : Lp E p μ)
    (hN : eLpNorm f p μ ≠ 0) {t : ℝ} (ht : 0 < t) :
    t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f) ≤
      2 * (eLpNorm f p μ).toReal := by
  obtain ⟨ha, har, hrb, hγa, hγb, hc, hI⟩ := toReal_exponents_and_norm hθ h₀ h₁ hp₁ hp f hN
  set γ := -(θ * p₀.toReal) / (p.toReal - p₀.toReal)
  set c := (eLpNorm f p μ).toReal
  have hh : 0 < c * t ^ γ := mul_pos hc (Real.rpow_pos_of_pos ht _)
  -- Each part of the split at the height `c t ^ γ` contributes at most `c t ^ θ`.
  have hA := setLIntegral_rpow_rpow_le (γ := γ) hc ht ha
    ((setLIntegral_lt_enorm_rpow_le (Lp.aestronglyMeasurable f) ha har.le _).trans_eq
      (by rw [hI]))
  have hB := setLIntegral_rpow_rpow_le (γ := γ) hc ht ((ha.trans har).trans hrb)
    ((setLIntegral_enorm_le_rpow_le (Lp.aestronglyMeasurable f)
      ((ha.trans har).trans hrb) hrb.le _).trans_eq (by rw [hI]))
  rw [hγa] at hA
  rw [hγb] at hB
  have hK : (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f) ≤
      c * t ^ θ + t * (c * t ^ (θ - 1)) := by
    have hK := (ofReal_kFunctional_lpToLebesgueSum_le (𝕜 := 𝕜) f h₀ h₁ hp₁ ht.le
      (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top).trans
        (add_le_add hA (mul_le_mul_right hB _))
    rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hK
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hK
  have hsum : c * t ^ θ + t * (c * t ^ (θ - 1)) = 2 * (c * t ^ θ) := by
    rw [Real.rpow_sub_one ht.ne']
    field_simp
    ring
  calc t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)
      ≤ t ^ (-θ) * (2 * (c * t ^ θ)) := by
        rw [← hsum]
        gcongr
    _ = 2 * c := by
        rw [Real.rpow_neg ht.le]
        field_simp

/-! ### The embedding -/

/-- **`Lᵖ` lies in the real interpolation spaces of `(L^{p₀}, L^{p₁})`.** For
`1 ≤ p₀ < p < p₁ < ∞` and `0 < θ < 1` with `1 / p = (1 - θ) / p₀ + θ / p₁`, and every secondary
exponent `p₁ ≤ q ≤ ∞`,

`‖f‖_{(L^{p₀}, L^{p₁})_{θ,q}} ≤ 2 c_{θ,q} ‖f‖_p`,

where `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` is `TauCeti.CompatibleCouple.kMethodConst θ q`. -/
theorem kMethodENorm_lpToLebesgueSum_le_two_mul_kMethodConst [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1)
    (h₀ : p₀ < p) (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    (hq : p₁ ≤ q) (f : Lp E p μ) :
    (lebesgue 𝕜 E μ p₀ p₁).kMethodENorm θ q (lpToLebesgueSum h₀.le h₁.le f) ≤
      2 * kMethodConst θ q * eLpNorm f p μ := by
  rcases eq_or_ne (eLpNorm f p μ) 0 with hN | hN
  · rw [norm_eq_zero.1 (by rw [Lp.norm_def, hN, ENNReal.toReal_zero] : ‖f‖ = 0)]
    simp
  rcases eq_or_ne q ∞ with rfl | hq'
  · -- For `q = ∞` the pointwise bound is the whole estimate.
    rw [kMethodConst_top (Ioo_subset_Icc_self hθ), mul_one]
    refine (kMethodENorm_le_eLpNorm_of_le fun t ht =>
      rpow_neg_mul_kFunctional_le hθ h₀ h₁ hp₁ hp f hN ht).trans_eq ?_
    have hμ : multHaar ≠ 0 := fun h0 => by simpa [h0] using multHaar_Icc_one_exp_one
    rw [eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_const _ hμ,
      Real.eNorm_eq_ofReal (by positivity), ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  -- For finite `q`, take the `q`-th root of the bound on the `K`-method integral.
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le ((Fact.out : 1 ≤ p₁).trans hq)).ne'
  set Q := q.toReal
  have hbQ : p₁.toReal ≤ Q := ENNReal.toReal_mono hq' hq
  have hQ : 0 < Q := ENNReal.toReal_pos hq0 hq'
  have hD : 0 < Q * θ * (1 - θ) := mul_pos (mul_pos hQ hθ.1) (sub_pos.2 hθ.2)
  rw [kMethodENorm_def, eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq'
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ _)]
  refine (ENNReal.rpow_le_rpow (lintegral_multHaar_enorm_rpow_le hθ h₀ h₁ hp₁ hp hbQ f hN)
    (by positivity)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hQ.ne', ENNReal.rpow_one, kMethodConst_eq hθ hq0 hq']
  gcongr ?_ * _
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `(2 ^ (Q - 1) / D) ^ (1 / Q) = 2 ^ ((Q - 1) / Q) D ^ (-1 / Q)` with `2 ^ ((Q - 1) / Q) ≤ 2`.
  rw [Real.div_rpow (by positivity) hD.le, show θ * (1 - θ) * Q = Q * θ * (1 - θ) by ring,
    Real.rpow_neg hD.le, one_div, div_eq_mul_inv]
  gcongr
  rw [← Real.rpow_mul zero_le_two]
  calc (2 : ℝ) ^ ((Q - 1) * Q⁻¹) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by
          rw [← div_eq_mul_inv, div_le_one hQ]; linarith)
    _ = 2 := Real.rpow_one 2

private theorem norm_mk_lpToLebesgueSum_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : p₁ ≤ q) (f : Lp E p μ) :
    ‖KMethodSpace.mk (lpToLebesgueSum h₀.le h₁.le f)
        (lpToLebesgueSum_mem_kMethod (𝕜 := 𝕜) hθ (h₀.trans h₁) hp (h₁.le.trans hq) h₀.le h₁.le
          f)‖ ≤
      2 * (kMethodConst θ q).toReal * ‖f‖ := by
  rw [KMethodSpace.norm_mk, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (kMethodConst_lt_top hθ q).ne) (Lp.eLpNorm_ne_top f))
    (kMethodENorm_lpToLebesgueSum_le_two_mul_kMethodConst hθ h₀ h₁ hp₁ hp hq f)

variable (𝕜 E μ θ) in
/-- For `1 ≤ p₀ < p < p₁ < ∞`, `0 < θ < 1` with `1 / p = (1 - θ) / p₀ + θ / p₁` and
`p₁ ≤ q ≤ ∞`, the continuous inclusion `Lᵖ → (L^{p₀}, L^{p₁})_{θ,q}`, of norm at most
`2 c_{θ,q}` (`TauCeti.CompatibleCouple.norm_lpToLebesgueKMethod_le`). -/
noncomputable def lpToLebesgueKMethod [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (hq : p₁ ≤ q) :
    Lp E p μ →L[𝕜] (lebesgue 𝕜 E μ p₀ p₁).KMethodSpace θ q :=
  LinearMap.mkContinuous
    { toFun f := KMethodSpace.mk (lpToLebesgueSum h₀.le h₁.le f)
        (lpToLebesgueSum_mem_kMethod hθ (h₀.trans h₁) hp (h₁.le.trans hq) h₀.le h₁.le f)
      map_add' f g := by ext; simp
      map_smul' c f := by ext; simp }
    (2 * (kMethodConst θ q).toReal) (norm_mk_lpToLebesgueSum_le hθ h₀ h₁ hp₁ hp hq)

@[simp]
theorem toSumₗ_lpToLebesgueKMethod [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : p₁ ≤ q) (f : Lp E p μ) :
    KMethodSpace.toSumₗ (lpToLebesgueKMethod 𝕜 E μ θ hθ h₀ h₁ hp₁ hp q hq f) =
      lpToLebesgueSum h₀.le h₁.le f :=
  KMethodSpace.toSumₗ_mk _ _

/-- The norm of `f ∈ Lᵖ` in `(L^{p₀}, L^{p₁})_{θ,q}` is at most `2 c_{θ,q} ‖f‖_p`. -/
theorem norm_lpToLebesgueKMethod_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : p₁ ≤ q) (f : Lp E p μ) :
    ‖lpToLebesgueKMethod 𝕜 E μ θ hθ h₀ h₁ hp₁ hp q hq f‖ ≤ 2 * (kMethodConst θ q).toReal * ‖f‖ :=
  norm_mk_lpToLebesgueSum_le hθ h₀ h₁ hp₁ hp hq f

end TauCeti.CompatibleCouple
