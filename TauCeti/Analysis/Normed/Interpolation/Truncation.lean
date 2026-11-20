/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
public import TauCeti.Analysis.Normed.Interpolation.RealMethod
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# `Lᵖ` inside the real interpolation spaces of the Lebesgue couple

Let `1 ≤ p₀ < p < p₁ < ∞` and `0 < θ < 1` with `1 / p = (1 - θ) / p₀ + θ / p₁`. This file proves
that `Lᵖ(μ; E)` embeds continuously in the real interpolation space `(L^{p₀}, L^{p₁})_{θ,q}` of the
Lebesgue couple for every secondary exponent `p₁ ≤ q ≤ ∞`, with the explicit bound

`‖f‖_{θ,q} ≤ 2 c_{θ,q} ‖f‖_p`,

where `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` is `TauCeti.CompatibleCouple.kMethodConst θ q`
(`TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le`,
`TauCeti.CompatibleCouple.lpToLebesgueKMethod`). The measure is arbitrary.

This is half of the identification `(L^{p₀}, L^{p₁})_{θ,q} = L^{p,q}` with the Lorentz space
(Bergh–Löfström, Theorem 5.3.1), in the range `q ≥ p₁` where it has an elementary proof by
truncation. That range contains the exponent `q = 2 ≥ p₁` of Keel and Tao's proof of the endpoint
Strichartz estimate, where `L^{r'}` with `r' < 2` has to be placed in the real interpolation space
of two nearby Lebesgue spaces before the bilinear interpolation theorem
`TauCeti.CompatibleCouple.kMethodENorm_apply_apply_le` applies. The couple `(L¹, L^∞)`, where the
identification is complete, is treated with decreasing rearrangements in
`TauCeti.Analysis.Normed.Interpolation.Lorentz`.

## The argument

Let `N = ‖f‖_p` and `γ = -θ p₀ / (p - p₀) < 0`. For `t > 0`, split `f` at the height `N t ^ γ`:
`f = f₀ + f₁`, where `f₀` is the part of `f` where `‖f‖ > N t ^ γ` and `f₁` the rest. Then `f₀`
lies in `L^{p₀}` because `p₀ < p`, `f₁` lies in `L^{p₁}` because `p < p₁`, and

`K(t, f) ≤ (∫_{‖f‖ > N t ^ γ} ‖f‖ ^ p₀) ^ (1 / p₀) + t (∫_{‖f‖ ≤ N t ^ γ} ‖f‖ ^ p₁) ^ (1 / p₁)`.

Integrating the `q`-th power against `t ^ (-q θ) dt / t`, Minkowski's integral inequality, in the
form `TauCeti.lintegral_mul_setLIntegral_rpow_le_of_le`, moves the powers `q / p₀ ≥ 1` and
`q / p₁ ≥ 1` inside the integrals over the space, and for a fixed point `x` the integrals in `t`
are elementary (`TauCeti.lintegral_indicator_ofReal_mul_rpow_lt_le`,
`TauCeti.lintegral_indicator_le_ofReal_mul_rpow_le`). The exponent `γ` is the one that turns both
terms into multiples of `∫ ‖f‖ ^ p`: the interpolation relation gives
`γ = -θ p₀ / (p - p₀) = (1 - θ) p₁ / (p - p₁)`, and the two terms contribute
`N ^ q / (q θ)` and `N ^ q / (q (1 - θ))`. Since `(x + y) ^ q ≤ 2 ^ (q - 1) (x ^ q + y ^ q)`,

`‖f‖_{θ,q} ^ q ≤ 2 ^ (q - 1) N ^ q / (q θ (1 - θ)) ≤ 2 ^ q c_{θ,q} ^ q N ^ q`.

For `q = ∞` the same splitting bounds each term by `N t ^ θ` pointwise. Minkowski's inequality is
where `q ≥ p₁` enters; it needs an s-finite measure, and since `f` lies in `Lᵖ` the measure
restricted to `{f ≠ 0}` is σ-finite (`TauCeti.sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top`).

## Main declarations

* `TauCeti.CompatibleCouple.kMethodENorm_lpToLebesgueSum_le`: `‖f‖_{θ,q} ≤ 2 c_{θ,q} ‖f‖_p`.
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

/-- Above a height `h`, the power `‖f‖ ^ s` with `0 < s ≤ p` is at most `h ^ (s - p) ‖f‖ ^ p`. -/
private theorem setLIntegral_lt_enorm_rpow_le {s : ℝ} (hs : 0 < s) (hsp : s ≤ p.toReal)
    (h : ℝ≥0∞) :
    ∫⁻ x in {x | h < ‖f x‖ₑ}, ‖f x‖ₑ ^ s ∂μ ≤
      h ^ (s - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  rw [← lintegral_const_mul _ (((Lp.stronglyMeasurable f).eNorm).pow_const _)]
  refine (setLIntegral_mono' (measurableSet_lt measurable_const ((Lp.stronglyMeasurable f).eNorm))
    fun x hx => ?_).trans (setLIntegral_le_lintegral _ _)
  exact ENNReal.rpow_le_rpow_sub_mul_rpow hs eNorm_ne_top
    (ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hx) (sub_nonpos.2 hsp))

/-- Up to a height `h`, the power `‖f‖ ^ s` with `p ≤ s` is at most `h ^ (s - p) ‖f‖ ^ p`. -/
private theorem setLIntegral_enorm_le_rpow_le {s : ℝ} (hs : 0 < s) (hsp : p.toReal ≤ s)
    (h : ℝ≥0∞) :
    ∫⁻ x in {x | ‖f x‖ₑ ≤ h}, ‖f x‖ₑ ^ s ∂μ ≤
      h ^ (s - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  rw [← lintegral_const_mul _ (((Lp.stronglyMeasurable f).eNorm).pow_const _)]
  refine (setLIntegral_mono' (measurableSet_le ((Lp.stronglyMeasurable f).eNorm) measurable_const)
    fun x hx => ?_).trans (setLIntegral_le_lintegral _ _)
  exact ENNReal.rpow_le_rpow_sub_mul_rpow hs eNorm_ne_top
    (ENNReal.rpow_le_rpow hx (sub_nonneg.2 hsp))

/-- The part of `f` on a measurable set `S` has `L^s` norm `(∫_S ‖f‖ ^ s) ^ (1 / s)` for
`0 < s < ∞`, and lies in `Lˢ` when that integral is finite. -/
private theorem eLpNorm_indicator_eq_and_memLp {s : ℝ≥0∞} (hs0 : s ≠ 0) (hs : s ≠ ∞) {S : Set α}
    (hS : MeasurableSet S) (hfin : ∫⁻ x in S, ‖f x‖ₑ ^ s.toReal ∂μ ≠ ∞) :
    eLpNorm (S.indicator f) s μ = (∫⁻ x in S, ‖f x‖ₑ ^ s.toReal ∂μ) ^ (1 / s.toReal) ∧
      MemLp (S.indicator f) s μ := by
  have e : eLpNorm (S.indicator f) s μ = (∫⁻ x in S, ‖f x‖ₑ ^ s.toReal ∂μ) ^ (1 / s.toReal) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hs0 hs (Lp.aestronglyMeasurable f).restrict]
  exact ⟨e, by rw [MemLp, e]; exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin⟩

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
  have hC : h ^ (p₀.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ ∧
      h ^ (p₁.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≠ ∞ := by
    rw [lintegral_rpow_enorm_eq_eLpNorm_rpow (zero_lt_one.trans_le Fact.out).ne'
      (ne_top_of_lt h₁) (Lp.aestronglyMeasurable f)]
    exact ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hh hh')
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (Lp.eLpNorm_ne_top f)),
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hh hh')
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (Lp.eLpNorm_ne_top f))⟩
  -- The two parts, with their norms.
  obtain ⟨e₀, m₀⟩ := eLpNorm_indicator_eq_and_memLp f (zero_lt_one.trans_le Fact.out).ne' hp₀
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable f).eNorm)
    (ne_top_of_le_ne_top hC.1 (setLIntegral_lt_enorm_rpow_le f ha
      (ENNReal.toReal_mono (ne_top_of_lt h₁) h₀.le) h))
  obtain ⟨e₁, m₁⟩ := eLpNorm_indicator_eq_and_memLp f (zero_lt_one.trans_le Fact.out).ne' hp₁
    (measurableSet_le (Lp.stronglyMeasurable f).eNorm measurable_const)
    (ne_top_of_le_ne_top hC.2 (setLIntegral_enorm_le_rpow_le f hb
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
    _ = _ := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hQ0, hroot]
        rw [hone, hpow, hpow, hinv, mul_left_comm, mul_add, ← mul_assoc, ← mul_assoc, hmul,
          hmul, hmul]
        congr 4 <;> ring_nf

/-! ### The exponents -/

omit [Fact (1 ≤ p₁)] in
/-- The real exponents of `1 ≤ p₀ < p < p₁ < ∞` are positive and in the same order. -/
private theorem toReal_exponents (h₀ : p₀ < p) (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞) :
    0 < p₀.toReal ∧ p₀.toReal < p.toReal ∧ p.toReal < p₁.toReal :=
  ⟨ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' (ne_top_of_lt h₀),
    ENNReal.toReal_strict_mono (ne_top_of_lt h₁) h₀, ENNReal.toReal_strict_mono hp₁ h₁⟩

/-- The interpolation relation `1 / p = (1 - θ) / p₀ + θ / p₁` between the real exponents. -/
private theorem inv_toReal_eq (hθ : θ ∈ Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    p.toReal⁻¹ = (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ := by
  have h := congrArg ENNReal.toReal (inv_eq_ofReal_of_inv_eq
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
    (Ioo_subset_Icc_self hθ) hp)
  have h1 : 0 ≤ 1 - θ := sub_nonneg.2 hθ.2.le
  have h2 : 0 ≤ θ := hθ.1.le
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_inv] at h

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

/-! ### The estimate -/

/-- One endpoint of the `K`-method integral: Minkowski's integral inequality and the elementary
integral in `t` for the part of `g` above the height `c t ^ γ`. -/
private theorem setLIntegral_Ioi_upper_le {ν : Measure α} [SFinite ν] {g : α → ℝ≥0∞}
    (hg : Measurable g) {a r Q γ c : ℝ} (ha : 0 < a) (har : a < r) (haQ : a ≤ Q) (hθ : 0 < θ)
    (hγ : γ * (a - r) / a = θ) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(Q * θ) - 1)) *
        (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < g x}, g x ^ a ∂ν) ^ (Q / a) ≤
      ENNReal.ofReal (c ^ (-(Q * (r - a) / a)) / (Q * θ)) * (∫⁻ x, g x ^ r ∂ν) ^ (Q / a) := by
  have hQ : 0 < Q := ha.trans_le haQ
  have hγ0 : γ ≠ 0 := by rintro rfl; simp at hγ; exact hθ.ne' hγ.symm
  have hγ' : (-(Q * θ) - 1 + 1) / γ = Q * (r - a) / a := by
    rw [sub_add_cancel, ← hγ]
    field_simp
    ring
  have hR : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1 ^ γ) < g z.2} :=
    measurableSet_lt ((measurable_fst.pow_const γ).const_mul c).ennreal_ofReal
      (hg.comp measurable_snd)
  refine lintegral_mul_setLIntegral_rpow_le_of_le hR hg.aemeasurable ha haQ fun x => ?_
  have hin := lintegral_indicator_ofReal_mul_rpow_lt_le hc
    (hγ' ▸ div_pos (mul_pos hQ (sub_pos.2 har)) ha) (g x)
  rwa [hγ', sub_add_cancel, abs_neg, abs_of_pos (mul_pos hQ hθ)] at hin

/-- The other endpoint of the `K`-method integral, for the part of `g` up to the height
`c t ^ γ`. -/
private theorem setLIntegral_Ioi_lower_le {ν : Measure α} [SFinite ν] {g : α → ℝ≥0∞}
    (hg : Measurable g) {b r Q γ c : ℝ} (hr : 0 < r) (hrb : r < b) (hbQ : b ≤ Q) (hθ : θ < 1)
    (hγ : γ * (b - r) / b = θ - 1) (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (Q - Q * θ - 1)) *
        (∫⁻ x in {x | g x ≤ ENNReal.ofReal (c * t ^ γ)}, g x ^ b ∂ν) ^ (Q / b) ≤
      ENNReal.ofReal (c ^ (-(Q * (r - b) / b)) / (Q - Q * θ)) * (∫⁻ x, g x ^ r ∂ν) ^ (Q / b) := by
  have hb : 0 < b := hr.trans hrb
  have hQ : 0 < Q := hb.trans_le hbQ
  have hγ0 : γ ≠ 0 := by rintro rfl; simp at hγ; linarith
  have hγ' : (Q - Q * θ - 1 + 1) / γ = Q * (r - b) / b := by
    rw [sub_add_cancel, show Q - Q * θ = -Q * (θ - 1) by ring, ← hγ]
    field_simp
    ring
  have hR : MeasurableSet {z : ℝ × α | g z.2 ≤ ENNReal.ofReal (c * z.1 ^ γ)} :=
    measurableSet_le (hg.comp measurable_snd)
      ((measurable_fst.pow_const γ).const_mul c).ennreal_ofReal
  refine lintegral_mul_setLIntegral_rpow_le_of_le hR hg.aemeasurable hb hbQ fun x => ?_
  have hin := lintegral_indicator_le_ofReal_mul_rpow_le hc
    (hγ' ▸ div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hQ (sub_neg.2 hrb)) hb) (g x)
  have hQθ : 0 < Q - Q * θ := by nlinarith
  rwa [hγ', sub_add_cancel, abs_of_pos hQθ] at hin

/-- The constant of the two endpoints together: since
`c ^ (-Q (r - e) / e) (c ^ r) ^ (Q / e) = c ^ Q` for `e = a, b`, the two terms add up to
`2 ^ (Q - 1) c ^ Q / (Q θ (1 - θ))`. -/
private theorem two_rpow_mul_add_eq {c a r b Q : ℝ} (hc : 0 < c) (ha : a ≠ 0) (hb : b ≠ 0)
    (hQ : 0 < Q) (hθ : θ ∈ Ioo 0 1) :
    2 ^ (Q - 1) * (ENNReal.ofReal (c ^ (-(Q * (r - a) / a)) / (Q * θ)) *
          (ENNReal.ofReal c ^ r) ^ (Q / a) +
        ENNReal.ofReal (c ^ (-(Q * (r - b) / b)) / (Q - Q * θ)) *
          (ENNReal.ofReal c ^ r) ^ (Q / b)) =
      ENNReal.ofReal (2 ^ (Q - 1) / (Q * θ * (1 - θ))) * ENNReal.ofReal c ^ Q := by
  have hD₀ : 0 < Q * θ := mul_pos hQ hθ.1
  have hD₁ : 0 < Q - Q * θ := by nlinarith [hθ.2]
  have hcQ : 0 ≤ c ^ Q := Real.rpow_nonneg hc.le Q
  -- Each term is `c ^ Q` over its denominator.
  have hterm : ∀ (e D : ℝ), -(Q * (r - e) / e) + r * (Q / e) = Q →
      ENNReal.ofReal (c ^ (-(Q * (r - e) / e)) / D) * (ENNReal.ofReal c ^ r) ^ (Q / e) =
        ENNReal.ofReal (c ^ Q / D) := fun e D he => by
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos hc,
      ← ENNReal.ofReal_mul' (Real.rpow_nonneg hc.le _), div_mul_eq_mul_div,
      ← Real.rpow_add hc, he]
  rw [hterm a _ (by field_simp; ring), hterm b _ (by field_simp; ring),
    ENNReal.ofReal_rpow_of_pos hc,
    ← ENNReal.ofReal_add (div_nonneg hcQ hD₀.le) (div_nonneg hcQ hD₁.le),
    ← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos two_pos,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _),
    ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg zero_le_two _)
      (mul_pos hD₀ (sub_pos.2 hθ.2)).le)]
  congr 1
  rw [show Q - Q * θ = Q * (1 - θ) by ring]
  field_simp [hQ.ne', hθ.1.ne', (sub_pos.2 hθ.2).ne']
  ring

/-- **The `K`-method integral against `dt / t` of a split.** If `g` has `∫ g ^ r = c ^ r`, then the
two weighted truncated integrals of `g` at the height `c t ^ γ` add up to at most
`2 ^ (Q - 1) c ^ Q / (Q θ (1 - θ))`. -/
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
  have hR₀ : MeasurableSet {z : ℝ × α | ENNReal.ofReal (c * z.1 ^ γ) < g z.2} :=
    measurableSet_lt ((measurable_fst.pow_const γ).const_mul c).ennreal_ofReal
      (hg.comp measurable_snd)
  have hm₀ : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-(Q * θ) - 1)) *
      (∫⁻ x in {x | ENNReal.ofReal (c * t ^ γ) < g x}, g x ^ a ∂ν) ^ (Q / a) :=
    (measurable_id.pow_const _).ennreal_ofReal.mul ((measurable_setLIntegral_of_measurableSet
      (R := fun t x => ENNReal.ofReal (c * t ^ γ) < g x) hR₀
      (hg.pow_const a).aemeasurable).pow_const _)
  have hb₀ := setLIntegral_Ioi_upper_le hg ha har (har.le.trans (hrb.le.trans hbQ)) hθ.1 hγa hc
    (ν := ν) (Q := Q)
  have hb₁ := setLIntegral_Ioi_lower_le hg (ha.trans har) hrb hbQ hθ.2 hγb hc (ν := ν)
  rw [hI] at hb₀ hb₁
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero two_ne_zero ENNReal.ofNat_ne_top),
    lintegral_add_left hm₀, ← two_rpow_mul_add_eq hc ha.ne' hb.ne' hQ hθ]
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
  obtain ⟨ha, har, hrb⟩ := toReal_exponents h₀ h₁ hp₁
  obtain ⟨hγa, hγb⟩ := height_exponent_spec ha har hrb (inv_toReal_eq hθ hp)
  have hQ1 : 1 ≤ Q := le_trans (by simpa using ENNReal.toReal_mono hp₁ (Fact.out : 1 ≤ p₁)) hbQ
  set c := (eLpNorm f p μ).toReal
  have hc : 0 < c := ENNReal.toReal_pos hN (Lp.eLpNorm_ne_top f)
  have hNc : eLpNorm f p μ = ENNReal.ofReal c :=
    (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)).symm
  set g : α → ℝ≥0∞ := fun x => ‖f x‖ₑ
  have hg : Measurable g := (Lp.stronglyMeasurable f).eNorm
  have hr : 0 < p.toReal := ha.trans har
  have hI : ∫⁻ x, g x ^ p.toReal ∂μ = ENNReal.ofReal c ^ p.toReal := by
    rw [← hNc]
    exact lintegral_rpow_enorm_eq_eLpNorm_rpow (zero_lt_one.trans_le Fact.out).ne'
      (ne_top_of_lt h₁) (Lp.aestronglyMeasurable f)
  have : SigmaFinite (μ.restrict {x | 0 < g x}) :=
    sigmaFinite_restrict_pos_of_lintegral_rpow_ne_top hg.aemeasurable hr
      (hI ▸ ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top)
  have key : ∀ e : ℝ, 0 < e → ∀ S : Set α,
      ∫⁻ x in S, g x ^ e ∂(μ.restrict {x | 0 < g x}) = ∫⁻ x in S, g x ^ e ∂μ :=
    fun _ he S => setLIntegral_rpow_restrict_pos hg he S
  rw [hNc, lintegral_multHaar_eq_setLIntegral]
  refine (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_).trans
    (setLIntegral_Ioi_two_mul_add_le hg ha har hrb hbQ hθ hγa hγb hc
      (by simpa [hI] using key _ hr univ))
  simpa only [key _ ha, key _ (ha.trans (har.trans hrb))] using
    ofReal_inv_mul_enorm_rpow_le f h₀ h₁ hp₁ hQ1 ht
      (ENNReal.ofReal_pos.2 (mul_pos hc (Real.rpow_pos_of_pos ht _))).ne' ENNReal.ofReal_ne_top

/-- The height `c t ^ γ` raised to the power `(s - r) / s` and multiplied by `c ^ (r / s)`:
`((c t ^ γ) ^ (s - r) c ^ r) ^ (1 / s) = c t ^ (γ (s - r) / s)`. -/
private theorem rpow_sub_mul_rpow_rpow_eq {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (γ r : ℝ) {s : ℝ}
    (hs : s ≠ 0) :
    ((c * t ^ γ) ^ (s - r) * c ^ r) ^ (1 / s) = c * t ^ (γ * (s - r) / s) := by
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg ht.le _), mul_right_comm, ← Real.rpow_add hc,
    sub_add_cancel, Real.mul_rpow (Real.rpow_nonneg hc.le _)
      (Real.rpow_nonneg (Real.rpow_nonneg ht.le _) _), ← Real.rpow_mul hc.le, mul_one_div_cancel hs,
    Real.rpow_one, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, mul_one_div]

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
  obtain ⟨ha, har, hrb⟩ := toReal_exponents h₀ h₁ hp₁
  obtain ⟨hγa, hγb⟩ := height_exponent_spec ha har hrb (inv_toReal_eq hθ hp)
  set γ := -(θ * p₀.toReal) / (p.toReal - p₀.toReal)
  set c := (eLpNorm f p μ).toReal
  have hc : 0 < c := ENNReal.toReal_pos hN (Lp.eLpNorm_ne_top f)
  have hh : 0 < c * t ^ γ := mul_pos hc (Real.rpow_pos_of_pos ht _)
  have hI : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = ENNReal.ofReal c ^ p.toReal := by
    rw [ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
    exact lintegral_rpow_enorm_eq_eLpNorm_rpow (zero_lt_one.trans_le Fact.out).ne'
      (ne_top_of_lt h₁) (Lp.aestronglyMeasurable f)
  -- Each part of the split at the height `c t ^ γ` contributes at most `c t ^ θ`.
  have hA := setLIntegral_rpow_rpow_le (γ := γ) hc ht ha
    ((setLIntegral_lt_enorm_rpow_le f ha har.le _).trans_eq (by rw [hI]))
  have hB := setLIntegral_rpow_rpow_le (γ := γ) hc ht ((ha.trans har).trans hrb)
    ((setLIntegral_enorm_le_rpow_le f ((ha.trans har).trans hrb) hrb.le _).trans_eq (by rw [hI]))
  rw [hγa] at hA
  rw [hγb] at hB
  have hK := (ofReal_kFunctional_lpToLebesgueSum_le (𝕜 := 𝕜) f h₀ h₁ hp₁ ht.le
    (ENNReal.ofReal_pos.2 hh).ne' ENNReal.ofReal_ne_top).trans
      (add_le_add hA (mul_le_mul_right hB _))
  rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), mul_left_comm,
    ← Real.rpow_one_add' ht.le (by linarith [hθ.1]), add_sub_cancel] at hK
  calc t ^ (-θ) * (lebesgue 𝕜 E μ p₀ p₁).kFunctional t (lpToLebesgueSum h₀.le h₁.le f)
      ≤ t ^ (-θ) * (2 * (c * t ^ θ)) := by
        gcongr
        linarith
    _ = 2 * c := by
        rw [mul_left_comm, mul_left_comm (t ^ (-θ)), ← Real.rpow_add ht, neg_add_cancel,
          Real.rpow_zero, mul_one]

/-! ### The embedding -/

/-- **`Lᵖ` lies in the real interpolation spaces of `(L^{p₀}, L^{p₁})`.** For
`1 ≤ p₀ < p < p₁ < ∞` and `0 < θ < 1` with `1 / p = (1 - θ) / p₀ + θ / p₁`, and every secondary
exponent `p₁ ≤ q ≤ ∞`,

`‖f‖_{(L^{p₀}, L^{p₁})_{θ,q}} ≤ 2 c_{θ,q} ‖f‖_p`,

where `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` is `TauCeti.CompatibleCouple.kMethodConst θ q`. -/
theorem kMethodENorm_lpToLebesgueSum_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
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


private theorem lpToLebesgueSum_mem_kMethod [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    (hq : p₁ ≤ q) (f : Lp E p μ) :
    lpToLebesgueSum h₀.le h₁.le f ∈ (lebesgue 𝕜 E μ p₀ p₁).kMethod θ q :=
  mem_kMethod_iff.2 ((kMethodENorm_lpToLebesgueSum_le hθ h₀ h₁ hp₁ hp hq f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (kMethodConst_lt_top hθ q))
      (Lp.eLpNorm_lt_top f)))

private theorem norm_mk_lpToLebesgueSum_le [Fact (1 ≤ p)] (hθ : θ ∈ Ioo 0 1) (h₀ : p₀ < p)
    (h₁ : p < p₁) (hp₁ : p₁ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : p₁ ≤ q) (f : Lp E p μ) :
    ‖KMethodSpace.mk (lpToLebesgueSum h₀.le h₁.le f)
        (lpToLebesgueSum_mem_kMethod (𝕜 := 𝕜) hθ h₀ h₁ hp₁ hp hq f)‖ ≤
      2 * (kMethodConst θ q).toReal * ‖f‖ := by
  rw [KMethodSpace.norm_mk, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (kMethodConst_lt_top hθ q).ne) (Lp.eLpNorm_ne_top f))
    (kMethodENorm_lpToLebesgueSum_le hθ h₀ h₁ hp₁ hp hq f)

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
        (lpToLebesgueSum_mem_kMethod hθ h₀ h₁ hp₁ hp hq f)
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
