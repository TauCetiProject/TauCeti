/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.Basic
import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.Exponent

/-!
# Local boundedness of weak subsolutions with lower-order terms (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, let `b` and
`c` be measurable and bounded on `Ω`, with `‖b‖ ≤ β` and `c ≥ 0`, and let `u ∈ H¹(Ω)` be a weak
subsolution of the full divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with
drift `b` and mass coefficient `c`. This file proves De Giorgi's local boundedness theorem for
such `u`: on every ball `B(x₀, R) ⊆ Ω` and above every level `k ≥ 0`,

`u ≤ k + D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

with `D` depending only on `λ`, `Λ`, the dimension `n ≥ 1` and the normalization of the additive
Haar measure. For weak solutions, `u` and `-u` are both subsolutions, which gives the two-sided
bound `|u| ≤ D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖u‖_{L²(B(x₀, R))}` on `B(x₀, R/2)`.

Under the sign condition `c ≥ 0` and at levels `k ≥ 0`, the truncations `(u - k)⁺` satisfy the
Caccioppoli inequality

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w²`

(`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos`
in `TauCeti.PDE`), and De Giorgi's iteration
(`TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli`) turns
it into the bound above. Unlike the principal part, the drift term is not invariant under
dilations: it is comparable to the cutoff term only on balls with `βR/λ` bounded, which is why
the constant depends on `βR/λ`. The mass coefficient `c` enters only through its sign; its bound
serves to make the energy form integrable. The condition `k ≥ 0` is what makes the mass term
`c u (u - k)⁺` nonnegative, so it can be dropped from the Caccioppoli inequality.

## A mass coefficient of either sign

Without the sign condition the bound holds above the level `0`, with the mass coefficient
entering through the dimensionless `γR²/λ`, where `‖c‖ ≤ γ`:

`u ≤ D (1 + (βR/λ)² + γR²/λ)ⁿ R^{-n/2} ‖u⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`

(`TauCeti.PDE.exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`). At a level
`l ≥ 0` the negative part of `c` contributes `-c u (u - l)⁺ ≤ γ ((u - l)⁺ + l) (u - l)⁺`, a
zeroth-order term and a term linear in the truncation with coefficient proportional to `l`, so
weak subsolutions belong to De Giorgi's class above `0` with a linear term
(`TauCeti.PDE.UniformlyEllipticOn.caccioppoliAboveLinear_lowerOrder`), and De Giorgi's iteration
(`exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear`)
applies. As for the principal part, the `L²` norm can then be replaced by any `Lᵖ` norm with
`0 < p ≤ 2`: on balls with `βR ≤ θλ` and `γR² ≤ θλ`,

`u ≤ D R^{-n/p} ‖u⁺‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

with `D` depending on `λ`, `Λ`, `p`, `θ` and the dimension
(`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`). This is the
supremum bound for subsolutions in Moser's proof of the Harnack inequality for equations with
lower-order terms (Gilbarg–Trudinger, Theorems 8.17 and 8.20), where a nonnegative solution is a
subsolution whatever the sign of `c`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAbove_lowerOrder`: under `c ≥ 0`, weak
  subsolutions belong to De Giorgi's class above every level `k ≥ 0`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: local
  boundedness of weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` with `c ≥ 0`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: the
  two-sided bound `|u| ≤ D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖u‖_{L²(B(x₀, R))}` for weak solutions.
* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAboveLinear_lowerOrder`: without a sign condition
  on `c`, weak subsolutions belong to De Giorgi's class above `0` with a linear term.
* `TauCeti.PDE.exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: local
  boundedness of weak subsolutions with a mass coefficient of either sign.
* `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`: its `Lᵖ` form,
  `0 < p ≤ 2`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.17.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ContDiff Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- Under `c ≥ 0`, weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` belong to De Giorgi's
class above every level `k ≥ 0`, with `A = 2 (2Λ/λ)²` and `B = (2β/λ)²`. -/
theorem UniformlyEllipticOn.caccioppoliAbove_lowerOrder
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    {k : ℝ} (hk : 0 ≤ k) :
    CaccioppoliAbove u k (2 * (2 * Lam / lam) ^ 2) ((2 * beta / lam) ^ 2) := by
  refine .intro fun l hkl hl ψ hψ hcpt hts => ?_
  rw [W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) (hk.trans hkl) u hl]
  exact h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos ha hb hc
    hb_bound hc_bound hc_nonneg hu (hk.trans hkl) hψ hcpt hts

/-- **Local boundedness of weak subsolutions with lower-order terms (De Giorgi).** In every
dimension `n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization of
the additive Haar measure `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, and let `b` and `c` be measurable with
`‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on `Ω`. Let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`,
where `a(·, ·)` is the energy form with drift `b` and mass coefficient `c`. Then for every level
`k ≥ 0` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D (1 + (βR/λ)²)ⁿ R^{-n/2} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on
`B(x₀, R/2)`.

The bound `γ` does not enter the constant. For `b = 0` and `c = 0` this recovers
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral` at nonnegative levels. -/
theorem exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      0 ≤ k → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + (beta * R / lam) ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli (mu := mu)
  refine ⟨D * (4 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι, by positivity, ?_⟩
  intro Omega a b c beta gamma u k x₀ R h ha hb hc hb_bound hc_bound hc_nonneg hu hk hball
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hU : (⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega :=
    hball
  have hmono : mu.restrict (Metric.ball x₀ R) ≤ mu.restrict Omega :=
    Measure.restrict_mono hball le_rfl
  -- The restriction of `u` to the ball satisfies the Caccioppoli inequality at every level
  -- `l ≥ k ≥ 0`, with `A = 2 (2Λ/λ)²` and `B = (2β/λ)²`.
  have hbound := hmain (k := k) hball (by positivity) (sq_nonneg (2 * beta / lam)) hR
    ((h.mono_set hball).caccioppoliAbove_lowerOrder (ha.mono_measure hmono)
      (hb.mono_measure hmono) (hc.mono_measure hmono) (fun x hx => hb_bound x (hball hx))
      (fun x hx => hc_bound x (hball hx)) (fun x hx => hc_nonneg x (hball hx))
      (energyFormH1_restrictL_nonpos hU hu) hk)
  -- `1 + A + (2β/λ)² R² ≤ 4 (1 + A) (1 + (βR/λ)²)`.
  have hfac : D * (1 + 2 * (2 * Lam / lam) ^ 2 + (2 * beta / lam) ^ 2 * R ^ 2) ^ Fintype.card ι ≤
      D * (4 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι *
        (1 + (beta * R / lam) ^ 2) ^ Fintype.card ι := by
    rw [mul_assoc, ← mul_pow (4 * (1 + 2 * (2 * Lam / lam) ^ 2))]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) hD.le
    · positivity
    have hBR : (2 * beta / lam) ^ 2 * R ^ 2 = 4 * (beta * R / lam) ^ 2 := by ring
    rw [hBR]
    nlinarith [sq_nonneg (beta * R / lam), sq_nonneg (2 * Lam / lam),
      mul_nonneg (sq_nonneg (2 * Lam / lam)) (sq_nonneg (beta * R / lam))]
  filter_upwards [hbound] with x hx
  refine hx.trans ?_
  gcongr k + ?_ * _ * _

/-- **Local boundedness of weak solutions with lower-order terms (De Giorgi).** In every dimension
`n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `b` and `c` be measurable with `‖b‖ ≤ β`,
`‖c‖ ≤ γ` and `c ≥ 0` on `Ω`. Let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`. Then for every
ball `B(x₀, R) ⊆ Ω`,

`|u| ≤ D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖u‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is the two-sided form of
`TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`, applied at
the level `0` to the weak subsolutions `u` and `-u`. -/
theorem exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * (1 + (beta * R / lam) ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam)
  refine ⟨D, hD, ?_⟩
  intro Omega a b c beta gamma u x₀ R h ha hb hc hb_bound hc_bound hc_nonneg hu hball
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (-u) (v : W1p mu Omega 2) = 0 := fun v => by
    rw [energyFormH1_neg_left, hu v, neg_zero]
  exact ae_abs_value_le_mul_sqrt_setIntegral_of_ae_value_le (by positivity) hball
    (by simpa only [zero_add, sub_zero] using
      hbound h ha hb hc hb_bound hc_bound hc_nonneg (fun v _ => (hu v).le) le_rfl hball)
    (by simpa only [zero_add, sub_zero] using
      hbound h ha hb hc hb_bound hc_bound hc_nonneg (fun v _ => (hu' v).le) le_rfl hball)

/-- Without a sign condition on `c`, weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` belong
to De Giorgi's class above the level `0` with a linear term, with `A = 2 (2Λ/λ)²`,
`B = (2β/λ)² + 4γ/λ` and `E = 4γ/λ`. -/
theorem UniformlyEllipticOn.caccioppoliAboveLinear_lowerOrder
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    CaccioppoliAboveLinear u 0 (2 * (2 * Lam / lam) ^ 2) ((2 * beta / lam) ^ 2 + 4 * gamma / lam)
      (4 * gamma / lam) := by
  refine .intro fun l hl0 hl ψ hψ hcpt hts => ?_
  rw [W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) hl0 u hl, sub_zero]
  exact h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_add_of_nonpos ha hb hc
    hb_bound hc_bound hu hl0 hψ hcpt hts

/-- **Local boundedness of weak subsolutions with a mass coefficient of either sign (De Giorgi).**
In every dimension `n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `b` and `c` be measurable
with `‖b‖ ≤ β` and `‖c‖ ≤ γ` on `Ω`; no sign condition is imposed on `c`. Let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. Then for every ball `B(x₀, R) ⊆ Ω`,

`u ≤ D (1 + (βR/λ)² + γR²/λ)ⁿ R^{-n/2} (∫_{B(x₀, R)} (u⁺)²)^{1/2}` almost everywhere on
`B(x₀, R/2)`.

The mass coefficient enters only through the dimensionless `γR²/λ`. Unlike
`TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`, which
assumes `c ≥ 0` and holds above every level `k ≥ 0`, the bound is above the level `0`: for `c < 0`
a constant is no longer a subsolution, so levels `k > 0` are not comparable to `0`. -/
theorem exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ D * (1 + (beta * R / lam) ^ 2 + gamma * R ^ 2 / lam) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear
      (mu := mu)
  refine ⟨D * (12 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι, by positivity, ?_⟩
  intro Omega a b c beta gamma u x₀ R h ha hb hc hb_bound hc_bound hu hball
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hlam := h.pos
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (Metric.mem_ball_self hR)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  have hU : (⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega :=
    hball
  have hmono : mu.restrict (Metric.ball x₀ R) ≤ mu.restrict Omega :=
    Measure.restrict_mono hball le_rfl
  -- The restriction of `u` to the ball lies in De Giorgi's class above `0` with a linear term.
  have hbound := hmain (k := 0) hball (by positivity) (by positivity) (by positivity) hR
    ((h.mono_set hball).caccioppoliAboveLinear_lowerOrder (ha.mono_measure hmono)
      (hb.mono_measure hmono) (hc.mono_measure hmono) (fun x hx => hb_bound x (hball hx))
      (fun x hx => hc_bound x (hball hx)) (energyFormH1_restrictL_nonpos hU hu))
  -- `1 + A + (B + 2E) R² ≤ 12 (1 + A) (1 + (βR/λ)² + γR²/λ)` with `B + 2E = (2β/λ)² + 12γ/λ`.
  have hfac : D * (1 + 2 * (2 * Lam / lam) ^ 2 + ((2 * beta / lam) ^ 2 + 4 * gamma / lam +
      2 * (4 * gamma / lam)) * R ^ 2) ^ Fintype.card ι ≤
      D * (12 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι *
        (1 + (beta * R / lam) ^ 2 + gamma * R ^ 2 / lam) ^ Fintype.card ι := by
    rw [mul_assoc, ← mul_pow (12 * (1 + 2 * (2 * Lam / lam) ^ 2))]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hD.le
    have hBR : ((2 * beta / lam) ^ 2 + 4 * gamma / lam + 2 * (4 * gamma / lam)) * R ^ 2 =
        4 * (beta * R / lam) ^ 2 + 12 * (gamma * R ^ 2 / lam) := by
      field_simp
      ring
    have hg : 0 ≤ gamma * R ^ 2 / lam := by positivity
    rw [hBR]
    nlinarith [sq_nonneg (beta * R / lam), sq_nonneg (2 * Lam / lam),
      mul_nonneg (sq_nonneg (2 * Lam / lam)) (sq_nonneg (beta * R / lam)),
      mul_nonneg (sq_nonneg (2 * Lam / lam)) hg]
  filter_upwards [hbound] with x hx
  simp only [sub_zero, zero_add] at hx
  refine hx.trans ?_
  gcongr ?_ * _ * _

/-- **Local boundedness of weak subsolutions in `Lᵖ` with lower-order terms (De Giorgi).** Let
`0 < p ≤ 2` and `θ ≥ 0`. In every dimension `n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, `p`,
`θ`, the dimension and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `b` and
`c` be measurable with `‖b‖ ≤ β` and `‖c‖ ≤ γ` on `Ω`; no sign condition is imposed on `c`. Let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. Then for every ball
`B(x₀, R) ⊆ Ω` with `βR ≤ θλ` and `γR² ≤ θλ`,

`u ≤ D R^{-n/p} (∫_{B(x₀, R)} (u⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

The lower-order coefficients enter only through bounds on the dimensionless `βR/λ` and `γR²/λ`,
as in Gilbarg–Trudinger, Theorem 8.17. Small `p` is the form in which local boundedness enters
Moser's proof of the Harnack inequality. -/
theorem exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder [Nonempty ι] {p : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (θ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * R ≤ θ * lam → gamma * R ^ 2 ≤ θ * lam →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam)
  obtain ⟨C, hC, hmain⟩ := exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu)
    (-(Fintype.card ι : ℝ) / 2) (D * (1 + θ ^ 2 + θ) ^ Fintype.card ι) hp hp2
  refine ⟨C, hC, fun {Omega a b c beta gamma u x₀ R} h ha hb hc hb_bound hc_bound hu hball hβ hγ =>
    ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hlam := h.pos
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (Metric.mem_ball_self hR)
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ hx₀)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  have hθ : 0 ≤ θ := nonneg_of_mul_nonneg_left
    ((mul_nonneg hgamma (sq_nonneg R)).trans hγ) hlam
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hw2 : MemLp (fun x => max (W1p.value u x) 0) 2 (mu.restrict (Metric.ball x₀ R)) :=
    ((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).pos_part
  -- On every ball inside `B(x₀, R)` the radius is at most `R`, so the coefficient factor of the
  -- `L²` bound is at most `(1 + θ² + θ)ⁿ`.
  filter_upwards [hmain (fun x => le_max_right _ 0) hw2 fun y s hs hsub => by
    -- Comparing diameters, `2 s ≤ 2 R`.
    have hsR : s ≤ R := by
      have := (Metric.diam_ball_eq y hs.le).symm.trans_le
        ((Metric.diam_mono hsub Metric.isBounded_ball).trans (Metric.diam_ball hR.le))
      linarith
    filter_upwards [hbound h ha hb hc hb_bound hc_bound hu (hsub.trans hball)] with x hx
    refine max_le (hx.trans ?_) (by positivity)
    have hβs : beta * s / lam ≤ θ := by
      rw [div_le_iff₀ hlam]
      nlinarith
    have hγs : gamma * s ^ 2 / lam ≤ θ := by
      rw [div_le_iff₀ hlam]
      nlinarith [pow_le_pow_left₀ hs.le hsR 2]
    have hβ2 : (beta * s / lam) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by positivity) hβs 2
    have hfac := pow_le_pow_left₀ (by positivity)
      (by linarith : 1 + (beta * s / lam) ^ 2 + gamma * s ^ 2 / lam ≤ 1 + θ ^ 2 + θ)
      (Fintype.card ι)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfac hD.le) (Real.rpow_nonneg hs.le _))
      (Real.sqrt_nonneg _)] with x hx
  rw [show 2 * (-(Fintype.card ι : ℝ) / 2) / p = -(Fintype.card ι : ℝ) / p by ring] at hx
  exact (le_max_left _ _).trans hx

end PDE

end TauCeti
