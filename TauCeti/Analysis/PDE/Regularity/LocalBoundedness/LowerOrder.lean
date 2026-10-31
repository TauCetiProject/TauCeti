/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.Basic

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

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAbove_lowerOrder`: under `c ≥ 0`, weak
  subsolutions belong to De Giorgi's class above every level `k ≥ 0`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: local
  boundedness of weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` with `c ≥ 0`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: the
  two-sided bound `|u| ≤ D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖u‖_{L²(B(x₀, R))}` for weak solutions.

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
      0 ≤ k → 0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + (beta * R / lam) ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli (mu := mu)
  refine ⟨D * (4 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι, by positivity, ?_⟩
  intro Omega a b c beta gamma u k x₀ R h ha hb hc hb_bound hc_bound hc_nonneg hu hk hR hball
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
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * (1 + (beta * R / lam) ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam)
  refine ⟨D, hD, ?_⟩
  intro Omega a b c beta gamma u x₀ R h ha hb hc hb_bound hc_bound hc_nonneg hu hR hball
  have hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (-u) (v : W1p mu Omega 2) = 0 := fun v => by
    rw [energyFormH1_neg_left, hu v, neg_zero]
  exact ae_abs_value_le_mul_sqrt_setIntegral_of_ae_value_le (by positivity) hball
    (by simpa only [zero_add, sub_zero] using
      hbound h ha hb hc hb_bound hc_bound hc_nonneg (fun v _ => (hu v).le) le_rfl hR hball)
    (by simpa only [zero_add, sub_zero] using
      hbound h ha hb hc hb_bound hc_bound hc_nonneg (fun v _ => (hu' v).le) le_rfl hR hball)

end PDE

end TauCeti
