/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.LowerOrder
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.Basic
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Local boundedness of weak subsolutions with lower-order terms (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, let `b` and
`c` be measurable and bounded on `Ω`, with `‖b‖ ≤ β` and, to begin with, `c ≥ 0`, and let
`u ∈ H¹(Ω)` be a weak subsolution of the full divergence-form equation

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

Without a sign on `c`, with `|c| ≤ γ`, the mass term is no longer nonnegative, but where
`w = (u - l)⁺` is positive at a level `l ≥ 0` it is at most `γ (w² + l w)`. So the truncations
belong to De Giorgi's class with a linear term above the level `0`
(`TauCeti.PDE.CaccioppoliAboveLinear`), and the iteration gives

`u ≤ D (1 + (βR/λ)² + γR²/λ)ⁿ R^{-n/2} ‖u⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

now with `γ` in the constant. On balls where `βR/λ` and `γR²/λ` are bounded, the `L²` norm can
be replaced by any `Lᵖ` norm with `0 < p ≤ 2`
(`TauCeti.exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball`). For a positive weak
supersolution `u` of the same equation, `u⁻¹` is formally a subsolution of the equation with mass
coefficient `-c`, so Moser's weak Harnack and Harnack inequalities with lower-order terms need
local boundedness for mass coefficients of either sign.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAbove_lowerOrder`: under `c ≥ 0`, weak
  subsolutions belong to De Giorgi's class above every level `k ≥ 0`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: local
  boundedness of weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` with `c ≥ 0`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: the
  two-sided bound `|u| ≤ D (1 + (βR/λ)²)ⁿ R^{-n/2} ‖u‖_{L²(B(x₀, R))}` for weak solutions.
* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAboveLinear_lowerOrder`: without a sign on `c`, weak
  subsolutions belong to De Giorgi's class with a linear term above the level `0`.
* `TauCeti.PDE.exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`: local
  boundedness of weak subsolutions with `c` of either sign.
* `TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`: the same in `Lᵖ`,
  `0 < p ≤ 2`, on balls with `βR/λ` and `γR²/λ` bounded.

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

/-! ### A mass coefficient of either sign -/

omit [DecidableEq ι] in
/-- The mass term of the Caccioppoli inequality without a sign on `c`: for `|c| ≤ γ` on `Ω` and the
truncation `w = (u - l)⁺` at a level `l ≥ 0`, `∫_Ω ψ² (-c u) w ≤ γ ∫_Ω ψ² w² + γ l ∫_Ω ψ² w`,
because `w > 0` forces `u = w + l ≥ 0`. The forcing `0` is written as an element of `L²`, as the
Caccioppoli inequality with lower-order terms takes it. -/
private theorem setIntegral_sq_mul_sub_mul_mul_posPartAbove_le {Omega : Opens (EuclideanSpace ℝ ι)}
    {c : EuclideanSpace ℝ ι → ℝ} {gamma : ℝ} (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) {u : W1p mu Omega 2}
    {l : ℝ} (hl0 : 0 ≤ l) (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ) :
    let w := W1p.posPartAboveOfMemLp (by norm_num) l u hl
    ∫ x in Omega, ψ x ^ 2 * ((0 : Lp ℝ 2 (mu.restrict Omega)) x -
      c x * W1p.value u x) * W1p.value w x ∂mu ≤
      gamma * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu +
        gamma * l * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ∂mu := by
  intro w
  -- Integrability of the three integrands.
  obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := .of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hC : MemLp (fun x => (0 : Lp ℝ 2 (mu.restrict Omega)) x - c x * W1p.value u x) 2
      (mu.restrict Omega) :=
    (Lp.memLp _).sub ((memLp_top_of_bound hc gamma
      (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hc_bound)).fun_mul (Lp.memLp _))
  have hm : Integrable (fun x => ψ x ^ 2 * ((0 : Lp ℝ 2 (mu.restrict Omega)) x -
      c x * W1p.value u x) * W1p.value w x) (mu.restrict Omega) :=
    ((hC.integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2 hψ2M).congr
      (.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value w)).integrable_sq.bdd_mul hψ2 hψ2M
  have hW : Integrable (fun x => ψ x ^ 2 * W1p.value w x) (mu.restrict Omega) := by
    have hloc := (Lp.memLp (W1p.value w)).locallyIntegrable one_le_two
    simpa only [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport
      (g := fun x => ψ x ^ 2) (hψ.continuous.pow 2)
      (hcpt.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hZ.const_mul _)
    (hW.const_mul _)]
  refine integral_mono_ae hm ((hZ.const_mul _).add (hW.const_mul _)) ?_
  -- Pointwise, `-c u w ≤ γ w² + γ l w`.
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet,
    W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hl,
    Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx hwx hzero
  rw [hwx, hzero, Pi.zero_apply, zero_sub]
  have hcx : |c x| ≤ gamma := (Real.norm_eq_abs _).symm.trans_le (hc_bound x hx)
  rcases le_or_gt (W1p.value u x) l with hxu | hxu
  · rw [max_eq_right (by linarith)]
    simp
  · rw [max_eq_left (by linarith)]
    have hcu : -(c x * W1p.value u x) ≤ gamma * W1p.value u x := by
      nlinarith [neg_abs_le (c x), abs_nonneg (c x)]
    have hw0 : 0 ≤ W1p.value u x - l := by linarith
    have := mul_le_mul_of_nonneg_right hcu (mul_nonneg (sq_nonneg (ψ x)) hw0)
    linear_combination this

/-- Under no sign condition on `c`, weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0` belong
to De Giorgi's class with a linear term above the level `0`, with `A = 2 (2Λ/λ)²`,
`B = (2β/λ)² + 4γ/λ` and `E = 4γ/λ`: at a level `l ≥ 0` the mass term `-c u w` of the truncation
`w = (u - l)⁺` is at most `γ (w² + l w)`, because `w > 0` forces `u = w + l ≥ 0`. -/
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
  have hlam := h.pos
  -- Caccioppoli's inequality with the forcing `0`, whose mass term is then bounded.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp ha hb hc
    hb_bound hc_bound (f := 0) (fun v hv => (hu v hv).trans_eq (integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
      rw [hx, Pi.zero_apply, zero_mul])).symm) hl hψ hcpt hts
  have hmass := mul_le_mul_of_nonneg_left
    (setIntegral_sq_mul_sub_mul_mul_posPartAbove_le hc hc_bound hl0 hl hψ hcpt)
    (by positivity : (0 : ℝ) ≤ 4 / lam)
  dsimp only at hcacc hmass
  linear_combination hcacc + hmass

/-- **Local boundedness of weak subsolutions with a mass coefficient of either sign
(De Giorgi).** In every dimension `n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, the dimension
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `b` and `c` be measurable
with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, with no condition on the sign of `c`. Let `u ∈ H¹(Ω)` be a
weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with drift `b` and mass coefficient `c`. Then for
every ball `B(x₀, R) ⊆ Ω`,

`u ≤ D (1 + (βR/λ)² + γR²/λ)ⁿ R^{-n/2} (∫_{B(x₀, R)} (u⁺)²)^{1/2}` almost everywhere on
`B(x₀, R/2)`.

Unlike `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`, which
assumes `c ≥ 0`, the bound `γ` enters the constant, through the dimensionless quantity `γR²/λ`,
and the bound is at the level `0`: above a level `k > 0`, `u - k` is a subsolution of the equation
with the right-hand side `-c k`, which the truncations of `u - k` alone do not control. -/
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
  refine ⟨D * (8 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι, by positivity, ?_⟩
  intro Omega a b c beta gamma u x₀ R h ha hb hc hb_bound hc_bound hu hball
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  have hlam := h.pos
  -- The ball is nonempty, so the bounds `β` and `γ` are nonnegative.
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (Metric.mem_ball_self hR)
  have hγ : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  have hU : (⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega :=
    hball
  have hmono : mu.restrict (Metric.ball x₀ R) ≤ mu.restrict Omega :=
    Measure.restrict_mono hball le_rfl
  have hbound := hmain (k := 0) hball (by positivity) (by positivity) (by positivity) hR
    ((h.mono_set hball).caccioppoliAboveLinear_lowerOrder (ha.mono_measure hmono)
      (hb.mono_measure hmono) (hc.mono_measure hmono) (fun x hx => hb_bound x (hball hx))
      (fun x hx => hc_bound x (hball hx)) (energyFormH1_restrictL_nonpos hU hu))
  -- `1 + A + (B + E) R² ≤ 8 (1 + A) (1 + (βR/λ)² + γR²/λ)` with `A = 2 (2Λ/λ)²`.
  have hfac : D * (1 + 2 * (2 * Lam / lam) ^ 2 +
      ((2 * beta / lam) ^ 2 + 4 * gamma / lam + 4 * gamma / lam) * R ^ 2) ^ Fintype.card ι ≤
      D * (8 * (1 + 2 * (2 * Lam / lam) ^ 2)) ^ Fintype.card ι *
        (1 + (beta * R / lam) ^ 2 + gamma * R ^ 2 / lam) ^ Fintype.card ι := by
    rw [mul_assoc, ← mul_pow (8 * (1 + 2 * (2 * Lam / lam) ^ 2))]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hD.le
    have hX : (2 * beta / lam) ^ 2 * R ^ 2 = 4 * (beta * R / lam) ^ 2 := by ring
    have hY : 4 * gamma / lam * R ^ 2 = 4 * (gamma * R ^ 2 / lam) := by ring
    have hY0 : 0 ≤ gamma * R ^ 2 / lam := by positivity
    rw [add_mul, add_mul, hX, hY]
    nlinarith [sq_nonneg (beta * R / lam), sq_nonneg (2 * Lam / lam),
      mul_nonneg (sq_nonneg (2 * Lam / lam)) (sq_nonneg (beta * R / lam)),
      mul_nonneg (sq_nonneg (2 * Lam / lam)) hY0]
  filter_upwards [hbound] with x hx
  simp only [zero_add, sub_zero] at hx
  refine hx.trans ?_
  gcongr ?_ * _ * _

/-- **Local boundedness in `Lᵖ` of weak subsolutions with a mass coefficient of either sign
(De Giorgi).** Fix `σ` and `0 < p ≤ 2`. In every dimension `n ≥ 1` there is `D > 0`, depending
on `λ`, `Λ`, `σ`, `p`, the dimension and the normalization of the additive Haar measure `mu`,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, with no condition on the
sign of `c`, and let `u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. Then
on every ball `B(x₀, R) ⊆ Ω` with `βR ≤ σλ` and `γR² ≤ σλ`,

`u ≤ D R^{-n/p} (∫_{B(x₀, R)} (u⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

The lower-order terms enter only through the dimensionless quantities `βR/λ` and `γR²/λ`, which
`σ` bounds. Small `p` is the form in which local boundedness enters Moser's weak Harnack and
Harnack inequalities. -/
theorem exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder [Nonempty ι] (σ : ℝ)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
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
      beta * R ≤ σ * lam → gamma * R ^ 2 ≤ σ * lam →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam)
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu)
      (-(Fintype.card ι : ℝ) / 2) (D * (1 + σ ^ 2 + |σ|) ^ Fintype.card ι) (by positivity) hp hp2
  refine ⟨C, hC, ?_⟩
  intro Omega a b c beta gamma u x₀ R h ha hb hc hb_bound hc_bound hu hball hβ hγ
  have hlam := h.pos
  -- On every ball `B(y, s) ⊆ B(x₀, R)` the `L²` bound holds with the constant for `σ`.
  have H : ∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
      ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
        W1p.value u x ≤ 0 + D * (1 + σ ^ 2 + |σ|) ^ Fintype.card ι *
          s ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball y s, max (W1p.value u x - 0) 0 ^ 2 ∂mu) := fun y s hs hsub => by
    have hsR : s ≤ R := by
      linarith [(ball_subset_ball_iff hs).1 hsub, dist_nonneg (x := y) (y := x₀)]
    have hy : y ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (hsub (Metric.mem_ball_self hs))
    have hβ0 : 0 ≤ beta := (norm_nonneg _).trans (hb_bound y hy)
    have hγ0 : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound y hy)
    -- `(βs/λ)² ≤ σ²` and `γs²/λ ≤ |σ|`, since `0 ≤ βs ≤ βR ≤ σλ` and `0 ≤ γs² ≤ γR² ≤ σλ`.
    have h1 : beta * s / lam ≤ |σ| := by
      rw [div_le_iff₀ hlam]
      nlinarith [le_abs_self σ, mul_le_mul_of_nonneg_left hsR hβ0]
    have h2 : gamma * s ^ 2 / lam ≤ |σ| := by
      rw [div_le_iff₀ hlam]
      nlinarith [le_abs_self σ, mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hs.le hsR 2) hγ0]
    have hfac : (1 + (beta * s / lam) ^ 2 + gamma * s ^ 2 / lam) ^ Fintype.card ι ≤
        (1 + σ ^ 2 + |σ|) ^ Fintype.card ι := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have : (beta * s / lam) ^ 2 ≤ σ ^ 2 := by
        rw [← sq_abs σ]
        exact pow_le_pow_left₀ (by positivity) h1 2
      linarith
    filter_upwards [hbound h ha hb hc hb_bound hc_bound hu (hsub.trans hball)] with x hx
    simp only [zero_add, sub_zero]
    refine hx.trans ?_
    gcongr
  filter_upwards [hmain (k := 0) hball H] with x hx
  simpa only [zero_add, sub_zero,
    show 2 * (-(Fintype.card ι : ℝ) / 2) / p = -(Fintype.card ι : ℝ) / p by ring] using hx

end PDE

end TauCeti
