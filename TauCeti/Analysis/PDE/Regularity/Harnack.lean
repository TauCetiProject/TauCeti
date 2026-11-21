/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Crossover
public import TauCeti.Analysis.PDE.Regularity.ReverseHolder
public import TauCeti.Analysis.PDE.Regularity.Supersolution.Lp
import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.LowerOrder
import TauCeti.Analysis.PDE.Regularity.Supersolution.LowerOrder
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Moser's weak Harnack inequality and the Harnack inequality

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`. This file
proves, in every dimension `n ≥ 1`, the two Harnack inequalities of Moser for the divergence-form
equation `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, with no regularity of the coefficients beyond measurability.

* The **weak Harnack inequality**: if `u ∈ H¹(Ω)` is a weak supersolution, `a(u, v) ≥ 0` for
  every nonnegative `v ∈ H¹₀(Ω)`, and `u ≥ 0` almost everywhere, then for every exponent `s > 0`
  with `(n - 2) s < n` (that is `s < n/(n - 2)` when `n ≥ 3`, and any `s > 0` when `n ≤ 2`) and
  every ball with `B(x₀, 8√n r) ⊆ Ω`,

  `(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

  that is, the `L^s` average of `u` is controlled by its essential infimum. In particular `u^s`
  is integrable on `B(x₀, r)`, which is part of the conclusion.
* The **Harnack inequality**: if `u` is a weak solution, `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`,
  and `u ≥ 0` almost everywhere, then on every ball with `B(x₀, 16√n r) ⊆ Ω`,

  `u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

  that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`.

In both, `C` depends only on `λ`, `Λ`, the dimension, the normalization of the Haar measure and,
for the weak Harnack inequality, the exponent `s`. It does not depend on `u` or on the ball, so the
estimates are scale invariant.

The weak Harnack inequality at a small exponent is first proved for supersolutions with
`u ≥ ε > 0`, with a constant independent of `ε`, as in Moser's proof. On `B = B(x₀, 2r)`, at the
exponent `p₀ = min(cλ/Λ, 2)` of the crossover estimate, it combines

* the lower bound from negative powers, `u⁻¹ ≤ D |B|^{-1/p₀} ‖u⁻¹‖_{L^{p₀}(B)}` on `B(x₀, r)`
  (`TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow`), with
* the crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K`, from the John–Nirenberg inequality for
  `log u` (`TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le`).

Together they bound `(⨍_B u^{p₀})^{1/p₀}` by `C u(x)` for almost every `x ∈ B(x₀, r)`, in every
dimension `n ≥ 1`. A nonnegative supersolution is reduced to this case by applying it to `u + δ`
on the bounded ball `B(x₀, 8√n r)`, where constants lie in `H¹`, and letting `δ → 0`. Moser's
iteration for small positive powers of nonnegative supersolutions
(`TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv`) then raises the
exponent from `p₀` to any `s` with `(n - 2) s < n`. The Harnack inequality combines the weak
Harnack inequality at `s = 1`, which is admissible in every dimension, with the local boundedness
of subsolutions in `L¹` (`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow`).

## Lower-order terms

Both inequalities hold for the full equation `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0` with measurable
coefficients `‖b‖ ≤ β` and `|c| ≤ γ`, with no condition on the sign of `c`, on the balls of the
statements above on which `βr ≤ σλ` and `γr² ≤ σλ`; the constants then depend on `σ` as well. The
lower-order terms enter only through the dimensionless quantities `βr/λ` and `γr²/λ`, so this is
the scale-invariant form. The proof is the same, and it is carried out only in this generality:
the statements without lower-order terms are deduced from the case `b = 0`, `c = 0`. It uses the
lower-order versions of the ingredients above: the lower bound from negative powers
(`TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`), the crossover
estimate (`TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder`), whose
admissible exponent now also depends on `σ`, Moser's iteration
(`TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder`) and
local boundedness (`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`).
Only the reduction to supersolutions bounded below by a positive constant changes. Without a sign
on `c`, the shift `u + δ` is no longer a supersolution of the same equation; but for `u ≥ 0` it is
one of the equation with the mass coefficient `c u⁺ / (u⁺ + δ)`, whose product with `u + δ` is
`c u` and which is still bounded by `|c|`. So the estimate for `u + δ` holds with the same constant,
and letting `δ → 0` gives it for `u`.

## Main declarations

* `TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value`: the weak Harnack inequality
  at a small exponent `p₀`, in every dimension, for nonnegative supersolutions.
* `TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value`: Moser's weak Harnack
  inequality for nonnegative supersolutions, for every exponent `s > 0` with `(n - 2) s < n`.
* `TauCeti.PDE.exists_ae_ae_value_le_mul_value`: Moser's Harnack inequality for nonnegative
  solutions.
* `TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`: the weak Harnack
  inequality with lower-order terms.
* `TauCeti.PDE.exists_ae_ae_value_le_mul_value_lowerOrder`: the Harnack inequality with
  lower-order terms.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.18 and 8.20.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- **Moser's combination step.** On `B = B(x₀, 2r)`, a crossover bound
`⨍_B f^{p₀} · ⨍_B f^{-p₀} ≤ K` and a lower bound `f⁻¹ ≤ D (2r)^{-n/p₀} (∫_B f^{-p₀})^{1/p₀}` on
`B(x₀, r)` give `(⨍_B f^{p₀})^{1/p₀} ≤ K^{1/p₀} D |B(0, 1)|^{1/p₀} f` on `B(x₀, r)`. -/
private theorem ae_setAverage_rpow_rpow_inv_le_mul_of_mul_le {f : EuclideanSpace ℝ ι → ℝ}
    {p₀ K D r : ℝ} {x₀ : EuclideanSpace ℝ ι} (hp₀ : 0 < p₀) (hr : 0 < r)
    (hpos : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 < f y)
    (hcross : (⨍ y in ball x₀ (2 * r), f y ^ p₀ ∂mu) *
      (⨍ y in ball x₀ (2 * r), f y ^ (-p₀) ∂mu) ≤ K)
    (hlower : ∀ᵐ x ∂mu.restrict (ball x₀ r), (f x)⁻¹ ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / p₀) *
      (∫ y in ball x₀ (2 * r), (f y)⁻¹ ^ p₀ ∂mu) ^ p₀⁻¹) :
    ∀ᵐ x ∂mu.restrict (ball x₀ r), (⨍ y in ball x₀ (2 * r), f y ^ p₀ ∂mu) ^ p₀⁻¹ ≤
      K ^ p₀⁻¹ * D * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ p₀⁻¹ * f x := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  have h2r : 0 < 2 * r := by positivity
  set Ap := ⨍ y in ball x₀ (2 * r), f y ^ p₀ ∂mu
  set An := ⨍ y in ball x₀ (2 * r), f y ^ (-p₀) ∂mu
  have hAp : 0 ≤ Ap := average_nonneg_of_ae (hpos.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  have hAn : 0 ≤ An := average_nonneg_of_ae (hpos.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  -- The lower bound in averaged form, `f⁻¹ ≤ D V^{1/p₀} An^{1/p₀}`.
  have hint : ∫ y in ball x₀ (2 * r), (f y)⁻¹ ^ p₀ ∂mu = (2 * r) ^ n * V * An := by
    have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ n * V := by
      rw [Measure.addHaar_real_ball_of_pos mu x₀ h2r, finrank_euclideanSpace,
        ← Real.rpow_natCast]
    rw [← hvol, ← smul_eq_mul (mu.real _) An, measure_smul_setAverage _ measure_ball_lt_top.ne]
    exact integral_congr_ae (hpos.mono fun y hy => by
      simp only [Real.rpow_neg hy.le, Real.inv_rpow hy.le])
  rw [hint, Real.mul_rpow (by positivity) hAn, Real.mul_rpow (by positivity) hV.le,
    ← Real.rpow_mul h2r.le] at hlower
  filter_upwards [hlower,
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hpos] with x hx hux
  have e : D * (2 * r) ^ (-n / p₀) * ((2 * r) ^ (n * p₀⁻¹) * V ^ p₀⁻¹ * An ^ p₀⁻¹) =
      D * V ^ p₀⁻¹ * An ^ p₀⁻¹ := by
    rw [neg_div, Real.rpow_neg h2r.le, div_eq_mul_inv n p₀]
    field_simp
  rw [e] at hx
  -- Multiply the crossover estimate by the lower bound.
  rw [mul_assoc (K ^ p₀⁻¹) D]
  exact Real.rpow_le_mul_of_mul_le_of_inv_le (inv_nonneg.2 hp₀.le) hAp hAn hcross hx hux

omit [DecidableEq ι] in
/-- **Moser's final step.** If `⨍_{B(x₀, 2r)} f ≤ C₁ f(x)` for almost every `x ∈ B(x₀, 2r)` and
`f(y) ≤ D (2r)^{-n} ∫_{B(x₀, 2r)} f` for almost every `y ∈ B(x₀, r)`, then
`f(y) ≤ D |B(0, 1)| C₁ f(x)` for almost every `x, y ∈ B(x₀, r)`. -/
private theorem ae_ae_le_mul_of_setAverage_le {f : EuclideanSpace ℝ ι → ℝ} {C₁ D r : ℝ}
    {x₀ : EuclideanSpace ℝ ι} (hr : 0 < r) (hD : 0 < D)
    (hw : ∀ᵐ x ∂mu.restrict (ball x₀ (2 * r)), ⨍ y in ball x₀ (2 * r), f y ∂mu ≤ C₁ * f x)
    (hb : ∀ᵐ y ∂mu.restrict (ball x₀ r),
      f y ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ)) * ∫ y in ball x₀ (2 * r), f y ∂mu) :
    ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
      f y ≤ D * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) * C₁ * f x := by
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ Fintype.card ι * V := by
    rw [Measure.addHaar_real_ball_of_pos mu x₀ (by positivity), finrank_euclideanSpace]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hw]
    with x hx
  filter_upwards [hb] with y hy
  rw [setAverage_eq, smul_eq_mul, hvol, inv_mul_le_iff₀ (by positivity)] at hx
  calc f y ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ)) * ∫ y in ball x₀ (2 * r), f y ∂mu := hy
    _ ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ)) * ((2 * r) ^ Fintype.card ι * V * (C₁ * f x)) := by
        gcongr
    _ = D * V * C₁ * f x := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
        field_simp

/-! ### Lower-order terms -/

/-- On the doubled ball the dimensionless lower-order quantities are bounded in terms of `σ`: if
`0 ≤ βr ≤ σλ` and `γr² ≤ σλ`, then `(2βr/λ)² + γ(2r)²/λ ≤ (2σ)² + 4σ`. -/
private theorem sq_div_add_div_le {lam beta gamma r σ : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ beta)
    (hr : 0 ≤ r) (hβr : beta * r ≤ σ * lam) (hγr : gamma * r ^ 2 ≤ σ * lam) :
    (beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam ≤ (2 * σ) ^ 2 + 4 * σ := by
  have h1 : beta * (2 * r) / lam ≤ 2 * σ := by rw [div_le_iff₀ hlam]; linarith
  have h2 : gamma * (2 * r) ^ 2 / lam ≤ 4 * σ := by rw [div_le_iff₀ hlam]; linarith
  have h3 : 0 ≤ beta * (2 * r) / lam := by positivity
  exact add_le_add (pow_le_pow_left₀ h3 h1 2) h2

/-- The weak Harnack inequality at a small exponent with lower-order terms, for supersolutions
bounded below by a positive constant `ε`, with constants independent of `ε`. -/
private theorem exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder
    [Nonempty ι] (σ : ℝ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * r ≤ σ * lam → gamma * r ^ 2 ≤ σ * lam →
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ ≤ C * W1p.value u x := by
  -- Without `0 < λ ≤ Λ` there is no uniformly elliptic `a`, and any constants work.
  by_cases hlL : 0 < lam ∧ lam ≤ Lam
  swap
  · exact ⟨1, one_pos, one_le_two, 1, one_pos,
      fun h _ _ _ _ _ _ _ _ _ _ _ => absurd ⟨h.pos, h.le⟩ hlL⟩
  set σ₀ := max σ 0
  have hσ₀ : 0 ≤ σ₀ := le_max_right σ 0
  -- The exponent `p₀` at which the crossover estimate applies on balls of radius `2r`.
  obtain ⟨c₀, hc₀, K, hcross⟩ :=
    exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder (ι := ι)
  set S := √((Lam / lam) ^ 2 + (2 * σ₀) ^ 2 + 4 * σ₀)
  have hS : 0 < S := Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
    (pow_pos (div_pos (hlL.1.trans_le hlL.2) hlL.1) 2) (sq_nonneg _)) (by linarith))
  set p₀ := min (c₀ / S) 2
  have hp₀ : 0 < p₀ := lt_min (div_pos hc₀ hS) two_pos
  obtain ⟨D, hD, hlower⟩ := exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) (σ := 4 * σ₀) hp₀ (by linarith)
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  set K' := max K 1
  refine ⟨p₀, hp₀, min_le_right _ _, K' ^ p₀⁻¹ * D * V ^ p₀⁻¹, by positivity, ?_⟩
  intro Omega a b c beta gamma u ε x₀ r h ha hb hc hbβ hcγ hu hε hεu hball hβr hγr
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √n := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2r : 0 < 2 * r := by positivity
  have hρΩ : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hβ : 0 ≤ beta := (norm_nonneg _).trans (hbβ x₀ (hρΩ (mem_ball_self h2r)))
  have hσlam : σ * lam ≤ σ₀ * lam := mul_le_mul_of_nonneg_right (le_max_left σ 0) hlL.1.le
  have hσ₀lam : 0 ≤ σ₀ * lam := mul_nonneg hσ₀ hlL.1.le
  have hβ2 : beta * (2 * r) ≤ 4 * σ₀ * lam := by linarith
  have hγ2 : gamma * (2 * r) ^ 2 ≤ 4 * σ₀ * lam := by linarith
  -- The exponent `p₀` is admissible in the crossover estimate on `B(x₀, 2r)`.
  have hp₀c : |p₀| * √((Lam / lam) ^ 2 + (beta * (2 * r) / lam) ^ 2 +
      gamma * (2 * r) ^ 2 / lam) ≤ c₀ := by
    have := sq_div_add_div_le hlL.1 hβ hr.le (hβr.trans hσlam) (hγr.trans hσlam)
    rw [abs_of_pos hp₀, ← div_mul_cancel₀ c₀ hS.ne']
    exact mul_le_mul (min_le_left _ _) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      (div_pos hc₀ hS).le
  have hpos : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 < W1p.value u y :=
    (ae_restrict_of_ae_restrict_of_subset hρΩ hεu).mono fun y hy => hε.trans_le hy
  -- The lower bound `u⁻¹ ≤ D (2r)^{-n/p₀} (∫_B u^{-p₀})^{1/p₀}` on `B(x₀, r)`, `B = B(x₀, 2r)`.
  have h1 := hlower h ha hb hc hbβ hcγ hu hε hεu h2r hρΩ hβ2 hγ2
  rw [mul_div_cancel_left₀ r two_ne_zero] at h1
  -- Combine it with the crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K`.
  exact ae_setAverage_rpow_rpow_inv_le_mul_of_mul_le hp₀ hr hpos ((hcross mu h ha hb hc hbβ hcγ
    hu hε hεu (x₀ := x₀) (r := 2 * r) ((ball_subset_ball (by nlinarith)).trans hball)
    hp₀c).trans (le_max_left K 1)) h1

/-- The weak Harnack inequality with lower-order terms for supersolutions bounded below by a
positive constant `ε`, with constants independent of `ε`. -/
private theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder [Nonempty ι]
    (σ : ℝ) {s : ℝ} (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * r ≤ σ * lam → gamma * r ^ 2 ≤ σ * lam →
      IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu ∧ ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨p₀, hp₀, hp₀2, C₁, hC₁, hsmall⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam) σ
  obtain ⟨D, e, hD, he, hiter⟩ :=
    exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam) hp₀ hp₀2 hs hsn
  set σ₀ := max σ 0
  set F := (1 + √((2 * σ₀) ^ 2 + 4 * σ₀)) ^ e
  refine ⟨D * F * C₁, by positivity, ?_⟩
  intro Omega a b c beta gamma u ε x₀ r h ha hb hc hbβ hcγ hu hε hεu hball hβr hγr
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hlam := h.pos
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2r : 0 < 2 * r := by positivity
  have h2Ω : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hβ : 0 ≤ beta := (norm_nonneg _).trans (hbβ x₀ (h2Ω (mem_ball_self h2r)))
  have hσlam : σ * lam ≤ σ₀ * lam := mul_le_mul_of_nonneg_right (le_max_left σ 0) hlam.le
  -- The lower-order factor of Moser's iteration on `B(x₀, 2r)` is bounded in terms of `σ`.
  have hfac : (1 + √((beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)) ^ e ≤ F :=
    Real.rpow_le_rpow (by positivity) (add_le_add le_rfl (Real.sqrt_le_sqrt
      (sq_div_add_div_le hlam hβ hr.le (hβr.trans hσlam) (hγr.trans hσlam)))) he
  -- Moser's iteration passes from `L^{p₀}` on `B(x₀, 2r)` to `L^s` on `B(x₀, r)`.
  obtain ⟨hint, hiter'⟩ := hiter h ha hb hc hbβ hcγ hu hε hεu (x₀ := x₀) (R := 2 * r) h2Ω
  rw [mul_div_cancel_left₀ r two_ne_zero] at hint hiter'
  refine ⟨hint, ?_⟩
  filter_upwards [hsmall h ha hb hc hbβ hcγ hu hε hεu hball hβr hγr,
    ae_restrict_of_ae_restrict_of_subset ((ball_subset_ball (by linarith)).trans h2Ω) hεu]
    with x hx hux
  calc (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹
      ≤ D * (1 + √((beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)) ^ e *
          (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ := hiter'
    _ ≤ D * (1 + √((beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)) ^ e *
          (C₁ * W1p.value u x) := by gcongr
    _ ≤ D * F * (C₁ * W1p.value u x) := by
        gcongr
        exact mul_nonneg hC₁.le (hε.le.trans hux)
    _ = D * F * C₁ * W1p.value u x := by ring

/-- The weak Harnack inequality with lower-order terms for the shifts `u + δ`, `δ > 0`, of a
nonnegative supersolution `u`, with constants independent of `δ`. -/
private theorem exists_setAverage_add_const_rpow_rpow_inv_le_mul_lowerOrder [Nonempty ι]
    (σ : ℝ) {s : ℝ} (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r δ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * r ≤ σ * lam → gamma * r ^ 2 ≤ σ * lam →
      0 < δ →
      IntegrableOn (fun y => (W1p.value u y + δ) ^ s) (ball x₀ r) mu ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ r),
          (⨍ y in ball x₀ r, (W1p.value u y + δ) ^ s ∂mu) ^ s⁻¹ ≤ C * (W1p.value u x + δ) := by
  obtain ⟨C, hC, hpos⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) σ hs hsn
  refine ⟨C, hC, ?_⟩
  intro Omega a b c beta gamma u x₀ r δ h ha hb hc hbβ hcγ hu hu0 hball hβr hγr hδ0
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(x₀, 8√n r)`, where constants lie in `H¹(U)`. There
  -- `u + δ` is a supersolution bounded below by `δ`, with mass coefficient `c u⁺ / (u⁺ + δ)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (8 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hrU : ball x₀ r ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hum : AEStronglyMeasurable (W1p.value u) (mu.restrict Omega) := Lp.aestronglyMeasurable _
  set w := W1p.restrictL hU u + W1p.const δ
  have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value w y = W1p.value u y + δ := by
    filter_upwards [W1p.value_add_const_ae (W1p.restrictL hU u) δ,
      W1p.value_restrictL_ae hU u] with y h1 h2
    rw [h1, h2]
  have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y := by
    filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hball hu0] with y h1 h2
    rw [h1]
    linarith
  have hc' : AEStronglyMeasurable
      (fun x => c x * (max (W1p.value u x) 0 / (max (W1p.value u x) 0 + δ)))
      (mu.restrict Omega) :=
    hc.mul ((hum.aemeasurable.max aemeasurable_const).div
      ((hum.aemeasurable.max aemeasurable_const).add_const δ)).aestronglyMeasurable
  have hcγ' : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)),
      ‖c x * (max (W1p.value u x) 0 / (max (W1p.value u x) 0 + δ))‖ ≤ gamma := by
    intro x hx
    have hq : ‖max (W1p.value u x) 0 / (max (W1p.value u x) 0 + δ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by linarith) (by positivity)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hq).trans (hcγ x (hball hx))
  obtain ⟨hint, hH⟩ := hpos (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hb.mono_measure (Measure.restrict_mono hball le_rfl))
    (hc'.mono_measure (Measure.restrict_mono hball le_rfl)) (fun x hx => hbβ x (hball hx)) hcγ'
    (energyFormH1_restrictL_add_const_nonneg_mass hU hu
      (ae_restrict_of_ae_restrict_of_subset hball hu0) hδ0) hδ0 hδw (x₀ := x₀) (r := r)
    subset_rfl hβr hγr
  have hwvr := ae_restrict_of_ae_restrict_of_subset hrU hwv
  refine ⟨hint.congr_fun_ae (hwvr.mono fun y hy => congrArg (· ^ s) hy), ?_⟩
  have e : ⨍ y in ball x₀ r, W1p.value w y ^ s ∂mu =
      ⨍ y in ball x₀ r, (W1p.value u y + δ) ^ s ∂mu :=
    average_congr (hwvr.mono fun y hy => congrArg (· ^ s) hy)
  filter_upwards [hH, hwvr] with x hx hwx
  rwa [e, hwx] at hx

/-- **Moser's weak Harnack inequality with lower-order terms.** Let `n ≥ 1` be the dimension, let
`σ` be real and let `s > 0` with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3` and `s`
arbitrary when `n ≤ 2`. There is `C > 0`, depending only on `λ`, `Λ`, `σ`, `s`, the dimension and
the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with
`‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, with no condition on the sign of `c`, and let `u ∈ H¹(Ω)` be a
nonnegative weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for
every nonnegative `v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 8√n r) ⊆ Ω`, `βr ≤ σλ` and
`γr² ≤ σλ`,

`(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

and `u^s` is integrable on `B(x₀, r)`. The lower-order terms enter only through the dimensionless
quantities `βr/λ` and `γr²/λ`, which `σ` bounds. -/
theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder [Nonempty ι] (σ : ℝ) {s : ℝ}
    (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * r ≤ σ * lam → gamma * r ^ 2 ≤ σ * lam →
      IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu ∧ ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨C, hC, hshift⟩ := exists_setAverage_add_const_rpow_rpow_inv_le_mul_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) σ hs hsn
  refine ⟨C, hC, ?_⟩
  intro Omega a b c beta gamma u x₀ r h ha hb hc hbβ hcγ hu hu0 hball hβr hγr
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hu0r : ∀ᵐ y ∂mu.restrict (ball x₀ r), 0 ≤ W1p.value u y :=
    ae_restrict_of_ae_restrict_of_subset ((ball_subset_ball (by nlinarith)).trans hball) hu0
  have hδ := fun {δ : ℝ} (hδ : 0 < δ) => hshift h ha hb hc hbβ hcγ hu hu0 hball hβr hγr hδ
  -- `u^s` is integrable, being dominated by `(u + 1)^s`.
  have hint : IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu :=
    (integrable_and_average_rpow_le hs.le zero_le_one hu0r (hδ one_pos).1).1
  refine ⟨hint, ?_⟩
  have hk : ∀ k : ℕ, ∀ᵐ x ∂mu.restrict (ball x₀ r),
      (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤
        C * (W1p.value u x + 1 / ((k : ℝ) + 1)) := by
    intro k
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨hint', hbound⟩ := hδ hk0
    have hmono := (integrable_and_average_rpow_le hs.le hk0.le hu0r hint').2
    filter_upwards [hbound] with x hx
    exact (Real.rpow_le_rpow (average_nonneg_of_ae (hu0r.mono fun y hy => Real.rpow_nonneg hy _))
      hmono (inv_nonneg.2 hs.le)).trans hx
  -- Let `δ → 0`.
  filter_upwards [ae_all_iff.2 hk] with x hx
  simpa using ge_of_tendsto'
    ((tendsto_one_div_add_atTop_nhds_zero_nat.const_add _).const_mul C) hx

/-- **Moser's Harnack inequality with lower-order terms.** Let `n ≥ 1` be the dimension and let
`σ` be real. There is `C > 0`, depending only on `λ`, `Λ`, `σ`, the dimension and the
normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with
`‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, with no condition on the sign of `c`, and let `u ∈ H¹(Ω)` be a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, that is `a(u, v) = 0` for every
`v ∈ H¹₀(Ω)`, with `u ≥ 0` almost everywhere. Then on every ball with `B(x₀, 16√n r) ⊆ Ω`,
`βr ≤ σλ` and `γr² ≤ σλ`,

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. The lower-order terms enter only
through the dimensionless quantities `βr/λ` and `γr²/λ`, which `σ` bounds. -/
theorem exists_ae_ae_value_le_mul_value_lowerOrder [Nonempty ι] (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (16 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * r ≤ σ * lam → gamma * r ^ 2 ≤ σ * lam →
      ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
        W1p.value u y ≤ C * W1p.value u x := by
  -- On balls of radius `2r` the lower-order terms are bounded by `σ' = 4 max σ 0`.
  set σ' := 4 * max σ 0
  -- The weak Harnack inequality at `s = 1`, and local boundedness in `L¹`.
  obtain ⟨C₁, hC₁, hweak⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) σ' one_pos (by linarith)
  obtain ⟨D, hD, hbdd⟩ := exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) σ' one_pos one_le_two
  have hV : 0 < mu.real (ball (0 : EuclideanSpace ℝ ι) 1) := measureReal_ball_pos mu 0 one_pos
  refine ⟨D * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) * C₁, by positivity, ?_⟩
  intro Omega a b c beta gamma u x₀ r h ha hb hc hbβ hcγ hu hu0 hball hβr hγr
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hlam := h.pos
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hσlam : σ * lam ≤ max σ 0 * lam := mul_le_mul_of_nonneg_right (le_max_left σ 0) hlam.le
  have hσ₀lam : 0 ≤ max σ 0 * lam := mul_nonneg (le_max_right σ 0) hlam.le
  have hβ2 : beta * (2 * r) ≤ σ' * lam := by linarith
  have hγ2 : gamma * (2 * r) ^ 2 ≤ σ' * lam := by linarith
  have h2Ω : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hw := (hweak h ha hb hc hbβ hcγ (fun v _ => (hu v).ge) hu0 (x₀ := x₀) (r := 2 * r)
    ((ball_subset_ball (by nlinarith)).trans hball) hβ2 hγ2).2
  have hb' := hbdd h ha hb hc hbβ hcγ (fun v _ => (hu v).le) h2Ω hβ2 hγ2
  rw [mul_div_cancel_left₀ r two_ne_zero] at hb'
  -- On `B(x₀, 2r)` the positive part of `u` is `u`, so `u ≤ D (2r)^{-n} ∫_{B(x₀, 2r)} u`.
  have hmax : ∫ y in ball x₀ (2 * r), max (W1p.value u y) 0 ^ (1 : ℝ) ∂mu =
      ∫ y in ball x₀ (2 * r), W1p.value u y ∂mu :=
    integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset h2Ω hu0).mono fun y hy => by
      simp [max_eq_left hy])
  rw [hmax, inv_one, Real.rpow_one, div_one] at hb'
  exact ae_ae_le_mul_of_setAverage_le hr hD
    (hw.mono fun x hx => by simpa only [Real.rpow_one, inv_one] using hx) hb'

/-! ### Equations without lower-order terms -/

/-- **Moser's weak Harnack inequality at a small exponent.** Let `n ≥ 1` be the dimension. There
are an exponent `p₀ ∈ (0, 2]` and a constant `C > 0`, depending only on `λ`, `Λ`, the dimension
and the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
nonnegative weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every
nonnegative `v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 8√n r) ⊆ Ω`,

`(⨍_{B(x₀, 2r)} u^{p₀})^{1/p₀} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`.

The constant does not depend on `u` or the ball. -/
theorem exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value [Nonempty ι] :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨p₀, hp₀, hp₀2, C, hC, hpos⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam) 0
  refine ⟨p₀, hp₀, hp₀2, C, hC, fun {Omega a u x₀ r} h ha hu hu0 hball => ?_⟩
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(x₀, 8√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (8 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have h2U : ball x₀ (2 * r) ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have hrU : ball x₀ r ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (ball x₀ (2 * r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hu02 : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 ≤ W1p.value u y :=
    ae_restrict_of_ae_restrict_of_subset (h2U.trans hball) hu0
  have hmem : MemLp (W1p.value u) (ENNReal.ofReal p₀) (mu.restrict (ball x₀ (2 * r))) :=
    ((Lp.memLp _).mono_measure (Measure.restrict_mono (h2U.trans hball) le_rfl)).mono_exponent
      ((ENNReal.ofReal_le_ofReal hp₀2).trans_eq (ENNReal.ofReal_ofNat 2))
  -- For each `δ = 1/(k + 1)`, the estimate for the positive supersolution `u + δ` on `U`.
  have hδ : ∀ k : ℕ, ∀ᵐ x ∂mu.restrict (ball x₀ r),
      (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ ≤
        C * (W1p.value u x + 1 / ((k : ℝ) + 1)) := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ0 : 0 < δ := Nat.one_div_pos_of_nat
    set w := W1p.restrictL hU u + W1p.const δ
    have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value w y = W1p.value u y + δ :=
      ((W1p.value_add_const_ae _ δ).and (W1p.value_restrictL_ae hU u)).mono fun y h => by
        rw [h.1, h.2]
    have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y :=
      (hwv.and (ae_restrict_of_ae_restrict_of_subset hball hu0)).mono fun y h =>
        (le_add_of_nonneg_left h.2).trans_eq h.1.symm
    -- The case `b = 0`, `c = 0` of the estimate with lower-order terms.
    have hH := hpos (b := 0) (c := 0) (beta := 0) (gamma := 0) (h.mono_set hball)
      (ha.mono_measure (Measure.restrict_mono hball le_rfl)) aestronglyMeasurable_const
      aestronglyMeasurable_const (by simp) (by simp)
      (energyFormH1_restrictL_add_const_nonneg hU hu δ) hδ0 hδw (x₀ := x₀) (r := r) subset_rfl
      (by simp) (by simp)
    rw [average_congr ((ae_restrict_of_ae_restrict_of_subset h2U hwv).mono fun y hy =>
      congrArg (· ^ p₀) hy)] at hH
    -- The average of `u^{p₀}` is at most that of `(u + δ)^{p₀}`.
    have hmono := average_rpow_le_average_add_const_rpow hp₀ hδ0.le hmem hu02
    filter_upwards [hH, ae_restrict_of_ae_restrict_of_subset hrU hwv] with x hx hwx
    exact (Real.rpow_le_rpow (average_nonneg_of_ae (hu02.mono fun y hy => Real.rpow_nonneg hy _))
      hmono (inv_nonneg.2 hp₀.le)).trans (hx.trans_eq (by rw [hwx]))
  -- Let `δ → 0`.
  filter_upwards [ae_all_iff.2 hδ] with x hx
  simpa using ge_of_tendsto'
    ((tendsto_one_div_add_atTop_nhds_zero_nat.const_add _).const_mul C) hx

/-- **Moser's weak Harnack inequality.** Let `n ≥ 1` be the dimension. For every exponent `s > 0`
with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3` and `s` arbitrary when `n ≤ 2`, there
is `C > 0`, depending only on `λ`, `Λ`, `s`, the dimension and the normalization of the additive
Haar measure `mu`, with the following property. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a nonnegative weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Then on every ball
with `B(x₀, 8√n r) ⊆ Ω`,

`(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

and `u^s` is integrable on `B(x₀, r)`, so the left side is a genuine average even for `s > 2`.
The constant does not depend on `u` or the ball. -/
theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value [Nonempty ι] {s : ℝ} (hs : 0 < s)
    (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (8 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu ∧ ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨C, hC, hK⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder (mu := mu)
    (lam := lam) (Lam := Lam) 0 hs hsn
  refine ⟨C, hC, fun h ha hu hu0 hball => ?_⟩
  -- The case `b = 0`, `c = 0` of the inequality with lower-order terms.
  exact hK (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (by simp) (by simp) hu hu0 hball (by simp) (by simp)

/-- **Moser's Harnack inequality.** Let `n ≥ 1` be the dimension. There is `C > 0`, depending
only on `λ`, `Λ`, the dimension and the normalization of the additive Haar measure `mu`, with the
following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`,
and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every
`v ∈ H¹₀(Ω)`, with `u ≥ 0` almost everywhere. Then on every ball with `B(x₀, 16√n r) ⊆ Ω`,

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. The constant does not depend on `u`
or the ball. -/
theorem exists_ae_ae_value_le_mul_value [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (16 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
        W1p.value u y ≤ C * W1p.value u x := by
  obtain ⟨C, hC, hK⟩ := exists_ae_ae_value_le_mul_value_lowerOrder (mu := mu) (lam := lam)
    (Lam := Lam) 0
  refine ⟨C, hC, fun h ha hu hu0 hball => ?_⟩
  -- The case `b = 0`, `c = 0` of the inequality with lower-order terms.
  exact hK (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (by simp) (by simp) hu hu0 hball (by simp) (by simp)

end PDE

end TauCeti
