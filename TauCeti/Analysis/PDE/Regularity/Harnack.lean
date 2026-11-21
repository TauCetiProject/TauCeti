/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Crossover
public import TauCeti.Analysis.PDE.Regularity.ReverseHolder
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.LowerOrder
import TauCeti.Analysis.PDE.Regularity.Supersolution.LowerOrder
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Moser's weak Harnack inequality and the Harnack inequality

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let `b`
and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`. This file proves, in every dimension
`n ≥ 1`, the two Harnack inequalities of Moser for the full divergence-form equation
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, with no regularity of the coefficients beyond measurability
and no condition on the sign of `c`. The lower-order terms enter only through the dimensionless
quantities `βr/λ` and `γr²/λ` on the balls of radius `r` considered, which a parameter `σ`
bounds.

* The **weak Harnack inequality**: if `u ∈ H¹(Ω)` is a weak supersolution, `a(u, v) ≥ 0` for
  every nonnegative `v ∈ H¹₀(Ω)`, and `u ≥ 0` almost everywhere, then for every exponent `s > 0`
  with `(n - 2) s < n` (that is `s < n/(n - 2)` when `n ≥ 3`, and any `s > 0` when `n ≤ 2`) and
  every ball with `B(x₀, 8√n r) ⊆ Ω`, `βr ≤ σλ` and `γr² ≤ σλ`,

  `(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

  that is, the `L^s` average of `u` is controlled by its essential infimum. In particular `u^s`
  is integrable on `B(x₀, r)`, which is part of the conclusion.
* The **Harnack inequality**: if `u` is a weak solution, `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`,
  and `u ≥ 0` almost everywhere, then on every ball with `B(x₀, 16√n r) ⊆ Ω`, `βr ≤ σλ` and
  `γr² ≤ σλ`,

  `u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

  that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`.

In both, `C` depends only on `λ`, `Λ`, `σ`, the dimension, the normalization of the Haar measure
and, for the weak Harnack inequality, the exponent `s`. It does not depend on `u`, on the ball or
otherwise on `b` and `c`. For `b = 0` and `c = 0` the conditions on `β` and `γ` are void, and the
estimates are scale invariant (`TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value`,
`TauCeti.PDE.exists_ae_ae_value_le_mul_value`).

The weak Harnack inequality at a small exponent is first proved for supersolutions with
`u ≥ ε > 0`, with a constant independent of `ε`, as in Moser's proof. On `B = B(x₀, 2r)`, at an
exponent `p₀ ≤ 2` small enough for the crossover estimate, it combines

* the lower bound from negative powers, `u⁻¹ ≤ D |B|^{-1/p₀} ‖u⁻¹‖_{L^{p₀}(B)}` on `B(x₀, r)`
  (`TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`), with
* the crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K`, from the John–Nirenberg inequality for
  `log u` (`TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder`).

Together they bound `(⨍_B u^{p₀})^{1/p₀}` by `C u(x)` for almost every `x ∈ B(x₀, r)`. Moser's
iteration for small positive powers
(`TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder`) then
raises the exponent from `p₀` to any `s` with `(n - 2) s < n`. A nonnegative supersolution is
reduced to the positive case on the bounded ball `U = B(x₀, 8√n r)`, where constants lie in `H¹`:
`u + δ` is a supersolution on `U` for the mass coefficient `c u / (u + δ)`, which is bounded by
`|c|` (`TauCeti.PDE.exists_energyFormH1_restrictL_add_const_nonneg`), and then `δ → 0`; this
step uses no sign condition on `c`. The Harnack inequality combines the weak Harnack
inequality at `s = 1`, which is admissible in every dimension, with the local boundedness of
subsolutions in `L¹` (`TauCeti.PDE.exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`).

## Main declarations

* `TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`: the weak Harnack
  inequality at a small exponent `p₀`, for nonnegative supersolutions with lower-order terms;
  `TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value` is its case `b = 0`, `c = 0`.
* `TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`: Moser's weak Harnack
  inequality for nonnegative supersolutions with lower-order terms, for every exponent `s > 0`
  with `(n - 2) s < n`; `TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value` is its case
  `b = 0`, `c = 0`.
* `TauCeti.PDE.exists_ae_ae_value_le_mul_value_lowerOrder`: Moser's Harnack inequality for
  nonnegative solutions with lower-order terms; `TauCeti.PDE.exists_ae_ae_value_le_mul_value` is
  its case `b = 0`, `c = 0`.

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

/-- On the ball of radius `2 r`, the bounds `β r ≤ σ λ` and `γ r² ≤ σ λ` become
`β (2 r) ≤ τ λ` and `γ (2 r)² ≤ τ λ` with `τ = 4 max σ 0`, and the dimensionless size
`(β (2 r) / λ)² + γ (2 r)² / λ` of the lower-order coefficients is at most `τ² + τ`. -/
private lemma lowerOrder_two_mul_le {lam beta gamma σ r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hbeta : 0 ≤ beta) (hβ : beta * r ≤ σ * lam) (hγ : gamma * r ^ 2 ≤ σ * lam) :
    beta * (2 * r) ≤ 4 * max σ 0 * lam ∧ gamma * (2 * r) ^ 2 ≤ 4 * max σ 0 * lam ∧
      (beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam ≤
        (4 * max σ 0) ^ 2 + 4 * max σ 0 := by
  have hσ : σ * lam ≤ max σ 0 * lam := mul_le_mul_of_nonneg_right (le_max_left σ 0) hlam.le
  have h0 : 0 ≤ max σ 0 * lam := mul_nonneg (le_max_right σ 0) hlam.le
  have h1 : beta * (2 * r) ≤ 4 * max σ 0 * lam := by nlinarith
  have h2 : gamma * (2 * r) ^ 2 ≤ 4 * max σ 0 * lam := by nlinarith
  refine ⟨h1, h2, add_le_add (pow_le_pow_left₀ (by positivity) ?_ 2) ?_⟩
  · rwa [div_le_iff₀ hlam]
  · rwa [div_le_iff₀ hlam]

omit [DecidableEq ι] in
/-- Multiplying the crossover estimate on `B = B(x₀, 2r)` by Moser's lower bound from negative
powers: if `f > 0` almost everywhere on `B`, `⨍_B f^p · ⨍_B f^{-p} ≤ K` and
`f⁻¹ ≤ D (2r)^{-n/p} (∫_B f^{-p})^{1/p}` almost everywhere on `B(x₀, r)`, then
`(⨍_B f^p)^{1/p} ≤ K^{1/p} D |B(0, 1)|^{1/p} f` almost everywhere on `B(x₀, r)`. -/
private lemma ae_setAverage_rpow_rpow_inv_le_of_mul_le_of_inv_le {f : EuclideanSpace ℝ ι → ℝ}
    {x₀ : EuclideanSpace ℝ ι} {r p D K : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hf : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 < f y)
    (hcross : (⨍ y in ball x₀ (2 * r), f y ^ p ∂mu) * (⨍ y in ball x₀ (2 * r), f y ^ (-p) ∂mu) ≤
      K)
    (hlower : ∀ᵐ x ∂mu.restrict (ball x₀ r), (f x)⁻¹ ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / p) *
      (∫ y in ball x₀ (2 * r), (f y)⁻¹ ^ p ∂mu) ^ p⁻¹) :
    ∀ᵐ x ∂mu.restrict (ball x₀ r), (⨍ y in ball x₀ (2 * r), f y ^ p ∂mu) ^ p⁻¹ ≤
      K ^ p⁻¹ * D * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ p⁻¹ * f x := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  have h2r : 0 < 2 * r := by positivity
  set Ap := ⨍ y in ball x₀ (2 * r), f y ^ p ∂mu
  set An := ⨍ y in ball x₀ (2 * r), f y ^ (-p) ∂mu
  have hAp : 0 ≤ Ap := average_nonneg_of_ae (hf.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  have hAn : 0 ≤ An := average_nonneg_of_ae (hf.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  -- The lower bound in averaged form: `∫_B f^{-p} = |B| ⨍_B f^{-p}` with `|B| = (2r)ⁿ V`.
  have hint : ∫ y in ball x₀ (2 * r), (f y)⁻¹ ^ p ∂mu = (2 * r) ^ n * V * An := by
    have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ n * V := by
      rw [Measure.addHaar_real_ball_of_pos mu x₀ h2r, finrank_euclideanSpace,
        ← Real.rpow_natCast]
    rw [← hvol, ← smul_eq_mul (mu.real _) An, measure_smul_setAverage _ measure_ball_lt_top.ne]
    exact integral_congr_ae (hf.mono fun y hy => by
      simp only [Real.rpow_neg hy.le, Real.inv_rpow hy.le])
  rw [hint, Real.mul_rpow (by positivity) hAn, Real.mul_rpow (by positivity) hV.le,
    ← Real.rpow_mul h2r.le] at hlower
  filter_upwards [hlower, ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hf]
    with x hx hux
  have e : D * (2 * r) ^ (-n / p) * ((2 * r) ^ (n * p⁻¹) * V ^ p⁻¹ * An ^ p⁻¹) =
      D * V ^ p⁻¹ * An ^ p⁻¹ := by
    rw [neg_div, Real.rpow_neg h2r.le, div_eq_mul_inv n p]
    field_simp
  rw [e] at hx
  -- Multiply the crossover estimate by the lower bound.
  rw [mul_assoc (K ^ p⁻¹) D]
  exact Real.rpow_le_mul_of_mul_le_of_inv_le (inv_nonneg.2 hp.le) hAp hAn hcross hx hux

/-- The weak Harnack inequality at a small exponent for supersolutions with lower-order terms
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
  · exact ⟨1, one_pos, one_le_two, 1, one_pos, fun h => absurd ⟨h.pos, h.le⟩ hlL⟩
  -- The exponent `p₀` at which the crossover estimate applies on the balls `B(x₀, 2r)`.
  obtain ⟨c₀, hc₀, K, hcross⟩ :=
    exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder (ι := ι)
  have hQ : 0 < (Lam / lam) ^ 2 + (4 * max σ 0) ^ 2 + 4 * max σ 0 := by
    have := div_pos (hlL.1.trans_le hlL.2) hlL.1
    positivity
  set p₀ := min (c₀ / √((Lam / lam) ^ 2 + (4 * max σ 0) ^ 2 + 4 * max σ 0)) 2
  have hp₀ : 0 < p₀ := lt_min (div_pos hc₀ (Real.sqrt_pos.2 hQ)) two_pos
  obtain ⟨D, hD, hlower⟩ := exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder
    (mu := mu) (lam := lam) (Lam := Lam) hp₀ (by positivity : 0 ≤ 4 * max σ 0)
  have hV : 0 < mu.real (ball (0 : EuclideanSpace ℝ ι) 1) := measureReal_ball_pos mu 0 one_pos
  refine ⟨p₀, hp₀, min_le_right _ _,
    max K 1 ^ p₀⁻¹ * D * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ p₀⁻¹, by positivity, ?_⟩
  intro Omega a b c beta gamma u ε x₀ r h ha hb hc hb_bound hc_bound hu hε hεu hball hβ hγ
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2r : 0 < 2 * r := by positivity
  have hρΩ : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hρΩ (mem_ball_self h2r)
  obtain ⟨hβ2, hγ2, hsize⟩ := lowerOrder_two_mul_le hlL.1 hr.le
    ((norm_nonneg _).trans (hb_bound x₀ hx₀)) hβ hγ
  -- The exponent `p₀` is admissible in the crossover estimate on `B(x₀, 2r)`.
  have hp₀c : |p₀| * √((Lam / lam) ^ 2 + (beta * (2 * r) / lam) ^ 2 +
      gamma * (2 * r) ^ 2 / lam) ≤ c₀ := by
    rw [abs_of_pos hp₀]
    calc p₀ * √((Lam / lam) ^ 2 + (beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)
        ≤ c₀ / √((Lam / lam) ^ 2 + (4 * max σ 0) ^ 2 + 4 * max σ 0) *
            √((Lam / lam) ^ 2 + (4 * max σ 0) ^ 2 + 4 * max σ 0) := by
          refine mul_le_mul (min_le_left _ _) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            (div_nonneg hc₀.le (Real.sqrt_nonneg _))
          linarith
      _ = c₀ := div_mul_cancel₀ _ (Real.sqrt_pos.2 hQ).ne'
  have hpos : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 < W1p.value u y :=
    (ae_restrict_of_ae_restrict_of_subset hρΩ hεu).mono fun y hy => hε.trans_le hy
  -- The crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K` on `B = B(x₀, 2r)`.
  have hcross' := (hcross mu h ha hb hc hb_bound hc_bound hu hε hεu (x₀ := x₀) (r := 2 * r)
    ((ball_subset_ball (le_of_eq (by ring))).trans hball) hp₀c).trans (le_max_left K 1)
  -- The lower bound `u⁻¹ ≤ D (2r)^{-n/p₀} (∫_B u^{-p₀})^{1/p₀}` on `B(x₀, r)`.
  have h1 := hlower h ha hb hc hb_bound hc_bound hu hε hεu h2r hρΩ hβ2 hγ2
  rw [mul_div_cancel_left₀ r two_ne_zero] at h1
  exact ae_setAverage_rpow_rpow_inv_le_of_mul_le_of_inv_le hr hp₀ hpos hcross' h1

omit [DecidableEq ι] in
/-- **From positive to nonnegative supersolutions.** Let `u ∈ H¹(Ω)` be a nonnegative weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, and let `U ⊆ Ω` be open, of finite measure and
contain the balls `B(x₀, ρ)` and `B(x₀, r)`. Suppose that every weak supersolution `w ∈ H¹(U)` with
`w ≥ ε > 0`, for the same `a`, `b` and a measurable mass coefficient `c'` with `|c'| ≤ |c|`, has
`w^s` integrable on `B(x₀, ρ)` and `(⨍_{B(x₀, ρ)} w^s)^{1/s} ≤ C w(x)` for almost every
`x ∈ B(x₀, r)`. Then so does `u`. -/
private theorem integrableOn_and_ae_setAverage_rpow_rpow_inv_le_of_forall_pos
    {Omega U : Opens (EuclideanSpace ℝ ι)} (hU : U ≤ Omega) [IsFiniteMeasure (mu.restrict U)]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ r s C : ℝ}
    (hs : 0 < s) (hρ : ball x₀ ρ ⊆ (U : Set (EuclideanSpace ℝ ι)))
    (hr : ball x₀ r ⊆ (U : Set (EuclideanSpace ℝ ι)))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    (hu0 : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x)
    (hpos : ∀ {c' : EuclideanSpace ℝ ι → ℝ} {w : W1p mu U 2} {ε : ℝ},
      AEStronglyMeasurable c' (mu.restrict U) → (∀ x, ‖c' x‖ ≤ ‖c x‖) →
      (∀ v : W1p0 mu U 2, (∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) →
        0 ≤ energyFormH1 a b c' w (v : W1p mu U 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict U, ε ≤ W1p.value w x) →
      IntegrableOn (fun y => W1p.value w y ^ s) (ball x₀ ρ) mu ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ r),
          (⨍ y in ball x₀ ρ, W1p.value w y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value w x) :
    IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ ρ) mu ∧
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ ρ, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  have hUO : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  have hu0ρ : ∀ᵐ y ∂mu.restrict (ball x₀ ρ), 0 ≤ W1p.value u y :=
    ae_restrict_of_ae_restrict_of_subset (hρ.trans hUO) hu0
  -- For each `δ = 1/(k + 1)`, the estimate for the positive supersolution `u + δ` on `U`.
  have hδ : ∀ k : ℕ, IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ ρ) mu ∧
      ∀ᵐ x ∂mu.restrict (ball x₀ r), (⨍ y in ball x₀ ρ, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤
        C * (W1p.value u x + 1 / ((k : ℝ) + 1)) := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ0 : 0 < δ := Nat.one_div_pos_of_nat
    obtain ⟨c', hc', hc'c, hw⟩ := exists_energyFormH1_restrictL_add_const_nonneg hU hc hu hu0 hδ0
    set w := W1p.restrictL hU u + W1p.const δ
    have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value w y = W1p.value u y + δ := by
      filter_upwards [W1p.value_add_const_ae (W1p.restrictL hU u) δ,
        W1p.value_restrictL_ae hU u] with y h1 h2
      rw [h1, h2]
    have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y := by
      filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hUO hu0] with y h1 h2
      rw [h1]
      linarith
    obtain ⟨hint, hH⟩ := hpos hc' hc'c hw hδ0 hδw
    have hwvρ := ae_restrict_of_ae_restrict_of_subset hρ hwv
    have e : ⨍ y in ball x₀ ρ, W1p.value w y ^ s ∂mu =
        ⨍ y in ball x₀ ρ, (W1p.value u y + δ) ^ s ∂mu :=
      average_congr (hwvρ.mono fun y hy => by simp only [hy])
    rw [e] at hH
    -- `0 ≤ u^s ≤ (u + δ)^s`, and `(u + δ)^s` is integrable on `B(x₀, ρ)`, hence so is `u^s`.
    obtain ⟨hint₀, hmono⟩ := integrable_and_average_rpow_le hs.le hδ0.le hu0ρ
      (hint.congr (hwvρ.mono fun y hy => congrArg (· ^ s) hy))
    refine ⟨hint₀, ?_⟩
    filter_upwards [hH, ae_restrict_of_ae_restrict_of_subset hr hwv] with x hx hwx
    rw [hwx] at hx
    exact (Real.rpow_le_rpow (average_nonneg_of_ae (hu0ρ.mono fun y hy => Real.rpow_nonneg hy _))
      hmono (inv_nonneg.2 hs.le)).trans hx
  -- Let `δ → 0`.
  refine ⟨(hδ 0).1, ?_⟩
  filter_upwards [ae_all_iff.2 fun k => (hδ k).2] with x hx
  simpa using ge_of_tendsto'
    ((tendsto_one_div_add_atTop_nhds_zero_nat.const_add _).const_mul C) hx

/-- **Moser's weak Harnack inequality at a small exponent, with lower-order terms.** Let `n ≥ 1`
be the dimension and `σ` real. There are an exponent `p₀ ∈ (0, 2]` and a constant `C > 0`,
depending only on `λ`, `Λ`, `σ`, the dimension and the normalization of the additive Haar measure
`mu`, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let
`u ∈ H¹(Ω)` be a nonnegative weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is
`a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 8√n r) ⊆ Ω`,
`βr ≤ σλ` and `γr² ≤ σλ`,

`(⨍_{B(x₀, 2r)} u^{p₀})^{1/p₀} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`.

The constant does not depend on `u`, on the ball or on the sign of `c`. -/
theorem exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder [Nonempty ι] (σ : ℝ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
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
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ ≤ C * W1p.value u x := by
  obtain ⟨p₀, hp₀, hp₀2, C, hC, hpos⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam) σ
  refine ⟨p₀, hp₀, hp₀2, C, hC, ?_⟩
  intro Omega a b c beta gamma u x₀ r h ha hb hc hb_bound hc_bound hu hu0 hball hβ hγ
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(x₀, 8√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (8 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have h2U : ball x₀ (2 * r) ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (ball x₀ (2 * r))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmono : mu.restrict U ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  refine (integrableOn_and_ae_setAverage_rpow_rpow_inv_le_of_forall_pos hU hp₀ h2U
    (ball_subset_ball (by nlinarith)) hc hu hu0 fun {c' w ε} hc' hc'c hw hε hεw => ⟨?_, ?_⟩).2
  · -- `w ∈ L²(U)` and `p₀ ≤ 2`, so `w^{p₀}` is integrable on the ball `B(x₀, 2r) ⊆ U`.
    exact MemLp.integrable_rpow hp₀
      (((Lp.memLp (W1p.value w)).mono_measure (Measure.restrict_mono h2U le_rfl)).mono_exponent
        ((ENNReal.ofReal_le_ofReal hp₀2).trans_eq (ENNReal.ofReal_ofNat 2)))
  · exact hpos (h.mono_set hball) (ha.mono_measure hmono) (hb.mono_measure hmono) hc'
      (fun x hx => hb_bound x (hball hx)) (fun x hx => (hc'c x).trans (hc_bound x (hball hx))) hw
      hε hεw subset_rfl hβ hγ

/-- **Moser's weak Harnack inequality at a small exponent.** Let `n ≥ 1` be the dimension. There
are an exponent `p₀ ∈ (0, 2]` and a constant `C > 0`, depending only on `λ`, `Λ`, the dimension
and the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
nonnegative weak supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every
nonnegative `v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 8√n r) ⊆ Ω`,

`(⨍_{B(x₀, 2r)} u^{p₀})^{1/p₀} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`.

The constant does not depend on `u` or the ball. This is the case `b = 0`, `c = 0` of
`TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`. -/
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
  obtain ⟨p₀, hp₀, hp₀2, C, hC, H⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam) 0
  exact ⟨p₀, hp₀, hp₀2, C, hC, fun h ha hu hu0 hball =>
    H (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) hu hu0 hball
      (by simp) (by simp)⟩

/-- **Moser's weak Harnack inequality, with lower-order terms.** Let `n ≥ 1` be the dimension and
`σ` real. For every exponent `s > 0` with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3`
and `s` arbitrary when `n ≤ 2`, there is `C > 0`, depending only on `λ`, `Λ`, `σ`, `s`, the
dimension and the normalization of the additive Haar measure `mu`, with the following property.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be
measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a nonnegative weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 8√n r) ⊆ Ω`, `βr ≤ σλ` and `γr² ≤ σλ`,

`(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

and `u^s` is integrable on `B(x₀, r)`, so the left side is a genuine average even for `s > 2`.
The constant does not depend on `u`, on the ball or on the sign of `c`. -/
theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder [Nonempty ι] (σ : ℝ)
    {s : ℝ} (hs : 0 < s) (hsn : ((Fintype.card ι : ℝ) - 2) * s < Fintype.card ι) :
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
  obtain ⟨p₀, hp₀, hp₀2, C₁, hC₁, hsmall⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos_lowerOrder (mu := mu) (lam := lam)
      (Lam := Lam) σ
  obtain ⟨D, e, hD, he, hiter⟩ :=
    exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam) hp₀ hp₀2 hs hsn
  refine ⟨D * (1 + √((4 * max σ 0) ^ 2 + 4 * max σ 0)) ^ e * C₁, by positivity, ?_⟩
  intro Omega a b c beta gamma u x₀ r h ha hb hc hb_bound hc_bound hu hu0 hball hβ hγ
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(x₀, 8√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (8 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have h2U : ball x₀ (2 * r) ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmono : mu.restrict U ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  -- The factor of Moser's iteration on `B(x₀, 2r)` is bounded in terms of `σ`.
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball (mem_ball_self (by positivity))
  obtain ⟨-, -, hsize⟩ := lowerOrder_two_mul_le h.pos hr.le
    ((norm_nonneg _).trans (hb_bound x₀ hx₀)) hβ hγ
  have hF : (1 + √((beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)) ^ e ≤
      (1 + √((4 * max σ 0) ^ 2 + 4 * max σ 0)) ^ e := by
    gcongr
  refine integrableOn_and_ae_setAverage_rpow_rpow_inv_le_of_forall_pos hU hs
    (ball_subset_ball (by nlinarith)) (ball_subset_ball (by nlinarith)) hc hu hu0
    fun {c' w ε} hc' hc'c hw hε hεw => ?_
  have hU' := h.mono_set hball
  have ha' := ha.mono_measure hmono
  have hb' := hb.mono_measure hmono
  have hb_bound' : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta :=
    fun x hx => hb_bound x (hball hx)
  have hc'_bound : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖c' x‖ ≤ gamma :=
    fun x hx => (hc'c x).trans (hc_bound x (hball hx))
  -- Moser's iteration passes from `L^{p₀}` on `B(x₀, 2r)` to `L^s` on `B(x₀, r)`.
  obtain ⟨hint, hiter'⟩ := hiter hU' ha' hb' hc' hb_bound' hc'_bound hw hε hεw (x₀ := x₀)
    (R := 2 * r) h2U
  rw [mul_div_cancel_left₀ r two_ne_zero] at hint hiter'
  refine ⟨hint, ?_⟩
  have hA : 0 ≤ (⨍ y in ball x₀ (2 * r), W1p.value w y ^ p₀ ∂mu) ^ p₀⁻¹ :=
    Real.rpow_nonneg (average_nonneg_of_ae ((ae_restrict_of_ae_restrict_of_subset h2U hεw).mono
      fun y hy => Real.rpow_nonneg (hε.le.trans hy) _)) _
  filter_upwards [hsmall hU' ha' hb' hc' hb_bound' hc'_bound hw hε hεw subset_rfl hβ hγ] with x hx
  calc (⨍ y in ball x₀ r, W1p.value w y ^ s ∂mu) ^ s⁻¹
      ≤ D * (1 + √((beta * (2 * r) / lam) ^ 2 + gamma * (2 * r) ^ 2 / lam)) ^ e *
          (⨍ y in ball x₀ (2 * r), W1p.value w y ^ p₀ ∂mu) ^ p₀⁻¹ := hiter'
    _ ≤ D * (1 + √((4 * max σ 0) ^ 2 + 4 * max σ 0)) ^ e * (C₁ * W1p.value w x) := by
        gcongr
    _ = D * (1 + √((4 * max σ 0) ^ 2 + 4 * max σ 0)) ^ e * C₁ * W1p.value w x := by ring

/-- **Moser's weak Harnack inequality.** Let `n ≥ 1` be the dimension. For every exponent `s > 0`
with `(n - 2) s < n`, that is `s < n/(n - 2)` when `n ≥ 3` and `s` arbitrary when `n ≤ 2`, there
is `C > 0`, depending only on `λ`, `Λ`, `s`, the dimension and the normalization of the additive
Haar measure `mu`, with the following property. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a nonnegative weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Then on every ball
with `B(x₀, 8√n r) ⊆ Ω`,

`(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

and `u^s` is integrable on `B(x₀, r)`, so the left side is a genuine average even for `s > 2`.
The constant does not depend on `u` or the ball. This is the case `b = 0`, `c = 0` of
`TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder`. -/
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
  obtain ⟨C, hC, H⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder (mu := mu)
    (lam := lam) (Lam := Lam) 0 hs hsn
  exact ⟨C, hC, fun h ha hu hu0 hball =>
    H (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) hu hu0 hball
      (by simp) (by simp)⟩

/-- **Moser's Harnack inequality, with lower-order terms.** Let `n ≥ 1` be the dimension and `σ`
real. There is `C > 0`, depending only on `λ`, `Λ`, `σ`, the dimension and the normalization of
the additive Haar measure `mu`, with the following property. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ`
on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, that is
`a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, with `u ≥ 0` almost everywhere. Then on every ball with
`B(x₀, 16√n r) ⊆ Ω`, `βr ≤ σλ` and `γr² ≤ σλ`,

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. The constant does not depend on `u`, on
the ball or on the sign of `c`. -/
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
  -- The weak Harnack inequality at `s = 1` and local boundedness in `L¹`, both on balls of
  -- radius `2r`, where the lower-order coefficients are bounded by `4 max σ 0`.
  obtain ⟨C₁, hC₁, hweak⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_lowerOrder (mu := mu)
    (lam := lam) (Lam := Lam) (4 * max σ 0) one_pos (by linarith)
  obtain ⟨D, hD, hbdd⟩ := exists_ae_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder (mu := mu)
    (lam := lam) (Lam := Lam) (4 * max σ 0) one_pos one_le_two
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  refine ⟨D * V * C₁, by positivity, ?_⟩
  intro Omega a b c beta gamma u x₀ r h ha hb hc hb_bound hc_bound hu hu0 hball hβ hγ
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2Ω : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := h2Ω (mem_ball_self (by positivity))
  obtain ⟨hβ2, hγ2, -⟩ := lowerOrder_two_mul_le h.pos hr.le
    ((norm_nonneg _).trans (hb_bound x₀ hx₀)) hβ hγ
  have hw := (hweak h ha hb hc hb_bound hc_bound (fun v _ => (hu v).ge) hu0 (x₀ := x₀)
    (r := 2 * r) ((ball_subset_ball (le_of_eq (by ring))).trans hball) hβ2 hγ2).2
  have hb' := hbdd h ha hb hc hb_bound hc_bound (fun v _ => (hu v).le) h2Ω hβ2 hγ2
  rw [mul_div_cancel_left₀ r two_ne_zero] at hb'
  -- On `B(x₀, 2r)` the positive part of `u` is `u`, so `u ≤ D (2r)^{-n} ∫_{B(x₀, 2r)} u`.
  have hmax : ∫ y in ball x₀ (2 * r), max (W1p.value u y) 0 ^ (1 : ℝ) ∂mu =
      ∫ y in ball x₀ (2 * r), W1p.value u y ∂mu :=
    integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset h2Ω hu0).mono fun y hy => by
      simp [max_eq_left hy])
  have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ Fintype.card ι * V := by
    rw [Measure.addHaar_real_ball_of_pos mu x₀ (by positivity), finrank_euclideanSpace]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hw]
    with x hx
  filter_upwards [hb'] with y hy
  rw [hmax, inv_one, Real.rpow_one] at hy
  simp only [Real.rpow_one, inv_one] at hx
  rw [setAverage_eq, smul_eq_mul, hvol, inv_mul_le_iff₀ (by positivity)] at hx
  calc W1p.value u y
      ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / 1) * ∫ y in ball x₀ (2 * r), W1p.value u y ∂mu := hy
    _ ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / 1) * ((2 * r) ^ Fintype.card ι * V *
          (C₁ * W1p.value u x)) := by gcongr
    _ = D * V * C₁ * W1p.value u x := by
        rw [div_one, Real.rpow_neg (by positivity), Real.rpow_natCast]
        field_simp

/-- **Moser's Harnack inequality.** Let `n ≥ 1` be the dimension. There is `C > 0`, depending
only on `λ`, `Λ`, the dimension and the normalization of the additive Haar measure `mu`, with the
following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`,
and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every
`v ∈ H¹₀(Ω)`, with `u ≥ 0` almost everywhere. Then on every ball with `B(x₀, 16√n r) ⊆ Ω`,

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. The constant does not depend on `u`
or the ball. This is the case `b = 0`, `c = 0` of
`TauCeti.PDE.exists_ae_ae_value_le_mul_value_lowerOrder`. -/
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
  obtain ⟨C, hC, H⟩ := exists_ae_ae_value_le_mul_value_lowerOrder (mu := mu) (lam := lam)
    (Lam := Lam) 0
  exact ⟨C, hC, fun h ha hu hu0 hball =>
    H (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) hu hu0 hball
      (by simp) (by simp)⟩

end PDE

end TauCeti
