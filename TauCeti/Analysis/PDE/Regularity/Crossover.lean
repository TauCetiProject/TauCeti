/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Logarithm
public import TauCeti.MeasureTheory.Integral.JohnNirenberg
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Moser's crossover estimate for positive supersolutions

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants `0 < λ ≤ Λ`, and
let `u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ ε` almost everywhere for some
`ε > 0`. This file proves Moser's **crossover estimate**: there are constants `c > 0` and `K`,
depending only on the dimension, such that for every exponent `|p| ≤ c λ/Λ` and every ball with
`B(x₀, 4√n r) ⊆ Ω`,

`⨍_{B(x₀, r)} u^p · ⨍_{B(x₀, r)} u^{-p} ≤ K`.

Neither factor is controlled on its own, but their product is, uniformly in `u`, `ε` and the ball.
In Moser's proof of the weak Harnack inequality this links the bound on negative powers of a
positive supersolution to a bound on its positive powers: lower bounds on `u` are stated in terms
of `⨍ u^{-p}`, and the crossover estimate turns them into lower bounds in terms of `⨍ u^p`.

The proof combines two results. The logarithm `log u` has mean oscillation at most `C Λ/λ` on every
ball `B` with `2B ⊆ Ω` (`TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le`), and the
crossover form of the John–Nirenberg inequality on Euclidean balls
(`TauCeti.exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le`) bounds
`∫_B exp (p log u) · ∫_B exp (-p log u)` by `K |B|²` once `|p| Λ/λ` is small. On `B` the integrands
are `u^p` and `u^{-p}`.

The estimate extends to supersolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with measurable
`‖b‖ ≤ β` and `|c| ≤ γ`: the mean oscillation of `log u` on balls inside `B(x₀, 4√n r)` is then at
most a dimensional multiple of `√((Λ/λ)² + (βr/λ)² + γr²/λ)`
(`TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le_lowerOrder`), and the crossover estimate
holds for every exponent with `|p| √((Λ/λ)² + (βr/λ)² + γr²/λ) ≤ c`. The estimate without
lower-order terms is the case `b = 0`, `c = 0`.

## Main declarations

* `TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le`: the crossover estimate.
* `TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder`: the crossover
  estimate for supersolutions of the equation with lower-order terms.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the proofs of Theorems 8.18 and 8.20).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Moser's crossover estimate with lower-order terms.** There are constants `c₀ > 0` and `K`,
depending only on the dimension `n ≥ 1`, with the following property. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`
and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then for every
ball with `B(x₀, 4√n r) ⊆ Ω` and every exponent `p` with
`|p| √((Λ/λ)² + (βr/λ)² + γr²/λ) ≤ c₀`,

`⨍_{B(x₀, r)} u^p · ⨍_{B(x₀, r)} u^{-p} ≤ K`.

The bound is independent of `u`, `ε`, the coefficients and the ball; the admissible exponents
depend on the coefficients only through `Λ/λ`, `βr/λ` and `γr²/λ`. -/
theorem exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder [Nonempty ι] :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℝ, ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r p : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) → AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (4 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      |p| * √((Lam / lam) ^ 2 + (beta * r / lam) ^ 2 + gamma * r ^ 2 / lam) ≤ c₀ →
      (⨍ x in ball x₀ r, W1p.value u x ^ p ∂mu) * (⨍ x in ball x₀ r, W1p.value u x ^ (-p) ∂mu) ≤
        K := by
  obtain ⟨C₀, hC₀, hC₀'⟩ := exists_setAverage_abs_log_sub_setAverage_le_lowerOrder (ι := ι)
  obtain ⟨A, hA, C, hJN⟩ :=
    exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le (ι := ι)
  set s := √(Fintype.card ι : ℝ)
  have hs : 0 < s := EuclideanSpace.sqrt_card_pos
  refine ⟨A / (2 * s * (C₀ + 1)), by positivity, C, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u ε x₀ r p h ha hb hc hb_bound hc_bound hu hε hεu
    hball hp
  rcases le_or_gt r 0 with hr | hr
  · simp only [ball_eq_empty.2 hr, Measure.restrict_empty, average_zero_measure, mul_zero]
    positivity
  have hlam := h.pos
  set R := 2 * s * r
  have hRr : R / (2 * s) = r := mul_div_cancel_left₀ r (by positivity)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by exact_mod_cast Fintype.card_pos)
  have hrR : r ≤ R := by nlinarith
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  have hball' : ball x₀ (2 * R) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball' (mem_ball_self (by positivity))
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ hx₀)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ hx₀)
  -- The dimensionless size of the coefficients on balls of radius `ρ`, nondecreasing in `ρ ≥ 0`.
  set Q : ℝ → ℝ := fun ρ => (Lam / lam) ^ 2 + (beta * ρ / lam) ^ 2 + gamma * ρ ^ 2 / lam
  have hQmono : ∀ ρ, 0 ≤ ρ → ρ ≤ R → Q ρ ≤ Q R := fun ρ hρ hρR => by
    simp only [Q]
    gcongr
  have hQR : Q R ≤ (2 * s) ^ 2 * Q r := by
    have h4 : 1 ≤ (2 * s) ^ 2 := by nlinarith
    simp only [Q, R]
    have : 0 ≤ (Lam / lam) ^ 2 := sq_nonneg _
    have e1 : (beta * (2 * s * r) / lam) ^ 2 = (2 * s) ^ 2 * (beta * r / lam) ^ 2 := by ring
    have e2 : gamma * (2 * s * r) ^ 2 / lam = (2 * s) ^ 2 * (gamma * r ^ 2 / lam) := by ring
    rw [e1, e2]
    nlinarith
  -- `log u` has mean oscillation at most `C₀ √(Q R)` on every ball inside `B(x₀, R)`.
  set M : ℝ≥0 := (C₀ * √(Q R)).toNNReal
  have hMc : (M : ℝ) = C₀ * √(Q R) := Real.coe_toNNReal _ (by positivity)
  have hM : ∀ y ρ, ball y ρ ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, ‖f x - ⨍ z in ball y ρ, f z ∂mu‖ₑ ∂mu ≤ M := by
    intro y ρ hsub
    rcases le_or_gt ρ 0 with hρ | hρ
    · simp [ball_eq_empty.2 hρ]
    have hρR := (ball_subset_ball_iff hρ).1 hsub
    have h2 : ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
      (ball_subset_ball' (by linarith [dist_nonneg (x := y) (y := x₀)])).trans hball'
    refine (setLAverage_enorm_eq_ofReal_setAverage_norm
      (g := fun x => f x - ⨍ z in ball y ρ, f z ∂mu)
      ((W1p.integrableOn_log_value (by simp) hε hεu
        ((ball_subset_ball (by linarith : ρ ≤ 2 * ρ)).trans h2)
        measure_ball_lt_top.ne).sub (integrableOn_const measure_ball_lt_top.ne))).trans_le
      (ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C₀ * √(Q ρ) := by
          simpa only [Real.norm_eq_abs] using
            hC₀' mu h ha hb hc hb_bound hc_bound hu hε hεu hρ h2
      _ ≤ C₀ * √(Q R) := by
          gcongr
          exact hQmono ρ hρ.le (by linarith [dist_nonneg (x := y) (y := x₀)])
  -- For `|p| √(Q r) ≤ c₀` the John–Nirenberg crossover estimate applies to `log u` with `σ = p`.
  have hσ : |p| * M ≤ A := by
    rw [hMc]
    have hsqrt : √(Q R) ≤ 2 * s * √(Q r) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * s), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt hQR
    calc |p| * (C₀ * √(Q R)) ≤ |p| * (C₀ * (2 * s * √(Q r))) := by gcongr
      _ = 2 * s * C₀ * (|p| * √(Q r)) := by ring
      _ ≤ 2 * s * C₀ * (A / (2 * s * (C₀ + 1))) := by gcongr
      _ = A * (C₀ / (C₀ + 1)) := by field_simp
      _ ≤ A * 1 := by
          gcongr
          exact (div_le_one (by positivity)).2 (by linarith)
      _ = A := mul_one A
  have hJ := hJN (W1p.integrableOn_log_value (by simp) hε hεu
    ((ball_subset_ball (by linarith)).trans hball') measure_ball_lt_top.ne) hM hσ
  rw [hRr] at hJ
  have hBΩ : ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball'
  have hpos : ∀ᵐ x ∂mu.restrict (ball x₀ r), 0 < W1p.value u x :=
    (ae_restrict_of_ae_restrict_of_subset hBΩ hεu).mono fun x hx => hε.trans_le hx
  have hexp (q : ℝ) : ∫⁻ x in ball x₀ r, ENNReal.ofReal (W1p.value u x ^ q) ∂mu =
      ∫⁻ x in ball x₀ r, ENNReal.ofReal (Real.exp (q * f x)) ∂mu :=
    lintegral_congr_ae (hpos.mono fun x hx => by
      simp only [f]
      rw [Real.rpow_def_of_pos hx, mul_comm])
  refine setAverage_mul_setAverage_le_of_setLIntegral_mul_le
    (hpos.mono fun x hx => Real.rpow_nonneg hx.le p)
    (hpos.mono fun x hx => Real.rpow_nonneg hx.le (-p))
    ?_
  rw [hexp p, hexp (-p)]
  simpa only [neg_mul] using hJ

/-- **Moser's crossover estimate.** There are constants `c > 0` and `K`, depending only on the
dimension `n ≥ 1`, with the following property. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≥ 0` with `u ≥ ε` almost everywhere for some `ε > 0`. Then for every ball with
`B(x₀, 4√n r) ⊆ Ω` and every exponent `|p| ≤ c λ/Λ`,

`⨍_{B(x₀, r)} u^p · ⨍_{B(x₀, r)} u^{-p} ≤ K`.

The bound is independent of `u`, `ε`, `λ`, `Λ` and the ball. -/
theorem exists_setAverage_rpow_mul_setAverage_rpow_neg_le [Nonempty ι] :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {u : W1p mu Omega 2} {ε : ℝ} {x₀ : EuclideanSpace ℝ ι} {r p : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (4 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      |p| ≤ c * (lam / Lam) →
      (⨍ x in ball x₀ r, W1p.value u x ^ p ∂mu) * (⨍ x in ball x₀ r, W1p.value u x ^ (-p) ∂mu) ≤
        K := by
  obtain ⟨c, hc, K, hK⟩ := exists_setAverage_rpow_mul_setAverage_rpow_neg_le_lowerOrder (ι := ι)
  refine ⟨c, hc, K, fun mu _ Omega a lam Lam u ε x₀ r p h ha hu hε hεu hball hp => ?_⟩
  have hlam := h.pos
  have hLam : 0 < Lam := hlam.trans_le h.le
  -- The case `b = 0`, `c = 0` of the estimate with lower-order terms.
  refine hK mu (b := 0) (c := 0) (beta := 0) (gamma := 0) h ha aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ _ => by rw [Pi.zero_apply, norm_zero])
    (fun _ _ => by rw [Pi.zero_apply, norm_zero]) hu hε hεu hball ?_
  have hz : (Lam / lam) ^ 2 + (0 * r / lam) ^ 2 + 0 * r ^ 2 / lam = (Lam / lam) ^ 2 := by ring
  rw [hz, Real.sqrt_sq (by positivity)]
  calc |p| * (Lam / lam) ≤ c * (lam / Lam) * (Lam / lam) := by gcongr
    _ = c := by field_simp

end PDE

end TauCeti
