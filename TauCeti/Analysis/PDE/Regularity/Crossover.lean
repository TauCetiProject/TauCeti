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

## Main declarations

* `TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le`: the crossover estimate.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6 (the proof of Theorem 8.18).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-- If the mean absolute oscillation of `f` over `s` is at most `M`, then so is its mean
`‖·‖ₑ`-oscillation, as an extended nonnegative real. -/
theorem setLAverage_enorm_sub_setAverage_le_ofReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} {M : ℝ} (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (h : ⨍ x in s, |f x - ⨍ z in s, f z ∂μ| ∂μ ≤ M) :
    ⨍⁻ x in s, ‖f x - ⨍ z in s, f z ∂μ‖ₑ ∂μ ≤ ENNReal.ofReal M := by
  rw [setLAverage_eq]
  simp_rw [Real.enorm_eq_ofReal_abs]
  calc (∫⁻ x in s, ENNReal.ofReal |f x - ⨍ z in s, f z ∂μ| ∂μ) / μ s
      = ENNReal.ofReal (⨍ x in s, |f x - ⨍ z in s, f z ∂μ| ∂μ) :=
        (ofReal_setAverage (f := fun x => |f x - ⨍ z in s, f z ∂μ|)
          (hf.sub (integrableOn_const hs)).abs (ae_of_all _ fun _ => abs_nonneg _)).symm
    _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal h

/-- **From a John–Nirenberg bound to averages.** If `g` is almost everywhere positive on `B` and
`∫_B exp (p log g) · ∫_B exp (-p log g) ≤ C μ(B)²`, then `⨍_B g^p · ⨍_B g^{-p} ≤ C`. -/
theorem setAverage_rpow_mul_setAverage_rpow_neg_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} {g : α → ℝ} {p : ℝ} {C : ℝ≥0} (hB0 : μ B ≠ 0) (hBt : μ B ≠ ⊤)
    (hpos : ∀ᵐ x ∂μ.restrict B, 0 < g x) (hmeas : AEMeasurable g (μ.restrict B))
    (h : (∫⁻ x in B, ENNReal.ofReal (Real.exp (p * Real.log (g x))) ∂μ) *
        ∫⁻ x in B, ENNReal.ofReal (Real.exp (-(p * Real.log (g x)))) ∂μ ≤ C * μ B ^ 2) :
    (⨍ x in B, g x ^ p ∂μ) * (⨍ x in B, g x ^ (-p) ∂μ) ≤ C := by
  have hrpow (q : ℝ) : ⨍ x in B, g x ^ q ∂μ =
      (μ.real B)⁻¹ * (∫⁻ x in B, ENNReal.ofReal (Real.exp (q * Real.log (g x))) ∂μ).toReal := by
    rw [setAverage_eq, smul_eq_mul, integral_eq_lintegral_of_nonneg_ae
      (hpos.mono fun x hx => Real.rpow_nonneg hx.le q) (hmeas.pow_const q).aestronglyMeasurable]
    congr 2
    refine lintegral_congr_ae (hpos.mono fun x hx => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hB0 : 0 < μ.real B := ENNReal.toReal_pos hB0 hBt
  rw [hrpow, hrpow]
  simp only [neg_mul] at h ⊢
  calc (μ.real B)⁻¹ * (∫⁻ x in B, ENNReal.ofReal (Real.exp (p * Real.log (g x))) ∂μ).toReal *
        ((μ.real B)⁻¹ * (∫⁻ x in B, ENNReal.ofReal (Real.exp (-(p * Real.log (g x)))) ∂μ).toReal)
      = (μ.real B)⁻¹ ^ 2 * ((∫⁻ x in B, ENNReal.ofReal (Real.exp (p * Real.log (g x))) ∂μ) *
          ∫⁻ x in B, ENNReal.ofReal (Real.exp (-(p * Real.log (g x)))) ∂μ).toReal := by
        rw [ENNReal.toReal_mul]
        ring
    _ ≤ (μ.real B)⁻¹ ^ 2 * ((C : ℝ≥0∞) * μ B ^ 2).toReal := by
        gcongr
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top hBt)
    _ = C := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← measureReal_def]
        field_simp

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary estimate behind the choice of the exponent range in Moser's crossover
estimate: if `|p| ≤ A / (C₀ + 1) * (λ / Λ)` then `|p| * (C₀ Λ / λ) ≤ A`. -/
private lemma abs_mul_le_of_le_div_mul {A C₀ lam Lam p : ℝ} (hA : 0 < A) (hC₀ : 0 ≤ C₀)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hp : |p| ≤ A / (C₀ + 1) * (lam / Lam)) :
    |p| * (C₀ * (Lam / lam)) ≤ A := by
  have hratio : lam / Lam * (Lam / lam) ≤ 1 := by
    rw [div_mul_div_comm, mul_comm lam]
    exact div_self_le_one _
  calc |p| * (C₀ * (Lam / lam))
      ≤ A / (C₀ + 1) * (lam / Lam) * (C₀ * (Lam / lam)) := by gcongr
    _ = A * (C₀ / (C₀ + 1)) * (lam / Lam * (Lam / lam)) := by field_simp
    _ ≤ A * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ (by linarith) (by linarith)) hA.le) hratio (by positivity)
          (by positivity)
    _ = A := by rw [mul_one, mul_one]

omit [DecidableEq ι] in
/-- The logarithm of a Sobolev function bounded below by a positive constant is integrable on
every subset of `Ω` of finite measure. -/
private lemma integrableOn_log_value (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {ε : ℝ} (hε : 0 < ε)
    (hεu : ∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x)
    {S : Set (EuclideanSpace ℝ ι)} (hS : S ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hSt : mu S ≠ ⊤) :
    IntegrableOn (fun x => Real.log (W1p.value u x)) S mu := by
  obtain ⟨w, hwv, -⟩ := W1p.exists_value_gradient_ae_eq_log (by simp) hε hεu
  have : IsFiniteMeasure (mu.restrict S) := isFiniteMeasure_restrict.2 hSt
  exact (((Lp.memLp (W1p.value w)).ae_eq hwv).mono_measure
    (Measure.restrict_mono hS le_rfl)).integrable one_le_two

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
  obtain ⟨C₀, hC₀, hC₀'⟩ := exists_setAverage_abs_log_sub_setAverage_le (ι := ι)
  obtain ⟨A, hA, C, hJN⟩ :=
    exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le (ι := ι)
  refine ⟨A / (C₀ + 1), by positivity, C, ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r p h ha hu hε hεu hball hp
  set s := √(Fintype.card ι : ℝ)
  have hs : 0 < s := EuclideanSpace.sqrt_card_pos
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
  -- `log u` has mean oscillation at most `C₀ Λ/λ` on every ball inside `B(x₀, R)`.
  set M : ℝ≥0 := (C₀ * (Lam / lam)).toNNReal
  have hMc : (M : ℝ) = C₀ * (Lam / lam) :=
    Real.coe_toNNReal _ (mul_nonneg hC₀ (div_nonneg h.upper_nonneg hlam.le))
  have hM : ∀ y ρ, ball y ρ ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, ‖f x - ⨍ z in ball y ρ, f z ∂mu‖ₑ ∂mu ≤ M := by
    intro y ρ hsub
    rcases le_or_gt ρ 0 with hρ | hρ
    · simp [ball_eq_empty.2 hρ]
    have h2 : ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
      (ball_subset_ball' (by linarith [dist_nonneg (x := y) (y := x₀),
        (ball_subset_ball_iff hρ).1 hsub])).trans hball'
    exact setLAverage_enorm_sub_setAverage_le_ofReal measure_ball_lt_top.ne
      (integrableOn_log_value mu hε hεu ((ball_subset_ball (by linarith : ρ ≤ 2 * ρ)).trans h2)
        measure_ball_lt_top.ne) (hC₀' mu h ha hu hε hεu hρ h2)
  -- For `|p| ≤ c λ/Λ` the John–Nirenberg crossover estimate applies to `log u` with `σ = p`.
  have hσ : |p| * M ≤ A := by
    rw [hMc]
    exact abs_mul_le_of_le_div_mul hA hC₀ hlam h.upper_nonneg hp
  have hBΩ : ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by linarith)).trans hball'
  have hJ := hJN (integrableOn_log_value mu hε hεu ((ball_subset_ball (by linarith)).trans hball')
    measure_ball_lt_top.ne) hM hσ
  rw [hRr] at hJ
  exact setAverage_rpow_mul_setAverage_rpow_neg_le (measure_ball_pos mu x₀ hr).ne'
    measure_ball_lt_top.ne
    ((ae_restrict_of_ae_restrict_of_subset hBΩ hεu).mono fun x hx => hε.trans_le hx)
    (((Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hBΩ le_rfl)).aemeasurable)
    hJ

end PDE

end TauCeti
