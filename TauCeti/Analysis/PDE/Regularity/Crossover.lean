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

`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ ε` almost everywhere for some
`ε > 0`. This file proves Moser's **crossover estimate**: there is a constant `c > 0`, depending
only on the dimension, such that for every exponent `|p| ≤ c λ/Λ` and every ball with
`B(x₀, 4√n r) ⊆ Ω`,

`⨍_{B(x₀, r)} u^p · ⨍_{B(x₀, r)} u^{-p} ≤ 49 nⁿ`.

Neither factor is controlled on its own, but their product is, uniformly in `u`, `ε` and the ball.
In Moser's proof of the weak Harnack inequality this links the bound on negative powers of a
positive supersolution to a bound on its positive powers: lower bounds on `u` are stated in terms
of `⨍ u^{-p}`, and the crossover estimate turns them into lower bounds in terms of `⨍ u^p`.

The proof combines two results. The logarithm `log u` has mean oscillation at most `C Λ/λ` on every
ball `B` with `2B ⊆ Ω` (`TauCeti.PDE.exists_setAverage_abs_log_sub_setAverage_le`), and the
John–Nirenberg inequality on Euclidean balls
(`TauCeti.exists_setLIntegral_exp_mul_norm_sub_ball_le`) makes `exp (|p| |log u - m|)` integrable
on `B(x₀, r)` with average at most `7 √nⁿ`, for some constant `m`, once `|p| Λ/λ` is small. Then
`u^{±p} ≤ e^{±pm} exp (|p| |log u - m|)`, and the factors `e^{pm}` and `e^{-pm}` cancel in the
product.

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

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponent condition for the John–Nirenberg step: if `|p| ≤ log (3/2) / (D (C + 1)) · λ/Λ`,
then `exp (|p| D C Λ/λ) ≤ 3/2`. -/
private theorem exp_abs_mul_le_three_halves {D C lam Lam p : ℝ} (hD : 0 < D) (hC : 0 ≤ C)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hp : |p| ≤ Real.log (3 / 2) / (D * (C + 1)) * (lam / Lam)) :
    Real.exp (|p| * (D * (C * (Lam / lam)))) ≤ 3 / 2 := by
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hcancel : Real.log (3 / 2) / (D * (C + 1)) * D * C = Real.log (3 / 2) * (C / (C + 1)) := by
    field_simp
  have hratio : lam / Lam * (Lam / lam) ≤ 1 := by
    rw [div_mul_div_comm, mul_comm lam]
    exact div_self_le_one _
  have hX0 : 0 ≤ lam / Lam * (Lam / lam) :=
    mul_nonneg (div_nonneg hlam.le hLam) (div_nonneg hLam hlam.le)
  calc Real.exp (|p| * (D * (C * (Lam / lam))))
      ≤ Real.exp (Real.log (3 / 2) / (D * (C + 1)) * (lam / Lam) * (D * (C * (Lam / lam)))) := by
        gcongr
    _ = Real.exp (Real.log (3 / 2) * (C / (C + 1)) * (lam / Lam * (Lam / lam))) := by
        rw [← hcancel]
        ring_nf
    _ ≤ Real.exp (Real.log (3 / 2) * 1 * 1) :=
        Real.exp_le_exp.2 (mul_le_mul (mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ (by linarith) (by linarith)) hlog.le) hratio hX0 (by positivity))
    _ = 3 / 2 := by rw [mul_one, mul_one, Real.exp_log (by norm_num)]

/-- **Moser's crossover estimate.** There is a constant `c > 0`, depending only on the dimension
`n ≥ 1`, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with
`u ≥ ε` almost everywhere for some `ε > 0`. Then for every ball with `B(x₀, 4√n r) ⊆ Ω` and every
exponent `|p| ≤ c λ/Λ`,

`⨍_{B(x₀, r)} u^p · ⨍_{B(x₀, r)} u^{-p} ≤ 49 nⁿ`.

The bound is independent of `u`, `ε`, `λ`, `Λ` and the ball. -/
theorem exists_setAverage_rpow_mul_setAverage_rpow_neg_le [Nonempty ι] :
    ∃ c : ℝ, 0 < c ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
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
        49 * (Fintype.card ι : ℝ) ^ Fintype.card ι := by
  obtain ⟨C, hC0, hC⟩ := exists_setAverage_abs_log_sub_setAverage_le (ι := ι)
  set n := Fintype.card ι
  set s := √(n : ℝ)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by exact_mod_cast Fintype.card_pos)
  set D : ℝ := 2 ^ (n + 1) * (2 * (2 * s) ^ n) with hDdef
  have hD : 0 < D := by positivity
  refine ⟨Real.log (3 / 2) / (D * (C + 1)), div_pos (Real.log_pos (by norm_num)) (by positivity),
    ?_⟩
  intro mu _ Omega a lam Lam u ε x₀ r p h ha hu hε hεu hball hp
  rcases le_or_gt r 0 with hr | hr
  · simp only [ball_eq_empty.2 hr, Measure.restrict_empty, average_zero_measure, mul_zero]
    positivity
  have hlam := h.pos
  set f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (W1p.value u x)
  -- `log u` is a Sobolev function, hence integrable on sets of finite measure in `Ω`.
  obtain ⟨w, hwv, -⟩ := W1p.exists_value_gradient_ae_eq_log (by simp) hε hεu
  have hint : ∀ S ⊆ (Omega : Set (EuclideanSpace ℝ ι)), mu S ≠ ⊤ → IntegrableOn f S mu :=
    fun S hS hSt => by
      have : IsFiniteMeasure (mu.restrict S) := isFiniteMeasure_restrict.2 hSt
      exact (((Lp.memLp (W1p.value w)).ae_eq hwv).mono_measure
        (Measure.restrict_mono hS le_rfl)).integrable one_le_two
  -- `log u` has mean oscillation at most `C Λ/λ` on every ball inside `B(x₀, 2√n r)`.
  set M : ℝ≥0 := (C * (Lam / lam)).toNNReal
  have hMc : (M : ℝ) = C * (Lam / lam) :=
    Real.coe_toNNReal _ (mul_nonneg hC0 (div_nonneg h.upper_nonneg hlam.le))
  have hM : ∀ y ρ, 0 < ρ → ball y ρ ⊆ ball x₀ (2 * s * r) →
      ⨍⁻ x in ball y ρ, ‖f x - ⨍ z in ball y ρ, f z ∂mu‖ₑ ∂mu ≤ M := by
    intro y ρ hρ hsub
    have hd := (ball_subset_ball_iff hρ).1 hsub
    have h2 : ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
      (ball_subset_ball' (by linarith [dist_nonneg (x := y) (y := x₀)])).trans hball
    have hfi := hint (ball y ρ) ((ball_subset_ball (by linarith : ρ ≤ 2 * ρ)).trans h2)
      measure_ball_lt_top.ne
    rw [setLAverage_eq]
    simp_rw [Real.enorm_eq_ofReal_abs]
    calc (∫⁻ x in ball y ρ, ENNReal.ofReal |f x - ⨍ z in ball y ρ, f z ∂mu| ∂mu) / mu (ball y ρ)
        = ENNReal.ofReal (⨍ x in ball y ρ, |f x - ⨍ z in ball y ρ, f z ∂mu| ∂mu) :=
          (ofReal_setAverage (f := fun x => |f x - ⨍ z in ball y ρ, f z ∂mu|)
            (hfi.sub (integrableOn_const measure_ball_lt_top.ne)).abs
            (ae_of_all _ fun _ => abs_nonneg _)).symm
      _ ≤ M := ENNReal.ofReal_le_ofReal (hC mu h ha hu hε hεu hρ h2)
  -- For `|p| ≤ c λ/Λ` the John–Nirenberg inequality applies with `σ = |p|` and `ρ = 3/2`.
  have hσ : Real.exp (|p| * (2 ^ (n + 1) * (2 * (2 * s) ^ n * M))) ≤ 3 / 2 := by
    rw [hMc, show 2 ^ (n + 1) * (2 * (2 * s) ^ n * (C * (Lam / lam))) = D * (C * (Lam / lam)) by
      rw [hDdef]; ring]
    exact exp_abs_mul_le_three_halves hD hC0 hlam h.upper_nonneg hp
  have hBΩ : ball x₀ r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  obtain ⟨m, hm⟩ := exists_setLIntegral_exp_mul_norm_sub_ball_le
    (hint _ ((ball_subset_ball (by nlinarith)).trans hball) measure_ball_lt_top.ne) hM hσ
    (by norm_num)
  rw [show (1 + 2 * (3 / 2 : ℝ) / (2 - 3 / 2)) * s ^ n = 7 * s ^ n by norm_num] at hm
  -- Each of `⨍ u^p` and `⨍ u^{-p}` is at most `e^{±pm} · 7 √nⁿ`.
  have hpos : ∀ᵐ x ∂mu.restrict (ball x₀ r), 0 < W1p.value u x :=
    (ae_restrict_of_ae_restrict_of_subset hBΩ hεu).mono fun x hx => hε.trans_le hx
  have hmeas : AEMeasurable (fun x => W1p.value u x) (mu.restrict (ball x₀ r)) :=
    ((Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hBΩ le_rfl)).aemeasurable
  have hplus := setAverage_rpow_le_of_setLIntegral_exp_le measure_ball_lt_top.ne hpos hmeas
    (by positivity) le_rfl hm
  have hminus := setAverage_rpow_le_of_setLIntegral_exp_le (q := -p) measure_ball_lt_top.ne hpos
    hmeas (by positivity) (abs_neg p).le hm
  have hexp : Real.exp (p * m) * Real.exp (-p * m) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  calc (⨍ x in ball x₀ r, W1p.value u x ^ p ∂mu) * (⨍ x in ball x₀ r, W1p.value u x ^ (-p) ∂mu)
      ≤ (Real.exp (p * m) * (7 * s ^ n)) * (Real.exp (-p * m) * (7 * s ^ n)) :=
        mul_le_mul hplus hminus (average_nonneg_of_ae (hpos.mono fun x hx => by
          simpa using Real.rpow_nonneg hx.le (-p))) (by positivity)
    _ = 49 * (s ^ 2) ^ n := by
        rw [mul_mul_mul_comm, hexp]
        ring
    _ = 49 * (n : ℝ) ^ n := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

end PDE

end TauCeti
