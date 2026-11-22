/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Rapid decay from square integrability of every order

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E`, and let
`F : E → G` be Lipschitz with a polynomially growing constant:
`‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`. If the weighted functions
`(1 + ‖η‖ ^ 2) ^ (s / 2) F η` are square integrable with respect to `μ` on a set `Γ` for every
real `s`, then `F` decays rapidly on every set `Γ'` whose conic balls `closedBall η (c ‖η‖)`,
`c > 0`, lie in `Γ`.

On the closed ball of radius `δ = (1 + ‖η‖) ^ (-M)` about `η` the value `F η` is within
`A (1 + ‖η‖) ^ (k - M)` of `F`, and averaging `‖F‖ ^ 2` over that ball, which lies in `Γ` for
`η ∈ Γ'` far from the origin, bounds `‖F η‖ ^ 2` by `δ ^ (-n) (1 + ‖η‖) ^ (-2 s)` times the
weighted `L²` norm of order `s`, plus `A² (1 + ‖η‖) ^ (2 (k - M))`, where `n` is the dimension.
For `M` and then `s` large both terms are `O((1 + ‖η‖) ^ (-2 N))`. Applied to a localized Fourier
transform, this turns microlocal `H^s` regularity for every `s` into microlocal smoothness.

## Main results

* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_forall_memLp`: a function that is Lipschitz with
  polynomially growing constant and whose weighted squares are integrable on `Γ` for every weight
  decays rapidly on `Γ'`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1.
-/

public section

open MeasureTheory Metric Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {G : Type*} [NormedAddCommGroup G]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise step: within distance `δ ≤ 1` of a frequency `η` with `‖η‖ ≥ 1`, the value
`F η` is within `b = |A| (1 + ‖η‖) ^ k δ` of `F ζ`, and the weight `(1 + ‖ζ‖ ^ 2) ^ σ` is at least
`((1 + ‖η‖) ^ 2 / 8) ^ σ`. -/
private theorem sq_norm_le_of_norm_sub_le {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {η ζ : E}
    (hη : 1 ≤ ‖η‖) {δ : ℝ} (hδ : δ ≤ 1) (hd : ‖η - ζ‖ ≤ δ) (σ : ℕ) :
    ‖F η‖ ^ 2 ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) +
      2 * (|A| * (1 + ‖η‖) ^ k * δ) ^ 2 := by
  set b := |A| * (1 + ‖η‖) ^ k * δ
  have hFη : ‖F η‖ ≤ ‖F ζ‖ + b :=
    calc ‖F η‖ = ‖F ζ + (F η - F ζ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖F ζ‖ + ‖F η - F ζ‖ := norm_add_le _ _
      _ ≤ ‖F ζ‖ + A * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by gcongr; exact hLip η ζ (hd.trans hδ)
      _ ≤ ‖F ζ‖ + b := add_le_add le_rfl (by
        calc A * (1 + ‖η‖) ^ k * ‖η - ζ‖ ≤ |A| * (1 + ‖η‖) ^ k * ‖η - ζ‖ := by
              gcongr; exact le_abs_self A
          _ ≤ |A| * (1 + ‖η‖) ^ k * δ := by gcongr)
  -- `‖ζ‖ ≥ ‖η‖ - 1 ≥ 0`, so `1 + ‖ζ‖ ^ 2 ≥ (1 + ‖η‖) ^ 2 / 8`.
  have hw : (1 + ‖η‖) ^ 2 / 8 ≤ 1 + ‖ζ‖ ^ 2 := by
    have hζη : ‖η‖ - 1 ≤ ‖ζ‖ := by linarith [norm_sub_norm_le η ζ]
    nlinarith [mul_self_le_mul_self (sub_nonneg.2 hη) hζη, sq_nonneg (‖η‖ - 9 / 7)]
  have hw₀ : 0 < ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by positivity
  have hW : ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) ≤ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 := by
    rw [← pow_mul, mul_comm σ 2]
    exact pow_le_pow_left₀ (by positivity) hw _
  have hFζ : ‖F ζ‖ ^ 2 ≤
      ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ) := by
    rw [le_div_iff₀ hw₀, mul_comm]
    exact mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  calc ‖F η‖ ^ 2 ≤ 2 * ‖F ζ‖ ^ 2 + 2 * b ^ 2 := by
        nlinarith [norm_nonneg (F η), norm_nonneg (F ζ), sq_nonneg (‖F ζ‖ - b)]
    _ ≤ 2 * (((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ)) +
        2 * b ^ 2 := by gcongr
    _ = _ := by ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The averaging step: a pointwise bound `a ≤ e g ζ + c` on a set `B ⊆ Γ` of finite measure,
with `g ≥ 0` integrable on `Γ` and `e ≥ 0`, gives `μ(B) a ≤ e ∫_Γ g dμ + μ(B) c`. -/
private theorem measureReal_mul_le_mul_setIntegral_add {g : E → ℝ} {Γ B : Set E}
    (hB : MeasurableSet B) (hBfin : μ B ≠ ⊤) (hBΓ : B ⊆ Γ)
    (hg : Integrable g (μ.restrict Γ)) (hg0 : ∀ ζ, 0 ≤ g ζ) {a c e : ℝ} (he : 0 ≤ e)
    (h : ∀ ζ ∈ B, a ≤ e * g ζ + c) :
    μ.real B * a ≤ e * (∫ ζ in Γ, g ζ ∂μ) + μ.real B * c := by
  have hgB : Integrable g (μ.restrict B) :=
    hg.mono_measure (Measure.restrict_mono_set μ hBΓ)
  have hle := setIntegral_ge_of_const_le hB hBfin h
    ((hgB.const_mul e).add (integrableOn_const hBfin))
  rw [integral_add (hgB.const_mul e) (integrableOn_const hBfin), integral_const_mul,
    setIntegral_const, smul_eq_mul, smul_eq_mul] at hle
  exact hle.trans (add_le_add (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hg (.of_forall hg0) (ae_of_all _ hBΓ)) he) le_rfl)

/-- The estimate at a frequency `η` far from the origin: averaging the pointwise step over the
ball of radius `(1 + ‖η‖) ^ (-(N + k))` about `η`, which lies in `Γ`, bounds
`((1 + ‖η‖) ^ N ‖F η‖) ^ 2` by the weighted `L²` norm of order `4 σ` of `F` on `Γ`, where
`σ = d (N + k) + N` and `d` is the dimension. -/
private theorem sq_one_add_norm_pow_mul_norm_le [μ.IsAddHaarMeasure] {F : E → G} {A : ℝ}
    {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖) {Γ : Set E}
    (N : ℕ) (hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 *
      ‖F ζ‖ ^ 2) (μ.restrict Γ)) {η : E} (hη : 1 ≤ ‖η‖) (hΓ : closedBall η 1 ⊆ Γ) :
    ((1 + ‖η‖) ^ N * ‖F η‖) ^ 2 ≤
      2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ (finrank ℝ E * (N + k) + N)) ^ 2 * ‖F ζ‖ ^ 2 ∂μ) *
        8 ^ (2 * (finrank ℝ E * (N + k) + N)) / μ.real (ball (0 : E) 1) + 2 * A ^ 2 := by
  set d := finrank ℝ E
  set σ := d * (N + k) + N
  have ht1 : 1 ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
  have hδ0 : 0 < ((1 + ‖η‖) ^ (N + k))⁻¹ := by positivity
  have hδ1 : ((1 + ‖η‖) ^ (N + k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht1)
  have hle := measureReal_mul_le_mul_setIntegral_add measurableSet_closedBall
    measure_closedBall_lt_top.ne ((closedBall_subset_closedBall hδ1).trans hΓ) hint
    (fun ζ ↦ by positivity) (by positivity : (0 : ℝ) ≤ 2 / ((1 + ‖η‖) ^ 2 / 8) ^ (2 * σ))
    fun ζ hζ ↦
      sq_norm_le_of_norm_sub_le hLip hη hδ1 (by rw [← dist_eq_norm, dist_comm]; exact hζ) σ
  rw [Measure.addHaar_real_closedBall μ η hδ0.le] at hle
  -- Name the quantities of the estimate; `set` also abbreviates them in `hle`.
  set I := ∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 ∂μ
  set v := μ.real (ball (0 : E) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  set t := 1 + ‖η‖
  set δ := (t ^ (N + k))⁻¹
  set w₀ : ℝ := (t ^ 2 / 8) ^ (2 * σ)
  set b := |A| * t ^ k * δ
  have hmain : ‖F η‖ ^ 2 ≤ 2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2 := by
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    calc ‖F η‖ ^ 2 * (δ ^ d * v) = δ ^ d * v * ‖F η‖ ^ 2 := by ring
      _ ≤ 2 / w₀ * I + δ ^ d * v * (2 * b ^ 2) := hle
      _ = 2 / w₀ * I + 2 * b ^ 2 * (δ ^ d * v) := by ring
  -- The powers of `t` cancel, since `2 N + (N + k) d ≤ 4 σ` and `M = N + k`.
  have key₁ : t ^ (2 * N) ≤ 8 ^ (2 * σ) * (w₀ * δ ^ d) := by
    have h : 8 ^ (2 * σ) * (w₀ * δ ^ d) = t ^ (4 * σ) / t ^ ((N + k) * d) := by
      simp only [w₀, δ, div_pow, inv_pow, ← pow_mul]
      field_simp
      ring
    rw [h, le_div_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_right₀ ht1 (by
      simp only [σ]; nlinarith [Nat.zero_le (d * N), Nat.zero_le (d * k)])
  have key₂ : b ^ 2 * t ^ (2 * N) = A ^ 2 := by
    simp only [b, δ, mul_pow, sq_abs, inv_pow]
    field_simp
    ring
  calc (t ^ N * ‖F η‖) ^ 2 = t ^ (2 * N) * ‖F η‖ ^ 2 := by ring
    _ ≤ t ^ (2 * N) * (2 / w₀ * I / (δ ^ d * v) + 2 * b ^ 2) := by gcongr
    _ = 2 * I / v * (t ^ (2 * N) / (w₀ * δ ^ d)) + 2 * (b ^ 2 * t ^ (2 * N)) := by
      field_simp
    _ ≤ 2 * I / v * 8 ^ (2 * σ) + 2 * A ^ 2 := by
      rw [key₂]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      exact key₁
    _ = 2 * I * 8 ^ (2 * σ) / v + 2 * A ^ 2 := by ring

/-- **Rapid decay from square integrability of every order.** Let `F` be Lipschitz with a
polynomially growing constant, `‖F η - F ζ‖ ≤ A (1 + ‖η‖) ^ k ‖η - ζ‖` for `‖η - ζ‖ ≤ 1`, and let
`⟨η⟩ ^ s F η` be square integrable with respect to an additive Haar measure `μ` on a set `Γ` for
every real `s`, where `⟨η⟩ ^ s = (1 + ‖η‖ ^ 2) ^ (s / 2)`. If for some `c > 0` the closed ball of
radius `c ‖η‖` about every point `η` of `Γ'` lies in `Γ`, then `F` decays rapidly on `Γ'`. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_forall_memLp [μ.IsAddHaarMeasure]
    [NormedSpace ℝ G] {F : E → G} {A : ℝ} {k : ℕ}
    (hLip : ∀ η ζ, ‖η - ζ‖ ≤ 1 → ‖F η - F ζ‖ ≤ A * (1 + ‖η‖) ^ k * ‖η - ζ‖)
    {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    (hL : ∀ s : ℝ, MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) • F η) 2 (μ.restrict Γ))
    (N : ℕ) : ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N * ‖F η‖ ≤ C := by
  set σ : ℕ := finrank ℝ E * (N + k) + N
  -- The weighted squares of order `4 σ` are integrable on `Γ`.
  have hint : Integrable (fun ζ ↦ ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2) (μ.restrict Γ) := by
    refine ((hL (2 * σ)).integrable_norm_pow two_ne_zero).congr (.of_forall fun ζ ↦ ?_)
    have h2 : (2 * (σ : ℝ)) / 2 = σ := by ring
    simp only [h2, Real.rpow_natCast, norm_smul, mul_pow,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖ ^ 2) ^ σ)]
  -- Near the origin `F` is bounded; far from it, `closedBall η 1 ⊆ Γ` for `η ∈ Γ'`.
  set R₀ := max 1 c⁻¹
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun η ↦
    continuousAt_of_locally_lipschitz one_pos (|A| * (1 + ‖η‖) ^ k) fun ζ hζ ↦ by
      rw [dist_comm (F ζ), dist_comm ζ, dist_eq_norm, dist_eq_norm]
      refine (hLip η ζ (by rw [← dist_eq_norm, dist_comm]; exact hζ.le)).trans ?_
      gcongr
      exact le_abs_self A
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : E) R₀).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨max (Real.sqrt (2 * (∫ ζ in Γ, ((1 + ‖ζ‖ ^ 2) ^ σ) ^ 2 * ‖F ζ‖ ^ 2 ∂μ) * 8 ^ (2 * σ) /
    μ.real (ball (0 : E) 1) + 2 * A ^ 2)) ((1 + R₀) ^ N * C₁), fun η hη ↦ ?_⟩
  rcases lt_or_ge ‖η‖ R₀ with hsmall | hlarge
  · exact le_max_of_le_right (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) N)
      (hC₁ η (by simpa using hsmall.le)) (norm_nonneg _) (by positivity))
  have hct : 1 ≤ c * ‖η‖ :=
    calc 1 = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ c * ‖η‖ := by gcongr; exact (le_max_right _ _).trans hlarge
  exact le_max_of_le_left ((le_abs_self _).trans (Real.abs_le_sqrt
    (sq_one_add_norm_pow_mul_norm_le hLip N hint ((le_max_left _ _).trans hlarge)
      ((closedBall_subset_closedBall hct).trans (hΓ' η hη)))))

end TauCeti
