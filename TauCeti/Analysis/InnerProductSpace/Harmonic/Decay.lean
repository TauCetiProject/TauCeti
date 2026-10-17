/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Decay estimates for harmonic functions on concentric balls

Let `E` be a finite-dimensional real inner product space of dimension `n`, with an additive Haar
measure `μ`, and let `u : E → F` be harmonic on the ball `B_R = ball x₀ R`. This file proves the
two decay estimates on concentric balls `B_ρ ⊆ B_R` that a harmonic function satisfies:

`∫_{B_ρ} ‖u‖² ≤ 2ⁿ (ρ / R)ⁿ ∫_{B_R} ‖u‖²`,

`∫_{B_ρ} ‖u - u_ρ‖² ≤ 2^(3n + 8) (n + 1)² (ρ / R)^(n + 2) ∫_{B_R} ‖u - c‖²`

for every `0 ≤ ρ ≤ R` and every constant `c`, where `u_ρ` is the average of `u` over `B_ρ`. The
constants depend only on the dimension. The first estimate says that the `L²` mass of `u` on
small balls decays like the volume, as it would for a bounded function; the second says that the
`L²` mean oscillation decays two orders faster, as it would for a Lipschitz function.

These are the decay estimates of the frozen problem in the Campanato approach to elliptic
regularity, when the frozen operator is the Laplacian. There a solution of a perturbed equation,
such as Poisson's equation or an equation with variable coefficients, is compared on each ball
with the harmonic function having the same boundary values. The decay exponents `n` and `n + 2`
feed the iteration lemma `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add`, whose
output is a growth bound that Campanato's characterization of Hölder continuity
(`TauCeti.MeasureTheory.exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le`) turns into a
Hölder estimate. The function `u` is only assumed square integrable on the open ball `B_R`, as for
a harmonic function with prescribed `H¹` boundary values.

## The argument

Everything rests on the mean-value property on balls
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq`). Combined with the Cauchy–Schwarz
inequality it gives the pointwise bound `μ(B(y, s)) ‖u y‖² ≤ ∫_{B(y, s)} ‖u‖²`, so `‖u‖²` is bounded
on `B_{R/2}` by `2ⁿ / μ(B_R)` times `∫_{B_R} ‖u‖²`; integrating this bound over `B_ρ` gives the
first estimate.

For the second, comparing the mean values of `u` over two balls `B(y, s)` and `B(z, s)` of the
same radius leaves only the integrals of `u` over the two differences, each contained in a
spherical shell of width `‖y - z‖` (the comparison behind Nelson's proof of Liouville's theorem).
If `‖u‖ ≤ M` on both balls this gives the Lipschitz bound
`‖u y - u z‖ ≤ 2ⁿ n M ‖y - z‖ / s` for `‖y - z‖ ≤ s`, the difference form of the interior gradient
estimate. Applied to `u - c`, with `M` from the pointwise bound, it controls the oscillation of
`u` on `B_ρ` by `(ρ / R)` times the `L²` norm of `u - c` on `B_R`, for `ρ ≤ R / 8`. For larger `ρ`
the estimate follows from replacing the average `u_ρ` by `c`
(`TauCeti.setIntegral_norm_sub_setAverage_sq_le`).

## Linear changes of variables

Both estimates survive a linear change of variables, with constants depending on its condition
number. If `e : E' ≃L[ℝ] E` is a continuous linear equivalence with `‖e⁻¹ x‖ ≤ a ‖x‖` and
`‖e y‖ ≤ b ‖y‖`, and `u ∘ e` is harmonic on `e⁻¹(B_R)`, then `u` satisfies the two estimates with
the factors `(a b)ⁿ` and `4 (a b)^(n + 2)` inserted. The ball `B_ρ` is pulled back into a ball of
radius `a ρ` and a ball of radius `R / b` is pushed into `B_R`, and the harmonic estimates are
applied for the Haar measure `μ.map e⁻¹`, for which `e` carries one integral to the other without
a Jacobian factor. A second-order operator with constant elliptic coefficients becomes the
Laplacian after such a change of variables, so this is the decay estimate for its solutions.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.measureReal_ball_mul_norm_sq_le_setIntegral`: the pointwise bound
  `μ(B(y, s)) ‖u y‖² ≤ ∫_{B(y, s)} ‖u‖²`.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sq_le`: decay of the `L²` mass with
  exponent `n`.
* `InnerProductSpace.HarmonicOnNhd.norm_sub_le_of_norm_le`: the Lipschitz bound for a bounded
  harmonic function.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`: decay of the `L²`
  mean oscillation with exponent `n + 2`.
* `TauCeti.setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp` and
  `TauCeti.setIntegral_ball_norm_sub_setAverage_sq_le_of_harmonicOnNhd_comp`: the two estimates
  for `u` when `u ∘ e` is harmonic, `e` a continuous linear equivalence.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le_add`:
  the comparison step of the Campanato approach. A square-integrable `f` close in `L²(B_R)` to a
  harmonic function inherits its decay, up to the distance `∫_{B_R} ‖f - u‖²`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Chapter 5 (decay estimates for constant coefficients and the
  Campanato approach to Schauder estimates).
* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter III.
* E. Nelson, *A proof of Liouville's theorem*, Proc. Amer. Math. Soc. 12 (1961), 995.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 7 (estimates on
  derivatives).
-/

public section

open InnerProductSpace MeasureTheory Metric Module Set

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : E → F}

omit [CompleteSpace F] in
/-- A function harmonic on a neighbourhood of `closedBall y s` is integrable on `ball y s`. -/
private lemma _root_.InnerProductSpace.HarmonicOnNhd.integrableOn_ball {y : E} {s : ℝ}
    (hu : HarmonicOnNhd u (closedBall y s)) : IntegrableOn u (ball y s) μ :=
  (hu.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set ball_subset_closedBall

/-- **The pointwise `L²` bound for harmonic functions.** If `u` is harmonic on a neighbourhood of
the closed ball `closedBall y s`, then the measure of the ball `ball y s` times `‖u y‖²` is at most
the integral of `‖u‖²` over that ball. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.measureReal_ball_mul_norm_sq_le_setIntegral
    {y : E} {s : ℝ} (hu : HarmonicOnNhd u (closedBall y s)) :
    μ.real (ball y s) * ‖u y‖ ^ 2 ≤ ∫ x in ball y s, ‖u x‖ ^ 2 ∂μ := by
  have hc : ContinuousOn u (closedBall y s) := hu.continuousOn
  have hint : IntegrableOn u (ball y s) μ := hu.integrableOn_ball
  have hint2 : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball y s) μ :=
    ((hc.norm.pow 2).integrableOn_compact (isCompact_closedBall y s)).mono_set
      ball_subset_closedBall
  have hB : 0 ≤ μ.real (ball y s) := measureReal_nonneg
  -- By the mean-value property, `μ(B) ‖u y‖ = ‖∫_B u‖ ≤ ∫_B ‖u‖`.
  have h1 : μ.real (ball y s) * ‖u y‖ ≤ ∫ x in ball y s, ‖u x‖ ∂μ := by
    calc μ.real (ball y s) * ‖u y‖ = ‖∫ x in ball y s, u x ∂μ‖ := by
          rw [hu.setIntegral_ball_eq, norm_smul, Real.norm_of_nonneg hB]
      _ ≤ _ := norm_integral_le_integral_norm _
  have h2 : μ.real (ball y s) * (μ.real (ball y s) * ‖u y‖ ^ 2) ≤
      μ.real (ball y s) * ∫ x in ball y s, ‖u x‖ ^ 2 ∂μ := by
    calc μ.real (ball y s) * (μ.real (ball y s) * ‖u y‖ ^ 2)
        = (μ.real (ball y s) * ‖u y‖) ^ 2 := by ring
      _ ≤ (∫ x in ball y s, ‖u x‖ ∂μ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ _ := MeasureTheory.sq_setIntegral_le_measureReal_mul_setIntegral_sq _ _
          measure_ball_lt_top.ne hint.norm hint2
  rcases hB.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity
  · exact le_of_mul_le_mul_left h2 hpos

/-- If `u` is harmonic on the ball `ball x₀ R` and `‖u‖²` is integrable there, then `‖u‖²` is
bounded on the half ball `ball x₀ (R / 2)` by `2ⁿ / μ(ball 0 1) R⁻ⁿ` times its integral over
`ball x₀ R`. -/
private lemma norm_sq_le_of_mem_ball_half {x₀ x : E} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (ball x₀ R)) (hint : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball x₀ R) μ)
    (hx : x ∈ ball x₀ (R / 2)) :
    ‖u x‖ ^ 2 ≤ 2 ^ finrank ℝ E * (∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ) /
      (R ^ finrank ℝ E * μ.real (ball (0 : E) 1)) := by
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  have hsub : closedBall x (R / 2) ⊆ ball x₀ R := by
    intro z hz
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z x x₀]
  have h := (hu.mono hsub).measureReal_ball_mul_norm_sq_le_setIntegral (μ := μ)
  have hmono : ∫ z in ball x (R / 2), ‖u z‖ ^ 2 ∂μ ≤ ∫ z in ball x₀ R, ‖u z‖ ^ 2 ∂μ :=
    setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
      (ball_subset_closedBall.trans hsub).eventuallyLE
  rw [μ.addHaar_real_ball_of_pos x (half_pos hR), div_pow] at h
  rw [le_div_iff₀ (by positivity)]
  have h2 : (0 : ℝ) < 2 ^ finrank ℝ E := by positivity
  calc ‖u x‖ ^ 2 * (R ^ finrank ℝ E * μ.real (ball (0 : E) 1))
      = 2 ^ finrank ℝ E *
          (R ^ finrank ℝ E / 2 ^ finrank ℝ E * μ.real (ball (0 : E) 1) * ‖u x‖ ^ 2) := by
        field_simp
    _ ≤ _ := by gcongr; exact h.trans hmono

/-- **Decay of the `L²` mass of a harmonic function.** If `u` is harmonic on the ball
`ball x₀ R` and `‖u‖²` is integrable there, then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u‖² ≤ 2ⁿ (ρ / R)ⁿ ∫_{ball x₀ R} ‖u‖²`,

where `n` is the dimension of `E`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sq_le {x₀ : E} {ρ R : ℝ}
    (hu : HarmonicOnNhd u (ball x₀ R)) (hint : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball x₀ R) μ)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤
      2 ^ finrank ℝ E * (ρ / R) ^ finrank ℝ E * ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ := by
  set I := ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity
  rcases hρ.eq_or_lt with rfl | hρ
  · simp only [ball_zero, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hR : 0 < R := hρ.trans_le hρR
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  rcases le_or_gt (2 * ρ) R with h2 | h2
  · -- On `ball x₀ ρ ⊆ ball x₀ (R / 2)`, `‖u‖²` is bounded by the pointwise estimate.
    calc ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ
        ≤ ∫ _ in ball x₀ ρ,
            2 ^ finrank ℝ E * I / (R ^ finrank ℝ E * μ.real (ball (0 : E) 1)) ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
            (integrableOn_const measure_ball_lt_top.ne) ?_
          refine (ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ?_
          exact norm_sq_le_of_mem_ball_half hR hu hint
            (ball_subset_ball (by linarith) hx)
      _ = 2 ^ finrank ℝ E * (ρ / R) ^ finrank ℝ E * I := by
          rw [setIntegral_const, smul_eq_mul, μ.addHaar_real_ball_of_pos x₀ hρ, div_pow]
          field_simp
  · -- For `ρ > R / 2` the factor `2ⁿ (ρ / R)ⁿ` is at least one.
    have hle : (1 : ℝ) ≤ 2 ^ finrank ℝ E * (ρ / R) ^ finrank ℝ E := by
      rw [← mul_pow]
      exact one_le_pow₀ (by rw [← mul_div_assoc, le_div_iff₀ hR]; linarith)
    calc ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤ I :=
          setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
            (ball_subset_ball hρR).eventuallyLE
      _ ≤ 2 ^ finrank ℝ E * (ρ / R) ^ finrank ℝ E * I := le_mul_of_one_le_left hI hle

/-- Comparing the mean values of `u` over two balls of the same radius `s`: if `‖u‖ ≤ M` on both,
then `μ(ball 0 s) ‖u y - u z‖ ≤ 2 M ((s + dist y z)ⁿ - sⁿ) μ(ball 0 1)`. -/
private lemma mul_norm_sub_le_of_norm_le (μ : Measure E) [μ.IsAddHaarMeasure] {y z : E}
    {s M : ℝ} (hy : HarmonicOnNhd u (closedBall y s)) (hz : HarmonicOnNhd u (closedBall z s))
    (hM : ∀ x ∈ ball y s ∪ ball z s, ‖u x‖ ≤ M) (hs : 0 < s) :
    s ^ finrank ℝ E * μ.real (ball (0 : E) 1) * ‖u y - u z‖ ≤
      2 * M * (((s + dist y z) ^ finrank ℝ E - s ^ finrank ℝ E) * μ.real (ball (0 : E) 1)) := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hiy : IntegrableOn u (ball y s) μ := hy.integrableOn_ball
  have hiz : IntegrableOn u (ball z s) μ := hz.integrableOn_ball
  -- By the mean-value property, `sⁿ ω (u y - u z)` is the difference of the integrals of `u` over
  -- `ball y s` and `ball z s`, in which the integrals over their intersection cancel.
  have hdiff : (s ^ n * ω) • (u y - u z) =
      (∫ x in ball y s \ ball z s, u x ∂μ) - ∫ x in ball z s \ ball y s, u x ∂μ := by
    have hmy := hy.setIntegral_ball_eq (μ := μ)
    have hmz := hz.setIntegral_ball_eq (μ := μ)
    rw [μ.addHaar_real_ball_of_pos y hs] at hmy
    rw [μ.addHaar_real_ball_of_pos z hs] at hmz
    have hy' := integral_inter_add_sdiff (measurableSet_ball (x := z) (ε := s)) hiy
    have hz' := integral_inter_add_sdiff (measurableSet_ball (x := y) (ε := s)) hiz
    rw [inter_comm] at hz'
    rw [smul_sub, ← hmy, ← hmz, ← hy', ← hz']
    abel
  -- Each difference of balls has measure at most `((s + dist y z)ⁿ - sⁿ) ω`.
  have hshell : ∀ a b : E, (∀ x ∈ ball a s, ‖u x‖ ≤ M) →
      ‖∫ x in ball a s \ ball b s, u x ∂μ‖ ≤ M * (((s + dist a b) ^ n - s ^ n) * ω) := by
    intro a b hMa
    refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top_of_subset sdiff_subset
      measure_ball_lt_top.ne) fun x hx ↦ hMa x hx.1).trans ?_
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMa a (mem_ball_self hs))
    gcongr
    exact μ.addHaar_real_ball_sdiff_ball_le a b hs
  calc s ^ n * ω * ‖u y - u z‖ = ‖(s ^ n * ω) • (u y - u z)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ ‖∫ x in ball y s \ ball z s, u x ∂μ‖ + ‖∫ x in ball z s \ ball y s, u x ∂μ‖ := by
        rw [hdiff]; exact norm_sub_le _ _
    _ ≤ M * (((s + dist y z) ^ n - s ^ n) * ω) + M * (((s + dist y z) ^ n - s ^ n) * ω) := by
        refine add_le_add (hshell y z fun x hx ↦ hM x (Or.inl hx)) ?_
        rw [dist_comm y z]
        exact hshell z y fun x hx ↦ hM x (Or.inr hx)
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The Lipschitz bound for bounded harmonic functions.** Let `u` be harmonic on neighbourhoods
of the closed balls `closedBall y s` and `closedBall z s`, with `0 < s` and `dist y z ≤ s`, and let
`‖u‖ ≤ M` on the open balls `ball y s` and `ball z s`. Then

`‖u y - u z‖ ≤ 2ⁿ n M dist y z / s`,

where `n` is the dimension of `E`. This is the difference form of the interior gradient estimate
`|∇u| ≤ C M / s` for harmonic functions. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.norm_sub_le_of_norm_le {y z : E} {s M : ℝ}
    (hy : HarmonicOnNhd u (closedBall y s)) (hz : HarmonicOnNhd u (closedBall z s))
    (hM : ∀ x ∈ ball y s ∪ ball z s, ‖u x‖ ≤ M) (hs : 0 < s) (hyz : dist y z ≤ s) :
    ‖u y - u z‖ ≤ 2 ^ finrank ℝ E * finrank ℝ E * M * dist y z / s := by
  borelize E
  have hmain := mul_norm_sub_le_of_norm_le Measure.addHaar hy hz hM hs
  set n := finrank ℝ E
  set ω := (Measure.addHaar : Measure E).real (ball 0 1)
  set d := dist y z
  have hω : 0 < ω := measureReal_ball_pos _ 0 one_pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (Or.inl (mem_ball_self hs)))
  have hd : 0 ≤ d := dist_nonneg
  rw [le_div_iff₀ hs]
  -- In dimension `0` both points coincide; otherwise `(s + d)ⁿ - sⁿ ≤ n d (2 s)ⁿ⁻¹`.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h : ω * ‖u y - u z‖ ≤ 0 := by simpa [hn] using hmain
    simpa [hn] using mul_nonpos_of_nonpos_of_nonneg (nonpos_of_mul_nonpos_right h hω) hs.le
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hk] at hmain ⊢
  have hpow : (s + d) ^ (k + 1) - s ^ (k + 1) ≤ d * (k + 1) * (2 * s) ^ k := by
    refine (le_abs_self _).trans ((abs_pow_sub_pow_le (s + d) s (k + 1)).trans ?_)
    simp only [add_sub_cancel_left, Nat.add_sub_cancel, Nat.cast_succ]
    gcongr <;> grind
  have hmain' : s ^ (k + 1) * ω * ‖u y - u z‖ ≤
      s ^ (k + 1) * ω * (2 ^ (k + 1) * (k + 1) * M * d / s) := by
    refine hmain.trans ?_
    calc 2 * M * (((s + d) ^ (k + 1) - s ^ (k + 1)) * ω)
        ≤ 2 * M * (d * (k + 1) * (2 * s) ^ k * ω) := by gcongr
      _ = _ := by field_simp; ring
  have := le_of_mul_le_mul_left hmain' (by positivity)
  rw [le_div_iff₀ hs] at this
  push_cast
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- On `ball x₀ ρ` with `8 ρ ≤ R`, a function harmonic on `ball x₀ R` with `‖u - c‖ ≤ M` on
`ball x₀ (R / 2)` oscillates by at most `2ⁿ⁺³ n M ρ / R`. -/
private lemma norm_sub_le_of_mem_ball_of_eight_mul_le {x₀ y z : E} {ρ R M : ℝ} {c : F}
    (hu : HarmonicOnNhd u (ball x₀ R)) (hM : ∀ x ∈ ball x₀ (R / 2), ‖u x - c‖ ≤ M)
    (hρ : 0 < ρ) (h8 : 8 * ρ ≤ R) (hy : y ∈ ball x₀ ρ) (hz : z ∈ ball x₀ ρ) :
    ‖u y - u z‖ ≤ 2 ^ (finrank ℝ E + 3) * finrank ℝ E * M * ρ / R := by
  rw [mem_ball] at hy hz
  have hR : 0 < R := by linarith
  -- Both balls of radius `R / 4` about `y` and `z` lie in `ball x₀ (R / 2)`.
  have hcl : ∀ w, dist w x₀ < ρ → closedBall w (R / 4) ⊆ ball x₀ R := fun w hw x hx ↦ by
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith [dist_triangle x w x₀]
  have hop : ∀ w, dist w x₀ < ρ → ball w (R / 4) ⊆ ball x₀ (R / 2) := fun w hw x hx ↦ by
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle x w x₀]
  have hyz : dist y z < 2 * ρ := by linarith [dist_triangle_right y z x₀]
  have hv : HarmonicOnNhd (fun x ↦ u x - c) (ball x₀ R) := hu.sub (harmonicOnNhd_const c)
  have h := (hv.mono (hcl y hy)).norm_sub_le_of_norm_le (hv.mono (hcl z hz))
    (fun x hx ↦ hM x (hx.elim (hop y hy ·) (hop z hz ·))) (by positivity) (by linarith)
  rw [sub_sub_sub_cancel_right] at h
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_ball_self (half_pos hR)))
  refine h.trans ?_
  calc 2 ^ finrank ℝ E * finrank ℝ E * M * dist y z / (R / 4)
      ≤ 2 ^ finrank ℝ E * finrank ℝ E * M * (2 * ρ) / (R / 4) := by gcongr
    _ = _ := by field_simp; ring

/-- The decay of the mean oscillation for small balls, `8 ρ ≤ R`, with constant `2^(3n + 6) n²`. -/
private lemma setIntegral_ball_norm_sub_setAverage_sq_le_of_eight_mul_le {x₀ : E} {ρ R : ℝ}
    (hu : HarmonicOnNhd u (ball x₀ R)) {c : F}
    (hint : IntegrableOn (fun x ↦ ‖u x - c‖ ^ 2) (ball x₀ R) μ) (hρ : 0 < ρ) (h8 : 8 * ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * finrank ℝ E + 6) * finrank ℝ E ^ 2 * (ρ / R) ^ (finrank ℝ E + 2) *
        ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ := by
  set n := finrank ℝ E with hn
  set I := ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ
  have hR : 0 < R := by linarith
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  -- The pointwise bound on `ball x₀ (R / 2)` bounds `‖u - c‖` there by `M`, and so the
  -- oscillation of `u` on `ball x₀ ρ` by `L`.
  set M := √(2 ^ n * I / (R ^ n * μ.real (ball (0 : E) 1)))
  have hM2 : M ^ 2 = 2 ^ n * I / (R ^ n * μ.real (ball (0 : E) 1)) :=
    Real.sq_sqrt (by positivity)
  have hv : HarmonicOnNhd (fun x ↦ u x - c) (ball x₀ R) := hu.sub (harmonicOnNhd_const c)
  set L := 2 ^ (n + 3) * n * M * ρ / R
  have hlip : ∀ y ∈ ball x₀ ρ, ∀ z ∈ ball x₀ ρ, ‖u y - u z‖ ≤ L := fun y hy z hz ↦
    norm_sub_le_of_mem_ball_of_eight_mul_le hu
      (fun x hx ↦ Real.le_sqrt_of_sq_le (norm_sq_le_of_mem_ball_half hR hv hint hx)) hρ h8 hy hz
  -- Every value of `u` on `ball x₀ ρ` therefore lies within `L` of the average.
  have hiu : IntegrableOn u (ball x₀ ρ) μ :=
    (hu.mono (closedBall_subset_ball (by linarith))).integrableOn_ball
  have hdev : ∀ y ∈ ball x₀ ρ, ‖u y - ⨍ z in ball x₀ ρ, u z ∂μ‖ ≤ L := fun y hy ↦ by
    have h := Convex.set_average_mem (convex_closedBall (u y) L) isClosed_closedBall
      (measure_ball_pos μ x₀ hρ).ne' measure_ball_lt_top.ne
      ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
        exact hlip y hy z hz) hiu
    rwa [mem_closedBall, dist_eq_norm, norm_sub_rev] at h
  calc ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ
      ≤ ∫ _ in ball x₀ ρ, L ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
          (integrableOn_const measure_ball_lt_top.ne) ?_
        refine (ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (hdev x hx) 2
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, μ.addHaar_real_ball_of_pos x₀ hρ, ← hn]
        simp only [L, div_pow, mul_pow, hM2]
        field_simp
        ring

/-- **Decay of the `L²` mean oscillation of a harmonic function.** If `u` is harmonic on the ball
`ball x₀ R` and `‖u - c‖²` is integrable there for some constant `c`, then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u - u_ρ‖² ≤ 2^(3n + 8) (n + 1)² (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖u - c‖²`,

where `u_ρ` is the average of `u` over `ball x₀ ρ` and `n` is the dimension of `E`. Taking for `c`
the average of `u` over `ball x₀ R` gives the Campanato decay estimate of the mean oscillation. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le
    {x₀ : E} {ρ R : ℝ} (hu : HarmonicOnNhd u (ball x₀ R)) {c : F}
    (hint : IntegrableOn (fun x ↦ ‖u x - c‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2 * (ρ / R) ^ (finrank ℝ E + 2) *
        ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ := by
  set n := finrank ℝ E with hn
  set I := ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity
  rcases hρ.eq_or_lt with rfl | hρ
  · simp only [ball_zero, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hR : 0 < R := hρ.trans_le hρR
  rcases le_or_gt (8 * ρ) R with h8 | h8
  · refine (setIntegral_ball_norm_sub_setAverage_sq_le_of_eight_mul_le hu hint hρ h8).trans ?_
    gcongr <;> simp [← hn]
  -- For `ρ > R / 8`, compare with the constant `c` and use `(ρ / R)^(n + 2) ≥ 8^-(n + 2)`.
  have hiu : IntegrableOn u (ball x₀ R) μ := by
    have hm : AEStronglyMeasurable (fun x ↦ u x - c) (μ.restrict (ball x₀ R)) :=
      (hu.continuousOn.sub continuousOn_const).aestronglyMeasurable measurableSet_ball
    have : IsFiniteMeasure (μ.restrict (ball x₀ R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have h := ((memLp_two_iff_integrable_sq_norm hm).2 hint).integrable one_le_two
    exact (h.add (integrableOn_const (C := c) measure_ball_lt_top.ne)).congr
      (ae_of_all _ fun x ↦ by simp)
  have hle : 4 ≤ 2 ^ (3 * n + 8) * ((n : ℝ) + 1) ^ 2 * (ρ / R) ^ (n + 2) := by
    have h8' : (1 : ℝ) / 8 ≤ ρ / R := by
      rw [div_le_div_iff₀ (by norm_num) hR]; linarith
    calc (4 : ℝ) = 2 ^ (3 * n + 8) * 1 * (1 / 8) ^ (n + 2) := by
          rw [one_div, inv_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ
      ≤ 4 * ∫ x in ball x₀ ρ, ‖u x - c‖ ^ 2 ∂μ :=
        setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
          (hiu.mono_set (ball_subset_ball hρR)) (hint.mono_set (ball_subset_ball hρR))
    _ ≤ 4 * I := by
        gcongr
        exact setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
          (ball_subset_ball hρR).eventuallyLE
    _ ≤ _ := by gcongr

/-! ### Linear changes of variables -/

section LinearChange

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {e : E' ≃L[ℝ] E}

variable {a b : ℝ}

omit [FiniteDimensional ℝ E] in
/-- **Decay of the `L²` mass after a linear change of variables.** Let `e : E' ≃L[ℝ] E` be a
continuous linear equivalence with `‖e.symm x‖ ≤ a ‖x‖` and `‖e y‖ ≤ b ‖y‖`, and let `u ∘ e`
be harmonic on `e ⁻¹' ball x₀ R`, with `‖u‖²` integrable on `ball x₀ R`. Then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u‖² ≤ 2ⁿ (a b)ⁿ (ρ / R)ⁿ ∫_{ball x₀ R} ‖u‖²`,

where `n` is the dimension of `E`. The constant depends on `e` only through the bound `a b` for
its condition number. -/
theorem setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp (e : E' ≃L[ℝ] E)
    (hae : ∀ x, ‖e.symm x‖ ≤ a * ‖x‖) (hbe : ∀ y, ‖e y‖ ≤ b * ‖y‖) {x₀ : E}
    {ρ R : ℝ} (hu : HarmonicOnNhd (u ∘ e) (e ⁻¹' ball x₀ R))
    (hint : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤
      2 ^ finrank ℝ E * (a * b) ^ finrank ℝ E * (ρ / R) ^ finrank ℝ E *
        ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ := by
  set n := finrank ℝ E
  set I := ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity
  have hmono : ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤ I :=
    setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
      (ball_subset_ball hρR).eventuallyLE
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In a zero-dimensional space all the powers are `1`.
    simpa [n, finrank_zero_of_subsingleton] using hmono
  -- In a nontrivial space the two bounds force `a` and `b` to be positive.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have ha : 0 < a := pos_of_mul_pos_left
    ((norm_pos_iff.2 (e.symm.map_ne_zero_iff.2 hx)).trans_le (hae x)) (norm_nonneg x)
  have hb : 0 < b := pos_of_mul_pos_left
    ((norm_pos_iff.2 hx).trans_le (by simpa using hbe (e.symm x))) (norm_nonneg _)
  rcases hρ.eq_or_lt with rfl | hρ
  · simp only [ball_zero, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hR : 0 < R := hρ.trans_le hρR
  rcases le_or_gt (a * ρ) (R / b) with hle | hlt
  · -- Pull the integrals back along `e` and apply the harmonic estimate for `μ.map e.symm`.
    set ν := μ.map e.symm
    -- `e` carries `ν` to `μ`, so it transports integrals over preimages without a Jacobian.
    have hmp : MeasurePreserving e ν μ := by
      simpa using e.symm.toHomeomorph.toMeasurableEquiv.measurePreserving_symm μ
    have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    -- The bounds on `e` and `e.symm` make them Lipschitz, which compares the balls.
    have hsub : ball (e.symm x₀) (R / b) ⊆ e ⁻¹' ball x₀ R := fun y hy ↦ by
      simpa [Real.coe_toNNReal _ hb.le, mul_div_cancel₀ _ hb.ne'] using
        (AddMonoidHomClass.lipschitz_of_bound e b hbe).mapsTo_ball (by simpa using hb) _ _ hy
    have hsup : e ⁻¹' ball x₀ ρ ⊆ ball (e.symm x₀) (a * ρ) := fun y hy ↦ by
      simpa [Real.coe_toNNReal _ ha.le] using
        (AddMonoidHomClass.lipschitz_of_bound e.symm a hae).mapsTo_ball (by simpa using ha) _ _ hy
    have hint' : IntegrableOn (fun y ↦ ‖(u ∘ e) y‖ ^ 2) (e ⁻¹' ball x₀ R) ν :=
      (hmp.integrableOn_comp_preimage hemb (f := fun x ↦ ‖u x‖ ^ 2)).2 hint
    have hdec := (hu.mono hsub).setIntegral_ball_norm_sq_le (μ := ν) (hint'.mono_set hsub)
      (by positivity) hle
    rw [e.toLinearEquiv.finrank_eq] at hdec
    calc ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ
        = ∫ y in e ⁻¹' ball x₀ ρ, ‖(u ∘ e) y‖ ^ 2 ∂ν :=
          (hmp.setIntegral_preimage_emb hemb (fun x ↦ ‖u x‖ ^ 2) _).symm
      _ ≤ ∫ y in ball (e.symm x₀) (a * ρ), ‖(u ∘ e) y‖ ^ 2 ∂ν :=
          setIntegral_mono_set (hint'.mono_set ((ball_subset_ball hle).trans hsub))
            (ae_of_all _ fun _ ↦ by positivity) hsup.eventuallyLE
      _ ≤ 2 ^ n * (a * ρ / (R / b)) ^ n * ∫ y in ball (e.symm x₀) (R / b), ‖(u ∘ e) y‖ ^ 2 ∂ν :=
          hdec
      _ ≤ 2 ^ n * (a * ρ / (R / b)) ^ n * ∫ y in e ⁻¹' ball x₀ R, ‖(u ∘ e) y‖ ^ 2 ∂ν := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact setIntegral_mono_set hint' (ae_of_all _ fun _ ↦ by positivity) hsub.eventuallyLE
      _ = _ := by
          -- `MeasurePreserving.setIntegral_preimage_emb` matches the goal only after unfolding
          -- `∘`, so state the pullback of `I` in the form in which it appears here.
          have hI' : ∫ y in e ⁻¹' ball x₀ R, ‖(u ∘ e) y‖ ^ 2 ∂ν = I :=
            hmp.setIntegral_preimage_emb hemb (fun x ↦ ‖u x‖ ^ 2) _
          rw [hI']
          field_simp
          ring
  · -- For `a ρ > R / b` the factor `2ⁿ (a b)ⁿ (ρ / R)ⁿ` is at least one.
    have h1 : 1 ≤ 2 ^ n * (a * b) ^ n * (ρ / R) ^ n := by
      rw [← mul_pow, ← mul_pow]
      refine one_le_pow₀ ?_
      rw [div_lt_iff₀ hb] at hlt
      rw [← mul_div_assoc, le_div_iff₀ hR]
      nlinarith
    exact hmono.trans (le_mul_of_one_le_left hI h1)

/-- **Decay of the `L²` mean oscillation after a linear change of variables.** Let
`e : E' ≃L[ℝ] E` be a continuous linear equivalence with `‖e.symm x‖ ≤ a ‖x‖` and
`‖e y‖ ≤ b ‖y‖`, and let `u ∘ e` be harmonic on `e ⁻¹' ball x₀ R`, with `‖u - c‖²` integrable on
`ball x₀ R` for some constant `c`. Then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u - u_ρ‖² ≤ C (a b)^(n + 2) (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖u - c‖²`
with `C = 2^(3n + 10) (n + 1)²`,

where `u_ρ` is the average of `u` over `ball x₀ ρ` and `n` is the dimension of `E`. -/
theorem setIntegral_ball_norm_sub_setAverage_sq_le_of_harmonicOnNhd_comp (e : E' ≃L[ℝ] E)
    (hae : ∀ x, ‖e.symm x‖ ≤ a * ‖x‖) (hbe : ∀ y, ‖e y‖ ≤ b * ‖y‖)
    {x₀ : E} {ρ R : ℝ} (hu : HarmonicOnNhd (u ∘ e) (e ⁻¹' ball x₀ R)) {c : F}
    (hint : IntegrableOn (fun x ↦ ‖u x - c‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * finrank ℝ E + 10) * (finrank ℝ E + 1) ^ 2 * (a * b) ^ (finrank ℝ E + 2) *
        (ρ / R) ^ (finrank ℝ E + 2) * ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ := by
  set n := finrank ℝ E with hn
  set I := ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ ↦ by positivity
  -- `u` is continuous on `ball x₀ R`, so `u - c'` is square integrable there for every `c'`.
  have hcont : ContinuousOn u (ball x₀ R) := by
    refine (hu.continuousOn.comp e.symm.continuous.continuousOn fun x hx ↦ ?_).congr
      fun x _ ↦ by simp
    simpa using hx
  have hfin : IsFiniteMeasure (μ.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmeas : AEStronglyMeasurable u (μ.restrict (ball x₀ R)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hL2 : MemLp (fun x ↦ u x - c) 2 (μ.restrict (ball x₀ R)) :=
    (memLp_two_iff_integrable_sq_norm (hmeas.sub aestronglyMeasurable_const)).2 hint
  have hint_c : ∀ c' : F, IntegrableOn (fun x ↦ ‖u x - c'‖ ^ 2) (ball x₀ R) μ := fun c' ↦ by
    have h : MemLp (fun x ↦ u x - c') 2 (μ.restrict (ball x₀ R)) :=
      (hL2.add (memLp_const (c - c'))).congr_norm (hmeas.sub aestronglyMeasurable_const)
        (ae_of_all _ fun x ↦ by simp)
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  have hiu : IntegrableOn u (ball x₀ ρ) μ :=
    IntegrableOn.mono_set (((hL2.integrable one_le_two).add (integrable_const c)).congr
      (ae_of_all _ fun x ↦ by simp)) (ball_subset_ball hρR)
  -- Comparing with the constant `c` gives the estimate whenever the factor is at least `4`.
  have hfour : ∀ K : ℝ, 4 ≤ K →
      ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤ K * I := fun K hK ↦
    calc ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ
        ≤ 4 * ∫ x in ball x₀ ρ, ‖u x - c‖ ^ 2 ∂μ :=
          setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne hiu
            (hint.mono_set (ball_subset_ball hρR))
      _ ≤ 4 * I := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact setIntegral_mono_set hint (ae_of_all _ fun _ ↦ by positivity)
            (ball_subset_ball hρR).eventuallyLE
      _ ≤ K * I := by gcongr
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In a zero-dimensional space `u` is constant, so the left side vanishes.
    have hconst : ∀ y, u y = u x₀ := fun y ↦ congrArg u (Subsingleton.elim y x₀)
    have hzero : ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ = 0 := by
      rcases hρ.eq_or_lt with rfl | hρ'
      · simp
      simp_rw [hconst, setAverage_const (measure_ball_pos μ x₀ hρ').ne' measure_ball_lt_top.ne,
        sub_self, norm_zero]
      simp
    rw [hzero]
    simp only [hn, finrank_zero_of_subsingleton, zero_add]
    positivity
  -- In a nontrivial space the two bounds force `a` and `b` to be positive.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have ha : 0 < a := pos_of_mul_pos_left
    ((norm_pos_iff.2 (e.symm.map_ne_zero_iff.2 hx)).trans_le (hae x)) (norm_nonneg x)
  have hb : 0 < b := pos_of_mul_pos_left
    ((norm_pos_iff.2 hx).trans_le (by simpa using hbe (e.symm x))) (norm_nonneg _)
  rcases hρ.eq_or_lt with rfl | hρ
  · simp only [ball_zero, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hR : 0 < R := hρ.trans_le hρR
  rcases le_or_gt (a * ρ) (R / b) with hle | hlt
  · -- Compare with the average `c'` of `u ∘ e` over `ball (e.symm x₀) (a ρ)` for `μ.map e.symm`,
    -- pull the integrals back along `e`, and apply the harmonic estimate for that measure.
    set ν := μ.map e.symm
    set c' := ⨍ y in ball (e.symm x₀) (a * ρ), (u ∘ e) y ∂ν
    -- `e` carries `ν` to `μ`, so it transports integrals over preimages without a Jacobian.
    have hmp : MeasurePreserving e ν μ := by
      simpa using e.symm.toHomeomorph.toMeasurableEquiv.measurePreserving_symm μ
    have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    -- The bounds on `e` and `e.symm` make them Lipschitz, which compares the balls.
    have hsub : ball (e.symm x₀) (R / b) ⊆ e ⁻¹' ball x₀ R := fun y hy ↦ by
      simpa [Real.coe_toNNReal _ hb.le, mul_div_cancel₀ _ hb.ne'] using
        (AddMonoidHomClass.lipschitz_of_bound e b hbe).mapsTo_ball (by simpa using hb) _ _ hy
    have hsup : e ⁻¹' ball x₀ ρ ⊆ ball (e.symm x₀) (a * ρ) := fun y hy ↦ by
      simpa [Real.coe_toNNReal _ ha.le] using
        (AddMonoidHomClass.lipschitz_of_bound e.symm a hae).mapsTo_ball (by simpa using ha) _ _ hy
    have hint' : IntegrableOn (fun y ↦ ‖(u ∘ e) y - c‖ ^ 2) (e ⁻¹' ball x₀ R) ν :=
      (hmp.integrableOn_comp_preimage hemb (f := fun x ↦ ‖u x - c‖ ^ 2)).2 hint
    have hint'' : IntegrableOn (fun y ↦ ‖(u ∘ e) y - c'‖ ^ 2) (e ⁻¹' ball x₀ R) ν :=
      (hmp.integrableOn_comp_preimage hemb (f := fun x ↦ ‖u x - c'‖ ^ 2)).2 (hint_c c')
    have hdec := (hu.mono hsub).setIntegral_ball_norm_sub_setAverage_sq_le (μ := ν)
      (hint'.mono_set hsub) (by positivity) hle
    rw [e.toLinearEquiv.finrank_eq] at hdec
    calc ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ
        ≤ 4 * ∫ x in ball x₀ ρ, ‖u x - c'‖ ^ 2 ∂μ :=
          setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne hiu
            ((hint_c c').mono_set (ball_subset_ball hρR))
      _ = 4 * ∫ y in e ⁻¹' ball x₀ ρ, ‖(u ∘ e) y - c'‖ ^ 2 ∂ν :=
          congrArg (4 * ·) (hmp.setIntegral_preimage_emb hemb (fun x ↦ ‖u x - c'‖ ^ 2) _).symm
      _ ≤ 4 * ∫ y in ball (e.symm x₀) (a * ρ), ‖(u ∘ e) y - c'‖ ^ 2 ∂ν := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact setIntegral_mono_set (hint''.mono_set ((ball_subset_ball hle).trans hsub))
            (ae_of_all _ fun _ ↦ by positivity) hsup.eventuallyLE
      _ ≤ 4 * (2 ^ (3 * n + 8) * (n + 1) ^ 2 * (a * ρ / (R / b)) ^ (n + 2) *
            ∫ y in ball (e.symm x₀) (R / b), ‖(u ∘ e) y - c‖ ^ 2 ∂ν) := by
          gcongr
      _ ≤ 4 * (2 ^ (3 * n + 8) * (n + 1) ^ 2 * (a * ρ / (R / b)) ^ (n + 2) *
            ∫ y in e ⁻¹' ball x₀ R, ‖(u ∘ e) y - c‖ ^ 2 ∂ν) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num)
          exact setIntegral_mono_set hint' (ae_of_all _ fun _ ↦ by positivity) hsub.eventuallyLE
      _ = _ := by
          -- `MeasurePreserving.setIntegral_preimage_emb` matches the goal only after unfolding
          -- `∘`, so state the pullback of `I` in the form in which it appears here.
          have hI' : ∫ y in e ⁻¹' ball x₀ R, ‖(u ∘ e) y - c‖ ^ 2 ∂ν = I :=
            hmp.setIntegral_preimage_emb hemb (fun x ↦ ‖u x - c‖ ^ 2) _
          rw [hI']
          field_simp
          ring
  · -- For `a ρ > R / b` compare with the constant `c`; the factor is then at least `4`.
    have h1 : 1 ≤ (a * b * (ρ / R)) ^ (n + 2) := by
      refine one_le_pow₀ ?_
      rw [div_lt_iff₀ hb] at hlt
      rw [← mul_div_assoc, le_div_iff₀ hR]
      nlinarith
    have h4 : 4 ≤ 2 ^ (3 * n + 10) * ((n : ℝ) + 1) ^ 2 * (a * b) ^ (n + 2) * (ρ / R) ^ (n + 2) := by
      rw [mul_assoc _ ((a * b) ^ (n + 2)), ← mul_pow]
      have h2 : (4 : ℝ) ≤ 2 ^ (3 * n + 10) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * n + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])
      calc (4 : ℝ) = 4 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    exact hfour _ h4

end LinearChange

end TauCeti

namespace InnerProductSpace.HarmonicOnNhd

open MeasureTheory Metric Module Set TauCeti TauCeti.MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Comparison with a harmonic function.** Let `H` be harmonic on `B_r = ball x₀ r` in a space
of dimension `n`, and let `f` and `H` be square integrable on `B_r`. For `0 < ρ ≤ r`, the square
mean oscillation `ψ(t) = ∫_{B_t} ‖f - f_{B_t}‖²` of `f` decays like that of `H`, up to the
distance `∫_{B_r} ‖f - H‖²` between them:
`ψ(ρ) ≤ 4D (ρ / r)^(n + 2) ψ(r) + (4D + 2) ∫_{B_r} ‖f - H‖²`, where `D = 2^(3n + 8) (n + 1)²` is
the constant of `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`. -/
theorem setIntegral_ball_norm_sub_setAverage_sq_le_add {f H : E → F}
    {x₀ : E} {ρ r : ℝ} (hH : HarmonicOnNhd H (ball x₀ r)) (hf : MemLp f 2 (μ.restrict (ball x₀ r)))
    (hHm : MemLp H 2 (μ.restrict (ball x₀ r))) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, f y ∂μ‖ ^ 2 ∂μ ≤
      4 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2) * (ρ / r) ^ (finrank ℝ E + 2) *
          (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
        (4 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2) + 2) *
          ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
  have hr : 0 < r := hρ.trans_le hρr
  have hsubρ : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hfint : ∀ c, IntegrableOn (fun x => ‖f x - c‖ ^ 2) (ball x₀ r) μ :=
    hf.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne
  have hHint : ∀ c, IntegrableOn (fun x => ‖H x - c‖ ^ 2) (ball x₀ r) μ :=
    hHm.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne
  have hfH : IntegrableOn (fun x => ‖f x - H x‖ ^ 2) (ball x₀ r) μ :=
    (hf.sub hHm).integrable_norm_pow two_ne_zero
  have hE0 : 0 ≤ ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hψr : 0 ≤ ∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hD : (0 : ℝ) ≤ 2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2 := by positivity
  have hq0 : 0 ≤ (ρ / r) ^ (finrank ℝ E + 2) := by positivity
  have hq1 : (ρ / r) ^ (finrank ℝ E + 2) ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  -- The decay of the harmonic `H` from `B_r` to `B_ρ`.
  have hdecay := hH.setIntegral_ball_norm_sub_setAverage_sq_le (hHint (⨍ y in ball x₀ r, f y ∂μ))
    hρ.le hρr
  -- On `B_ρ`, compare `f` with the average of `H`, then split off `f - H`.
  have step1 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
    measure_ball_lt_top.ne (hf.integrableOn_of_subset one_le_two hsubρ measure_ball_lt_top.ne)
    (hf.integrableOn_norm_sub_sq_of_subset hsubρ measure_ball_lt_top.ne
      (⨍ y in ball x₀ ρ, H y ∂μ))
  have step2 : ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, H y ∂μ‖ ^ 2 ∂μ ≤
      2 * (∫ x in ball x₀ ρ, ‖H x - ⨍ y in ball x₀ ρ, H y ∂μ‖ ^ 2 ∂μ) +
        2 * ∫ x in ball x₀ ρ, ‖f x - H x‖ ^ 2 ∂μ := by
    simpa only [sub_add_sub_cancel'] using
      setIntegral_norm_add_sq_le ((hHint _).mono_set hsubρ) (hfH.mono_set hsubρ)
  -- On `B_r`, compare `H` with the average of `f`.
  have step3 : ∫ x in ball x₀ r, ‖H x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ ≤
      2 * (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
        2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
    have hHf : IntegrableOn (fun x => ‖H x - f x‖ ^ 2) (ball x₀ r) μ := by
      simpa only [norm_sub_rev (f _)] using hfH
    simpa only [sub_add_sub_cancel', norm_sub_rev (H _)] using
      setIntegral_norm_add_sq_le (hfint (⨍ y in ball x₀ r, f y ∂μ)) hHf
  have step4 : ∫ x in ball x₀ ρ, ‖f x - H x‖ ^ 2 ∂μ ≤ ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ :=
    setIntegral_mono_set hfH (ae_of_all _ fun _ => by positivity) hsubρ.eventuallyLE
  calc ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, f y ∂μ‖ ^ 2 ∂μ
      ≤ 2 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2 * (ρ / r) ^ (finrank ℝ E + 2) *
          (2 * (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
            2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ)) +
          2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
        refine step1.trans (step2.trans (add_le_add ?_ ?_))
        · gcongr
          exact hdecay.trans (by gcongr)
        · gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hq1 (mul_nonneg hD hE0)]

end InnerProductSpace.HarmonicOnNhd
