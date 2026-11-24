/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Fourier.RiemannLebesgue

/-!
# Darboux's method

For `f` holomorphic on a punctured disc `0 < |z - c| < r`, the Laurent coefficient
`f_n = TauCeti.circleLaurentCoeff f c ρ n = (2πi)⁻¹ ∮_{|z - c| = ρ} (z - c)^{-n-1} f(z) dz` does not
depend on `ρ ∈ (0, r)`. Darboux's method compares `f` with a function `g`, holomorphic on the same
punctured disc, whose coefficients `g_n` are known: if the difference `f - g` extends
continuously to the closed punctured disc `0 < |z - c| ≤ r`, then `f_n = g_n + o(r^{-n})` as
`n → ±∞` (DLMF 2.10.29). Typically `g` collects the singular parts of `f` on the circle
`|z - c| = r`, and the theorem says that they alone determine the coefficients of `f` up to an
error that is `o(r^{-n})`.
More generally (DLMF 2.10.31), if the `m`-th derivative `f⁽ᵐ⁾ - g⁽ᵐ⁾` extends continuously to
`0 < |z - c| ≤ r`, then `f_n = g_n + o(r^{-n} |n|^{-m})`.

The proof moves the integration circle out to the boundary circle `|z - c| = r`, which
`TauCeti.circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable` allows because the
continuous extension of `f - g` is continuous up to that circle. More generally, the coefficients
extracted on the inner circle of a closed annulus `ρ ≤ |z - c| ≤ r`, of any function continuous on
the annulus and holomorphic inside it, are `o(r^{-n})`. On a circle of radius `R ≠ 0`,
`R ^ n` times the `n`-th Laurent coefficient of any function is the `n`-th Fourier coefficient of
`θ ↦ f(c + R e^{iθ})` on `[0, 2π]`, and these tend to `0` by the Riemann--Lebesgue lemma.
For the derivative form, the coefficients of `f⁽ᵐ⁾` are those of `f` multiplied by falling
factorials (`TauCeti.circleLaurentCoeff_iteratedDeriv`), which grow like `|n|ᵐ`.

## Main results

* `TauCeti.zpow_smul_circleLaurentCoeff_eq_fourierCoeffOn`: on a circle of radius `R ≠ 0`,
  `R ^ n • circleLaurentCoeff f c R n` is the `n`-th Fourier coefficient of `θ ↦ f(c + R e^{iθ})`
  on `[0, 2π]`.
* `TauCeti.tendsto_zpow_smul_circleLaurentCoeff`: `R ^ n • circleLaurentCoeff f c R n → 0` as
  `n → ±∞`, for every function `f` and radius `R`.
* `TauCeti.tendsto_zpow_smul_circleLaurentCoeff_of_differentiable_on_annulus_off_countable`:
  `r ^ n • circleLaurentCoeff f c ρ n → 0` as `n → ±∞` for `f` continuous on the closed annulus
  `ρ ≤ |z - c| ≤ r` and holomorphic off a countable set inside it.
* `TauCeti.tendsto_zpow_smul_circleLaurentCoeff_sub`: Darboux's comparison theorem (DLMF 2.10.29).
* `TauCeti.tendsto_pow_mul_zpow_smul_circleLaurentCoeff_sub_of_iteratedDeriv`: its refinement for
  continuous `m`-th derivatives (DLMF 2.10.31).

Worked examples with explicit simple poles are in
`TauCeti.Analysis.Complex.Laurent.Examples.Darboux`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.10(iv),
  <https://dlmf.nist.gov/2.10.iv>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 8.
-/

public section

open Complex Set Metric Filter Polynomial
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On a circle of radius `R ≠ 0`, the Laurent coefficient of degree `n`, scaled by `R ^ n`, is the
`n`-th Fourier coefficient on `[0, 2π]` of the restriction `θ ↦ f(c + R e^{iθ})` of `f` to the
circle. -/
theorem zpow_smul_circleLaurentCoeff_eq_fourierCoeffOn (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0)
    (n : ℤ) :
    R ^ n • circleLaurentCoeff f c R n =
      fourierCoeffOn Real.two_pi_pos (fun θ ↦ f (circleMap c R θ)) n := by
  -- On the circle, `(z - c) ^ (-n)` is `R ^ (-n)` times the Fourier character of degree `-n`.
  have hpt (θ : ℝ) : circleMap 0 R θ ^ (-n) =
      ((R ^ (-n) : ℝ) : ℂ) * fourier (-n) (θ : AddCircle (2 * π - 0)) := by
    rw [circleMap_zero_zpow, circleMap_zero, fourier_coe_apply]
    push_cast [sub_zero]
    congr 2
    field_simp
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [circleLaurentCoeff_def, circleIntegral_sub_zpow_sub_one_smul f c hR (-n),
    fourierCoeffOn_eq_integral]
  simp_rw [hpt, mul_smul, intervalIntegral.integral_smul, smul_smul, ← Complex.coe_smul, smul_smul]
  -- What remains is the scalar identity `R ^ n (2πi)⁻¹ i R ^ (-n) = (2π)⁻¹`.
  congr 1
  push_cast [sub_zero]
  rw [zpow_neg]
  field_simp

/-- **Riemann--Lebesgue for Laurent coefficients**: on any circle of radius `R`, the Laurent
coefficients of any function satisfy `R ^ n • circleLaurentCoeff f c R n → 0` as `n → ±∞`, that is,
`circleLaurentCoeff f c R n = o(R ^ (-n))` when `R ≠ 0`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff (f : ℂ → E) (c : ℂ) (R : ℝ) :
    Tendsto (fun n : ℤ ↦ R ^ n • circleLaurentCoeff f c R n) cofinite (𝓝 0) := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp
  simp_rw [zpow_smul_circleLaurentCoeff_eq_fourierCoeffOn f c hR]
  exact tendsto_fourierCoeffOn_cofinite _ _

/-- **Riemann--Lebesgue on an annulus**: let `f` be continuous on the closed annulus
`ρ ≤ |z - c| ≤ r` (`0 < ρ`) and complex differentiable off a countable set in its interior. Then
the Laurent coefficients extracted on the inner circle satisfy `f_n = o(r ^ (-n))` as `n → ±∞`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff_of_differentiable_on_annulus_off_countable
    {f : ℂ → E} {c : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c r \ ball c ρ))
    (hd : ∀ z ∈ (ball c r \ closedBall c ρ) \ s, DifferentiableAt ℂ f z) :
    Tendsto (fun n : ℤ ↦ r ^ n • circleLaurentCoeff f c ρ n) cofinite (𝓝 0) :=
  -- Move the integration circle out to radius `r`, where Riemann--Lebesgue applies.
  (tendsto_zpow_smul_circleLaurentCoeff f c r).congr fun n ↦ by
    rw [circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hρ hρr hs hc hd]

/-- **Darboux's method** (DLMF 2.10.29). Let `f` and `g` be holomorphic on the punctured disc
`0 < |z - c| < r`, and let `f - g` agree there with a function `h` continuous on the closed
punctured disc `0 < |z - c| ≤ r`. Then the Laurent coefficients, extracted on any circle of radius
`ρ ∈ (0, r)`, satisfy `f_n = g_n + o(r ^ (-n))` as `n → ±∞`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff_sub {f g h : ℂ → E} {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hf : DifferentiableOn ℂ f (ball c r \ {c}))
    (hg : DifferentiableOn ℂ g (ball c r \ {c})) (hh : ContinuousOn h (closedBall c r \ {c}))
    (hfgh : EqOn (f - g) h (ball c r \ {c})) :
    Tendsto (fun n : ℤ ↦ r ^ n • (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n))
      cofinite (𝓝 0) := by
  have hsph : sphere c ρ ⊆ ball c r \ {c} :=
    subset_sdiff_singleton (sphere_subset_ball hρr) fun hc ↦ ne_of_mem_sphere hc hρ.ne' rfl
  have hann : closedBall c r \ ball c ρ ⊆ closedBall c r \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_ball_self hρ))
  have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
  -- `h` satisfies the annulus hypotheses, and `f_n - g_n` is the coefficient of `h` on the circle
  -- of radius `ρ`.
  refine (tendsto_zpow_smul_circleLaurentCoeff_of_differentiable_on_annulus_off_countable hρ hρr.le
    countable_empty (hh.mono hann) fun z hz ↦ ?_).congr fun n ↦ ?_
  · have hz' : z ∈ ball c r \ {c} :=
      ⟨hz.1.1, fun hzc ↦ hz.1.2 (hzc ▸ mem_closedBall_self hρ.le)⟩
    exact ((hf.sub hg).differentiableAt (hopen.mem_nhds hz')).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hopen.mem_nhds hz') hfgh).symm
  · rw [← circleLaurentCoeff_sub ((hf.continuousOn.mono hsph).circleIntegrable hρ.le)
        ((hg.continuousOn.mono hsph).circleIntegrable hρ.le),
      circleLaurentCoeff_congr (f := fun z ↦ f z - g z) (g := h) hρ.le
        (fun z hz ↦ hfgh (hsph hz))]

/-- The falling factorial `n (n - 1) ⋯ (n - m + 1)` is at least `|n|ᵐ / 2ᵐ` once `|n| ≥ 2m`. -/
private theorem abs_pow_le_two_pow_mul_norm_descPochhammer_eval {m : ℕ} {n : ℤ}
    (hn : 2 * (m : ℝ) ≤ |(n : ℝ)|) :
    |(n : ℝ)| ^ m ≤ 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ := by
  calc |(n : ℝ)| ^ m = ∏ _j ∈ Finset.range m, |(n : ℝ)| := by simp
    _ ≤ ∏ j ∈ Finset.range m, 2 * ‖(n : ℂ) - j‖ := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun j hj ↦ ?_
      have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hj
      have h := norm_sub_norm_le (n : ℂ) (j : ℂ)
      rw [norm_intCast, Complex.norm_natCast] at h
      linarith
    _ = 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        descPochhammer_eval_eq_prod_range, norm_prod]

/-- **Darboux's method with derivatives** (DLMF 2.10.31). Let `f` and `g` be holomorphic on the
punctured disc `0 < |z - c| < r`, and let `f⁽ᵐ⁾ - g⁽ᵐ⁾` agree there with a function `h` continuous
on the closed punctured disc `0 < |z - c| ≤ r`. Then the Laurent coefficients, extracted on any
circle of radius `ρ ∈ (0, r)`, satisfy `f_n = g_n + o(r ^ (-n) |n| ^ (-m))` as `n → ±∞`. For
`m = 0` this is `tendsto_zpow_smul_circleLaurentCoeff_sub`. -/
theorem tendsto_pow_mul_zpow_smul_circleLaurentCoeff_sub_of_iteratedDeriv [CompleteSpace E]
    {f g h : ℂ → E} {c : ℂ} {r ρ : ℝ} (m : ℕ) (hρ : 0 < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball c r \ {c})) (hg : DifferentiableOn ℂ g (ball c r \ {c}))
    (hh : ContinuousOn h (closedBall c r \ {c}))
    (hfgh : EqOn (iteratedDeriv m f - iteratedDeriv m g) h (ball c r \ {c})) :
    Tendsto (fun n : ℤ ↦ ((n : ℝ) ^ m * r ^ n) •
      (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n)) cofinite (𝓝 0) := by
  have hr : 0 < r := hρ.trans hρr
  have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
  have hD {φ : ℂ → E} (hφ : DifferentiableOn ℂ φ (ball c r \ {c})) :
      DifferentiableOn ℂ (iteratedDeriv m φ) (ball c r \ {c}) := by
    simpa only [iteratedDeriv_eq_iterate] using
      ((hφ.analyticOnNhd hopen).iterated_deriv m).differentiableOn
  have hdom : ball c r \ {c} = eball c (ENNReal.ofReal r) \ closedBall c 0 := by
    rw [eball_ofReal, closedBall_zero]
  have hρR : ENNReal.ofReal ρ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 hρr
  -- Darboux's theorem for the `m`-th derivatives, read at the shifted degree `n - m`.
  have hT := ((tendsto_zpow_smul_circleLaurentCoeff_sub hρ hρr (hD hf) (hD hg) hh hfgh).comp
    (sub_left_injective (b := (m : ℤ))).tendsto_cofinite).norm.const_mul ((2 * r) ^ m)
  rw [norm_zero, mul_zero] at hT
  refine squeeze_zero_norm' ?_ hT
  have hfin : ∀ᶠ n : ℤ in cofinite, 2 * (m : ℝ) ≤ |(n : ℝ)| := by
    refine eventually_cofinite.2 ((Set.finite_Ioo (-(2 * (m : ℤ))) (2 * m)).subset fun n hn ↦ ?_)
    have hn := abs_lt.1 (not_le.1 hn)
    refine ⟨?_, ?_⟩
    · have : ((-(2 * (m : ℤ)) : ℤ) : ℝ) < n := by push_cast; linarith
      exact_mod_cast this
    · have : (n : ℝ) < ((2 * (m : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  -- For `|n| ≥ 2m`, the coefficients of the derivatives are the falling factorial, of size at
  -- least `|n|ᵐ / 2ᵐ`, times those of `f - g`.
  filter_upwards [hfin] with n hn
  rw [hdom] at hf hg
  simp only [Function.comp_apply, circleLaurentCoeff_iteratedDeriv hf le_rfl hρ hρR,
    circleLaurentCoeff_iteratedDeriv hg le_rfl hρ hρR, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_of_pos (zpow_pos hr _)]
  have hpow : r ^ n = r ^ (n - m) * r ^ m := by
    rw [← zpow_natCast, ← zpow_add₀ hr.ne', sub_add_cancel]
  calc |(n : ℝ)| ^ m * r ^ n * ‖circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n‖
      ≤ 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ * r ^ n *
          ‖circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n‖ := by
        gcongr
        exact abs_pow_le_two_pow_mul_norm_descPochhammer_eval hn
    _ = _ := by rw [hpow, mul_pow]; ring

end TauCeti
