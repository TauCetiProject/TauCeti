/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.Analysis.Complex.Laurent.Expansion
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
error of smaller exponential order.

The proof moves the integration circle out to the boundary circle `|z - c| = r`, which
`TauCeti.circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable` allows because the
continuous extension of `f - g` is continuous up to that circle. On a circle of radius `R ≠ 0`,
`R ^ n` times the `n`-th Laurent coefficient of any function is the `n`-th Fourier coefficient of
`θ ↦ f(c + R e^{iθ})` on `[0, 2π]`, and these tend to `0` by the Riemann--Lebesgue lemma.

## Main results

* `TauCeti.zpow_smul_circleLaurentCoeff_eq_fourierCoeffOn`: on a circle of radius `R ≠ 0`,
  `R ^ n • circleLaurentCoeff f c R n` is the `n`-th Fourier coefficient of `θ ↦ f(c + R e^{iθ})`
  on `[0, 2π]`.
* `TauCeti.tendsto_zpow_smul_circleLaurentCoeff`: `R ^ n • circleLaurentCoeff f c R n → 0` as
  `n → ±∞`, for every function `f` and radius `R`.
* `TauCeti.tendsto_circleLaurentCoeff_sub`: Darboux's comparison theorem (DLMF 2.10.29).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.10(iv),
  <https://dlmf.nist.gov/2.10.iv>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 8.
-/

public section

open Complex Set Metric Filter
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
  rw [circleLaurentCoeff_def, fourierCoeffOn_eq_integral, circleIntegral, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← intervalIntegral.integral_smul,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  have he : cexp (θ * I) ≠ 0 := exp_ne_zero _
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [deriv_circleMap, circleMap_sub_center, circleMap_zero, fourier_coe_apply, smul_smul]
  have hθ : (2 * π * I * ((-n : ℤ) : ℂ) * θ / ((2 * π - 0 : ℝ) : ℂ)) = -(n * (θ * I)) := by
    push_cast [sub_zero]
    field_simp
  congr 1
  rw [zpow_sub_one₀ (mul_ne_zero hRc he), mul_zpow, zpow_neg, zpow_neg, ← exp_int_mul, hθ,
    exp_neg]
  push_cast [sub_zero]
  field_simp

/-- **Riemann--Lebesgue for Laurent coefficients**: on any circle of radius `R`, the Laurent
coefficients of any function satisfy `R ^ n • circleLaurentCoeff f c R n → 0` as `n → ±∞`, that is,
`circleLaurentCoeff f c R n = o(R ^ (-n))` when `R ≠ 0`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff (f : ℂ → E) (c : ℂ) (R : ℝ) :
    Tendsto (fun n : ℤ ↦ R ^ n • circleLaurentCoeff f c R n) cofinite (𝓝 0) := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp [circleLaurentCoeff_def, circleIntegral.integral_radius_zero]
  simp_rw [zpow_smul_circleLaurentCoeff_eq_fourierCoeffOn f c hR]
  exact tendsto_fourierCoeffOn_cofinite _ _

/-- **Darboux's method** (DLMF 2.10.29). Let `f` and `g` be holomorphic on the punctured disc
`0 < |z - c| < r`, and let `f - g` agree there with a function `h` continuous on the closed
punctured disc `0 < |z - c| ≤ r`. Then the Laurent coefficients, extracted on any circle of radius
`ρ ∈ (0, r)`, satisfy `f_n = g_n + o(r ^ (-n))` as `n → ±∞`. -/
theorem tendsto_circleLaurentCoeff_sub {f g h : ℂ → E} {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hf : DifferentiableOn ℂ f (ball c r \ {c}))
    (hg : DifferentiableOn ℂ g (ball c r \ {c})) (hh : ContinuousOn h (closedBall c r \ {c}))
    (hfgh : EqOn (f - g) h (ball c r \ {c})) :
    Tendsto (fun n : ℤ ↦ r ^ n • (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n))
      cofinite (𝓝 0) := by
  have hsph : sphere c ρ ⊆ ball c r \ {c} := fun z hz ↦
    ⟨mem_ball.2 ((mem_sphere.1 hz).trans_lt hρr), ne_of_mem_sphere hz hρ.ne'⟩
  have hann : closedBall c r \ ball c ρ ⊆ closedBall c r \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_ball_self hρ))
  have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
  -- Replace `f_n - g_n` by the coefficient of `h` on the circle of radius `ρ`, then move that
  -- circle out to radius `r`, where Riemann--Lebesgue applies.
  refine (tendsto_zpow_smul_circleLaurentCoeff h c r).congr fun n ↦ ?_
  rw [← circleLaurentCoeff_sub ((hf.continuousOn.mono hsph).circleIntegrable hρ.le)
      ((hg.continuousOn.mono hsph).circleIntegrable hρ.le),
    circleLaurentCoeff_congr (f := fun z ↦ f z - g z) (g := h) hρ.le (fun z hz ↦ hfgh (hsph hz)),
    circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hρ hρr.le countable_empty
      (hh.mono hann)]
  intro z hz
  have hz' : z ∈ ball c r \ {c} :=
    ⟨hz.1.1, fun hzc ↦ hz.1.2 (hzc ▸ mem_closedBall_self hρ.le)⟩
  exact ((hf.sub hg).differentiableAt (hopen.mem_nhds hz')).congr_of_eventuallyEq
    (eventuallyEq_of_mem (hopen.mem_nhds hz') hfgh).symm

/-! ### Examples -/

/-- On every circle `|z| = ρ` with `0 < ρ < 1`, the Laurent coefficients of `1 / (1 - z)` are `1`
in every nonnegative degree and `0` in every negative degree. -/
example {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (n : ℤ) :
    circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n = if 0 ≤ n then 1 else 0 := by
  simpa using circleLaurentCoeff_inv_sub (a := 1) (c := 0) hρ (by simpa using hρ1) n

/-- Darboux's method with `f(z) = 1 / (1 - z) + 1 / (2 - z)`, `g(z) = 1 / (1 - z)` and `r = 1`:
`f - g = 1 / (2 - z)` is continuous on `|z| ≤ 1`, and `f_n - g_n = 2 ^ (-n - 1)` for `n ≥ 0` and
`0` for `n < 0`, which is `o(1)` as `n → ±∞`. -/
example {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∀ n : ℤ, circleLaurentCoeff (fun z ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
        circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n = if 0 ≤ n then 2 ^ (-n - 1) else 0) ∧
      Tendsto (fun n : ℤ ↦ (1 : ℝ) ^ n • (circleLaurentCoeff (fun z ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
        circleLaurentCoeff (fun z ↦ (1 - z)⁻¹) 0 ρ n)) cofinite (𝓝 0) := by
  have hball : ∀ a : ℂ, 1 ≤ ‖a‖ → ∀ z ∈ ball (0 : ℂ) 1 \ {0}, a - z ≠ 0 := fun a ha z hz h ↦ by
    rw [← sub_eq_zero.1 h, Set.mem_sdiff, mem_ball_zero_iff] at hz
    exact (ha.trans_lt hz.1).false
  have hdiff : ∀ a : ℂ, 1 ≤ ‖a‖ → DifferentiableOn ℂ (fun z : ℂ ↦ (a - z)⁻¹) (ball 0 1 \ {0}) :=
    fun a ha ↦ ((differentiableOn_const a).sub differentiableOn_id).inv (hball a ha)
  refine ⟨fun n ↦ ?_, tendsto_circleLaurentCoeff_sub (h := fun z ↦ (2 - z)⁻¹) hρ hρ1
    ((hdiff 1 (by simp)).add (hdiff 2 (by simp))) (hdiff 1 (by simp)) ?_ fun z _ ↦ ?_⟩
  · have hsph : ∀ a : ℂ, 1 ≤ ‖a‖ → CircleIntegrable (fun z : ℂ ↦ (a - z)⁻¹) 0 ρ := fun a ha ↦
      ((hdiff a ha).continuousOn.mono fun z hz ↦
        ⟨mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hz).trans_lt hρ1),
          ne_of_mem_sphere hz hρ.ne'⟩).circleIntegrable hρ.le
    rw [circleLaurentCoeff_add (hsph 1 (by simp)) (hsph 2 (by simp)), add_sub_cancel_left,
      circleLaurentCoeff_inv_sub hρ (by simpa using hρ1.trans one_lt_two), sub_zero]
  · refine (continuousOn_const.sub continuousOn_id).inv₀ fun z hz h ↦ ?_
    simp only [Pi.sub_apply, id_eq, sub_eq_zero] at h
    subst h
    norm_num at hz
  · simp

end TauCeti
