/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Complex.Laurent.Basic
import Mathlib.Analysis.Polynomial.Basic
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Fourier.RiemannLebesgue

/-!
# Darboux's method

For `f` holomorphic on an annulus `a < |z - c| < r` (`0 ≤ a`; the punctured disc when `a = 0`), the
Laurent coefficient
`f_n = TauCeti.circleLaurentCoeff f c ρ n = (2πi)⁻¹ ∮_{|z - c| = ρ} (z - c)^{-n-1} f(z) dz` does not
depend on `ρ ∈ (a, r)`. Darboux's method compares `f` with a function `g`, holomorphic on the same
annulus, whose coefficients `g_n` are known: if the difference `f - g` extends continuously to
`ρ ≤ |z - c| ≤ r`, then `f_n = g_n + o(r^{-n})` as `n → ±∞` (DLMF 2.10.29). Typically `g` collects
the singular parts of `f` on the circle `|z - c| = r`, and the theorem says that they alone
determine the coefficients of `f` up to an error that is `o(r^{-n})`.
More generally (DLMF 2.10.31), if the `m`-th derivative `f⁽ᵐ⁾ - g⁽ᵐ⁾` extends continuously to
`ρ ≤ |z - c| ≤ r`, then `f_n = g_n + o(r^{-n} |n|^{-m})`.

The proof moves the integration circle out to the boundary circle `|z - c| = r`, which
`TauCeti.circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable` allows because the
continuous extension of `f - g` is continuous up to that circle. More generally, the coefficients
extracted on the inner circle of a closed annulus `ρ ≤ |z - c| ≤ r`, of any function continuous on
the annulus and holomorphic inside it, are `o(r^{-n})`. On a circle of radius `R ≠ 0`,
`R ^ n` times the `n`-th Laurent coefficient of any function is the `n`-th Fourier coefficient of
`θ ↦ f(c + R e^{iθ})` on `[0, 2π]`, and these tend to `0` by the Riemann--Lebesgue lemma.
For the derivative form, the coefficients of `f⁽ᵐ⁾` are those of `f` multiplied by falling
factorials (`TauCeti.circleLaurentCoeff_iteratedDeriv`), which are asymptotic to `nᵐ`.

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

open Complex Set Metric Filter Polynomial Asymptotics
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

/-- **Darboux's method** (DLMF 2.10.29). Let `f` and `g` be holomorphic on the annulus
`a < |z - c| < r` (`0 ≤ a`), and let `f - g` agree there with a function `h` continuous on the
closed annulus `ρ ≤ |z - c| ≤ r` for some `ρ ∈ (a, r)`. Then the Laurent coefficients extracted on
the circle of radius `ρ` satisfy `f_n = g_n + o(r ^ (-n))` as `n → ±∞`. The punctured-disc form of
DLMF is the case `a = 0`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff_sub {f g h : ℂ → E} {c : ℂ} {a r ρ : ℝ}
    (ha : 0 ≤ a) (haρ : a < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball c r \ closedBall c a))
    (hg : DifferentiableOn ℂ g (ball c r \ closedBall c a))
    (hh : ContinuousOn h (closedBall c r \ ball c ρ))
    (hfgh : EqOn (f - g) h (ball c r \ closedBall c a)) :
    Tendsto (fun n : ℤ ↦ r ^ n • (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n))
      cofinite (𝓝 0) := by
  have hρ : 0 < ρ := ha.trans_lt haρ
  have hU : IsOpen (ball c r \ closedBall c a) := isOpen_ball.sdiff isClosed_closedBall
  have hsph : sphere c ρ ⊆ ball c r \ closedBall c a := fun z hz ↦
    ⟨sphere_subset_ball hρr hz, fun hz' ↦ by linarith [mem_sphere.1 hz, mem_closedBall.1 hz']⟩
  have hann : ball c r \ closedBall c ρ ⊆ ball c r \ closedBall c a :=
    sdiff_subset_sdiff_right (closedBall_subset_closedBall haρ.le)
  -- `h` satisfies the annulus hypotheses, and `f_n - g_n` is the coefficient of `h` on the circle
  -- of radius `ρ`.
  refine (tendsto_zpow_smul_circleLaurentCoeff_of_differentiable_on_annulus_off_countable hρ hρr.le
    countable_empty hh fun z hz ↦ ?_).congr fun n ↦ ?_
  · exact ((hf.sub hg).differentiableAt (hU.mem_nhds (hann hz.1))).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hU.mem_nhds (hann hz.1)) hfgh).symm
  · rw [← circleLaurentCoeff_sub ((hf.continuousOn.mono hsph).circleIntegrable hρ.le)
        ((hg.continuousOn.mono hsph).circleIntegrable hρ.le),
      circleLaurentCoeff_congr (f := fun z ↦ f z - g z) (g := h) hρ.le
        (fun z hz ↦ hfgh (hsph hz))]

/-- **Darboux's method with derivatives** (DLMF 2.10.31). Let `f` and `g` be holomorphic on the
annulus `a < |z - c| < r` (`0 ≤ a`), and let `f⁽ᵐ⁾ - g⁽ᵐ⁾` agree there with a function `h`
continuous on the closed annulus `ρ ≤ |z - c| ≤ r` for some `ρ ∈ (a, r)`. Then the Laurent
coefficients extracted on the circle of radius `ρ` satisfy `f_n = g_n + o(r ^ (-n) |n| ^ (-m))` as
`n → ±∞`. The punctured-disc form of DLMF is the case `a = 0`. -/
theorem tendsto_pow_mul_zpow_smul_circleLaurentCoeff_sub_of_iteratedDeriv [CompleteSpace E]
    {f g h : ℂ → E} {c : ℂ} {a r ρ : ℝ} (m : ℕ) (ha : 0 ≤ a) (haρ : a < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball c r \ closedBall c a))
    (hg : DifferentiableOn ℂ g (ball c r \ closedBall c a))
    (hh : ContinuousOn h (closedBall c r \ ball c ρ))
    (hfgh : EqOn (iteratedDeriv m f - iteratedDeriv m g) h (ball c r \ closedBall c a)) :
    Tendsto (fun n : ℤ ↦ ((n : ℝ) ^ m * r ^ n) •
      (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n)) cofinite (𝓝 0) := by
  have hρ : 0 < ρ := ha.trans_lt haρ
  have hr : 0 < r := hρ.trans hρr
  have hU : IsOpen (ball c r \ closedBall c a) := isOpen_ball.sdiff isClosed_closedBall
  have hsph : sphere c ρ ⊆ ball c r \ closedBall c a := fun z hz ↦
    ⟨sphere_subset_ball hρr hz, fun hz' ↦ by linarith [mem_sphere.1 hz, mem_closedBall.1 hz']⟩
  have hann : ball c r \ closedBall c ρ ⊆ ball c r \ closedBall c a :=
    sdiff_subset_sdiff_right (closedBall_subset_closedBall haρ.le)
  have hD {φ : ℂ → E} (hφ : DifferentiableOn ℂ φ (ball c r \ closedBall c a)) :
      DifferentiableOn ℂ (iteratedDeriv m φ) (ball c r \ closedBall c a) := by
    simpa only [iteratedDeriv_eq_iterate] using
      ((hφ.analyticOnNhd hU).iterated_deriv m).differentiableOn
  -- Riemann--Lebesgue on the annulus `ρ ≤ |z - c| ≤ r` for `h`, read at the degree `n - m`.
  have hT := ((tendsto_zpow_smul_circleLaurentCoeff_of_differentiable_on_annulus_off_countable
    hρ hρr.le countable_empty hh fun z hz ↦
      (((hD hf).sub (hD hg)).differentiableAt (hU.mem_nhds (hann hz.1))).congr_of_eventuallyEq
        (eventuallyEq_of_mem (hU.mem_nhds (hann hz.1)) hfgh).symm).comp
    (sub_left_injective (b := (m : ℤ))).tendsto_cofinite).const_smul (r ^ m)
  rw [smul_zero] at hT
  -- The coefficients of `h` are the falling factorial times those of `f - g`.
  have hcoeff (n : ℤ) : circleLaurentCoeff h c ρ (n - m) = (descPochhammer ℂ m).eval (n : ℂ) •
      (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n) := by
    rw [← circleLaurentCoeff_congr (f := fun z ↦ iteratedDeriv m f z - iteratedDeriv m g z)
        hρ.le (fun z hz ↦ hfgh (hsph hz)),
      circleLaurentCoeff_sub (((hD hf).continuousOn.mono hsph).circleIntegrable hρ.le)
        (((hD hg).continuousOn.mono hsph).circleIntegrable hρ.le),
      circleLaurentCoeff_iteratedDeriv hU hf hρ hsph,
      circleLaurentCoeff_iteratedDeriv hU hg hρ hsph,
      smul_sub]
  -- The falling factorial is asymptotic to its leading monomial `n ^ m`.
  have hcast : Tendsto (fun n : ℤ ↦ (n : ℂ)) cofinite (Bornology.cobounded ℂ) :=
    Int.cofinite_eq ▸ tendsto_intCast_atBot_sup_atTop_cobounded
  obtain ⟨C, hC⟩ := ((isEquivalent_cobounded_leading_monomial (P := descPochhammer ℂ m)).symm
    |>.isBigO.comp_tendsto hcast).bound
  refine IsBigO.trans_tendsto (IsBigO.of_bound C (hC.mono fun n hn ↦ ?_)) hT
  have hpow : r ^ m * r ^ (n - m) = r ^ n := by
    rw [← zpow_natCast, ← zpow_add₀ hr.ne', add_sub_cancel]
  simp only [Function.comp_apply, hcoeff, (monic_descPochhammer ℂ m).leadingCoeff,
    descPochhammer_natDegree, one_mul, norm_smul, norm_mul, norm_pow, norm_zpow,
    norm_intCast, Real.norm_eq_abs, abs_of_pos hr] at hn ⊢
  calc |(n : ℝ)| ^ m * r ^ n * ‖circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n‖
      ≤ C * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ * r ^ n *
          ‖circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n‖ := by gcongr
    _ = _ := by rw [← hpow]; ring

end TauCeti
