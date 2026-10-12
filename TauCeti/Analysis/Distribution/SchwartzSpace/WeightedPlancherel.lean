/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.MeasureTheory.Integral.DistRpow

/-!
# Weighted Plancherel and `L¹` bounds for inverse Fourier transforms

Let `V` be a finite-dimensional real inner product space of dimension `n` and `σ` a Schwartz
function on `V` with values in a complex Hilbert space. Differentiating `σ` along `m` multiplies
its inverse Fourier transform by `-2πi ⟪x, m⟫`, so Plancherel's theorem gives the **weighted
Plancherel identity**

`(2π) ^ (2N) ∫ ⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖² dx = ‖∂_m^N σ‖²_{L²}`.

Summing it along an orthonormal basis `b` controls `∫ ‖x‖ ^ (2N) ‖𝓕⁻ σ x‖²`. When `2N > n`, the
weight `‖x‖ ^ (-2N)` is integrable away from the origin, and the Cauchy–Schwarz inequality turns
the weighted `L²` bound into an `L¹` bound on the tail:

`∫_{‖x‖ > R} ‖𝓕⁻ σ x‖ dx ≤ C R ^ (n/2 - N) (∑ᵢ ‖∂_{bᵢ}^N σ‖²_{L²}) ^ (1/2)`.

On the ball `‖x‖ ≤ R`, Cauchy–Schwarz and Plancherel bound the integral by `C R ^ (n/2) ‖σ‖_{L²}`.
Together these bound the `L¹` norm of the kernel `𝓕⁻ σ` by the `L²` norms of `σ` and of its
derivatives of order `N > n/2`. This is a quantitative form, for Schwartz functions, of
Bernstein's theorem on absolutely convergent Fourier integrals.

These are the estimates on the kernel of a single dyadic piece in the proof of the
Mihlin–Hörmander multiplier theorem. If the symbol `σ` is supported where `‖ξ‖ ~ 2ʲ`, its kernel
`𝓕⁻ σ` is controlled by taking `R = 2⁻ʲ`. The translation estimate
`∫ ‖𝓕⁻ σ (x + h) - 𝓕⁻ σ x‖ ≤ 2π ∫ ‖𝓕⁻ (⟪·, h⟫ σ)‖` reduces the smoothness of the kernel to the
same `L¹` bound for the symbol `⟪ξ, h⟫ σ(ξ)`.

## Main declarations

* `SchwartzMap.integral_inner_pow_mul_norm_fourierInv_sq`: the weighted Plancherel identity.
* `SchwartzMap.integral_norm_pow_mul_norm_fourierInv_sq_le`: its consequence for the weight
  `‖x‖ ^ (2N)`.
* `SchwartzMap.setIntegral_closedBall_norm_fourierInv_le`: the `L¹` bound on `‖x‖ ≤ R`.
* `SchwartzMap.exists_setIntegral_norm_fourierInv_le`: the `L¹` bound on `{‖x‖ > R}`.
* `SchwartzMap.exists_integral_norm_fourierInv_le`: the `L¹` bound on `V`.
* `SchwartzMap.integral_norm_fourierInv_add_sub_le`: the translation estimate.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2 (proof of Theorem 6.2.7).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  §3.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Real LineDeriv ENNReal
open FourierTransform MeasureTheory Metric Module

namespace SchwartzMap

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Normed

variable [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- For a Schwartz function `σ`, the function `⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖²` is integrable. -/
theorem integrable_inner_pow_mul_norm_fourierInv_sq (σ : 𝓢(V, H)) (m : V) (N : ℕ) :
    Integrable fun x ↦ ⟪x, m⟫ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2 := by
  refine ((((𝓕⁻ ((∂_{m})^[N] σ)).memLp 2).integrable_norm_pow two_ne_zero).const_mul
    ((2 * π) ^ (2 * N))⁻¹).congr (.of_forall fun x ↦ ?_)
  simp only [norm_fourierInv_iterate_lineDerivOp_sq]
  field_simp

/-- **The translation estimate for an inverse Fourier transform**: translating `𝓕⁻ σ` by `h`
moves it in `L¹` by at most `2π` times the `L¹` norm of the inverse Fourier transform of
`ξ ↦ ⟪ξ, h⟫ σ ξ`. -/
theorem integral_norm_fourierInv_add_sub_le (σ : 𝓢(V, H)) (h : V) :
    ∫ x, ‖𝓕⁻ σ (x + h) - 𝓕⁻ σ x‖ ≤
      2 * π * ∫ x, ‖𝓕⁻ (smulLeftCLM H (inner ℝ · h) σ) x‖ := by
  have hu : ContDiff ℝ 1 ⇑(𝓕⁻ σ : 𝓢(V, H)) := (𝓕⁻ σ).smooth 1
  -- The derivative of `𝓕⁻ σ` along `h` is the inverse Fourier transform of `2πi ⟪ξ, h⟫ σ ξ`.
  have hD (x : V) : ‖fderiv ℝ ⇑(𝓕⁻ σ : 𝓢(V, H)) x h‖ₑ =
      ENNReal.ofReal (2 * π * ‖𝓕⁻ (smulLeftCLM H (inner ℝ · h) σ) x‖) := by
    rw [← lineDerivOp_apply_eq_fderiv, lineDerivOp_fourierInv_eq, fourierInv_smul, smul_apply,
      ← ofReal_norm, norm_smul, Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  have hle := hu.setLIntegral_enorm_comp_add_sub_rpow_le (mu := volume) le_rfl h
    MeasurableSet.univ (K := Set.univ) fun _ _ _ _ ↦ Set.mem_univ _
  simp only [Measure.restrict_univ, ENNReal.rpow_one, hD] at hle
  rw [← ofReal_integral_eq_lintegral_ofReal
    (((𝓕⁻ (smulLeftCLM H (inner ℝ · h) σ)).integrable.norm).const_mul _)
    (.of_forall fun _ ↦ by positivity), integral_const_mul] at hle
  rw [integral_norm_eq_lintegral_enorm (by fun_prop)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- **Cauchy–Schwarz on `{‖x‖ > R}`**, splitting `‖𝓕⁻ σ x‖ = ‖x‖ ^ (-N) · ‖x‖ ^ N ‖𝓕⁻ σ x‖`. -/
private theorem setLIntegral_enorm_fourierInv_le (σ : 𝓢(V, H)) (N : ℕ) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in {x | R < ‖x‖}, ‖𝓕⁻ σ x‖ₑ ≤
      (∫⁻ x in {x : V | R < ‖x‖}, ENNReal.ofReal (‖x‖ ^ (-((2 * N : ℕ) : ℝ)))) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2)) ^ (1 / (2 : ℝ)) := by
  have hS : MeasurableSet {x : V | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have heq : ∫⁻ x in {x | R < ‖x‖}, ‖𝓕⁻ σ x‖ₑ = ∫⁻ x in {x | R < ‖x‖},
      ENNReal.ofReal (‖x‖ ^ (-(N : ℝ))) * ENNReal.ofReal (‖x‖ ^ N * ‖𝓕⁻ σ x‖) := by
    refine setLIntegral_congr_fun hS fun x hx ↦ ?_
    have hx0 : 0 < ‖x‖ := hR.trans hx
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, Real.rpow_neg hx0.le,
      Real.rpow_natCast, inv_mul_cancel₀ (by positivity), one_mul, ofReal_norm]
  rw [heq]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
    (f := fun x ↦ ENNReal.ofReal (‖x‖ ^ (-(N : ℝ))))
    (g := fun x ↦ ENNReal.ofReal (‖x‖ ^ N * ‖𝓕⁻ σ x‖)) (by fun_prop) (by fun_prop)).trans ?_
  refine mul_le_mul' (ENNReal.rpow_le_rpow (lintegral_congr fun x ↦ ?_).le (by norm_num))
    (ENNReal.rpow_le_rpow ((setLIntegral_le_lintegral _ _).trans_eq
      (lintegral_congr fun x ↦ ?_)) (by norm_num))
  · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    push_cast
    ring
  · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two, Real.rpow_two, mul_pow,
      ← pow_mul, mul_comm N 2]

end Normed

section Hilbert

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The weighted Plancherel identity**: for a Schwartz function `σ`,

`(2π) ^ (2N) ∫ ⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖² dx = ‖∂_m^N σ‖²_{L²}`. -/
theorem integral_inner_pow_mul_norm_fourierInv_sq (σ : 𝓢(V, H)) (m : V) (N : ℕ) :
    (2 * π) ^ (2 * N) * ∫ x, ⟪x, m⟫ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2 =
      ‖((∂_{m})^[N] σ).toLp 2‖ ^ 2 := by
  rw [← norm_fourierInv_toL2_eq, ← Lp.integral_norm_sq_eq_norm_sq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕⁻ ((∂_{m})^[N] σ)).coeFn_toLp 2] with x hx
  rw [hx, norm_fourierInv_iterate_lineDerivOp_sq]

/-- **The weighted Plancherel bound**: for a Schwartz function `σ`, an orthonormal basis `b` of
`V` indexed by `ι`, and `N ≠ 0`,

`(2π) ^ (2N) ∫ ‖x‖ ^ (2N) ‖𝓕⁻ σ x‖² dx ≤ (#ι) ^ (N - 1) ∑ᵢ ‖∂_{bᵢ}^N σ‖²_{L²}`. -/
theorem integral_norm_pow_mul_norm_fourierInv_sq_le {ι : Type*} [Fintype ι] (σ : 𝓢(V, H))
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : N ≠ 0) :
    (2 * π) ^ (2 * N) * ∫ x, ‖x‖ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) ^ (N - 1) * ∑ i, ‖((∂_{b i})^[N] σ).toLp 2‖ ^ 2 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN
  -- `‖x‖ ^ (2 (M + 1)) = (∑ᵢ ⟪x, bᵢ⟫²) ^ (M + 1) ≤ (#ι) ^ M ∑ᵢ ⟪x, bᵢ⟫ ^ (2 (M + 1))`.
  have hpt (x : V) : ‖x‖ ^ (2 * (M + 1)) * ‖𝓕⁻ σ x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) ^ M * ∑ i, ⟪x, b i⟫ ^ (2 * (M + 1)) * ‖𝓕⁻ σ x‖ ^ 2 := by
    rw [pow_mul, ← b.sum_sq_inner_left x, ← Finset.sum_mul, ← mul_assoc]
    gcongr
    simp_rw [pow_mul]
    exact pow_sum_le_card_mul_sum_pow (fun i _ ↦ sq_nonneg _) M
  have hint : Integrable fun x ↦
      (Fintype.card ι : ℝ) ^ M * ∑ i, ⟪x, b i⟫ ^ (2 * (M + 1)) * ‖𝓕⁻ σ x‖ ^ 2 :=
    (integrable_finsetSum _ fun i _ ↦
      integrable_inner_pow_mul_norm_fourierInv_sq σ (b i) (M + 1)).const_mul _
  refine (mul_le_mul_of_nonneg_left
    (integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) hint (.of_forall hpt))
    (by positivity)).trans_eq ?_
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_inner_pow_mul_norm_fourierInv_sq σ (b i) (M + 1), Nat.add_sub_cancel,
    mul_left_comm, Finset.mul_sum]
  simp_rw [integral_inner_pow_mul_norm_fourierInv_sq]

/-- **The inverse Fourier transform on a ball in `L¹`**, by Cauchy–Schwarz and Plancherel:
`∫_{‖x‖ ≤ R} ‖𝓕⁻ σ x‖ dx ≤ √(|B(0, 1)| Rⁿ) ‖σ‖_{L²}`. -/
theorem setIntegral_closedBall_norm_fourierInv_le (σ : 𝓢(V, H)) {R : ℝ} (hR : 0 < R) :
    ∫ x in closedBall (0 : V) R, ‖𝓕⁻ σ x‖ ≤
      √(volume.real (ball (0 : V) 1)) * R ^ ((finrank ℝ V : ℝ) / 2) * ‖σ.toLp 2‖ := by
  set A : ℝ := volume.real (ball (0 : V) 1)
  have hA : 0 ≤ A := measureReal_nonneg
  have hvol : volume (closedBall (0 : V) R) = ENNReal.ofReal (R ^ finrank ℝ V * A) := by
    rw [Measure.addHaar_closedBall _ _ hR.le, ← ofReal_measureReal,
      ← ENNReal.ofReal_mul (by positivity)]
  have hL2 : ∫⁻ x, ‖𝓕⁻ σ x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖σ.toLp 2‖ ^ 2) := by
    rw [← norm_fourierInv_toL2_eq, ← Lp.integral_norm_sq_eq_norm_sq,
      ofReal_integral_eq_lintegral_ofReal ((Lp.memLp _).integrable_norm_pow two_ne_zero)
        (.of_forall fun _ ↦ by positivity)]
    refine lintegral_congr_ae ?_
    filter_upwards [(𝓕⁻ σ).coeFn_toLp 2] with x hx
    rw [hx, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
      Real.rpow_two]
  have hle : ∫⁻ x in closedBall (0 : V) R, ‖𝓕⁻ σ x‖ₑ ≤
      ENNReal.ofReal (√A * R ^ ((finrank ℝ V : ℝ) / 2) * ‖σ.toLp 2‖) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (closedBall (0 : V) R))
      Real.HolderConjugate.two_two (f := fun _ ↦ 1) (g := fun x ↦ ‖𝓕⁻ σ x‖ₑ)
      aemeasurable_const (by fun_prop)
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply,
      MeasurableSet.univ, Set.univ_inter, hvol] at h
    refine (h.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
      ((setLIntegral_le_lintegral _ _).trans_eq hL2) (by norm_num)))).trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    ring_nf
  rw [integral_norm_eq_lintegral_enorm (by fun_prop)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- **The tail of an inverse Fourier transform in `L¹`.** Let `b` be an orthonormal basis of the
`n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` such that for every
Schwartz function `σ` and every `R > 0`,

`∫_{‖x‖ > R} ‖𝓕⁻ σ x‖ dx ≤ C R ^ (n/2 - N) (∑ᵢ ‖∂_{bᵢ}^N σ‖²_{L²}) ^ (1/2)`. -/
theorem exists_setIntegral_norm_fourierInv_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : 𝓢(V, H)) (R : ℝ), 0 < R →
      ∫ x in {x | R < ‖x‖}, ‖𝓕⁻ σ x‖ ≤
        C * R ^ ((finrank ℝ V : ℝ) / 2 - N) * √(∑ i, ‖((∂_{b i})^[N] σ).toLp 2‖ ^ 2) := by
  set n : ℕ := finrank ℝ V
  have hN0 : N ≠ 0 := by omega
  have hns : (n : ℝ) < (2 * N : ℕ) := by exact_mod_cast hN
  set A : ℝ := volume.real (ball (0 : V) 1)
  set c : ℝ := 2 ^ (n : ℝ) / (1 - 2 ^ ((n : ℝ) - (2 * N : ℕ)))
  set D : ℝ := (Fintype.card ι : ℝ) ^ (N - 1) / (2 * π) ^ (2 * N)
  have hA : 0 ≤ A := measureReal_nonneg
  have hc : 0 ≤ c := div_nonneg (by positivity) (sub_nonneg.2
    (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)))
  have hD : 0 ≤ D := by positivity
  refine ⟨√(A * c) * √D, by positivity, fun σ R hR ↦ ?_⟩
  set S : Set V := {x | R < ‖x‖}
  set T : ℝ := √(∑ i, ‖((∂_{b i})^[N] σ).toLp 2‖ ^ 2)
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  -- The weighted `L²` bound: `∫ ‖x‖ ^ (2N) ‖𝓕⁻ σ x‖² ≤ D T²`.
  have hW : ∫ x, ‖x‖ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2 ≤ D * T ^ 2 := by
    have h := integral_norm_pow_mul_norm_fourierInv_sq_le σ b hN0
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ by positivity), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- Cauchy–Schwarz splits the tail integral into the tail of `‖x‖ ^ (-2N)`, which is
  -- `O(R ^ (n - 2N))`, and the weighted `L²` integral, which is at most `D T²`.
  have hCS := setLIntegral_enorm_fourierInv_le σ N hR
  have htail := (volume : Measure V).setLIntegral_ofReal_norm_rpow_neg_le hns hR
  rw [← ofReal_measureReal] at htail
  have hK : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2) ≤
      ENNReal.ofReal (D * T ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_pow_mul_norm_sq _ _)
      (.of_forall fun _ ↦ by positivity)]
    exact ENNReal.ofReal_le_ofReal hW
  -- Taking square roots gives the bound in `∫⁻` form.
  have hle : ∫⁻ x in S, ‖𝓕⁻ σ x‖ₑ ≤
      ENNReal.ofReal (√(A * c) * √D * R ^ ((n : ℝ) / 2 - N) * T) := by
    have hRpow : √(R ^ ((n : ℝ) - (2 * N : ℕ))) = R ^ ((n : ℝ) / 2 - N) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
      congr 1
      push_cast
      ring
    refine (hCS.trans (mul_le_mul' (ENNReal.rpow_le_rpow htail (by norm_num))
      (ENNReal.rpow_le_rpow hK (by norm_num)))).trans_eq ?_
    rw [← ENNReal.ofReal_mul hA, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← mul_assoc A c, Real.sqrt_mul (by positivity), Real.sqrt_mul hD, Real.sqrt_sq hT, hRpow]
    ring_nf
  rw [integral_norm_eq_lintegral_enorm (by fun_prop)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- **An inverse Fourier transform in `L¹`.** Let `b` be an orthonormal basis of the
`n`-dimensional space `V` and `2N > n`. There is a constant `C ≥ 0` such that for every
Schwartz function `σ` and every `R > 0`,

`∫ ‖𝓕⁻ σ x‖ dx ≤ C (R ^ (n/2) ‖σ‖_{L²} + R ^ (n/2 - N) (∑ᵢ ‖∂_{bᵢ}^N σ‖²_{L²}) ^ (1/2))`. -/
theorem exists_integral_norm_fourierInv_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {N : ℕ} (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (σ : 𝓢(V, H)) (R : ℝ), 0 < R →
      ∫ x, ‖𝓕⁻ σ x‖ ≤ C * (R ^ ((finrank ℝ V : ℝ) / 2) * ‖σ.toLp 2‖ +
        R ^ ((finrank ℝ V : ℝ) / 2 - N) * √(∑ i, ‖((∂_{b i})^[N] σ).toLp 2‖ ^ 2)) := by
  obtain ⟨C, -, hC⟩ := exists_setIntegral_norm_fourierInv_le (H := H) b hN
  set A : ℝ := volume.real (ball (0 : V) 1)
  have hA : 0 ≤ A := measureReal_nonneg
  refine ⟨max √A C, (Real.sqrt_nonneg _).trans (le_max_left _ _), fun σ R hR ↦ ?_⟩
  set S : Set V := {x | R < ‖x‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hSc : Sᶜ = closedBall (0 : V) R := by
    ext x
    simp [S]
  have hnear := setIntegral_closedBall_norm_fourierInv_le σ hR
  rw [← hSc] at hnear
  have hint : Integrable fun x ↦ ‖𝓕⁻ σ x‖ := (𝓕⁻ σ).integrable.norm
  rw [← integral_add_compl hS hint, mul_add, add_comm]
  refine add_le_add (hnear.trans ?_) ((hC σ R hR).trans ?_) <;> rw [← mul_assoc] <;>
    gcongr
  exacts [le_max_left _ _, le_max_right _ _]

end Hilbert

end SchwartzMap
