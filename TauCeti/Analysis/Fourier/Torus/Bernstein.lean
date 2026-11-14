/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Fourier.AddCircle.Periodization
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Convolution
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Bernstein's inequalities on the torus

On the torus `𝕋ᵈ = (ℝ / ℤ)^d` with its volume, the product of the Haar probability measures of
the circle factors, let `f` be an integrable function whose Fourier coefficients vanish outside the
ball `‖n‖ ≤ R`, `R ≥ 1`, for the supremum norm on `d → ℤ`: almost everywhere, a trigonometric
polynomial of degree at most `R` in each variable. **Bernstein's inequalities** say that for
`1 ≤ p ≤ q ≤ ∞` there is `C`, depending only on `d`, `p` and `q`, with

`‖∂_{v 0} ⋯ ∂_{v (k - 1)} f‖_q ≤ C ^ (k + 1) R ^ (k + d (1/p - 1/q)) ∏ l, ‖v l‖ ‖f‖_p`

(`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`). The derivative is
described on the Fourier side: `g` is the derivative of `f` along `v 0, …, v (k - 1)` when
`ĝ(n) = (∏ l, 2πi ⟪n, v l⟫) f̂(n)`, which
`TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv` provides for the derivatives of
the lift of a smooth function. The case `k = 0` is **Nikol'skii's inequality**
`‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`, the gain of integrability of a trigonometric polynomial
(`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero`).

These are the periodic counterparts of the whole-space inequalities
`TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`: a block of a
periodic Littlewood–Paley decomposition with frequencies of size `2 ^ j` behaves like a function at
the single scale `2 ^ (-j)`, so that each derivative costs a factor `2 ^ j` and passing from `Lᵖ`
to `L^q` costs `2 ^ (j d (1/p - 1/q))`.

## The argument

The proof follows the whole-space one, convolution with a reproducing kernel, with Poisson
summation to control the periodic kernel. Let `χ` be a smooth cutoff equal to one on `[-1, 1]` and
supported in `(-2, 2)`. The kernel of de la Vallée Poussin type
`V_R(x) = ∑ n, (∏ i, χ (n i / R)) e_n(x)` is a trigonometric polynomial whose coefficients equal one
on the ball `‖n‖ ≤ R`, so `V_R ⋆ f = f` almost everywhere
(`UnitAddTorus.convolution_sum_smul_mFourier_apply` and the uniqueness of Fourier
coefficients, `MeasureTheory.Integrable.ae_eq_sum_mFourier_smul_mFourierCoeff`). It is the tensor
product of the one-dimensional kernels `t ↦ ∑ n, χ (n / R) e_n(t)`. By Poisson summation
(`SchwartzMap.tsum_eq_tsum_fourier`) each of these is the periodization of the kernel
`𝓕⁻ (χ (· / R))` on `ℝ`, a dilate of `𝓕⁻ χ`, so its `L¹` norm on the circle is at most
`∫ ‖𝓕⁻ χ‖`, whatever `R` (`TauCeti.integral_norm_tsum_mul_fourier_le`). Hence `V_R` is
bounded in `L¹` uniformly in `R`, while `‖V_R‖_∞ ≤ (7 R) ^ d` by counting its frequencies, and the
logarithmic convexity of `Lʳ` norms (`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`)
gives `‖V_R‖_r ≤ C R ^ (d (1 - 1/r))`. Young's inequality with `1/r + 1/p = 1 + 1/q`
(`MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv_eq`) gives Nikol'skii's inequality.

For a derivative along `v`, the symbol `2πi ⟪n, v⟫ ∏ j, χ (n j / R)` is the combination
`∑ i, 2πi R v i ∏ j, ηᵢⱼ (n j / R)` of tensor-product symbols, with `ηᵢᵢ(ξ) = ξ χ(ξ)` and `ηᵢⱼ = χ`
for `j ≠ i`. Its kernel therefore has `L¹` norm at most a constant times `R ‖v‖`, and Young's
inequality for an integrable kernel bounds one derivative at a fixed exponent. Derivatives of
higher order follow by iteration through intermediate trigonometric polynomials, and the gain of
integrability is applied last.

## Main declarations

* `TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero`: Nikol'skii's inequality.
* `TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`: Bernstein's
  inequalities for derivatives of every order.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1 (the
  whole-space inequalities, proved by the same convolution argument).
* S. M. Nikol'skii, *Approximation of Functions of Several Variables and Imbedding Theorems*,
  Grundlehren der mathematischen Wissenschaften 205, Springer, 1975, Chapter 3 (Bernstein's and
  Nikol'skii's inequalities for trigonometric polynomials).
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal NNReal ContDiff Convolution

/-! The kernels below take a point of the torus as an explicit argument, so they live in the
root `UnitAddTorus` namespace. -/

namespace UnitAddTorus

open TauCeti TauCeti.UnitAddTorus

/-! ### Tensor-product kernels on the torus -/

section Tensor

variable {d : Type*} [Fintype d]

/-- The tensor-product kernel `x ↦ ∏ i, ∑ n, η i (n / R) e_n (x i)` on the torus, whose Fourier
coefficient at `n` is `∏ i, η i (n i / R)`. -/
private noncomputable def tensorKernel (η : d → ℝ → ℂ) (R : ℝ) (x : UnitAddTorus d) : ℂ :=
  ∏ i, ∑' n : ℤ, η i (n / R) * fourier n (x i)

/-- If every `η i` vanishes outside `[-M, M]`, the tensor-product kernel is the trigonometric
polynomial with coefficients `∏ i, η i (n i / R)` on the box `‖n‖ ≤ ⌈M R⌉`. -/
private theorem tensorKernel_eq_sum [DecidableEq d] {η : d → ℝ → ℂ} {M R : ℝ} (hR : 0 < R)
    (hη : ∀ i ξ, M < |ξ| → η i ξ = 0) (x : UnitAddTorus d) :
    tensorKernel η R x = ∑ n ∈ Fintype.piFinset fun _ : d ↦ Finset.Icc (-⌈M * R⌉) ⌈M * R⌉,
      (∏ i, η i (n i / R)) * mFourier n x := by
  simp only [tensorKernel, fun i ↦ tsum_mul_fourier_eq_sum hR (hη i) (x i)]
  rw [Finset.prod_univ_sum]
  simp only [mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]

private theorem continuous_tensorKernel {η : d → ℝ → ℂ} (hc : ∀ i, HasCompactSupport (η i))
    {R : ℝ} (hR : 0 < R) : Continuous (tensorKernel η R) :=
  continuous_finsetProd _ fun i _ ↦ (continuous_tsum_mul_fourier (hc i) hR).comp
    (continuous_apply i)

/-- The `L¹` norm of a tensor-product kernel is at most the product of the `L¹` norms of the
inverse Fourier transforms of its factors. -/
private theorem integral_norm_tensorKernel_le {η : d → ℝ → ℂ} (hη : ∀ i, ContDiff ℝ ∞ (η i))
    (hc : ∀ i, HasCompactSupport (η i)) {R : ℝ} (hR : 0 < R) :
    ∫ x, ‖tensorKernel η R x‖ ≤ ∏ i, ∫ y, ‖𝓕⁻ (η i) y‖ := by
  simp only [tensorKernel, norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun i t ↦ ‖∑' n : ℤ, η i (n / R) * fourier n t‖)]
  exact Finset.prod_le_prod₀ (fun i _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    fun i _ ↦ integral_norm_tsum_mul_fourier_le (hη i) (hc i) hR

end Tensor

/-! ### The cutoff and its kernels -/

/-- The bump function equal to one on `[-1, 1]` and supported in `(-2, 2)`. -/
private noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- A smooth cutoff `ℝ → ℂ`, equal to one on `[-1, 1]` and to zero outside `(-2, 2)`. -/
private noncomputable def cutoff (ξ : ℝ) : ℂ := (bump ξ : ℂ)

private theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

private theorem hasCompactSupport_cutoff : HasCompactSupport cutoff :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

private theorem cutoff_eq_one {ξ : ℝ} (hξ : |ξ| ≤ 1) : cutoff ξ = 1 := by
  have h : ξ ∈ Metric.closedBall (0 : ℝ) bump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hξ
  rw [cutoff, bump.one_of_mem_closedBall h, Complex.ofReal_one]

private theorem cutoff_eq_zero {ξ : ℝ} (hξ : 2 < |ξ|) : cutoff ξ = 0 := by
  rw [cutoff, bump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hξ.le),
    Complex.ofReal_zero]

private theorem norm_cutoff_le (ξ : ℝ) : ‖cutoff ξ‖ ≤ 1 := by
  rw [cutoff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
  exact bump.le_one

/-- The symbol `ξ χ(ξ)` of the derivative kernels. -/
private noncomputable def derivCutoff (ξ : ℝ) : ℂ := ξ * cutoff ξ

private theorem contDiff_derivCutoff : ContDiff ℝ ∞ derivCutoff :=
  (Complex.ofRealCLM.contDiff).mul contDiff_cutoff

private theorem hasCompactSupport_derivCutoff : HasCompactSupport derivCutoff :=
  hasCompactSupport_cutoff.mul_left

private theorem derivCutoff_eq_zero {ξ : ℝ} (hξ : 2 < |ξ|) : derivCutoff ξ = 0 := by
  rw [derivCutoff, cutoff_eq_zero hξ, mul_zero]

variable {d : Type*} [Fintype d]

omit [Fintype d] in
/-- A property shared by `cutoff` and `derivCutoff` holds for every factor
`Function.update (fun _ ↦ cutoff) i derivCutoff j` of the derivative kernels. -/
private theorem update_cutoff_derivCutoff [DecidableEq d] {P : (ℝ → ℂ) → Prop} (h₀ : P cutoff)
    (h₁ : P derivCutoff) (i j : d) : P (Function.update (fun _ : d ↦ cutoff) i derivCutoff j) := by
  rcases eq_or_ne j i with rfl | hj
  · rwa [Function.update_self]
  · rwa [Function.update_of_ne hj]

/-- The box `‖n‖ ≤ ⌈2 R⌉` of frequencies carrying the kernels at scale `R`. -/
private noncomputable def box (d : Type*) [Fintype d] [DecidableEq d] (R : ℝ) :
    Finset (d → ℤ) :=
  Fintype.piFinset fun _ : d ↦ Finset.Icc (-⌈2 * R⌉) ⌈2 * R⌉

private theorem lt_norm_of_notMem_box [DecidableEq d] {R : ℝ} (hR : 0 < R) {n : d → ℤ}
    (hn : n ∉ box d R) :
    R < ‖n‖ := by
  simp only [box, Fintype.mem_piFinset, not_forall] at hn
  obtain ⟨i, hi⟩ := hn
  rw [Finset.mem_Icc, ← abs_le, not_le] at hi
  have h : (⌈2 * R⌉ : ℝ) < |(n i : ℝ)| := by exact_mod_cast hi
  have hceil : 2 * R ≤ ⌈2 * R⌉ := Int.le_ceil _
  calc R < |(n i : ℝ)| := by linarith
    _ = ‖n i‖ := (Int.norm_eq_abs _).symm
    _ ≤ ‖n‖ := norm_le_pi_norm n i

private theorem prod_cutoff_eq_one {R : ℝ} (hR : 0 < R) {n : d → ℤ} (hn : ‖n‖ ≤ R) :
    ∏ i, cutoff (n i / R) = 1 := by
  refine Finset.prod_eq_one fun i _ ↦ cutoff_eq_one ?_
  rw [abs_div, abs_of_pos hR, div_le_one hR, ← Int.norm_eq_abs]
  exact (norm_le_pi_norm n i).trans hn

/-- The reproducing kernel at scale `R`, the trigonometric polynomial with coefficients
`∏ i, χ (n i / R)`. -/
private theorem tensorKernel_cutoff_eq_sum [DecidableEq d] {R : ℝ} (hR : 0 < R)
    (x : UnitAddTorus d) :
    tensorKernel (fun _ ↦ cutoff) R x =
      ∑ n ∈ box d R, (∏ i, cutoff (n i / R)) * mFourier n x :=
  tensorKernel_eq_sum hR (fun _ _ ↦ cutoff_eq_zero) x

/-- The reproducing kernel at scale `R ≥ 1` is bounded by `(7 R) ^ d`. -/
private theorem norm_tensorKernel_cutoff_le {R : ℝ} (hR : 1 ≤ R) (x : UnitAddTorus d) :
    ‖tensorKernel (fun _ ↦ cutoff) R x‖ ≤ (7 * R) ^ Fintype.card d := by
  have hR0 : 0 < R := one_pos.trans_le hR
  rw [tensorKernel, norm_prod]
  refine (Finset.prod_le_prod₀ (g := fun _ ↦ 7 * R) (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_).trans
    (by rw [Finset.prod_const, Finset.card_univ])
  rw [tsum_mul_fourier_eq_sum hR0 fun _ ↦ cutoff_eq_zero]
  refine (norm_sum_le _ _).trans ?_
  have hterm (n : ℤ) : ‖cutoff (n / R) * fourier n (x i)‖ ≤ 1 := by
    rw [norm_mul, TauCeti.norm_fourier_apply, mul_one]
    exact norm_cutoff_le _
  refine (Finset.sum_le_sum fun n _ ↦ hterm n).trans ?_
  rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
  have hceil : (⌈2 * R⌉ : ℝ) < 2 * R + 1 := Int.ceil_lt_add_one _
  have hnn : (0 : ℤ) ≤ ⌈2 * R⌉ + 1 - -⌈2 * R⌉ := by
    have : (0 : ℤ) ≤ ⌈2 * R⌉ := Int.ceil_nonneg (by linarith)
    omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  push_cast
  linarith

/-- The `Lʳ` norm of the reproducing kernel at scale `R ≥ 1` is `O(R ^ (d (1 - 1/r)))`, by
interpolation between its `L¹` bound, uniform in `R`, and its supremum bound `(7 R) ^ d`. -/
private theorem eLpNorm_tensorKernel_cutoff_le {R : ℝ} (hR : 1 ≤ R) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (tensorKernel (fun _ : d ↦ cutoff) R) r volume ≤
      ENNReal.ofReal (max 1 (∫ y, ‖𝓕⁻ cutoff y‖) ^ Fintype.card d * 7 ^ Fintype.card d *
        R ^ ((Fintype.card d : ℝ) * (1 - r⁻¹.toReal))) := by
  have hR0 : 0 < R := one_pos.trans_le hR
  set K := tensorKernel (fun _ : d ↦ cutoff) R
  set A := ∫ y, ‖𝓕⁻ cutoff y‖
  set k := Fintype.card d
  have hK : Continuous K := continuous_tensorKernel (fun _ ↦ hasCompactSupport_cutoff) hR0
  -- The two endpoint bounds.
  have h1 : eLpNorm K 1 volume ≤ ENNReal.ofReal (A ^ k) := by
    rw [eLpNorm_one_eq_lintegral_eNorm hK.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm
        (hK.integrable_of_hasCompactSupport (.of_compactSpace _))]
    refine ENNReal.ofReal_le_ofReal ((integral_norm_tensorKernel_le
      (fun _ ↦ contDiff_cutoff) (fun _ ↦ hasCompactSupport_cutoff) hR0).trans_eq ?_)
    rw [Finset.prod_const, Finset.card_univ]
  have hinf : eLpNorm K ⊤ volume ≤ ENNReal.ofReal ((7 * R) ^ k) := by
    rw [eLpNorm_exponent_top hK.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun x ↦ ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_tensorKernel_cutoff_le hR x)
  -- Interpolation between them, with `θ = 1 - 1/r`.
  set θ : ℝ := 1 - r⁻¹.toReal
  have hrinv : r⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (one_pos.trans_le hr).ne'
  have hr1 : r⁻¹.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact ENNReal.inv_le_one.2 hr)
  have hθ : θ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ENNReal.toReal_nonneg (a := r⁻¹)]⟩
  have hinterp := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (f := K) (μ := volume) (p₀ := 1)
    (p₁ := ⊤) (p := r) hθ (by
      rw [inv_one, mul_one, ENNReal.inv_top, mul_zero, add_zero, sub_sub_cancel,
        ENNReal.ofReal_toReal hrinv])
  calc eLpNorm K r volume ≤ eLpNorm K 1 volume ^ (1 - θ) * eLpNorm K ⊤ volume ^ θ := hinterp
    _ ≤ ENNReal.ofReal (A ^ k) ^ (1 - θ) * ENNReal.ofReal ((7 * R) ^ k) ^ θ := by
        gcongr
        linarith [hθ.2]
    _ = ENNReal.ofReal ((A ^ k) ^ (1 - θ) * ((7 * R) ^ k) ^ θ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith [hθ.2]),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ.1, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (max 1 A ^ k * 7 ^ k * R ^ ((k : ℝ) * θ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hAk : (A ^ k) ^ (1 - θ) ≤ max 1 A ^ k := by
          calc (A ^ k) ^ (1 - θ) ≤ (max 1 A ^ k) ^ (1 - θ) := by
                gcongr
                · linarith [hθ.2]
                · exact le_max_right _ _
            _ ≤ (max 1 A ^ k) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
                (one_le_pow₀ (le_max_left _ _)) (by linarith [hθ.1])
            _ = max 1 A ^ k := Real.rpow_one _
        have h7R : ((7 * R) ^ k) ^ θ ≤ 7 ^ k * R ^ ((k : ℝ) * θ) := by
          rw [mul_pow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast R,
            ← Real.rpow_mul hR0.le]
          gcongr
          calc ((7 : ℝ) ^ k) ^ θ ≤ ((7 : ℝ) ^ k) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hθ.2
            _ = 7 ^ k := Real.rpow_one _
        calc (A ^ k) ^ (1 - θ) * ((7 * R) ^ k) ^ θ ≤ max 1 A ^ k * (7 ^ k * R ^ ((k : ℝ) * θ)) :=
              mul_le_mul hAk h7R (by positivity) (by positivity)
          _ = _ := by ring

/-- The symbol `2πi ∑ i, n i * v i` of the derivative along `v`. -/
private noncomputable def derivSymbol (v : d → ℝ) (n : d → ℤ) : ℂ :=
  2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * v i

/-- The kernel of the derivative along `v` at scale `R`: the trigonometric polynomial with
coefficients `2πi ⟪n, v⟫ ∏ j, χ (n j / R)`. -/
private noncomputable def derivKernel [DecidableEq d] (v : d → ℝ) (R : ℝ) (x : UnitAddTorus d) :
    ℂ :=
  ∑ n ∈ box d R, (derivSymbol v n * ∏ j, cutoff (n j / R)) * mFourier n x

/-- The derivative kernel is a combination of tensor-product kernels, with the factor `ξ χ(ξ)` in
one coordinate and `χ` in the others. -/
private theorem derivKernel_eq_sum_tensorKernel [DecidableEq d] (v : d → ℝ) {R : ℝ} (hR : 0 < R)
    (x : UnitAddTorus d) :
    derivKernel v R x = ∑ i, (2 * Real.pi * Complex.I * R * v i) *
      tensorKernel (Function.update (fun _ ↦ cutoff) i derivCutoff) R x := by
  have hη (i : d) : ∀ j ξ, 2 < |ξ| →
      Function.update (fun _ : d ↦ cutoff) i derivCutoff j ξ = 0 := fun j ξ hξ ↦
    update_cutoff_derivCutoff (P := fun η ↦ η ξ = 0) (cutoff_eq_zero hξ) (derivCutoff_eq_zero hξ)
      i j
  simp only [fun i ↦ tensorKernel_eq_sum hR (hη i) x, Finset.mul_sum, derivKernel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [derivSymbol, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have herase : ∏ j ∈ Finset.univ.erase i,
      Function.update (fun _ ↦ cutoff) i derivCutoff j (n j / R) =
        ∏ j ∈ Finset.univ.erase i, cutoff (n j / R) :=
    Finset.prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j ↦ Function.update (fun _ ↦ cutoff) i derivCutoff j
      (n j / R)) (Finset.mem_univ i), Function.update_self, herase, derivCutoff]
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  field_simp

/-- The `L¹` norm of the derivative kernel along `v` at scale `R` is at most `C R ‖v‖`. -/
private theorem eLpNorm_derivKernel_le [DecidableEq d] (v : d → ℝ) {R : ℝ} (hR : 0 < R) :
    eLpNorm (derivKernel v R) 1 volume ≤ ENNReal.ofReal (2 * Real.pi * Fintype.card d *
      max (∫ y, ‖𝓕⁻ cutoff y‖) (∫ y, ‖𝓕⁻ derivCutoff y‖) ^ Fintype.card d * R * ‖v‖) := by
  set B := max (∫ y, ‖𝓕⁻ cutoff y‖) (∫ y, ‖𝓕⁻ derivCutoff y‖)
  set T : d → UnitAddTorus d → ℂ := fun i ↦
    tensorKernel (Function.update (fun _ ↦ cutoff) i derivCutoff) R
  have hcont (i : d) : Continuous (T i) := continuous_tensorKernel
    (update_cutoff_derivCutoff hasCompactSupport_cutoff hasCompactSupport_derivCutoff i) hR
  have hint (i : d) : Integrable (T i) :=
    (hcont i).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hT (i : d) : ∫ x, ‖T i x‖ ≤ B ^ Fintype.card d := by
    refine (integral_norm_tensorKernel_le
      (update_cutoff_derivCutoff contDiff_cutoff contDiff_derivCutoff i)
      (update_cutoff_derivCutoff hasCompactSupport_cutoff hasCompactSupport_derivCutoff i)
      hR).trans ?_
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun j _ ↦
      update_cutoff_derivCutoff (P := fun η ↦ ∫ y, ‖𝓕⁻ η y‖ ≤ B) (le_max_left _ _)
        (le_max_right _ _) i j
  have hK : derivKernel v R = fun x ↦ ∑ i, (2 * Real.pi * Complex.I * R * v i) * T i x :=
    funext (derivKernel_eq_sum_tensorKernel v hR)
  have hKint : Integrable (derivKernel v R) := by
    rw [hK]
    exact integrable_finsetSum _ fun i _ ↦ (hint i).const_mul _
  rw [eLpNorm_one_eq_lintegral_eNorm hKint.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_eNorm hKint]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ x, ‖derivKernel v R x‖
      ≤ ∫ x, ∑ i, 2 * Real.pi * R * ‖v‖ * ‖T i x‖ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
          (integrable_finsetSum _ fun i _ ↦ (hint i).norm.const_mul _) (ae_of_all _ fun x ↦ ?_)
        rw [hK]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        have hc : ‖(2 * Real.pi * Complex.I * R * v i : ℂ)‖ = 2 * Real.pi * R * ‖v i‖ := by
          simp [abs_of_pos hR, abs_of_pos Real.pi_pos]
        rw [norm_mul, hc]
        gcongr
        exact norm_le_pi_norm v i
    _ = ∑ i, 2 * Real.pi * R * ‖v‖ * ∫ x, ‖T i x‖ := by
        rw [integral_finsetSum _ fun i _ ↦ (hint i).norm.const_mul _]
        simp only [integral_const_mul]
    _ ≤ ∑ _i : d, 2 * Real.pi * R * ‖v‖ * B ^ Fintype.card d :=
        Finset.sum_le_sum fun i _ ↦ by gcongr; exact hT i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end UnitAddTorus

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

/-! ### Bernstein's inequalities -/

section Bernstein

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- **Reproducing formula.** Let `f` be integrable with spectrum in the ball `‖n‖ ≤ R`, and let
`g` be integrable with `ĝ = σ • f̂`. If the coefficients `c` of a trigonometric polynomial on the
box `box d R` agree with `σ` on that ball, then `g` is the convolution of that polynomial with
`f`. -/
private theorem ae_eq_convolution_of_mFourierCoeff_eq_smul [DecidableEq d] {R : ℝ} (hR : 0 < R)
    {f g : UnitAddTorus d → E} (hf : Integrable f) (hg : Integrable g)
    (hspec : ∀ n, R < ‖n‖ → mFourierCoeff f n = 0) {σ c : (d → ℤ) → ℂ}
    (hc : ∀ n, ‖n‖ ≤ R → c n = σ n) (hfg : ∀ n, mFourierCoeff g n = σ n • mFourierCoeff f n) :
    g =ᵐ[volume]
      (fun t ↦ ∑ n ∈ box d R, c n * mFourier n t) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f := by
  have hfS (n : d → ℤ) (hn : n ∉ box d R) : mFourierCoeff f n = 0 :=
    hspec n (lt_norm_of_notMem_box hR hn)
  have hgS (n : d → ℤ) (hn : n ∉ box d R) : mFourierCoeff g n = 0 := by
    rw [hfg, hfS n hn, smul_zero]
  filter_upwards [hg.ae_eq_sum_mFourier_smul_mFourierCoeff hgS] with x hx
  rw [hx, convolution_sum_smul_mFourier_apply hf]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hn : ‖n‖ ≤ R
  · rw [hc n hn, hfg, smul_comm]
  · rw [hfg, hspec n (not_le.1 hn), smul_zero, smul_zero, smul_zero]

/-- **Nikol'skii's inequality on the torus**, Bernstein's inequality without derivatives: for
`1 ≤ p ≤ q ≤ ∞` there is `C` such that every integrable `f` on `(ℝ / ℤ)^d` whose Fourier
coefficients vanish outside the ball `‖n‖ ≤ R`, `R ≥ 1`, satisfies
`‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`. Here `‖n‖` is the supremum norm of `n : d → ℤ`. -/
theorem exists_eLpNorm_le_of_mFourierCoeff_eq_zero {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 1 ≤ R → ∀ {f : UnitAddTorus d → E}, Integrable f →
      (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      eLpNorm f q volume ≤ ENNReal.ofReal (C * R ^ ((Fintype.card d : ℝ) *
        (p.toReal⁻¹ - q.toReal⁻¹))) * eLpNorm f p volume := by
  classical
  -- The exponent `r` of Young's inequality, with `1/r + 1/p = 1 + 1/q`.
  set r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hqp : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hp1 : p⁻¹ ≤ 1 + q⁻¹ := (ENNReal.inv_le_one.2 hp).trans le_self_add
  have hq1 : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (one_pos.trans_le (hp.trans hpq)).ne'
  have hr : 1 ≤ r := ENNReal.one_le_inv.2 (tsub_le_iff_right.2 (by gcongr))
  have hrpq : r⁻¹ + p⁻¹ = 1 + q⁻¹ := by rw [inv_inv, tsub_add_cancel_of_le hp1]
  have hrexp : 1 - r⁻¹.toReal = p.toReal⁻¹ - q.toReal⁻¹ := by
    rw [inv_inv, ENNReal.toReal_sub_of_le hp1 (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hq1⟩),
      ENNReal.toReal_add ENNReal.one_ne_top hq1, ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_one]
    ring
  refine ⟨max 1 (∫ y, ‖𝓕⁻ cutoff y‖) ^ Fintype.card d * 7 ^ Fintype.card d, by positivity,
    fun {R} hR {f} hf hspec ↦ ?_⟩
  have hR0 : 0 < R := one_pos.trans_le hR
  set K := tensorKernel (fun _ : d ↦ cutoff) R
  have hK : Continuous K := continuous_tensorKernel (fun _ ↦ hasCompactSupport_cutoff) hR0
  have hae : f =ᵐ[volume] K ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f := by
    rw [show K = fun t ↦ ∑ n ∈ box d R, (∏ i, cutoff (n i / R)) * mFourier n t from
      funext (tensorKernel_cutoff_eq_sum hR0)]
    exact ae_eq_convolution_of_mFourierCoeff_eq_smul hR0 hf hf hspec (σ := 1)
      (fun n hn ↦ prod_cutoff_eq_one hR0 hn) fun n ↦ by rw [Pi.one_apply, one_smul]
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (K ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) q volume
      ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ₑ * eLpNorm K r volume *
          eLpNorm f p volume :=
        eLpNorm_convolution_le_of_inv_add_inv_eq _ hr hp hrpq hK.aestronglyMeasurable
          hf.aestronglyMeasurable
    _ ≤ 1 * ENNReal.ofReal (max 1 (∫ y, ‖𝓕⁻ cutoff y‖) ^ Fintype.card d *
          7 ^ Fintype.card d * R ^ ((Fintype.card d : ℝ) * (1 - r⁻¹.toReal))) *
          eLpNorm f p volume := by
        gcongr
        · exact ContinuousLinearMap.opENorm_lsmul_le
        · exact eLpNorm_tensorKernel_cutoff_le hR hr
    _ = _ := by rw [one_mul, hrexp]

/-- **Bernstein's inequality for one derivative at a fixed exponent.** If the Fourier
coefficients of `f` vanish outside the ball `‖n‖ ≤ R` and those of `g` are
`2πi ⟪n, v⟫ f̂(n)`, so that `g` is the derivative of `f` along `v`, then
`‖g‖_p ≤ C R ‖v‖ ‖f‖_p`. -/
private theorem exists_eLpNorm_le_of_mFourierCoeff_eq_derivSymbol_smul {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : d → ℝ) {R : ℝ}, 0 < R → ∀ {f g : UnitAddTorus d → E},
      Integrable f → Integrable g → (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n = derivSymbol v n • mFourierCoeff f n) →
      eLpNorm g p volume ≤ ENNReal.ofReal (C * R * ‖v‖) * eLpNorm f p volume := by
  classical
  refine ⟨2 * Real.pi * Fintype.card d *
      max (∫ y, ‖𝓕⁻ cutoff y‖) (∫ y, ‖𝓕⁻ derivCutoff y‖) ^ Fintype.card d,
    by positivity, fun v {R} hR {f g} hf hg hspec hfg ↦ ?_⟩
  have hK : Continuous (derivKernel v R) := by
    unfold derivKernel
    fun_prop
  have hae : g =ᵐ[volume] derivKernel v R ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f :=
    ae_eq_convolution_of_mFourierCoeff_eq_smul hR hf hg hspec
      (fun n hn ↦ by rw [prod_cutoff_eq_one hR hn, mul_one]) hfg
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (derivKernel v R ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) p volume
      ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ₑ *
          eLpNorm (derivKernel v R) 1 volume * eLpNorm f p volume :=
        eLpNorm_convolution_le _ hK.aestronglyMeasurable hf.aestronglyMeasurable hp
    _ ≤ 1 * ENNReal.ofReal (2 * Real.pi * Fintype.card d *
          max (∫ y, ‖𝓕⁻ cutoff y‖) (∫ y, ‖𝓕⁻ derivCutoff y‖) ^ Fintype.card d * R * ‖v‖) *
          eLpNorm f p volume := by
        gcongr
        · exact ContinuousLinearMap.opENorm_lsmul_le
        · exact eLpNorm_derivKernel_le v hR
    _ = _ := by rw [one_mul]

/-- **Bernstein's inequality for `k` derivatives at a fixed exponent**, by iterating the case of
one derivative through the intermediate trigonometric polynomials. -/
private theorem exists_eLpNorm_le_of_mFourierCoeff_eq_prod_derivSymbol_smul {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (v : Fin k → d → ℝ) {R : ℝ}, 0 < R →
      ∀ {f g : UnitAddTorus d → E}, Integrable f → Integrable g →
      (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n = (∏ l, derivSymbol (v l) n) • mFourierCoeff f n) →
      eLpNorm g p volume ≤ ENNReal.ofReal ((C * R) ^ k * ∏ l, ‖v l‖) * eLpNorm f p volume := by
  classical
  obtain ⟨C, hC, hderiv⟩ :=
    exists_eLpNorm_le_of_mFourierCoeff_eq_derivSymbol_smul (d := d) (E := E) hp
  refine ⟨C, hC, fun k ↦ ?_⟩
  induction k with
  | zero =>
    intro v R _ f g hf hg _ hfg
    have hae : g =ᵐ[volume] f := hg.ae_eq_of_forall_mFourierCoeff_eq hf fun n ↦ by
      rw [hfg, Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [eLpNorm_congr_ae hae, pow_zero, one_mul, Finset.univ_eq_empty, Finset.prod_empty,
      ENNReal.ofReal_one, one_mul]
  | succ k ih =>
    intro v R hR f g hf hg hspec hfg
    -- The intermediate trigonometric polynomial carrying the first `k` derivatives.
    set c : (d → ℤ) → E := fun n ↦ (∏ l : Fin k, derivSymbol (v l.castSucc) n) • mFourierCoeff f n
    have hcdef (n : d → ℤ) :
        c n = (∏ l : Fin k, derivSymbol (v l.castSucc) n) • mFourierCoeff f n := rfl
    set h : UnitAddTorus d → E := fun x ↦ ∑ n ∈ box d R, mFourier n x • c n
    have hhint : Integrable h := (by fun_prop : Continuous h).integrable_of_hasCompactSupport
      (.of_compactSpace _)
    have hhc (n : d → ℤ) : mFourierCoeff h n = c n := by
      rw [mFourierCoeff_sum_mFourier_smul]
      split_ifs with hn
      · rfl
      · rw [hcdef, hspec n (lt_norm_of_notMem_box hR hn), smul_zero]
    have hhspec (n : d → ℤ) (hn : R < ‖n‖) : mFourierCoeff h n = 0 := by
      rw [hhc, hcdef, hspec n hn, smul_zero]
    have hgh (n : d → ℤ) :
        mFourierCoeff g n = derivSymbol (v (Fin.last k)) n • mFourierCoeff h n := by
      rw [hfg, hhc, hcdef, Fin.prod_univ_castSucc, mul_comm, mul_smul]
    calc eLpNorm g p volume
        ≤ ENNReal.ofReal (C * R * ‖v (Fin.last k)‖) * eLpNorm h p volume :=
          hderiv _ hR hhint hg hhspec hgh
      _ ≤ ENNReal.ofReal (C * R * ‖v (Fin.last k)‖) *
            (ENNReal.ofReal ((C * R) ^ k * ∏ l : Fin k, ‖v l.castSucc‖) * eLpNorm f p volume) := by
          gcongr
          exact ih (fun l ↦ v l.castSucc) hR hf hhint hspec fun n ↦ hhc n
      _ = ENNReal.ofReal ((C * R) ^ (k + 1) * ∏ l, ‖v l‖) * eLpNorm f p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Fin.prod_univ_castSucc]
          congr 2
          ring

/-- **Bernstein's inequalities on the torus.** For `1 ≤ p ≤ q ≤ ∞` there is `C` with the following
property. Let `f` be integrable on `(ℝ / ℤ)^d` with Fourier coefficients vanishing outside the ball
`‖n‖ ≤ R`, `R ≥ 1`, and let `g` be integrable with Fourier coefficients
`(∏ l, 2πi ⟪n, v l⟫) f̂(n)`, so that `g` is the derivative of `f` along `v 0, …, v (k - 1)`. Then

`‖g‖_q ≤ C ^ (k + 1) R ^ (k + d (1/p - 1/q)) ∏ l, ‖v l‖ ‖f‖_p`.

Here `‖n‖` and `‖v l‖` are supremum norms. When the lift of `f` to `d → ℝ` is `Cᵏ`, the hypothesis
on `g` holds for its `k`-th derivative along `v`, by
`TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv`. -/
theorem exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (v : Fin k → d → ℝ) {R : ℝ}, 1 ≤ R →
      ∀ {f g : UnitAddTorus d → E}, Integrable f → Integrable g →
      (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n =
        (∏ l, 2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * v l i) • mFourierCoeff f n) →
      eLpNorm g q volume ≤ ENNReal.ofReal (C ^ (k + 1) *
        R ^ ((k : ℝ) + Fintype.card d * (p.toReal⁻¹ - q.toReal⁻¹)) * ∏ l, ‖v l‖) *
          eLpNorm f p volume := by
  obtain ⟨C₀, hC₀, hnik⟩ := exists_eLpNorm_le_of_mFourierCoeff_eq_zero (d := d) (E := E) hp hpq
  obtain ⟨C₁, hC₁, hder⟩ :=
    exists_eLpNorm_le_of_mFourierCoeff_eq_prod_derivSymbol_smul (d := d) (E := E) hp
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun k v {R} hR {f g} hf hg hspec hfg ↦ ?_⟩
  have hR0 : 0 < R := one_pos.trans_le hR
  have hgspec (n : d → ℤ) (hn : R < ‖n‖) : mFourierCoeff g n = 0 := by
    rw [hfg, hspec n hn, smul_zero]
  set θ : ℝ := Fintype.card d * (p.toReal⁻¹ - q.toReal⁻¹)
  calc eLpNorm g q volume ≤ ENNReal.ofReal (C₀ * R ^ θ) * eLpNorm g p volume := hnik hR hg hgspec
    _ ≤ ENNReal.ofReal (C₀ * R ^ θ) *
          (ENNReal.ofReal ((C₁ * R) ^ k * ∏ l, ‖v l‖) * eLpNorm f p volume) := by
        gcongr
        exact hder k v hR0 hf hg hspec hfg
    _ = ENNReal.ofReal (C₀ * C₁ ^ k * R ^ ((k : ℝ) + θ) * ∏ l, ‖v l‖) * eLpNorm f p volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Real.rpow_add hR0,
          Real.rpow_natCast]
        congr 2
        ring
    _ ≤ _ := by
        gcongr
        rw [pow_succ']
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _

end Bernstein

end TauCeti.UnitAddTorus
