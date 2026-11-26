/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.Bernstein
import TauCeti.Analysis.Distribution.SchwartzSpace.Dilation
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Convolution
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Fourier.Torus.SchwartzMultiplier
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Bernstein's inequalities on the torus

On the torus `𝕋ᵈ = (ℝ / ℤ)^d` with its volume, the product of the Haar probability measures of
the circle factors, let `f` be an integrable function whose Fourier coefficients vanish outside the
ball `‖n‖ ≤ R`, `R ≥ 1`, for the supremum norm on `d → ℤ`: almost everywhere, a trigonometric
polynomial of degree at most `R` in each variable. **Bernstein's inequalities** say that there is
`C`, depending only on `d` (the same for every complex Banach space of values), such that for
`1 ≤ p ≤ q ≤ ∞`

`‖∂_{v 0} ⋯ ∂_{v (k - 1)} f‖_q ≤ C ^ (k + 1) R ^ (k + d (1/p - 1/q)) ∏ l, ‖v l‖ ‖f‖_p`

(`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`). The derivative is
described on the Fourier side: when `g` is integrable and `ĝ(n) = (∏ l, 2πi ⟪n, v l⟫) f̂(n)`,
the function `g` agrees almost everywhere with the derivative along `v 0, …, v (k - 1)` of the
trigonometric polynomial that represents `f` almost everywhere. This hypothesis is what
`TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv` provides for the derivatives of
the lift of a smooth function. The case `k = 0` is **Nikol'skii's inequality**
`‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`, the gain of integrability of a trigonometric polynomial
(`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm`).

These are the periodic counterparts of the whole-space inequalities
`TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`: a block of a
periodic Littlewood–Paley decomposition with frequencies of size `2 ^ j` behaves like a function at
the single scale `2 ^ (-j)`, so that each derivative costs a factor `2 ^ j` and passing from `Lᵖ`
to `L^q` costs `2 ^ (j d (1/p - 1/q))`.

Conversely, on an annulus the derivatives control the function. The **reverse Bernstein
inequality** says that there is `C`, depending only on `d` and `θ`, such that for `1 ≤ p ≤ ∞`
every integrable `f` with Fourier coefficients vanishing outside the annulus `R ≤ ‖n‖ ≤ θ R`,
`R > 0`, for the Euclidean norm of `n`, satisfies

`‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖∂ᵢ f‖_p`

(`TauCeti.UnitAddTorus.exists_eLpNorm_le_div_mul_sum_eLpNorm_of_mFourierCoeff_eq`), where `∂ᵢ f`
is any integrable function with Fourier coefficients `2πi nᵢ f̂(n)`. Its whole-space
counterpart is `OrthonormalBasis.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq`.

## The argument

The proof follows the whole-space one, convolution with a reproducing kernel, with Poisson
summation to control the periodic kernel. Let `χ` be a smooth cutoff equal to one on `[-1, 1]` and
supported in `(-2, 2)`. The kernel of de la Vallée Poussin type
`V_R(x) = ∑ n, (∏ i, χ (n i / R)) e_n(x)` is a trigonometric polynomial whose coefficients equal one
on the ball `‖n‖ ≤ R`, so `V_R ⋆ f = f` almost everywhere
(`MeasureTheory.Integrable.ae_eq_convolution_of_mFourierCoeff_eq_smul`). Its coefficients are the
values at the points `n / R` of the symbol `τ(ξ) = ∏ i, χ (ξ i)` on `ℝᵈ`. By Poisson summation
`V_R` is the periodization of the kernel `𝓕⁻ (τ (· / R))` on `ℝᵈ`, a dilate of `𝓕⁻ τ`, so its `L¹`
norm on the torus is at most `∫ ‖𝓕⁻ τ‖` for every `R > 0`
(`SchwartzMap.lintegral_eNorm_tsum_fourier_mul_mFourier_le`). Hence `V_R` is bounded in `L¹`
uniformly in `R > 0`, while `‖V_R‖_∞ ≤ (7 R) ^ d` by counting its frequencies, and the logarithmic
convexity of `Lʳ` norms (`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`) gives
`‖V_R‖_r ≤ C R ^ (d (1 - 1/r))` for `1 ≤ r ≤ ∞`. Young's inequality with `1/r + 1/p = 1 + 1/q`
(`MeasureTheory.eLpNorm_convolution_le_of_inv_add_inv_eq`) gives Nikol'skii's inequality.

For a derivative along `v`, the symbol `2πi ⟪n, v⟫ ∏ j, χ (n j / R)` is the combination
`∑ i, 2πi R v i τᵢ (n / R)` of the symbols `τᵢ(ξ) = ξ i ∏ j, χ (ξ j)`. Its kernel therefore has
`L¹` norm at most a constant times `R ‖v‖`, and Young's inequality for an integrable kernel bounds
one derivative at a fixed exponent. Derivatives of higher order follow by iteration through
intermediate trigonometric polynomials, and the gain of integrability is applied last.

For the reverse inequality, there are Schwartz symbols `σᵢ` on `ℝᵈ` with `∑ i, σᵢ(ξ) 2πi ξ i = 1`
on the annulus `1 ≤ ‖ξ‖ ≤ θ` (`OrthonormalBasis.exists_sum_mul_eq_one_of_one_le_norm_of_norm_le`,
whose symbols are built from `ξ i / (2πi ‖ξ‖²)`). Hence
`f = R⁻¹ ∑ᵢ Kᵢ ⋆ ∂ᵢ f` for the periodic kernels `Kᵢ` of the dilated symbols `σᵢ (· / R)`, and
Young's inequality for these kernels (`SchwartzMap.eLpNorm_periodicKernel_convolution_le`) bounds
each term by `∫ ‖𝓕⁻ σᵢ‖`, for every `R > 0`. This is the periodic counterpart of the whole-space
proof in `TauCeti/Analysis/Distribution/SchwartzSpace/Bernstein.lean`
(`SchwartzMap.exists_eLpNorm_le_eLpNorm_iteratedFDeriv_of_support_fourier_subset`), with the same
symbols. The reverse Bernstein inequality for `Lᵖ` functions on a Euclidean space,
`OrthonormalBasis.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq`, is proved through tempered
distributions with different, explicitly cut off symbols.

## Main declarations

* `TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm`: Nikol'skii's
  inequality.
* `TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`: Bernstein's
  inequalities for derivatives of every order.
* `TauCeti.UnitAddTorus.exists_eLpNorm_le_div_mul_sum_eLpNorm_of_mFourierCoeff_eq`: the reverse
  Bernstein inequality on an annulus.

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
open scoped ENNReal NNReal ContDiff Convolution SchwartzMap

/-! The kernels below take a point of the torus as an explicit argument, so they live in the
root `UnitAddTorus` namespace. -/

namespace UnitAddTorus

open TauCeti TauCeti.UnitAddTorus

/-! ### Kernels with frequencies in a box -/

section Box

variable {d : Type*} [Fintype d]

/-- The box `‖n‖ ≤ ⌈2 R⌉` of frequencies carrying the kernels at scale `R`. -/
private noncomputable def box (d : Type*) [Fintype d] [DecidableEq d] (R : ℝ) :
    Finset (d → ℤ) :=
  Fintype.piFinset fun _ : d ↦ Finset.Icc (-⌈2 * R⌉) ⌈2 * R⌉

private theorem exists_lt_abs_of_notMem_box [DecidableEq d] {n : d → ℤ} {R : ℝ}
    (hn : n ∉ box d R) : ∃ i, 2 * R < |(n i : ℝ)| := by
  simp only [box, Fintype.mem_piFinset, not_forall] at hn
  obtain ⟨i, hi⟩ := hn
  rw [Finset.mem_Icc, ← abs_le, not_le] at hi
  have h : (⌈2 * R⌉ : ℝ) < |(n i : ℝ)| := by exact_mod_cast hi
  exact ⟨i, (Int.le_ceil _).trans_lt h⟩

private theorem lt_norm_of_notMem_box [DecidableEq d] {R : ℝ} (hR : 0 < R) {n : d → ℤ}
    (hn : n ∉ box d R) :
    R < ‖n‖ := by
  obtain ⟨i, hi⟩ := exists_lt_abs_of_notMem_box hn
  calc R < |(n i : ℝ)| := by linarith
    _ = ‖n i‖ := (Int.norm_eq_abs _).symm
    _ ≤ ‖n‖ := norm_le_pi_norm n i

/-- The box `box d R`, `R ≥ 1`, has at most `(7 R) ^ d` points. -/
private theorem card_box_le [DecidableEq d] {R : ℝ} (hR : 1 ≤ R) :
    ((box d R).card : ℝ) ≤ (7 * R) ^ Fintype.card d := by
  rw [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  gcongr
  rw [Int.card_Icc]
  have hceil : (⌈2 * R⌉ : ℝ) < 2 * R + 1 := Int.ceil_lt_add_one _
  have hnn : (0 : ℤ) ≤ ⌈2 * R⌉ + 1 - -⌈2 * R⌉ := by
    have : (0 : ℤ) ≤ ⌈2 * R⌉ := Int.ceil_nonneg (by linarith)
    omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  push_cast
  linarith

/-- **The `L¹` norm of a kernel with a dilated symbol.** Let `τ` be a smooth symbol on `ℝᵈ`
vanishing wherever one coordinate exceeds `2` in absolute value. By Poisson summation the
trigonometric polynomial `x ↦ ∑ n, τ (n / R) e_n(x)` is the periodization of the kernel
`𝓕⁻ (τ (· / R))` on `ℝᵈ`, a dilate of `𝓕⁻ τ`, so its `L¹` norm on the torus is at most
`∫ ‖𝓕⁻ τ‖`, uniformly over the scales `R > 0` (`SchwartzMap.eLpNorm_periodicKernel_le`). -/
private theorem eLpNorm_sum_box_le [DecidableEq d] {τ : EuclideanSpace ℝ d → ℂ}
    (hτ : ContDiff ℝ ∞ τ) (h0 : ∀ (ξ : EuclideanSpace ℝ d) i, 2 < |ξ i| → τ ξ = 0) {R : ℝ}
    (hR : 0 < R) :
    eLpNorm (fun x ↦ ∑ n ∈ box d R, τ (R⁻¹ • latticePoint n) * mFourier n x) 1 volume ≤
      ENNReal.ofReal (∫ y, ‖𝓕⁻ τ y‖) := by
  -- The dilated symbol `τ (· / R)` as a Schwartz function.
  have hcR : HasCompactSupport fun ξ : EuclideanSpace ℝ d ↦ τ (R⁻¹ • ξ) :=
    (hasCompactSupport_of_eq_zero_of_notMem_coordinate_Icc (fun _ ↦ -2)
      (fun _ ↦ 2) fun ξ i hi ↦ h0 ξ i (not_le.1 fun h ↦ hi (abs_le.1 h))).comp_smul
        (inv_ne_zero hR.ne')
  have hsR : ContDiff ℝ ∞ fun ξ : EuclideanSpace ℝ d ↦ τ (R⁻¹ • ξ) :=
    hτ.comp (contDiff_const_smul _)
  set S : SchwartzMap (EuclideanSpace ℝ d) ℂ := hcR.toSchwartzMap hsR
  have hS (ξ : EuclideanSpace ℝ d) : S ξ = τ (R⁻¹ • ξ) :=
    HasCompactSupport.toSchwartzMap_toFun _ _ _
  -- The periodic kernel of `S` is the trigonometric polynomial on the box.
  have hsum (x : UnitAddTorus d) : ∑' n : d → ℤ, S (latticePoint n) * mFourier n x =
      ∑ n ∈ box d R, τ (R⁻¹ • latticePoint n) * mFourier n x := by
    simp only [hS]
    refine tsum_eq_sum fun n hn ↦ ?_
    obtain ⟨i, hi⟩ := exists_lt_abs_of_notMem_box hn
    rw [h0 _ i ?_, zero_mul]
    rw [PiLp.smul_apply, latticePoint_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hR,
      lt_inv_mul_iff₀ hR]
    linarith
  have hFS : ∫ y, ‖𝓕⁻ (S : EuclideanSpace ℝ d → ℂ) y‖ = ∫ y, ‖𝓕⁻ τ y‖ := by
    rw [show (S : EuclideanSpace ℝ d → ℂ) = fun ξ ↦ τ (R⁻¹ • ξ) from funext hS]
    exact integral_norm_fourierInv_comp_smul τ (inv_ne_zero hR.ne')
  have hK : ⇑S.periodicKernel = fun x ↦ ∑ n ∈ box d R, τ (R⁻¹ • latticePoint n) * mFourier n x :=
    funext fun x ↦ by rw [SchwartzMap.periodicKernel_apply, hsum]
  have h := S.eLpNorm_periodicKernel_le
  rwa [hK, hFS] at h

end Box

/-! ### The cutoff and its kernels -/

/-- The bump function equal to one on `[-1, 1]` and supported in `(-2, 2)`. -/
private noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- A smooth cutoff `ℝ → ℂ`, equal to one on `[-1, 1]` and to zero outside `(-2, 2)`. -/
private noncomputable def cutoff (ξ : ℝ) : ℂ := (bump ξ : ℂ)

private theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

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

variable {d : Type*} [Fintype d]

/-- The symbol `∏ i, χ (ξ i)` of the reproducing kernels. -/
private noncomputable def cutoffSymbol (ξ : EuclideanSpace ℝ d) : ℂ := ∏ i, cutoff (ξ i)

private theorem contDiff_cutoffSymbol : ContDiff ℝ ∞ (cutoffSymbol (d := d)) :=
  contDiff_prod fun _ _ ↦ contDiff_cutoff.comp (contDiff_piLp_apply 2)

private theorem cutoffSymbol_eq_zero (ξ : EuclideanSpace ℝ d) (i : d) (hξ : 2 < |ξ i|) :
    cutoffSymbol ξ = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (cutoff_eq_zero hξ)

private theorem norm_cutoffSymbol_le (ξ : EuclideanSpace ℝ d) : ‖cutoffSymbol ξ‖ ≤ 1 := by
  rw [cutoffSymbol, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ norm_cutoff_le _

private theorem cutoffSymbol_eq_one {R : ℝ} (hR : 0 < R) {n : d → ℤ} (hn : ‖n‖ ≤ R) :
    cutoffSymbol (R⁻¹ • latticePoint n) = 1 := by
  refine Finset.prod_eq_one fun i _ ↦ cutoff_eq_one ?_
  rw [PiLp.smul_apply, latticePoint_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hR,
    inv_mul_le_one₀ hR, ← Int.norm_eq_abs]
  exact (norm_le_pi_norm n i).trans hn

/-- The symbol `ξ i ∏ j, χ (ξ j)` of the derivative kernels. -/
private noncomputable def derivCutoffSymbol (i : d) (ξ : EuclideanSpace ℝ d) : ℂ :=
  ξ i * cutoffSymbol ξ

private theorem contDiff_derivCutoffSymbol (i : d) : ContDiff ℝ ∞ (derivCutoffSymbol i) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2)).mul contDiff_cutoffSymbol

private theorem derivCutoffSymbol_eq_zero (i : d) (ξ : EuclideanSpace ℝ d) (j : d)
    (hξ : 2 < |ξ j|) : derivCutoffSymbol i ξ = 0 := by
  rw [derivCutoffSymbol, cutoffSymbol_eq_zero ξ j hξ, mul_zero]

/-- The reproducing kernel at scale `R`, the trigonometric polynomial with coefficients
`∏ i, χ (n i / R)`. -/
private noncomputable def cutoffKernel [DecidableEq d] (R : ℝ) (x : UnitAddTorus d) : ℂ :=
  ∑ n ∈ box d R, cutoffSymbol (R⁻¹ • latticePoint n) * mFourier n x

private theorem continuous_cutoffKernel [DecidableEq d] (R : ℝ) :
    Continuous (cutoffKernel (d := d) R) := by
  unfold cutoffKernel
  fun_prop

/-- The reproducing kernel at scale `R ≥ 1` is bounded by `(7 R) ^ d`. -/
private theorem norm_cutoffKernel_le [DecidableEq d] {R : ℝ} (hR : 1 ≤ R) (x : UnitAddTorus d) :
    ‖cutoffKernel R x‖ ≤ (7 * R) ^ Fintype.card d := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun n _ ↦ ?_).trans ?_)
  · rw [norm_mul, norm_mFourier_apply, mul_one]
    exact norm_cutoffSymbol_le _
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_box_le hR

/-- The real-arithmetic step of the interpolation below: for `0 ≤ θ ≤ 1`,
`A ^ (1 - θ) ((7 R) ^ k) ^ θ ≤ max 1 A 7 ^ k R ^ (k θ)`. -/
private theorem rpow_one_sub_mul_rpow_le {A R θ : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    A ^ (1 - θ) * ((7 * R) ^ k) ^ θ ≤ max 1 A * 7 ^ k * R ^ ((k : ℝ) * θ) := by
  have hAk : A ^ (1 - θ) ≤ max 1 A := by
    calc A ^ (1 - θ) ≤ (max 1 A) ^ (1 - θ) := by
          gcongr
          · linarith [hθ.2]
          · exact le_max_right _ _
      _ ≤ max 1 A := Real.rpow_le_self_of_one_le (le_max_left _ _) (by linarith [hθ.1])
  have h7R : ((7 * R) ^ k) ^ θ ≤ 7 ^ k * R ^ ((k : ℝ) * θ) := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast R,
      ← Real.rpow_mul hR]
    gcongr
    exact Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hθ.2
  rw [mul_assoc]
  exact mul_le_mul hAk h7R (by positivity) (by positivity)

/-- For `1 ≤ r ≤ ∞`, the `Lʳ` norm of the reproducing kernel at scale `R ≥ 1` is
`O(R ^ (d (1 - 1/r)))`, by interpolation between its `L¹` bound, uniform in `R`, and its supremum
bound `(7 R) ^ d`. -/
private theorem eLpNorm_cutoffKernel_le [DecidableEq d] {R : ℝ} (hR : 1 ≤ R) {r : ℝ≥0∞}
    (hr : 1 ≤ r) :
    eLpNorm (cutoffKernel (d := d) R) r volume ≤
      ENNReal.ofReal (max 1 (∫ y, ‖𝓕⁻ (cutoffSymbol (d := d)) y‖) * 7 ^ Fintype.card d *
        R ^ ((Fintype.card d : ℝ) * (1 - r⁻¹.toReal))) := by
  have hR0 : 0 < R := one_pos.trans_le hR
  set K := cutoffKernel (d := d) R
  set A := ∫ y, ‖𝓕⁻ (cutoffSymbol (d := d)) y‖
  set k := Fintype.card d
  have hK : Continuous K := continuous_cutoffKernel R
  -- The two endpoint bounds.
  have h1 : eLpNorm K 1 volume ≤ ENNReal.ofReal A :=
    eLpNorm_sum_box_le contDiff_cutoffSymbol cutoffSymbol_eq_zero hR0
  have hinf : eLpNorm K ⊤ volume ≤ ENNReal.ofReal ((7 * R) ^ k) := by
    rw [eLpNorm_exponent_top hK.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun x ↦ ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_cutoffKernel_le hR x)
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
    _ ≤ ENNReal.ofReal A ^ (1 - θ) * ENNReal.ofReal ((7 * R) ^ k) ^ θ := by
        gcongr
        linarith [hθ.2]
    _ = ENNReal.ofReal (A ^ (1 - θ) * ((7 * R) ^ k) ^ θ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
            (by linarith [hθ.2]),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ.1, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (max 1 A * 7 ^ k * R ^ ((k : ℝ) * θ)) :=
        ENNReal.ofReal_le_ofReal (rpow_one_sub_mul_rpow_le (integral_nonneg fun _ ↦ norm_nonneg _)
          hR0.le hθ k)

/-- The symbol `2πi ∑ i, n i * v i` of the derivative along `v`. -/
private noncomputable def derivSymbol (v : d → ℝ) (n : d → ℤ) : ℂ :=
  2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * v i

/-- The kernel of the derivative along `v` at scale `R`: the trigonometric polynomial with
coefficients `2πi ⟪n, v⟫ ∏ j, χ (n j / R)`. -/
private noncomputable def derivKernel [DecidableEq d] (v : d → ℝ) (R : ℝ) (x : UnitAddTorus d) :
    ℂ :=
  ∑ n ∈ box d R, (derivSymbol v n * cutoffSymbol (R⁻¹ • latticePoint n)) * mFourier n x

/-- The derivative kernel is the combination `∑ i, 2πi R v i K_i` of the kernels `K_i` with the
symbols `ξ i ∏ j, χ (ξ j)` dilated by `R`. -/
private theorem derivKernel_eq_sum [DecidableEq d] (v : d → ℝ) {R : ℝ} (hR : 0 < R)
    (x : UnitAddTorus d) :
    derivKernel v R x = ∑ i, (2 * Real.pi * Complex.I * R * v i) *
      ∑ n ∈ box d R, derivCutoffSymbol i (R⁻¹ • latticePoint n) * mFourier n x := by
  simp only [Finset.mul_sum, derivKernel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [derivSymbol, derivCutoffSymbol, PiLp.smul_apply, latticePoint_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  field_simp

/-- The `L¹` norm of the derivative kernel along `v` at a scale `R > 0` is at most `C R ‖v‖`,
with `C` depending only on `d`. -/
private theorem eLpNorm_derivKernel_le [DecidableEq d] (v : d → ℝ) {R : ℝ} (hR : 0 < R) :
    eLpNorm (derivKernel v R) 1 volume ≤ ENNReal.ofReal (2 * Real.pi *
      (∑ i : d, ∫ y, ‖𝓕⁻ (derivCutoffSymbol i) y‖) * R * ‖v‖) := by
  set T : d → UnitAddTorus d → ℂ := fun i x ↦
    ∑ n ∈ box d R, derivCutoffSymbol i (R⁻¹ • latticePoint n) * mFourier n x
  have hT (i : d) :
      eLpNorm (T i) 1 volume ≤ ENNReal.ofReal (∫ y, ‖𝓕⁻ (derivCutoffSymbol i) y‖) :=
    eLpNorm_sum_box_le (contDiff_derivCutoffSymbol i) (derivCutoffSymbol_eq_zero i) hR
  have hK : derivKernel v R = ∑ i, (2 * Real.pi * Complex.I * R * v i) • T i := by
    ext x
    simp only [derivKernel_eq_sum v hR, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, T]
  rw [hK]
  refine (eLpNorm_sum_le le_rfl).trans ?_
  simp only [eLpNorm_const_smul]
  calc ∑ i, ‖(2 * Real.pi * Complex.I * R * v i : ℂ)‖ₑ * eLpNorm (T i) 1 volume
      ≤ ∑ i : d, ENNReal.ofReal (2 * Real.pi * R * ‖v‖ * ∫ y, ‖𝓕⁻ (derivCutoffSymbol i) y‖) :=
        Finset.sum_le_sum fun i _ ↦ by
          have hc : ‖(2 * Real.pi * Complex.I * R * v i : ℂ)‖ = 2 * Real.pi * R * ‖v i‖ := by
            simp [abs_of_pos hR, abs_of_pos Real.pi_pos]
          rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm, hc]
          gcongr
          · exact norm_le_pi_norm v i
          · exact hT i
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦
          mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _)]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

end UnitAddTorus

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

/-! ### Bernstein's inequalities -/

section Bernstein

universe u

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- **Reproducing formula.** Let `f` be integrable with spectrum in the ball `‖n‖ ≤ R`, and let
`g` be integrable with `ĝ = σ • f̂`. If the coefficients `c` of a trigonometric polynomial on the
box `box d R` agree with `σ` on that ball, then `g` agrees almost everywhere with the convolution
of that polynomial with `f`. -/
private theorem ae_eq_convolution_of_mFourierCoeff_eq_smul [DecidableEq d] {R : ℝ} (hR : 0 < R)
    {f g : UnitAddTorus d → E} (hf : Integrable f) (hg : Integrable g)
    (hspec : ∀ n, R < ‖n‖ → mFourierCoeff f n = 0) {σ c : (d → ℤ) → ℂ}
    (hc : ∀ n, ‖n‖ ≤ R → c n = σ n) (hfg : ∀ n, mFourierCoeff g n = σ n • mFourierCoeff f n) :
    g =ᵐ[volume]
      (fun t ↦ ∑ n ∈ box d R, c n * mFourier n t) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f := by
  refine hg.ae_eq_convolution_of_mFourierCoeff_eq_smul hf
    (fun n hn ↦ by rw [hfg, hspec n (lt_norm_of_notMem_box hR hn), smul_zero]) fun n _ ↦ ?_
  by_cases hn : ‖n‖ ≤ R
  · rw [hc n hn, hfg]
  · rw [hfg, hspec n (not_le.1 hn), smul_zero, smul_zero]

/-- **Nikol'skii's inequality on the torus**, Bernstein's inequality without derivatives: there is
`C`, depending only on `d`, such that for every complex Banach space `E` and `1 ≤ p ≤ q ≤ ∞`, every
integrable `f : (ℝ / ℤ)^d → E` whose Fourier coefficients vanish outside the ball `‖n‖ ≤ R`,
`R ≥ 1`, satisfies `‖f‖_q ≤ C R ^ (d (1/p - 1/q)) ‖f‖_p`. Here `‖n‖` is the supremum norm of
`n : d → ℤ`. -/
theorem exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {p q : ℝ≥0∞}, 1 ≤ p → p ≤ q → ∀ {R : ℝ}, 1 ≤ R →
      ∀ {f : UnitAddTorus d → E}, Integrable f → (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      eLpNorm f q volume ≤ ENNReal.ofReal (C * R ^ ((Fintype.card d : ℝ) *
        (p.toReal⁻¹ - q.toReal⁻¹))) * eLpNorm f p volume := by
  classical
  refine ⟨max 1 (∫ y, ‖𝓕⁻ (cutoffSymbol (d := d)) y‖) * 7 ^ Fintype.card d, by positivity, ?_⟩
  intro E _ _ _ p q hp hpq R hR f hf hspec
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
  have hR0 : 0 < R := one_pos.trans_le hR
  set K := cutoffKernel (d := d) R
  have hK : Continuous K := continuous_cutoffKernel R
  have hae : f =ᵐ[volume] K ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f :=
    ae_eq_convolution_of_mFourierCoeff_eq_smul hR0 hf hf hspec (σ := 1)
      (fun n hn ↦ cutoffSymbol_eq_one hR0 hn) fun n ↦ by rw [Pi.one_apply, one_smul]
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (K ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) q volume
      ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ₑ * eLpNorm K r volume *
          eLpNorm f p volume :=
        eLpNorm_convolution_le_of_inv_add_inv_eq _ hr hp hrpq hK.aestronglyMeasurable
          hf.aestronglyMeasurable
    _ ≤ 1 * ENNReal.ofReal (max 1 (∫ y, ‖𝓕⁻ (cutoffSymbol (d := d)) y‖) *
          7 ^ Fintype.card d * R ^ ((Fintype.card d : ℝ) * (1 - r⁻¹.toReal))) *
          eLpNorm f p volume := by
        gcongr
        · exact ContinuousLinearMap.opENorm_lsmul_le
        · exact eLpNorm_cutoffKernel_le hR hr
    _ = _ := by rw [one_mul, hrexp]

/-- **Bernstein's inequality for one derivative at a fixed exponent.** If `f` is integrable with
Fourier coefficients vanishing outside the ball `‖n‖ ≤ R`, and `g` is integrable with Fourier
coefficients `2πi ⟪n, v⟫ f̂(n)`, so that `g` agrees almost everywhere with the derivative along
`v` of the trigonometric polynomial representing `f`, then for `R > 0` and `1 ≤ p ≤ ∞`
`‖g‖_p ≤ C R ‖v‖ ‖f‖_p`, with `C` depending only on `d` and not on `p` or on the complex Banach
space `E` of values. -/
private theorem exists_eLpNorm_le_of_mFourierCoeff_eq_derivSymbol_smul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {p : ℝ≥0∞}, 1 ≤ p → ∀ (v : d → ℝ) {R : ℝ}, 0 < R →
      ∀ {f g : UnitAddTorus d → E},
      Integrable f → Integrable g → (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n = derivSymbol v n • mFourierCoeff f n) →
      eLpNorm g p volume ≤ ENNReal.ofReal (C * R * ‖v‖) * eLpNorm f p volume := by
  classical
  refine ⟨2 * Real.pi * ∑ i : d, ∫ y, ‖𝓕⁻ (derivCutoffSymbol (d := d) i) y‖,
    by positivity, ?_⟩
  intro E _ _ _ p hp v R hR f g hf hg hspec hfg
  have hK : Continuous (derivKernel v R) := by
    unfold derivKernel
    fun_prop
  have hae : g =ᵐ[volume] derivKernel v R ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f :=
    ae_eq_convolution_of_mFourierCoeff_eq_smul hR hf hg hspec
      (fun n hn ↦ by rw [cutoffSymbol_eq_one hR hn, mul_one]) hfg
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (derivKernel v R ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) p volume
      ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E)‖ₑ *
          eLpNorm (derivKernel v R) 1 volume * eLpNorm f p volume :=
        eLpNorm_convolution_le _ hK.aestronglyMeasurable hf.aestronglyMeasurable hp
    _ ≤ 1 * ENNReal.ofReal (2 * Real.pi * (∑ i : d, ∫ y, ‖𝓕⁻ (derivCutoffSymbol i) y‖) * R *
          ‖v‖) *
          eLpNorm f p volume := by
        gcongr
        · exact ContinuousLinearMap.opENorm_lsmul_le
        · exact eLpNorm_derivKernel_le v hR
    _ = _ := by rw [one_mul]

/-- **Bernstein's inequality for `k` derivatives at a fixed exponent.** If `f` is integrable with
Fourier coefficients vanishing outside the ball `‖n‖ ≤ R`, and `g` is integrable with Fourier
coefficients `(∏ l, 2πi ⟪n, v l⟫) f̂(n)`, then for `R > 0` and `1 ≤ p ≤ ∞`
`‖g‖_p ≤ (C R) ^ k ∏ l, ‖v l‖ ‖f‖_p`, with `C` depending only on `d` and not on `p` or on the
complex Banach space `E` of values. The proof iterates the case of one derivative through the
intermediate trigonometric polynomials. -/
private theorem exists_eLpNorm_le_of_mFourierCoeff_eq_prod_derivSymbol_smul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {p : ℝ≥0∞}, 1 ≤ p → ∀ (k : ℕ) (v : Fin k → d → ℝ) {R : ℝ}, 0 < R →
      ∀ {f g : UnitAddTorus d → E}, Integrable f → Integrable g →
      (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n = (∏ l, derivSymbol (v l) n) • mFourierCoeff f n) →
      eLpNorm g p volume ≤ ENNReal.ofReal ((C * R) ^ k * ∏ l, ‖v l‖) * eLpNorm f p volume := by
  classical
  obtain ⟨C, hC, hderiv⟩ := exists_eLpNorm_le_of_mFourierCoeff_eq_derivSymbol_smul.{u} (d := d)
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ p hp k
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
          hderiv hp _ hR hhint hg hhspec hgh
      _ ≤ ENNReal.ofReal (C * R * ‖v (Fin.last k)‖) *
            (ENNReal.ofReal ((C * R) ^ k * ∏ l : Fin k, ‖v l.castSucc‖) * eLpNorm f p volume) := by
          gcongr
          exact ih (fun l ↦ v l.castSucc) hR hf hhint hspec fun n ↦ hhc n
      _ = ENNReal.ofReal ((C * R) ^ (k + 1) * ∏ l, ‖v l‖) * eLpNorm f p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Fin.prod_univ_castSucc]
          congr 2
          ring

/-- **Bernstein's inequalities on the torus.** There is `C`, depending only on `d`, with the
following property for every complex Banach space `E` and all `1 ≤ p ≤ q ≤ ∞`. Let
`f : (ℝ / ℤ)^d → E` be integrable with Fourier coefficients vanishing outside the ball `‖n‖ ≤ R`,
`R ≥ 1`, and let `g` be integrable with Fourier coefficients `(∏ l, 2πi ⟪n, v l⟫) f̂(n)`, so
that `g` agrees almost everywhere with the derivative along `v 0, …, v (k - 1)` of the
trigonometric polynomial representing `f`. Then

`‖g‖_q ≤ C ^ (k + 1) R ^ (k + d (1/p - 1/q)) ∏ l, ‖v l‖ ‖f‖_p`.

Here `‖n‖` and `‖v l‖` are supremum norms. When the lift of `f` to `d → ℝ` is `Cᵏ`, the hypothesis
on `g` holds for its `k`-th derivative along `v`, by
`TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv`. -/
theorem exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {p q : ℝ≥0∞}, 1 ≤ p → p ≤ q →
      ∀ (k : ℕ) (v : Fin k → d → ℝ) {R : ℝ}, 1 ≤ R →
      ∀ {f g : UnitAddTorus d → E}, Integrable f → Integrable g →
      (∀ n, R < ‖n‖ → mFourierCoeff f n = 0) →
      (∀ n, mFourierCoeff g n =
        (∏ l, 2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * v l i) • mFourierCoeff f n) →
      eLpNorm g q volume ≤ ENNReal.ofReal (C ^ (k + 1) *
        R ^ ((k : ℝ) + Fintype.card d * (p.toReal⁻¹ - q.toReal⁻¹)) * ∏ l, ‖v l‖) *
          eLpNorm f p volume := by
  obtain ⟨C₀, hC₀, hnik⟩ := exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm.{u} (d := d)
  obtain ⟨C₁, hC₁, hder⟩ :=
    exists_eLpNorm_le_of_mFourierCoeff_eq_prod_derivSymbol_smul.{u} (d := d)
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, ?_⟩
  intro E _ _ _ p q hp hpq k v R hR f g hf hg hspec hfg
  have hR0 : 0 < R := one_pos.trans_le hR
  have hgspec (n : d → ℤ) (hn : R < ‖n‖) : mFourierCoeff g n = 0 := by
    rw [hfg, hspec n hn, smul_zero]
  set θ : ℝ := Fintype.card d * (p.toReal⁻¹ - q.toReal⁻¹)
  calc eLpNorm g q volume ≤ ENNReal.ofReal (C₀ * R ^ θ) * eLpNorm g p volume :=
        hnik hp hpq hR hg hgspec
    _ ≤ ENNReal.ofReal (C₀ * R ^ θ) *
          (ENNReal.ofReal ((C₁ * R) ^ k * ∏ l, ‖v l‖) * eLpNorm f p volume) := by
        gcongr
        exact hder hp k v hR0 hf hg hspec hfg
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

/-! ### The reverse Bernstein inequality -/

section ReverseBernstein

universe u

variable {d : Type*} [Fintype d]

/-- The periodic kernel of a Schwartz symbol dilated by `R > 0`, `ξ ↦ σ (R⁻¹ • ξ)`. -/
private noncomputable def dilatedKernel (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) {R : ℝ} (hR : 0 < R) :
    C(UnitAddTorus d, ℂ) :=
  (SchwartzMap.compSMulCLM ℂ (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')) σ).periodicKernel

private theorem mFourierCoeff_dilatedKernel (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) {R : ℝ} (hR : 0 < R)
    (n : d → ℤ) : mFourierCoeff (dilatedKernel σ hR) n = σ (R⁻¹ • latticePoint n) := by
  simp [dilatedKernel, Units.smul_def]

/-- **Young's inequality for the dilated kernels**, uniformly in the scale: convolution with
`dilatedKernel σ hR` is bounded on `Lᵖ(𝕋ᵈ; E)`, `1 ≤ p ≤ ∞`, by `∫ ‖𝓕⁻ σ‖`. -/
private theorem eLpNorm_dilatedKernel_convolution_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {g : UnitAddTorus d → E} (hg : AEStronglyMeasurable g) :
    eLpNorm (⇑(dilatedKernel σ hR) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g) p volume ≤
      ENNReal.ofReal (∫ y, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y‖) * eLpNorm g p volume := by
  have h : ⇑(SchwartzMap.compSMulCLM ℂ (Units.mk0 R⁻¹ (inv_ne_zero hR.ne')) σ) =
      fun ξ ↦ σ (R⁻¹ • ξ) := funext fun ξ ↦ by simp [Units.smul_def]
  rw [volume_eq_pi_haarAddCircle, ← integral_norm_fourierInv_comp_smul _ (inv_ne_zero hR.ne'),
    ← h]
  exact SchwartzMap.eLpNorm_periodicKernel_convolution_le _ hp
    (by rwa [volume_eq_pi_haarAddCircle] at hg)

/-- **Reproducing formula on an annulus.** If the symbols `σᵢ` invert the partial derivatives on
the annulus `1 ≤ ‖ξ‖ ≤ θ`, `f` has spectrum in the annulus `R ≤ ‖n‖ ≤ θ R` and `ĝᵢ(n) =
2πi nᵢ f̂(n)`, then `f = R⁻¹ ∑ᵢ Kᵢ ⋆ gᵢ` almost everywhere, for the kernels `Kᵢ` of the symbols
`σᵢ` dilated by `R`. -/
private theorem ae_eq_sum_smul_dilatedKernel_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {θ : ℝ} {σ : d → 𝓢(EuclideanSpace ℝ d, ℂ)}
    (hσ : ∀ ξ : EuclideanSpace ℝ d, 1 ≤ ‖ξ‖ → ‖ξ‖ ≤ θ →
      ∑ i, σ i ξ * (2 * Real.pi * Complex.I * ξ i) = 1)
    {R : ℝ} (hR : 0 < R) {f : UnitAddTorus d → E} {g : d → UnitAddTorus d → E}
    (hf : Integrable f) (hg : ∀ i, Integrable (g i))
    (hspec : ∀ n, (‖latticePoint n‖ < R ∨ θ * R < ‖latticePoint n‖) → mFourierCoeff f n = 0)
    (hfg : ∀ i n, mFourierCoeff (g i) n = (2 * Real.pi * Complex.I * n i) • mFourierCoeff f n) :
    f =ᵐ[volume] ∑ i, ((R⁻¹ : ℝ) : ℂ) •
      (⇑(dilatedKernel (σ i) hR) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g i) := by
  classical
  -- The spectrum of `f`, and the trigonometric polynomials representing `f` and the `gᵢ`.
  set S := (finite_setOf_norm_latticePoint_le (ι := d) (θ * R)).toFinset
  have hS (n : d → ℤ) (hn : n ∉ S) : mFourierCoeff f n = 0 :=
    hspec n (Or.inr (by simpa [S] using hn))
  have hgS (i : d) (n : d → ℤ) (hn : n ∉ S) : mFourierCoeff (g i) n = 0 := by
    rw [hfg, hS n hn, smul_zero]
  filter_upwards [hf.ae_eq_sum_mFourier_smul_mFourierCoeff hS] with x hx
  simp only [Finset.sum_apply, Pi.smul_apply]
  -- Each `Kᵢ ⋆ gᵢ` is the trigonometric polynomial with coefficients `K̂ᵢ(n) ĝᵢ(n)`.
  have hconv (i : d) : (⇑(dilatedKernel (σ i) hR) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g i) x =
      ∑ n ∈ S, (σ i (R⁻¹ • latticePoint n) * mFourier n x) • mFourierCoeff (g i) n := by
    rw [convolution_congr _ (Filter.EventuallyEq.refl _ _)
      ((hg i).ae_eq_sum_mFourier_smul_mFourierCoeff (hgS i)),
      ((dilatedKernel (σ i) hR).continuous.integrable_of_hasCompactSupport
        (.of_compactSpace _)).convolution_sum_mFourier_smul_apply]
    simp only [mFourierCoeff_dilatedKernel]
  simp_rw [hconv, Finset.smul_sum, smul_smul]
  rw [hx, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp_rw [hfg, smul_smul, ← Finset.sum_smul]
  by_cases hn : mFourierCoeff f n = 0
  · simp [hn]
  congr 1
  -- On the annulus the dilated symbols invert the derivatives.
  have hRn : R ≤ ‖latticePoint n‖ ∧ ‖latticePoint n‖ ≤ θ * R := by
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    exact hn (hspec n h)
  have hnorm : ‖R⁻¹ • latticePoint n‖ = ‖latticePoint n‖ / R := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), ← div_eq_inv_mul]
  have h1 := hσ _ (by rw [hnorm, le_div_iff₀ hR, one_mul]; exact hRn.1)
    (by rw [hnorm, div_le_iff₀ hR]; exact hRn.2)
  simp only [PiLp.smul_apply, latticePoint_apply, smul_eq_mul] at h1
  conv_lhs => rw [← mul_one (mFourier n x), ← h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

/-- **The reverse Bernstein inequality on the torus.** For every `θ` there is `C`, depending only
on `d` and `θ`, with the following property for every complex Banach space `E` and `1 ≤ p ≤ ∞`.
Let `f : (ℝ / ℤ)^d → E` be integrable with Fourier coefficients vanishing outside the annulus
`R ≤ ‖n‖ ≤ θ R`, `R > 0`, for the Euclidean norm of `n ∈ ℤᵈ`, and let `gᵢ` be integrable with
Fourier coefficients `2πi nᵢ f̂(n)`, so that `gᵢ` agrees almost everywhere with the `i`-th partial
derivative of the trigonometric polynomial representing `f`. Then

`‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖gᵢ‖_p`.

Together with Bernstein's inequality
`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`, this says that on an
annulus of radius `R` a derivative costs exactly a factor of order `R`, in both directions. -/
theorem exists_eLpNorm_le_div_mul_sum_eLpNorm_of_mFourierCoeff_eq (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {p : ℝ≥0∞}, 1 ≤ p → ∀ {R : ℝ}, 0 < R →
      ∀ {f : UnitAddTorus d → E} {g : d → UnitAddTorus d → E}, Integrable f →
      (∀ i, Integrable (g i)) →
      (∀ n, (‖latticePoint n‖ < R ∨ θ * R < ‖latticePoint n‖) → mFourierCoeff f n = 0) →
      (∀ i n, mFourierCoeff (g i) n = (2 * Real.pi * Complex.I * n i) • mFourierCoeff f n) →
      eLpNorm f p volume ≤ ENNReal.ofReal (C / R) * ∑ i, eLpNorm (g i) p volume := by
  -- Schwartz symbols inverting the partial derivatives on the annulus `1 ≤ ‖ξ‖ ≤ θ`.
  obtain ⟨σ, hσ⟩ := (EuclideanSpace.basisFun d ℝ).exists_sum_mul_eq_one_of_one_le_norm_of_norm_le θ
  simp only [EuclideanSpace.inner_basisFun_real] at hσ
  set A : d → ℝ := fun i ↦ ∫ y, ‖𝓕⁻ (σ i : EuclideanSpace ℝ d → ℂ) y‖
  have hA (i : d) : 0 ≤ A i := integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨∑ i, A i, Finset.sum_nonneg fun i _ ↦ hA i, ?_⟩
  intro E _ _ _ p hp R hR f g hf hg hspec hfg
  rw [eLpNorm_congr_ae (ae_eq_sum_smul_dilatedKernel_convolution hσ hR hf hg hspec hfg)]
  refine (eLpNorm_sum_le hp).trans ?_
  simp only [eLpNorm_const_smul]
  have hRe : ‖(((R⁻¹ : ℝ) : ℂ))‖ₑ = ENNReal.ofReal R⁻¹ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  calc ∑ i, ‖(((R⁻¹ : ℝ) : ℂ))‖ₑ *
        eLpNorm (⇑(dilatedKernel (σ i) hR) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g i) p volume
      ≤ ∑ i, ENNReal.ofReal R⁻¹ * (ENNReal.ofReal (∑ i, A i) * eLpNorm (g i) p volume) :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [hRe]
          gcongr
          refine (eLpNorm_dilatedKernel_convolution_le (σ i) hR hp
            (hg i).aestronglyMeasurable).trans ?_
          gcongr
          exact Finset.single_le_sum (fun j _ ↦ hA j) (Finset.mem_univ i)
    _ = ENNReal.ofReal R⁻¹ * ENNReal.ofReal (∑ i, A i) * ∑ i, eLpNorm (g i) p volume := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.2 hR.le), inv_mul_eq_div]

end ReverseBernstein

end TauCeti.UnitAddTorus
