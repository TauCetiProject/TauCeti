/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Planar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Square integrability of `exp u - 1` for planar Sobolev functions

Let `E` be a real inner product space of dimension two with an additive Haar measure `μ`. In the
plane, `W^{1,2}(E)` does not embed in `L^∞`, but its functions are exponentially integrable. This
file proves the global form of this fact used for semilinear equations with exponential
nonlinearity on the whole plane, such as the reduced vortex equation of Taubes: for every
`u ∈ W^{1,2}(E)`,

`exp u - 1 ∈ L²(E)`

(`TauCeti.W1p.memLp_exp_value_sub_one`). Since `|exp t - 1|` is comparable to `|t|` for small `t`,
this is the natural global statement; `exp u` itself is not integrable on `E`.

## The argument

For a compactly supported `C¹` function `f`, apply the two-dimensional Gagliardo–Nirenberg–Sobolev
inequality `∫ g² ≤ G (∫ ‖Dg‖)²` (`TauCeti.integral_sq_le_mul_sq_integral_norm_fderiv`) to
`g = f ^ (n + 2)`. Since `‖Dg‖ = (n + 2) |f| ^ (n + 1) ‖Df‖`, the Cauchy–Schwarz inequality gives
the moment recursion

`∫ f ^ (2n + 4) ≤ G (n + 2)² ∫ ‖Df‖² ∫ f ^ (2n + 2)`,

and hence `∫ f ^ (2n + 2) ≤ (G A) ^ n ((n + 1)!)² ∫ f²` with `A = ∫ ‖Df‖²`
(`TauCeti.integral_pow_le_mul_factorial_sq_mul`). Pointwise,
`(exp t - 1)² ≤ t² exp (2 |t|) ≤ 2 t² cosh (2t) = ∑ 2 · 4ⁿ t ^ (2n + 2) / (2n)!`, and
`((n + 1)!)² ≤ 4ⁿ (2n)!`. Summing the moment bounds therefore gives

`∫ (exp f - 1)² ≤ 4 ∫ f²`    whenever `32 G A ≤ 1`

(`TauCeti.lintegral_exp_sub_one_sq_le`). Fatou's lemma extends this to `u ∈ W^{1,2}(E)` with
`32 G ‖∇u‖₂² < 1` (`TauCeti.W1p.lintegral_exp_value_sub_one_sq_le`). A general `u` is a test
function `φ` plus a remainder `r` of small Sobolev norm, and
`exp u - 1 = exp φ (exp r - 1) + (exp φ - 1)`, where `exp φ` is bounded and `exp φ - 1` is
continuous with compact support.

## Main results

* `TauCeti.integral_pow_le_mul_factorial_sq_mul`: the moment bounds for compactly supported `C¹`
  functions.
* `TauCeti.lintegral_exp_sub_one_sq_le`: `∫ (exp f - 1)² ≤ 4 ∫ f²` for compactly supported `C¹`
  functions of small Dirichlet energy.
* `TauCeti.W1p.lintegral_exp_value_sub_one_sq_le`: the same bound on `W^{1,2}(E)`.
* `TauCeti.W1p.memLp_exp_value_sub_one`: `exp u - 1 ∈ L²(E)` for every `u ∈ W^{1,2}(E)`.

## References

* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology
open scoped ENNReal Nat Distributions

namespace TauCeti

/-! ### Compactly supported `C¹` functions -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- One step of the moment recursion: Gagliardo–Nirenberg–Sobolev applied to `f ^ (n + 2)`,
followed by Cauchy–Schwarz. -/
private theorem integral_pow_succ_le (hE : finrank ℝ E = 2) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) (n : ℕ) :
    ∫ x, f x ^ (2 * (n + 1) + 2) ∂μ ≤
      (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) * (n + 2) ^ 2 *
        (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) * ∫ x, f x ^ (2 * n + 2) ∂μ := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous fun x ↦ fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
  have hds : HasCompactSupport fun x ↦ fderiv ℝ f x := hfs.fderiv (𝕜 := ℝ)
  have hg : ContDiff ℝ 1 fun x ↦ f x ^ (n + 2) := hf.pow _
  have hgs : HasCompactSupport fun x ↦ f x ^ (n + 2) := hfs.comp_left (g := (· ^ (n + 2))) (by simp)
  have hps : HasCompactSupport fun x ↦ |f x| ^ (n + 1) :=
    hfs.comp_left (g := fun t ↦ |t| ^ (n + 1)) (by simp)
  have hder (x : E) : ‖fderiv ℝ (fun x ↦ f x ^ (n + 2)) x‖ =
      (n + 2) * (|f x| ^ (n + 1) * ‖fderiv ℝ f x‖) := by
    have h := ((hf.differentiable one_ne_zero) x).hasFDerivAt.pow (n + 2)
    rw [h.fderiv, norm_smul, Real.norm_eq_abs, nsmul_eq_mul, abs_mul, abs_pow,
      show n + 2 - 1 = n + 1 by omega, Nat.abs_cast]
    push_cast
    ring
  have hL1 : ∫ x, ‖fderiv ℝ (fun x ↦ f x ^ (n + 2)) x‖ ∂μ =
      (n + 2) * ∫ x, |f x| ^ (n + 1) * ‖fderiv ℝ f x‖ ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hder)
  have hpow (x : E) : (|f x| ^ (n + 1)) ^ 2 = f x ^ (2 * n + 2) := by
    rw [← pow_mul, pow_abs, show (n + 1) * 2 = 2 * n + 2 by ring]
    exact abs_of_nonneg (by rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; positivity)
  have hCS : (∫ x, |f x| ^ (n + 1) * ‖fderiv ℝ f x‖ ∂μ) ^ 2 ≤
      (∫ x, f x ^ (2 * n + 2) ∂μ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
    refine (sq_integral_mul_le_integral_sq_mul_integral_sq
      ((by fun_prop : Continuous fun x ↦ |f x| ^ (n + 1)).memLp_of_hasCompactSupport (μ := μ) hps)
      (hdc.norm.memLp_of_hasCompactSupport hds.norm)).trans_eq ?_
    rw [integral_congr_ae (Eventually.of_forall hpow)]
  have hpow' (x : E) : (f x ^ (n + 2)) ^ 2 = f x ^ (2 * (n + 1) + 2) := by
    rw [← pow_mul]; ring_nf
  calc ∫ x, f x ^ (2 * (n + 1) + 2) ∂μ = ∫ x, (f x ^ (n + 2)) ^ 2 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x ↦ (hpow' x).symm)
    _ ≤ G * (∫ x, ‖fderiv ℝ (fun x ↦ f x ^ (n + 2)) x‖ ∂μ) ^ 2 :=
        integral_sq_le_mul_sq_integral_norm_fderiv μ hE hg hgs
    _ = G * (n + 2) ^ 2 * (∫ x, |f x| ^ (n + 1) * ‖fderiv ℝ f x‖ ∂μ) ^ 2 := by
        rw [hL1]; ring
    _ ≤ G * (n + 2) ^ 2 * ((∫ x, f x ^ (2 * n + 2) ∂μ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) := by
        gcongr
    _ = _ := by ring

/-- **Moment bounds in dimension two.** For a compactly supported `C¹` function `f`,
`∫ f ^ (2n + 2) ≤ (G A) ^ n ((n + 1)!)² ∫ f²`, where `A = ∫ ‖Df‖²` and `G` is the constant of
the Gagliardo–Nirenberg–Sobolev inequality `TauCeti.integral_sq_le_mul_sq_integral_norm_fderiv`. -/
theorem integral_pow_le_mul_factorial_sq_mul (hE : finrank ℝ E = 2) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) (n : ℕ) :
    ∫ x, f x ^ (2 * n + 2) ∂μ ≤
      ((lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) ^ n *
        ((n + 1)! : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  set A := ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ
  have hGA : 0 ≤ G * A := mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun x ↦ by positivity)
  induction n with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, pow_zero, Nat.factorial_one, Nat.cast_one,
      one_pow, one_mul, le_refl]
  | succ k ih =>
    have hk : (0 : ℝ) ≤ (G * A) * (k + 2) ^ 2 := mul_nonneg hGA (by positivity)
    calc ∫ x, f x ^ (2 * (k + 1) + 2) ∂μ ≤ G * (k + 2) ^ 2 * A * ∫ x, f x ^ (2 * k + 2) ∂μ :=
          integral_pow_succ_le μ hE hf hfs k
      _ = (G * A) * (k + 2) ^ 2 * ∫ x, f x ^ (2 * k + 2) ∂μ := by ring
      _ ≤ (G * A) * (k + 2) ^ 2 * ((G * A) ^ k * ((k + 1)! : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left ih hk
      _ = (G * A) ^ (k + 1) * ((k + 1 + 1)! : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ := by
          rw [Nat.factorial_succ (k + 1), Nat.cast_mul]; push_cast; ring

/-- **Exponential square integrability for small energy.** For a compactly supported `C¹`
function `f` with `32 G ∫ ‖Df‖² ≤ 1`, where `G` is the constant of the Gagliardo–Nirenberg–Sobolev
inequality, `∫ (exp f - 1)² ≤ 4 ∫ f²`. -/
theorem lintegral_exp_sub_one_sq_le (hE : finrank ℝ E = 2) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f)
    (hA : 32 * (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) *
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ ≤ 1) :
    ∫⁻ x, ENNReal.ofReal ((Real.exp (f x) - 1) ^ 2) ∂μ ≤
      ENNReal.ofReal (4 * ∫ x, f x ^ 2 ∂μ) := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  set A := ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ
  set M := ∫ x, f x ^ 2 ∂μ
  have hfc : Continuous f := hf.continuous
  -- The terms of the series `2 t² cosh (2t) = ∑ 2 · 4ⁿ t ^ (2n + 2) / (2n)!`.
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n ↦ (2 * 4 ^ n / (2 * n)! : ℝ) := ⟨_, rfl⟩
  have hc0 (n : ℕ) : 0 ≤ c n := by rw [hc]; positivity
  have heven (n : ℕ) (t : ℝ) : 0 ≤ t ^ (2 * n + 2) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]; positivity
  have hsum (x : E) :
      HasSum (fun n ↦ c n * f x ^ (2 * n + 2)) (2 * f x ^ 2 * Real.cosh (2 * f x)) := by
    have h := (Real.hasSum_cosh (2 * f x)).mul_left (2 * f x ^ 2)
    convert h using 1
    funext n
    rw [hc, mul_pow, show (2 : ℝ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
    ring
  have hpt (x : E) : ENNReal.ofReal ((Real.exp (f x) - 1) ^ 2) ≤
      ∑' n, ENNReal.ofReal (c n * f x ^ (2 * n + 2)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ mul_nonneg (hc0 n) (heven n _))
      (hsum x).summable, (hsum x).tsum_eq]
    exact ENNReal.ofReal_le_ofReal (exp_sub_one_sq_le_two_mul_sq_mul_cosh (f x))
  have hint (n : ℕ) : Integrable (fun x ↦ c n * f x ^ (2 * n + 2)) μ :=
    ((hfc.pow _).integrable_of_hasCompactSupport
      (hfs.comp_left (g := (· ^ (2 * n + 2))) (by simp))).const_mul _
  -- Each term is bounded by the moment bound and `((n + 1)!)² ≤ 4ⁿ (2n)!`.
  have hterm (n : ℕ) : ∫⁻ x, ENNReal.ofReal (c n * f x ^ (2 * n + 2)) ∂μ ≤
      ENNReal.ofReal (2 * M) * ENNReal.ofReal (16 * (G * A)) ^ n := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x ↦ mul_nonneg (hc0 n) (heven n _)),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmom := integral_pow_le_mul_factorial_sq_mul μ hE hf hfs n
    have hfac : ((n + 1)! : ℝ) ^ 2 ≤ 4 ^ n * (2 * n)! := by
      exact_mod_cast Nat.factorial_succ_sq_le_four_pow_mul_factorial_two_mul n
    have hpos : (0 : ℝ) < (2 * n)! := by positivity
    rw [integral_const_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hpos]
    calc 2 * 4 ^ n * ∫ x, f x ^ (2 * n + 2) ∂μ
        ≤ 2 * 4 ^ n * ((G * A) ^ n * ((n + 1)! : ℝ) ^ 2 * M) := by gcongr
      _ = 2 * 4 ^ n * (G * A) ^ n * M * ((n + 1)! : ℝ) ^ 2 := by ring
      _ ≤ 2 * 4 ^ n * (G * A) ^ n * M * (4 ^ n * (2 * n)!) := by gcongr
      _ = 2 * M * (16 * (G * A)) ^ n * (2 * n)! := by
          have h16 : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
          rw [mul_pow (16 : ℝ), h16]; ring
  -- Sum the termwise bounds: a geometric series with ratio `16 G A ≤ 1 / 2`.
  have hq : ENNReal.ofReal (16 * (G * A)) ≤ 2⁻¹ := by
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ by
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ x, ENNReal.ofReal ((Real.exp (f x) - 1) ^ 2) ∂μ
      ≤ ∫⁻ x, ∑' n, ENNReal.ofReal (c n * f x ^ (2 * n + 2)) ∂μ := lintegral_mono hpt
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (c n * f x ^ (2 * n + 2)) ∂μ :=
        lintegral_tsum fun n ↦ (hint n).aemeasurable.ennreal_ofReal
    _ ≤ ∑' n, ENNReal.ofReal (2 * M) * ENNReal.ofReal (16 * (G * A)) ^ n :=
        tsum_le_tsum hterm
    _ = ENNReal.ofReal (2 * M) * (1 - ENNReal.ofReal (16 * (G * A)))⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (2 * M) * 2 := by
        gcongr
        rw [ENNReal.inv_le_iff_inv_le, show (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ by
          rw [ENNReal.one_sub_inv_two]]
        exact tsub_le_tsub_left hq 1
    _ = ENNReal.ofReal (4 * M) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]; ring_nf

end Smooth

/-! ### Sobolev functions -/

section Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- `TauCeti.lintegral_exp_sub_one_sq_le` for the Sobolev function of a test function. -/
private theorem W1p.lintegral_exp_value_ofTestFunctionₗ_sub_one_sq_le (hE : finrank ℝ E = 2)
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ))
    (hψ : 32 * (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) *
      ‖W1p.gradient (W1p.ofTestFunctionₗ μ ⊤ 2 ψ)‖ ^ 2 ≤ 1) :
    ∫⁻ x, ENNReal.ofReal ((Real.exp (W1p.value (W1p.ofTestFunctionₗ μ ⊤ 2 ψ) x) - 1) ^ 2) ∂μ ≤
      ENNReal.ofReal (4 * ‖W1p.value (W1p.ofTestFunctionₗ μ ⊤ 2 ψ)‖ ^ 2) := by
  set U := W1p.ofTestFunctionₗ μ ⊤ 2 ψ
  have hv : (W1p.value U : E → ℝ) =ᵐ[μ] ψ := W1p.value_ofTestFunctionₗ_top_ae ψ
  rw [W1p.norm_gradient_ofTestFunctionₗ_top_sq] at hψ
  rw [W1p.norm_value_ofTestFunctionₗ_top_sq]
  refine (lintegral_congr_ae (hv.mono fun x hx ↦ ?_)).trans_le
    (lintegral_exp_sub_one_sq_le μ hE (ψ.contDiff.of_le (by exact_mod_cast le_top))
      ψ.hasCompactSupport hψ)
  simp only [hx]

/-- **Exponential square integrability for small energy on `W^{1,2}`.** In dimension two, every
`u ∈ W^{1,2}(E)` with `32 G ‖∇u‖₂² < 1`, where `G` is the constant of the
Gagliardo–Nirenberg–Sobolev inequality `TauCeti.integral_sq_le_mul_sq_integral_norm_fderiv`,
satisfies `∫ (exp u - 1)² ≤ 4 ‖u‖₂²`. -/
theorem W1p.lintegral_exp_value_sub_one_sq_le (hE : finrank ℝ E = 2) (u : W1p μ ⊤ 2)
    (hu : 32 * (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ) * ‖W1p.gradient u‖ ^ 2 < 1) :
    ∫⁻ x, ENNReal.ofReal ((Real.exp (W1p.value u x) - 1) ^ 2) ∂μ ≤
      ENNReal.ofReal (4 * ‖W1p.value u‖ ^ 2) := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  -- Approximate `u` by test functions.
  obtain ⟨U, hU, hlim⟩ := mem_closure_iff_seq_limit.mp
    (W1p.denseRange_ofTestFunctionₗ_top (mu := μ) (p := 2) ENNReal.ofNat_ne_top u)
  choose ψ hψ using hU
  have hval : Tendsto (fun n ↦ W1p.value (U n)) atTop (𝓝 (W1p.value u)) := by
    have h := ((W1p.valueL (mu := μ) (Omega := ⊤) (p := 2)).continuous.tendsto u).comp hlim
    simpa only [Function.comp_def, W1p.valueL_apply] using h
  have hgrad : Tendsto (fun n ↦ 32 * G * ‖W1p.gradient (U n)‖ ^ 2) atTop
      (𝓝 (32 * G * ‖W1p.gradient u‖ ^ 2)) := by
    have h := ((W1p.gradientL (mu := μ) (Omega := ⊤) (p := 2)).continuous.tendsto u).comp hlim
    simp only [Function.comp_def, W1p.gradientL_apply] at h
    exact (h.norm.pow 2).const_mul _
  have hsmall : ∀ᶠ n in atTop, 32 * G * ‖W1p.gradient (U n)‖ ^ 2 ≤ 1 :=
    hgrad.eventually (ge_mem_nhds hu)
  -- Along a subsequence the values converge almost everywhere.
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hns
  set F : ℕ → E → ℝ≥0∞ := fun i x ↦ ENNReal.ofReal ((Real.exp (W1p.value (U (ns i)) x) - 1) ^ 2)
  have hF : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop
      (𝓝 (ENNReal.ofReal ((Real.exp (W1p.value u x) - 1) ^ 2))) :=
    hns.mono fun x hx ↦ (ENNReal.continuous_ofReal.tendsto _).comp
      ((((Real.continuous_exp.tendsto _).comp hx).sub_const 1).pow 2)
  have hFm (i : ℕ) : AEMeasurable (F i) μ :=
    ((Real.continuous_exp.comp_aestronglyMeasurable
      (W1p.memLp_value (U (ns i))).aestronglyMeasurable).sub
      aestronglyMeasurable_const |>.pow 2).aemeasurable.ennreal_ofReal
  have hbound : ∀ᶠ i in atTop, ∫⁻ x, F i x ∂μ ≤ ENNReal.ofReal (4 * ‖W1p.value (U (ns i))‖ ^ 2) :=
    (hmono.tendsto_atTop.eventually hsmall).mono fun i hi ↦ by
      simp only [F, ← hψ (ns i)] at hi ⊢
      exact W1p.lintegral_exp_value_ofTestFunctionₗ_sub_one_sq_le μ hE _ hi
  have hlimb : Tendsto (fun i ↦ ENNReal.ofReal (4 * ‖W1p.value (U (ns i))‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (4 * ‖W1p.value u‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((hval.comp hmono.tendsto_atTop).norm.pow 2).const_mul 4)
  calc ∫⁻ x, ENNReal.ofReal ((Real.exp (W1p.value u x) - 1) ^ 2) ∂μ
      = ∫⁻ x, liminf (fun i ↦ F i x) atTop ∂μ :=
        lintegral_congr_ae (hF.mono fun x hx ↦ hx.liminf_eq.symm)
    _ ≤ liminf (fun i ↦ ∫⁻ x, F i x ∂μ) atTop := lintegral_liminf_le' hFm
    _ ≤ liminf (fun i ↦ ENNReal.ofReal (4 * ‖W1p.value (U (ns i))‖ ^ 2)) atTop :=
        liminf_le_liminf hbound
    _ = ENNReal.ofReal (4 * ‖W1p.value u‖ ^ 2) := hlimb.liminf_eq

/-- **`exp u - 1` is square integrable for `u ∈ W^{1,2}` in the plane.** In dimension two, every
`u ∈ W^{1,2}(E)` satisfies `exp u - 1 ∈ L²(E)`. -/
theorem W1p.memLp_exp_value_sub_one (hE : finrank ℝ E = 2) (u : W1p μ ⊤ 2) :
    MemLp (fun x ↦ Real.exp (W1p.value u x) - 1) 2 μ := by
  set G : ℝ := (lintegralPowLePowLIntegralFDerivConst μ 2 : ℝ)
  have hG : 0 ≤ G := NNReal.coe_nonneg _
  -- Split `u = ψ + r` with `ψ` a test function and `r` of small Sobolev norm.
  set δ : ℝ := (32 * G + 1)⁻¹
  have hδ : 0 < δ := by positivity
  obtain ⟨U, ⟨ψ, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp
    (W1p.denseRange_ofTestFunctionₗ_top (mu := μ) (p := 2) ENNReal.ofNat_ne_top u) δ hδ
  set r := u - W1p.ofTestFunctionₗ μ ⊤ 2 ψ
  have hr : ‖W1p.gradient r‖ < δ :=
    (W1p.norm_gradient_le r).trans_lt (by rwa [← dist_eq_norm])
  have hsmall : 32 * G * ‖W1p.gradient r‖ ^ 2 < 1 := by
    have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h2 : ‖W1p.gradient r‖ ^ 2 ≤ δ := by
      calc ‖W1p.gradient r‖ ^ 2 ≤ δ ^ 2 := by gcongr
        _ ≤ δ := by nlinarith
    calc 32 * G * ‖W1p.gradient r‖ ^ 2 ≤ 32 * G * δ := by gcongr
      _ < 1 := by
          rw [← div_eq_mul_inv, div_lt_one (by positivity)]
          linarith
  -- `exp r - 1 ∈ L²`.
  have hrm : AEStronglyMeasurable (fun x ↦ Real.exp (W1p.value r x) - 1) μ :=
    (Real.continuous_exp.comp_aestronglyMeasurable (W1p.memLp_value r).aestronglyMeasurable).sub
      aestronglyMeasurable_const
  have hrL2 : MemLp (fun x ↦ Real.exp (W1p.value r x) - 1) 2 μ := by
    refine (memLp_two_iff_integrable_sq hrm).mpr ⟨hrm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ sq_nonneg _)]
    exact (W1p.lintegral_exp_value_sub_one_sq_le μ hE r hsmall).trans_lt ENNReal.ofReal_lt_top
  -- The test function contributes a bounded factor and a compactly supported term.
  have hψc : Continuous (ψ : E → ℝ) := ψ.continuous
  have hψs : HasCompactSupport fun x ↦ Real.exp (ψ x) - 1 :=
    ψ.hasCompactSupport.comp_left (g := fun t ↦ Real.exp t - 1) (by simp)
  have hψc' : Continuous fun x ↦ Real.exp (ψ x) - 1 := by fun_prop
  obtain ⟨C, hC⟩ := hψc'.bounded_above_of_compact_support hψs
  have htop : MemLp (fun x ↦ Real.exp (ψ x)) ⊤ μ := by
    refine memLp_top_of_bound (Real.continuous_exp.comp hψc).aestronglyMeasurable (C + 1)
      (Eventually.of_forall fun x ↦ ?_)
    have h := hC x
    simp only [Real.norm_eq_abs] at h ⊢
    calc |Real.exp (ψ x)| = |(Real.exp (ψ x) - 1) + 1| := by ring_nf
      _ ≤ |Real.exp (ψ x) - 1| + |1| := abs_add_le _ _
      _ ≤ C + 1 := by rw [abs_one]; linarith
  have hψL2 : MemLp (fun x ↦ Real.exp (ψ x) - 1) 2 μ := hψc'.memLp_of_hasCompactSupport hψs
  have hsum := (htop.mul hrL2).add hψL2
  refine hsum.ae_eq ?_
  -- `u = r + ψ` almost everywhere.
  have hu : (W1p.value u : E → ℝ) =ᵐ[μ] fun x ↦ W1p.value r x + ψ x := by
    have h1 : ⇑(W1p.value r) =ᵐ[μ] ⇑(W1p.value u) - ⇑(W1p.value (W1p.ofTestFunctionₗ μ ⊤ 2 ψ)) := by
      simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using
        W1p.value_sub_ae (mu := μ) (Omega := ⊤) (p := 2) u (W1p.ofTestFunctionₗ μ ⊤ 2 ψ)
    have h2 : (W1p.value (W1p.ofTestFunctionₗ μ ⊤ 2 ψ) : E → ℝ) =ᵐ[μ] ψ :=
      W1p.value_ofTestFunctionₗ_top_ae ψ
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [hx1, Pi.sub_apply, hx2]
    ring
  filter_upwards [hu] with x hx
  simp only [Pi.add_apply, Pi.mul_apply, hx, Real.exp_add]
  ring

end Sobolev

end TauCeti
