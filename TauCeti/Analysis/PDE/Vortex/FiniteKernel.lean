/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# The smooth `L²` kernel of the gauge-fixed vortex operator is finite-dimensional

Let `x` be a plane vortex, in the coordinates of `TauCeti.Vortex.equation`, with `|α| → 1` and
`∇₁ α → 0` at infinity. Its gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is the linearization whose kernel is the tangent space of the
vortex moduli space. This file proves that the space of `C²` square-integrable solutions of
`L_x y = 0` (`TauCeti.Vortex.gaugeFixedKernel`) is finite-dimensional
(`TauCeti.Vortex.finiteDimensional_gaugeFixedKernel_of_tendsto`). Unlike
`TauCeti.Vortex.finiteDimensional_gaugeFixedKernel`, which counts principal parts at the zeros of a
`C²` field with a degree-`m` end framing, this needs only a `C¹` vortex and the asymptotics of
`|α|` and `∇₁ α`, with no end framing. This is the kernel half of the Fredholm
property of `L_x`; the cokernel and the identification of the kernel with the tangent space of the
symmetric product `Sym^m ℂ` of divisors are separate.

The proof is the classical one, combining an estimate at infinity with compactness on a disc.

* **Interior estimate.** For a `C²` variation `u` supported in a closed disc, the energy identity
  `integral_norm_sq_gaugeFixedOperator` expresses `∫ |L_x u|²` as the integral of the squared
  covariant gradient plus zeroth-order terms. Since the coefficients of `x` are
  bounded on the disc, this gives the Gårding inequality
  `∫ |Du|² ≤ C (∫ |L_x u|² + ∫ |u|²)` (`TauCeti.Vortex.exists_integral_norm_fderiv_sq_le`).
* **Estimate at infinity.** The exterior coercivity
  `exists_exterior_integral_norm_sq_gaugeFixedOperator_ge` applies to `χ y` for a kernel element
  `y` and a cutoff `χ` vanishing on a large disc. Since `L_x (χ y)` is the principal symbol of `dχ`
  applied to `y`, which lives on an annulus, a kernel element is controlled by its mass on a
  disc: `∫ |y|² ≤ C ∫_{|z| ≤ ρ} |y|²` (`exists_integral_norm_sq_le_mul_setIntegral_closedBall`).
  As `y` is only square integrable, `χ y` is first truncated at large radius, with derivative
  errors that vanish in the limit.
* **Compactness.** For kernel elements `y` bounded in `L²`, the localizations `b y` by a fixed
  cutoff `b` equal to one on that disc are bounded in `H¹` by the interior estimate, and so form a
  totally bounded family in `L²` by the Fréchet–Kolmogorov criterion
  (`TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`). The estimate at
  infinity turns closeness of `b y` and `b y'` into closeness of `y` and `y'`. So bounded sets of
  the kernel are totally bounded in `L²`, which by Riesz's lemma forces finite dimension.

## Main results

* `TauCeti.Vortex.exists_integral_norm_sq_le_mul_setIntegral_closedBall`: kernel elements are
  controlled by their mass on a fixed disc.
* `TauCeti.Vortex.finiteDimensional_gaugeFixedKernel_of_tendsto`: the kernel is
  finite-dimensional.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Set
open scoped ENNReal Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

private theorem memLp_of_mem_gaugeFixedKernel {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ gaugeFixedKernel x) : MemLp y 2 :=
  (mem_gaugeFixedKernel.1 hy).2.1

private theorem continuous_of_mem_gaugeFixedKernel {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ gaugeFixedKernel x) : Continuous y :=
  (mem_gaugeFixedKernel.1 hy).1.continuous

/-! ### The estimate at infinity -/

/-- The exterior estimate extends from compactly supported variations to the product `χ y` of a
kernel element `y` with a cutoff `χ` vanishing on the disc: `c² ∫ |χ y|² ≤ 2 ∫ |dχ|² |y|²`. The
proof truncates `χ y` at large radius `n + 1` by cutoffs with derivative `O(1 / (n + 1))`, whose
contribution vanishes as `n → ∞`. -/
private theorem mul_integral_norm_sq_smul_le (hx : Continuous x) {c R : ℝ}
    (hR : ∀ u : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ z, ‖z‖ ≤ R → u z = 0) → c ^ 2 * (∫ z, ‖u z‖ ^ 2) ≤ ∫ z, ‖gaugeFixedOperator x u z‖ ^ 2)
    {χ : ℂ → ℝ} {χ' : ℂ → ℂ →L[ℝ] ℝ} (hχ : ContDiff ℝ 2 χ) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχ0 : ∀ z, ‖z‖ ≤ R → χ z = 0) (hχd : ∀ z, HasFDerivAt χ (χ' z) z)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x)
    (hB : Integrable fun z ↦ ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) :
    c ^ 2 * ∫ z, ‖χ z • y z‖ ^ 2 ≤ 2 * ∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2 := by
  obtain ⟨hy, hy₂, hLy⟩ := mem_gaugeFixedKernel.1 hy
  obtain ⟨A, -, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  -- `ψ n` is one on the disc of radius `n + 1`, with derivative at most `A / (n + 1)`.
  choose ψ ψ' hψ hψ01 hψ1 hψ0 hψd hψb using fun n : ℕ ↦ hcut 0 ((n : ℝ) + 1) (by positivity)
  have hn : Integrable fun z ↦ ‖y z‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hy₂.aestronglyMeasurable).mp hy₂
  set w : ℕ → ℂ → ℝ := fun n z ↦ ψ n z * χ z with hw
  have hwd (n : ℕ) (z : ℂ) : HasFDerivAt (w n) (ψ n z • χ' z + χ z • ψ' n z) z :=
    (hψd n z).mul (hχd z)
  have hw1 (n : ℕ) (z : ℂ) : ‖w n z‖ ≤ 1 := by
    have := hψ01 n z; have := hχ01 z
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  -- The truncations `w n • y` satisfy the exterior estimate, and `L_x (w n • y) = σ(dw n) y`.
  have hineq (n : ℕ) : c ^ 2 * ∫ z, ‖w n z • y z‖ ^ 2 ≤
      2 * (∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) + 2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ∫ z, ‖y z‖ ^ 2 := by
    have hu : ContDiff ℝ 2 fun z ↦ w n z • y z := ((hψ n 2).mul hχ).smul hy
    have huc : HasCompactSupport fun z ↦ w n z • y z :=
      HasCompactSupport.intro (isCompact_closedBall 0 (2 * ((n : ℝ) + 1))) fun z hz ↦ by
        simp [hw, hψ0 n z (by simpa using hz)]
    have hpt (z : ℂ) : ‖gaugeFixedOperator x (fun z ↦ w n z • y z) z‖ ^ 2 ≤
        2 * (‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) + 2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ‖y z‖ ^ 2 := by
      rw [gaugeFixedOperator_fun_smul x (hwd n z).differentiableAt
        (hy.differentiable two_ne_zero z), hLy z, smul_zero, zero_add,
        (hwd n z).fderiv, norm_sq_gaugeFixedOperatorSymbol]
      have hW : ‖ψ n z • χ' z + χ z • ψ' n z‖ ≤ ‖χ' z‖ + A * ((n : ℝ) + 1)⁻¹ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg (hψ01 n z).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hψ01 n z).2
        · rw [norm_smul, Real.norm_of_nonneg (hχ01 z).1]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hχ01 z).2).trans (hψb n z)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hW 2
      nlinarith [sq_nonneg (‖χ' z‖ - A * ((n : ℝ) + 1)⁻¹), sq_nonneg ‖y z‖]
    have hRHS : Integrable fun z ↦
        2 * (‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) + 2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ‖y z‖ ^ 2 :=
      (hB.const_mul 2).add (hn.const_mul _)
    have hLi : Integrable fun z ↦ ‖gaugeFixedOperator x (fun z ↦ w n z • y z) z‖ ^ 2 :=
      Integrable.mono' hRHS
        ((continuous_gaugeFixedOperator hx
          (hu.of_le (by norm_num))).norm.pow 2).aestronglyMeasurable
        (.of_forall fun z ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt z)
    calc c ^ 2 * ∫ z, ‖w n z • y z‖ ^ 2
        ≤ ∫ z, ‖gaugeFixedOperator x (fun z ↦ w n z • y z) z‖ ^ 2 :=
          hR _ hu huc fun z hz ↦ by simp [hw, hχ0 z hz]
      _ ≤ ∫ z, (2 * (‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) +
            2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ‖y z‖ ^ 2) := integral_mono hLi hRHS hpt
      _ = 2 * (∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) +
            2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ∫ z, ‖y z‖ ^ 2 := by
        rw [integral_add (hB.const_mul 2) (hn.const_mul _), integral_const_mul,
          integral_const_mul]
  -- Let the truncation radius tend to infinity, by dominated convergence on the left.
  have hlimL : Tendsto (fun n : ℕ ↦ ∫ z, ‖w n z • y z‖ ^ 2) atTop
      (𝓝 (∫ z, ‖χ z • y z‖ ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ ‖y z‖ ^ 2)
      (fun n ↦ ((((hψ n 0).continuous.mul hχ.continuous).smul
        hy.continuous).norm.pow 2).aestronglyMeasurable) hn
      (fun n ↦ .of_forall fun z ↦ ?_) (.of_forall fun z ↦ ?_)
    · rw [Real.norm_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hw1 n z))
    · refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖z‖⌉₊) fun n hn ↦ ?_
      have hz : ‖z‖ ≤ (n : ℝ) + 1 :=
        (Nat.le_ceil _).trans ((Nat.cast_le.mpr hn).trans (by linarith))
      simp [hw, hψ1 n z (by simpa using hz)]
  have hlimR : Tendsto (fun n : ℕ ↦ 2 * (∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) +
      2 * (A * ((n : ℝ) + 1)⁻¹) ^ 2 * ∫ z, ‖y z‖ ^ 2) atTop
      (𝓝 (2 * (∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2) + 2 * (A * 0) ^ 2 * ∫ z, ‖y z‖ ^ 2)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simp only [one_div] at h
    exact tendsto_const_nhds.add ((((h.const_mul A).pow 2).const_mul 2).mul_const _)
  simpa using le_of_tendsto_of_tendsto' (hlimL.const_mul _) hlimR hineq

/-- **A kernel element is controlled by its mass on a disc.** For a `C¹` plane vortex with
`|α| → 1` and `∇₁ α → 0` at infinity, there are a radius `ρ` and a constant `C` such that every
`C²` square-integrable solution of `L_x y = 0` satisfies `∫ |y|² ≤ C ∫_{|z| ≤ ρ} |y|²`. -/
theorem exists_integral_norm_sq_le_mul_setIntegral_closedBall (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0)) :
    ∃ ρ C : ℝ, ∀ y ∈ gaugeFixedKernel x,
      ∫ z, ‖y z‖ ^ 2 ≤ C * ∫ z in closedBall 0 ρ, ‖y z‖ ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_exterior_integral_norm_sq_gaugeFixedOperator_ge (μ := volume)
    hx hsol hlim hcov (c := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨A, -, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  -- `b` is one on the disc of radius `R` and vanishes beyond `2 R`; the cutoff is `1 - b`.
  obtain ⟨b, b', hb, hb01, hb1, hb0, hbd, hbb⟩ := hcut 0 R hR0
  refine ⟨2 * R, 1 + 32 * (A * R⁻¹) ^ 2, fun y hyK ↦ ?_⟩
  have hy₂ : MemLp y 2 := memLp_of_mem_gaugeFixedKernel hyK
  have hn : Integrable fun z ↦ ‖y z‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hy₂.aestronglyMeasurable).mp hy₂
  have hb'c : Continuous b' := by
    have h : b' = fderiv ℝ b := funext fun z ↦ (hbd z).fderiv.symm
    exact h ▸ (hb 1).continuous_fderiv one_ne_zero
  have hB : Integrable fun z ↦ ‖-b' z‖ ^ 2 * ‖y z‖ ^ 2 :=
    Integrable.mono' (hn.const_mul ((A * R⁻¹) ^ 2))
      ((hb'c.neg.norm.pow 2).aestronglyMeasurable.mul hn.aestronglyMeasurable)
      (.of_forall fun z ↦ by
        rw [Real.norm_of_nonneg (by positivity), norm_neg]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbb z) 2)
          (sq_nonneg _))
  have hχB := mul_integral_norm_sq_smul_le hx.continuous hR (χ := fun z ↦ 1 - b z)
    (contDiff_const.sub (hb 2)) (fun z ↦ ⟨by linarith [hb01 z], by linarith [hb01 z]⟩)
    (fun z hz ↦ by simp [hb1 z (by simpa using hz)]) (fun z ↦ (hbd z).const_sub 1) hyK hB
  simp only [norm_neg] at hχB
  -- The derivative of the cutoff lives on the disc of radius `2 R`.
  have hBball : ∫ z, ‖b' z‖ ^ 2 * ‖y z‖ ^ 2 ≤
      (A * R⁻¹) ^ 2 * ∫ z in closedBall 0 (2 * R), ‖y z‖ ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : ℂ) (2 * R))
      fun z hz ↦ by
        -- Beyond radius `2 R` the cutoff vanishes near `z`, so its derivative there is zero.
        have hev : b =ᶠ[𝓝 z] fun _ ↦ 0 := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
            (show 2 * R < ‖z‖ by simpa using hz)] with w hw
          exact hb0 w (by simpa using hw)
        rw [(hbd z).unique ((hasFDerivAt_const 0 z).congr_of_eventuallyEq hev)]
        simp, ← integral_const_mul]
    refine setIntegral_mono (by simpa using hB.integrableOn) (hn.const_mul _).integrableOn
      fun z ↦ ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbb z) 2) (sq_nonneg _)
  -- Off that disc the cutoff is one.
  have hχ : Integrable fun z ↦ ‖(1 - b z) • y z‖ ^ 2 :=
    Integrable.mono' hn ((((continuous_const.sub (hb 0).continuous).smul
      (continuous_of_mem_gaugeFixedKernel hyK)).norm.pow 2).aestronglyMeasurable)
      (.of_forall fun z ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
        refine mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hb01 z])
  have hout : ∫ z in (closedBall (0 : ℂ) (2 * R))ᶜ, ‖y z‖ ^ 2 ≤
      ∫ z, ‖(1 - b z) • y z‖ ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_closedBall.compl
      (g := fun z ↦ ‖(1 - b z) • y z‖ ^ 2) fun z hz ↦ by simp [hb0 z (by simpa using hz)]]
    exact setIntegral_le_integral hχ (.of_forall fun z ↦ sq_nonneg _)
  rw [← integral_add_compl (s := closedBall (0 : ℂ) (2 * R)) measurableSet_closedBall hn]
  nlinarith [setIntegral_nonneg (μ := volume) (s := closedBall (0 : ℂ) (2 * R))
    measurableSet_closedBall fun z _ ↦ sq_nonneg ‖y z‖]

/-! ### Compactness and finite dimension -/

/-- **Compactness of localized kernel elements.** For a cutoff `b` with values in `[0, 1]`
vanishing outside a disc and with bounded derivative, the `L²` classes of the localizations
`b y` of kernel elements `y` of bounded `L²` norm form a totally bounded set. -/
private theorem totallyBounded_setOf_ae_eq_smul (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0) {b : ℂ → ℝ} {b' : ℂ → ℂ →L[ℝ] ℝ} {r A : ℝ}
    (hb : ContDiff ℝ 2 b) (hb01 : ∀ z, 0 ≤ b z ∧ b z ≤ 1) (hb0 : ∀ z, r < ‖z‖ → b z = 0)
    (hbd : ∀ z, HasFDerivAt b (b' z) z) (hbb : ∀ z, ‖b' z‖ ≤ A) (R₀ : ℝ) :
    TotallyBounded {g : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) |
      ∃ y ∈ gaugeFixedKernel x, ∫ z, ‖y z‖ ^ 2 ≤ R₀ ^ 2 ∧ g =ᵐ[volume] fun z ↦ b z • y z} := by
  obtain ⟨C, hC⟩ := exists_integral_norm_fderiv_sq_le hx r
  set K := |C| * (A ^ 2 + 1)
  set B := √(K * R₀ ^ 2)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  -- The localization of a bounded kernel element has a bounded derivative in `L²`.
  have hloc {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x)
      (hyR : ∫ z, ‖y z‖ ^ 2 ≤ R₀ ^ 2) :
      ContDiff ℝ 2 (fun z ↦ b z • y z) ∧ MemLp (fun z ↦ b z • y z) 2 ∧
        eLpNorm (fderiv ℝ fun z ↦ b z • y z) 2 ≤ ENNReal.ofReal B := by
    obtain ⟨hy, hy₂, hLy⟩ := mem_gaugeFixedKernel.1 hy
    have hu : ContDiff ℝ 2 fun z ↦ b z • y z := hb.smul hy
    have hnorm (z : ℂ) : ‖b z • y z‖ ≤ ‖y z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hb01 z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb01 z).2
    have hu₂ : MemLp (fun z ↦ b z • y z) 2 :=
      hy₂.of_le hu.continuous.aestronglyMeasurable (.of_forall hnorm)
    have hn : Integrable fun z ↦ ‖y z‖ ^ 2 :=
      (memLp_two_iff_integrable_sq_norm hy₂.aestronglyMeasurable).mp hy₂
    have hun : Integrable fun z ↦ ‖b z • y z‖ ^ 2 :=
      (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
    have hL (z : ℂ) : ‖gaugeFixedOperator x (fun z ↦ b z • y z) z‖ ^ 2 ≤ A ^ 2 * ‖y z‖ ^ 2 := by
      rw [gaugeFixedOperator_fun_smul x (hbd z).differentiableAt
        (hy.differentiable two_ne_zero z), hLy z, smul_zero, zero_add,
        (hbd z).fderiv, norm_sq_gaugeFixedOperatorSymbol]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbb z) 2)
        (sq_nonneg _)
    have hLi : Integrable fun z ↦ ‖gaugeFixedOperator x (fun z ↦ b z • y z) z‖ ^ 2 :=
      Integrable.mono' (hn.const_mul (A ^ 2))
        ((continuous_gaugeFixedOperator hx.continuous
          (hu.of_le (by norm_num))).norm.pow 2).aestronglyMeasurable
        (.of_forall fun z ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hL z)
    have hD := hC _ hu (fun z hz ↦ by simp [hb0 z hz]) fun z _ ↦ hsol z
    have hc : HasCompactSupport fun z ↦ b z • y z :=
      HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) r) fun z hz ↦ by
        simp [hb0 z (by simpa using hz)]
    have hfc := hc.fderiv (𝕜 := ℝ)
    have hf₂ : MemLp (fderiv ℝ fun z ↦ b z • y z) 2 :=
      (hu.continuous_fderiv two_ne_zero).memLp_of_hasCompactSupport hfc
    refine ⟨hu, hu₂, ?_⟩
    rw [hf₂.eLpNorm_two_eq_ofReal_sqrt_integral]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    have hX : (∫ z, ‖gaugeFixedOperator x (fun z ↦ b z • y z) z‖ ^ 2) +
        ∫ z, ‖b z • y z‖ ^ 2 ≤ (A ^ 2 + 1) * ∫ z, ‖y z‖ ^ 2 := by
      rw [add_mul, one_mul, ← integral_const_mul]
      exact add_le_add (integral_mono hLi (hn.const_mul _) hL)
        (integral_mono hun hn fun z ↦ pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2)
    have hX0 : 0 ≤ (∫ z, ‖gaugeFixedOperator x (fun z ↦ b z • y z) z‖ ^ 2) +
        ∫ z, ‖b z • y z‖ ^ 2 :=
      add_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
    calc ∫ z, ‖fderiv ℝ (fun z ↦ b z • y z) z‖ ^ 2
        ≤ C * ((∫ z, ‖gaugeFixedOperator x (fun z ↦ b z • y z) z‖ ^ 2) +
          ∫ z, ‖b z • y z‖ ^ 2) := hD
      _ ≤ |C| * ((A ^ 2 + 1) * ∫ z, ‖y z‖ ^ 2) :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) hX0).trans
          (mul_le_mul_of_nonneg_left hX (abs_nonneg C))
      _ ≤ K * R₀ ^ 2 := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hyR (by positivity)
  refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl (p := 2)
    ENNReal.ofNat_ne_top (s := closedBall 0 r) isBounded_closedBall ?_
    (M := ENNReal.ofReal |R₀|) ENNReal.ofReal_ne_top ?_ ?_
  · rintro g ⟨y, -, -, hg⟩
    filter_upwards [hg] with z hz hzs
    simp [hz, hb0 z (by simpa using hzs)]
  · rintro g ⟨y, hy, hyR, hg⟩
    obtain ⟨-, hu₂, -⟩ := hloc hy hyR
    rw [eLpNorm_congr_ae hg, hu₂.eLpNorm_two_eq_ofReal_sqrt_integral]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.mpr ⟨abs_nonneg _, ?_⟩)
    rw [sq_abs]
    refine le_trans (integral_mono ?_ ?_ fun z ↦ ?_) hyR
    · exact (memLp_two_iff_integrable_sq_norm hu₂.aestronglyMeasurable).mp hu₂
    · have hy₂ := memLp_of_mem_gaugeFixedKernel hy
      exact (memLp_two_iff_integrable_sq_norm hy₂.aestronglyMeasurable).mp hy₂
    · refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [norm_smul, Real.norm_of_nonneg (hb01 z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb01 z).2
  · intro ε hε
    -- Every translation increment is at most `‖h‖ B`.
    have htr : ∀ g ∈ {g : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) |
        ∃ y ∈ gaugeFixedKernel x, ∫ z, ‖y z‖ ^ 2 ≤ R₀ ^ 2 ∧ g =ᵐ[volume] fun z ↦ b z • y z},
        ∀ h : ℂ, eLpNorm (fun z ↦ g (z + h) - g z) 2 ≤ ‖h‖ₑ * ENNReal.ofReal B := by
      rintro g ⟨y, hy, hyR, hg⟩ h
      obtain ⟨hu, -, hD⟩ := hloc hy hyR
      have hgh : (fun z ↦ g (z + h) - g z) =ᵐ[volume]
          fun z ↦ b (z + h) • y (z + h) - b z • y z := by
        filter_upwards [(measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
          hg, hg] with z hz₁ hz₂
        simp only [Function.comp_apply] at hz₁
        rw [hz₁, hz₂]
      rw [eLpNorm_congr_ae hgh]
      exact ((hu.of_le one_le_two).eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv one_le_two h).trans
        (mul_le_mul_right hD _)
    by_cases hεt : ε = ⊤
    · exact ⟨1, one_pos, fun g _ h _ ↦ hεt ▸ le_top⟩
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    refine ⟨ε.toReal / (B + 1), by positivity, fun g hg h hh ↦ (htr g hg h).trans ?_⟩
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_toReal hεt]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖h‖ * B ≤ ε.toReal / (B + 1) * B := mul_le_mul_of_nonneg_right hh.le hB
      _ ≤ ε.toReal := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- If kernel elements are controlled by their mass on a disc on which the cutoff `b` is one,
they are controlled by the `L²` norm of their localization `b y`. -/
private theorem integral_norm_sq_le_abs_mul_integral_norm_sq_smul {ρ C : ℝ}
    (hC : ∀ y ∈ gaugeFixedKernel x, ∫ z, ‖y z‖ ^ 2 ≤ C * ∫ z in closedBall 0 ρ, ‖y z‖ ^ 2)
    {b : ℂ → ℝ} (hb1 : ∀ z ∈ closedBall 0 ρ, b z = 1) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ gaugeFixedKernel x) (hby : Integrable fun z ↦ ‖b z • y z‖ ^ 2) :
    ∫ z, ‖y z‖ ^ 2 ≤ |C| * ∫ z, ‖b z • y z‖ ^ 2 := by
  have hball : ∫ z in closedBall 0 ρ, ‖y z‖ ^ 2 ≤ ∫ z, ‖b z • y z‖ ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_closedBall (g := fun z ↦ ‖b z • y z‖ ^ 2)
      fun z hz ↦ by simp only [hb1 z hz, one_smul]]
    exact setIntegral_le_integral hby (.of_forall fun _ ↦ sq_nonneg _)
  have hball0 : 0 ≤ ∫ z in closedBall 0 ρ, ‖y z‖ ^ 2 :=
    setIntegral_nonneg measurableSet_closedBall fun _ _ ↦ sq_nonneg _
  exact (hC y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hball0).trans
    (mul_le_mul_of_nonneg_left hball (abs_nonneg C)))

/-- The `L²` class of a kernel element, as a linear map. -/
private def gaugeFixedKernelToLp (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedKernel x →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) where
  toFun y := (memLp_of_mem_gaugeFixedKernel y.2).toLp y
  map_add' y v :=
    MemLp.toLp_add (memLp_of_mem_gaugeFixedKernel y.2) (memLp_of_mem_gaugeFixedKernel v.2)
  map_smul' t y := MemLp.toLp_const_smul t (memLp_of_mem_gaugeFixedKernel y.2)

private theorem gaugeFixedKernelToLp_apply (y : gaugeFixedKernel x) :
    gaugeFixedKernelToLp x y = (memLp_of_mem_gaugeFixedKernel y.2).toLp y := (rfl)

private theorem norm_gaugeFixedKernelToLp (y : gaugeFixedKernel x) :
    ‖gaugeFixedKernelToLp x y‖ = √(∫ z, ‖(y : ℂ → EuclideanSpace ℝ (Fin 4)) z‖ ^ 2) := by
  rw [gaugeFixedKernelToLp_apply, Lp.norm_toLp,
    (memLp_of_mem_gaugeFixedKernel y.2).eLpNorm_two_eq_ofReal_sqrt_integral,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- Kernel elements are continuous, so they are determined by their `L²` classes. -/
private theorem injective_gaugeFixedKernelToLp (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Function.Injective (gaugeFixedKernelToLp x) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ Subtype.ext ?_
  rw [gaugeFixedKernelToLp_apply] at hy
  have h := (memLp_of_mem_gaugeFixedKernel y.2).coeFn_toLp.symm.trans
    ((Lp.eq_zero_iff_ae_eq_zero).1 hy)
  exact ((continuous_of_mem_gaugeFixedKernel y.2).ae_eq_iff_eq volume continuous_const).1 h

/-- **The smooth `L²` kernel of the gauge-fixed vortex operator is finite-dimensional.** For a
`C¹` plane vortex with `|α| → 1` and `∇₁ α → 0` at infinity, the `C²` square-integrable solutions
of `L_x y = 0` form a finite-dimensional real vector space. -/
theorem finiteDimensional_gaugeFixedKernel_of_tendsto (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0)) :
    FiniteDimensional ℝ (gaugeFixedKernel x) := by
  obtain ⟨ρ, C, hC⟩ := exists_integral_norm_sq_le_mul_setIntegral_closedBall hx hsol hlim hcov
  obtain ⟨A, -, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  obtain ⟨b, b', hb, hb01, hb1, hb0, hbd, hbb⟩ := hcut 0 (max ρ 1) (by positivity)
  set T := gaugeFixedKernelToLp x
  -- A bounded sequence in the range of `T` with pairwise distances at least `1` is impossible.
  have : FiniteDimensional ℝ (LinearMap.range T) := by
    by_contra hfin
    obtain ⟨R₀, f, -, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
    choose y hy using fun n ↦ LinearMap.mem_range.1 (f n).2
    have hyR (n : ℕ) : ∫ z, ‖(y n : ℂ → EuclideanSpace ℝ (Fin 4)) z‖ ^ 2 ≤ R₀ ^ 2 := by
      have h := hfR n
      rw [← Submodule.norm_coe, ← hy n, norm_gaugeFixedKernelToLp] at h
      exact (Real.sqrt_le_iff.mp h).2
    have hmem (n : ℕ) : MemLp (fun z ↦ b z • (y n : ℂ → EuclideanSpace ℝ (Fin 4)) z) 2 :=
      (memLp_of_mem_gaugeFixedKernel (y n).2).of_le
        ((hb 0).continuous.smul (continuous_of_mem_gaugeFixedKernel (y n).2)).aestronglyMeasurable
        (.of_forall fun z ↦ by
          rw [norm_smul, Real.norm_of_nonneg (hb01 z).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hb01 z).2)
    set g : ℕ → Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) :=
      fun n ↦ (hmem n).toLp _
    have hS := totallyBounded_setOf_ae_eq_smul hx hsol (hb 2) hb01 (r := 2 * max ρ 1)
      (fun z hz ↦ hb0 z (by simpa using hz)) hbd hbb R₀
    set ε : ℝ := 1 / (2 * (|C| + 1))
    obtain ⟨t, htf, hcover⟩ := Metric.totallyBounded_iff.1 hS ε (by positivity)
    choose c hct hc using fun n ↦ mem_iUnion₂.1
      (hcover ⟨(y n : ℂ → EuclideanSpace ℝ (Fin 4)), (y n).2, hyR n, (hmem n).coeFn_toLp⟩)
    have := htf.to_subtype
    obtain ⟨m, n, hmn, hcmn⟩ :=
      Finite.exists_ne_map_eq_of_infinite fun n ↦ (⟨c n, hct n⟩ : t)
    -- The localizations of `y m` and `y n` are `2 ε`-close.
    have hd : dist (g m) (g n) < 2 * ε := by
      have hcmn' : c m = c n := congrArg Subtype.val hcmn
      calc dist (g m) (g n) ≤ dist (g m) (c m) + dist (g n) (c n) := by
            rw [hcmn']; exact dist_triangle_right _ _ _
        _ < ε + ε := add_lt_add (hc m) (hc n)
        _ = 2 * ε := by ring
    set d := (y m : ℂ → EuclideanSpace ℝ (Fin 4)) - (y n : ℂ → EuclideanSpace ℝ (Fin 4))
    have hdK : d ∈ gaugeFixedKernel x := sub_mem (y m).2 (y n).2
    have hdmem : MemLp (fun z ↦ b z • d z) 2 := by
      convert (hmem m).sub (hmem n) using 1
      funext z
      simp [d, smul_sub]
    have hdist : dist (g m) (g n) = √(∫ z, ‖b z • d z‖ ^ 2) := by
      have hae : ⇑(g m) - ⇑(g n) =ᵐ[volume] fun z ↦ b z • d z := by
        filter_upwards [(hmem m).coeFn_toLp, (hmem n).coeFn_toLp] with z h₁ h₂
        simp [g, h₁, h₂, d, smul_sub]
      rw [Lp.dist_def, eLpNorm_congr_ae hae, hdmem.eLpNorm_two_eq_ofReal_sqrt_integral,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    have hX : ∫ z, ‖b z • d z‖ ^ 2 < (2 * ε) ^ 2 :=
      (Real.sqrt_lt' (by positivity)).1 (hdist ▸ hd)
    -- But `y m - y n` has `L²` norm at least `1`.
    have h1 : 1 ≤ ∫ z, ‖d z‖ ^ 2 := by
      have h : 1 ≤ ‖f m - f n‖ := hsep hmn
      rw [← Submodule.norm_coe, Submodule.coe_sub, ← hy m, ← hy n, ← map_sub,
        norm_gaugeFixedKernelToLp] at h
      have h0 : 0 ≤ ∫ z, ‖d z‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
      have hsq := Real.sq_sqrt h0
      simp only [Submodule.coe_sub] at h
      nlinarith [Real.sqrt_nonneg (∫ z, ‖d z‖ ^ 2)]
    have hloc := integral_norm_sq_le_abs_mul_integral_norm_sq_smul hC
      (fun z hz ↦ hb1 z (closedBall_subset_closedBall (le_max_left _ _) hz)) hdK
      ((memLp_two_iff_integrable_sq_norm hdmem.aestronglyMeasurable).mp hdmem)
    have hε : |C| * (2 * ε) ^ 2 < 1 := by
      have h2ε : 2 * ε = (|C| + 1)⁻¹ := by
        simp only [ε]
        field_simp
      rw [h2ε, inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
      nlinarith [abs_nonneg C]
    nlinarith [mul_le_mul_of_nonneg_left hX.le (abs_nonneg C)]
  exact (LinearEquiv.ofInjective T (injective_gaugeFixedKernelToLp x)).symm.finiteDimensional

end TauCeti.Vortex
