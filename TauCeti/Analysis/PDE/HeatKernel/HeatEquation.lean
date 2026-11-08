/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.PDE.HeatKernel.Bounds
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The heat convolution solves the heat equation

Let `g` be a measurable, essentially bounded function on a finite-dimensional real inner product
space `E`, with values in a real normed space (a Banach space for the Laplacian, the heat
equation and the Hölder bounds). The candidate solution of the Cauchy problem `∂ₜu = Δu`,
`u(0, ·) = g`, is
`u(t, x) = (K_t ⋆ g)(x)`, where `K_t` is the heat kernel. The initial condition holds pointwise
at every point `x₀` where `g` is continuous (for `F` a Banach space): `u(t, x) → g(x₀)` as
`(t, x) → (0⁺, x₀)`, which is `TauCeti.tendsto_heatKernel_convolution`. At points where `g` is
discontinuous no such limit is asserted. This file proves the equation:

* `u(t, ·)` is smooth for every `t > 0`, however rough `g` is, and its derivatives are
  `D^m u(t, ·) = D^m K_t ⋆ g`, bounded by `‖D^m K_t‖_{L¹}` times the bound of `g`; for `m ≥ 1`,
  since `∫ D^m K_t = 0`, an `α`-Hölder datum gives the sharper bound
  `H ∫ ‖D^m K_t(z)‖ ‖z‖^α dz`, and similarly the difference of these derivatives at two times
  `a, b` is at most `H ∫ ‖D^m K_b(z) - D^m K_a(z)‖ ‖z‖^α dz`;
* `Δu(t, ·) = ΔK_t ⋆ g`, and `∂ₜu(t, x) = (ΔK_t ⋆ g)(x)`, so `∂ₜu = Δu` for `t > 0`.

Both derivatives are taken under the integral sign. In space, every derivative of `K_t` is
dominated, uniformly on unit translates, by a multiple of `K_{4t}`
(`TauCeti.exists_integrable_norm_iteratedFDeriv_heatKernel_add_le`), and this feeds the general
smoothness theorem `MeasureTheory.contDiff_convolution_left_of_dominated`. In time,
`∂ₜK_s = ΔK_s` is dominated for `s` near `t` by a multiple of `K_{4t}`.

## Main declarations

* `TauCeti.contDiff_heatKernel_convolution`: `K_t ⋆ g` is smooth for `t > 0`.
* `TauCeti.iteratedFDeriv_heatKernel_convolution`,
  `TauCeti.iteratedFDeriv_heatKernel_convolution_eq_integral_sub`: `D^m (K_t ⋆ g) = D^m K_t ⋆ g`,
  with the value at the base point subtracted for `m ≥ 1`.
* `TauCeti.iteratedFDeriv_heatKernel_convolution_eq_smul_integral`: the parabolic scaling
  `D^m (K_t ⋆ g)(x) = (√t)⁻¹ ^ m ∫ D^m K_1(y) ⊗ g(x - √t • y) dy`.
* `TauCeti.norm_iteratedFDeriv_heatKernel_convolution_le`,
  `TauCeti.norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith`: bounds on these
  derivatives for bounded and for Hölder data.
* `TauCeti.exists_norm_laplacian_heatKernel_convolution_le`: the bound
  `‖Δ (K_t ⋆ g)(x)‖ ≤ C H t^((α - 2)/2)` for bounded `α`-Hölder data.
* `TauCeti.norm_iteratedFDeriv_heatKernel_convolution_sub_le_of_holderWith`: the corresponding
  bound on their differences between two times, for Hölder data.
* `TauCeti.laplacian_heatKernel_convolution`: `Δ (K_t ⋆ g) = ΔK_t ⋆ g`.
* `TauCeti.hasDerivAt_heatKernel_convolution`: **the heat equation**
  `∂ₜ (K_t ⋆ g)(x) = Δ (K_t ⋆ g)(x)` for `t > 0`.
* `TauCeti.hasDerivAt_heatKernel_convolution_of_hasCompactSupport`: the heat equation in the form
  `∂ₜ (K_t ⋆ φ) = K_t ⋆ Δ φ` for `C²` data `φ` with compact support.
* `TauCeti.heatKernel_convolution_sub_eq_integral`: Duhamel's formula
  `(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds` for such `φ`.
* `TauCeti.stronglyMeasurable_heatKernel_convolution`: `(t, x) ↦ (K_t ⋆ g)(x)` is strongly
  measurable for continuous `g`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1, Theorem 1.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace Laplacian MeasureTheory Metric Module Real Set
open scoped Convolution ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {M t : ℝ}

/-- For `s` within a factor two of `t`, the time derivative `∂ₛK_s = ΔK_s` of the heat kernel is
dominated by a fixed multiple of `K_{4t}`. -/
private theorem exists_abs_laplacian_heatKernel_le (ht : 0 < t) :
    ∃ B, 0 ≤ B ∧ ∀ s, t / 2 < s → s ≤ 2 * t → ∀ y : E,
      |Δ (heatKernel s : E → ℝ) y| ≤ B * heatKernel (2 * (2 * t)) y := by
  have h2t : 0 < 2 * t := by positivity
  obtain ⟨C, hC₀, hC⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) h2t 2
  set d : ℝ := (finrank ℝ E : ℝ)
  refine ⟨(1 / t ^ 2 + d / t) * 4 ^ (d / 2) * C, by positivity, fun s hs hs' y => ?_⟩
  have hs₀ : 0 < s := by linarith
  have hKs := heatKernel_pos hs₀ y
  -- `ΔK_s = (‖y‖² / (4s²) - n / (2s)) K_s`, and the coefficient is `O((1 + ‖y‖)²)` uniformly.
  have hcoef : |‖y‖ ^ 2 / (4 * s ^ 2) - d / (2 * s)| ≤ (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 := by
    have h₁ : ‖y‖ ^ 2 / (4 * s ^ 2) ≤ ‖y‖ ^ 2 / t ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have h₂ : d / (2 * s) ≤ d / t := div_le_div_of_nonneg_left (by positivity) ht (by linarith)
    have h₃ : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    have h₄ : 1 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc ‖y‖ ^ 2 / (4 * s ^ 2) + d / (2 * s) ≤ ‖y‖ ^ 2 / t ^ 2 + d / t := add_le_add h₁ h₂
      _ ≤ (1 + ‖y‖) ^ 2 / t ^ 2 + d / t * (1 + ‖y‖) ^ 2 :=
          add_le_add (div_le_div_of_nonneg_right h₃ (by positivity))
            (le_mul_of_one_le_right (by positivity) h₄)
      _ = (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 := by ring
  have hKcomp : heatKernel s y ≤ 4 ^ (d / 2) * heatKernel (2 * t) y :=
    (heatKernel_le_mul_heatKernel hs₀ hs' y).trans <| mul_le_mul_of_nonneg_right
      (rpow_le_rpow (by positivity) ((div_le_iff₀ hs₀).2 (by linarith)) (by positivity))
      (heatKernel_pos h2t y).le
  rw [laplacian_heatKernel, abs_mul, abs_of_pos hKs]
  calc |‖y‖ ^ 2 / (4 * s ^ 2) - d / (2 * s)| * heatKernel s y
      ≤ (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 * (4 ^ (d / 2) * heatKernel (2 * t) y) :=
        mul_le_mul hcoef hKcomp hKs.le (by positivity)
    _ = (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * ((1 + ‖y‖) ^ 2 * heatKernel (2 * t) y) := by ring
    _ ≤ (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * (C * heatKernel (2 * (2 * t)) y) :=
        mul_le_mul_of_nonneg_left (hC y) (by positivity)
    _ = (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * C * heatKernel (2 * (2 * t)) y := by ring

variable [MeasurableSpace E] [BorelSpace E]

/-- **Smoothing by the heat kernel.** For `t > 0` and `g` measurable and essentially bounded,
`K_t ⋆ g` is smooth. -/
theorem contDiff_heatKernel_convolution (ht : 0 < t) (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) : ContDiff ℝ ∞ (heatKernel t ⋆ g) :=
  contDiff_convolution_left_of_dominated (lsmul ℝ ℝ) (contDiff_heatKernel t)
    (fun k _ => exists_integrable_norm_iteratedFDeriv_heatKernel_add_le ht k 1) hg hM

/-- **Derivatives of a heat convolution.** For `t > 0` and `g` measurable and essentially
bounded, every derivative of `K_t ⋆ g` is computed on the kernel:
`D^m (K_t ⋆ g)(x) = ∫ D^m K_t(z) ⊗ g(x - z) dz`, where `A ⊗ b` is the multilinear map
`v ↦ A v • b`. -/
theorem iteratedFDeriv_heatKernel_convolution (ht : 0 < t) (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (heatKernel t ⋆ g) x =
      ∫ z, (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z)) := by
  rw [iteratedFDeriv_convolution_left_of_dominated (lsmul ℝ ℝ) (N := ⊤) (contDiff_heatKernel t)
    (fun k _ => exists_integrable_norm_iteratedFDeriv_heatKernel_add_le ht k 1) hg hM le_top,
    convolution_def]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  ext v
  simp only [flip_apply, coe_comp, Function.comp_apply, lsmul_flip_apply,
    compContinuousMultilinearMapL_apply, ContinuousMultilinearMap.smulRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, toSpanSingleton_apply]

/-- The integrand `z ↦ D^m K_t(z) ⊗ g(x - z)` of `TauCeti.iteratedFDeriv_heatKernel_convolution`
is integrable. -/
private theorem integrable_smulRight_iteratedFDeriv_heatKernel (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) (x : E) :
    Integrable fun z => (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z)) := by
  simpa only [ConvolutionExistsAt, ContinuousMultilinearMap.smulRightL_apply] using
    convolutionExists_of_integrable_of_ae_norm_le
      (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F)
      (integrable_iteratedFDeriv_heatKernel ht m) hg hM x

/-- The integrand `z ↦ D^m K_t(z) ⊗ (g(x - z) - g(x))` of
`TauCeti.iteratedFDeriv_heatKernel_convolution_eq_integral_sub` is integrable. -/
private theorem integrable_smulRight_iteratedFDeriv_heatKernel_sub (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) (x : E) :
    Integrable fun z => (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z) - g x) := by
  refine ((integrable_smulRight_iteratedFDeriv_heatKernel ht hg hM m x).sub
    (((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).flip (g x)).integrable_comp
      (integrable_iteratedFDeriv_heatKernel ht m))).congr (ae_of_all _ fun z => ?_)
  ext v
  simp [smul_sub]

/-- **Bounds on the derivatives of a heat convolution.** If `‖g‖ ≤ M` almost everywhere, then
`‖D^m (K_t ⋆ g)(x)‖ ≤ ‖D^m K_t‖_{L¹} M` for `t > 0`. -/
theorem norm_iteratedFDeriv_heatKernel_convolution_le (ht : 0 < t) (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (heatKernel t ⋆ g) x‖ ≤
      (∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖) * M := by
  have hqmp := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E) x
  rw [iteratedFDeriv_heatKernel_convolution ht hg hM, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_iteratedFDeriv_heatKernel ht m).norm.mul_const M)
    ?_
  filter_upwards [hqmp.ae hM] with z hz
  rw [ContinuousMultilinearMap.norm_smulRight]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

/-- **Parabolic scaling of the derivatives of a heat convolution.** For `t > 0` and `g` measurable
and essentially bounded,
`D^m (K_t ⋆ g)(x) = (√t)⁻¹ ^ m ∫ D^m K_1(y) ⊗ g(x - √t • y) dy`, where `A ⊗ b` is the
multilinear map `v ↦ A v • b`. -/
theorem iteratedFDeriv_heatKernel_convolution_eq_smul_integral (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (heatKernel t ⋆ g) x = (√t)⁻¹ ^ m •
      ∫ y, (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) y).smulRight (g (x - √t • y)) := by
  have hst : 0 < √t := sqrt_pos.2 ht
  set φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F := fun y =>
    ((√t)⁻¹ ^ (finrank ℝ E + m)) •
      (iteratedFDeriv ℝ m (heatKernel 1 : E → ℝ) y).smulRight (g (x - √t • y)) with hφ_def
  -- Substitute `z = √t • y`, using the parabolic scaling of `D^m K_t`.
  have hφ (z : E) :
      φ ((√t)⁻¹ • z) = (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z)) := by
    have hpow : t ^ (-(finrank ℝ E + m : ℝ) / 2) = (√t)⁻¹ ^ (finrank ℝ E + m) := by
      rw [inv_sqrt_pow_eq_rpow ht.le]
      push_cast
      ring_nf
    have hinv : t ^ (-1 / 2 : ℝ) = (√t)⁻¹ := by
      simpa using (inv_sqrt_pow_eq_rpow ht.le 1).symm
    rw [iteratedFDeriv_heatKernel_eq_rpow_smul ht, hpow, hinv, hφ_def]
    ext v
    simp [smul_inv_smul₀ hst.ne', mul_smul]
  have hscalar : √t ^ finrank ℝ E * (√t)⁻¹ ^ (finrank ℝ E + m) = (√t)⁻¹ ^ m := by
    simp [pow_add, hst.ne']
  rw [iteratedFDeriv_heatKernel_convolution ht hg hM, ← funext hφ,
    Measure.integral_comp_inv_smul_of_nonneg _ _ hst.le, hφ_def, integral_smul, smul_smul,
    hscalar]

/-- **Cancellation in the derivatives of a heat convolution.** Since `∫ D^m K_t = 0` for `m ≥ 1`,
the value of `g` at the base point can be subtracted under the integral:
`D^m (K_t ⋆ g)(x) = ∫ D^m K_t(z) ⊗ (g(x - z) - g(x)) dz`. -/
theorem iteratedFDeriv_heatKernel_convolution_eq_integral_sub [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) {m : ℕ} (hm : m ≠ 0) (x : E) :
    iteratedFDeriv ℝ m (heatKernel t ⋆ g) x =
      ∫ z, (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z) - g x) := by
  have hL : ∫ z : E, (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g x) = 0 := by
    have := ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).flip
      (g x)).integral_comp_comm (integrable_iteratedFDeriv_heatKernel (E := E) ht m)
    simp only [flip_apply, ContinuousMultilinearMap.smulRightL_apply] at this
    rw [this, integral_iteratedFDeriv_heatKernel_eq_zero ht hm]
    ext v
    simp
  have hsub : ∀ z : E, (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z) - g x) =
      (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g (x - z)) -
        (iteratedFDeriv ℝ m (heatKernel t) z).smulRight (g x) := fun z => by
    ext v
    simp [smul_sub]
  rw [iteratedFDeriv_heatKernel_convolution ht hg hM, integral_congr_ae (ae_of_all _ hsub),
    integral_sub (integrable_smulRight_iteratedFDeriv_heatKernel ht hg hM m x), hL, sub_zero]
  exact ((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin m => E) F).flip
    (g x)).integrable_comp (integrable_iteratedFDeriv_heatKernel ht m)

/-- **Hölder bounds on the derivatives of a heat convolution.** If `g` is bounded and `α`-Hölder
with constant `H`, then for `m ≥ 1` and `t > 0`,
`‖D^m (K_t ⋆ g)(x)‖ ≤ H ∫ ‖D^m K_t(z)‖ ‖z‖^α dz`. By
`TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le` the right side is
`O(H t^((α - m) / 2))`, which for `m = 2` is integrable in time near `t = 0` when `α > 0`. -/
theorem norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) {H α : ℝ≥0} (hH : HolderWith H α g)
    {m : ℕ} (hm : m ≠ 0) (x : E) :
    ‖iteratedFDeriv ℝ m (heatKernel t ⋆ g) x‖ ≤
      H * ∫ z, ‖iteratedFDeriv ℝ m (heatKernel t : E → ℝ) z‖ * ‖z‖ ^ (α : ℝ) := by
  rw [iteratedFDeriv_heatKernel_convolution_eq_integral_sub ht hg hM hm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((integrable_norm_iteratedFDeriv_heatKernel_mul_rpow ht m α.coe_nonneg).const_mul _)
    (ae_of_all _ fun z => by simpa using hH.norm_smulRight_sub_le _ (x - z) x)

/-- **Hölder bound on the Laplacian of a heat convolution.** The Laplacian of the heat convolution
of a bounded `α`-Hölder function with constant `H` is `O(H τ^((α - 2)/2))`, uniformly in the
function. -/
theorem exists_norm_laplacian_heatKernel_convolution_le [CompleteSpace F] {α : ℝ≥0} :
    ∃ C ≥ 0, ∀ {g : E → F} {M τ : ℝ} {H : ℝ≥0}, AEStronglyMeasurable g → (∀ᵐ y, ‖g y‖ ≤ M) →
      HolderWith H α g → 0 < τ → ∀ x,
        ‖Δ (heatKernel τ ⋆ g) x‖ ≤ C * H * τ ^ (((α : ℝ) - 2) / 2) := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) 2 α.coe_nonneg
  refine ⟨finrank ℝ E * C, by positivity, fun {g M τ H} hg hM hH hτ x => ?_⟩
  have h₁ := norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hτ hg hM hH
    two_ne_zero x
  have h₂ := mul_le_mul_of_nonneg_left (hC τ hτ) H.coe_nonneg
  push_cast at h₂
  have h₃ : ‖fderiv ℝ (fderiv ℝ (heatKernel τ ⋆ g)) x‖ =
      ‖iteratedFDeriv ℝ 2 (heatKernel τ ⋆ g) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  refine (norm_laplacian_le _ x).trans ?_
  calc _ ≤ (finrank ℝ E : ℝ) * (H * (C * τ ^ (((α : ℝ) - 2) / 2))) := by
        rw [h₃]
        gcongr
        linarith
    _ = _ := by ring

/-- **Time differences of the derivatives of a heat convolution.** If `g` is bounded and
`α`-Hölder with constant `H`, then for `m ≥ 1` and times `a, b > 0`,
`‖D^m (K_b ⋆ g)(x) - D^m (K_a ⋆ g)(x)‖ ≤ H ∫ ‖D^m K_b(z) - D^m K_a(z)‖ ‖z‖^α dz`. By
`TauCeti.exists_integral_norm_iteratedFDeriv_heatKernel_sub_mul_rpow_le` the right side is
`O(H (b - a) a^((α - m - 2) / 2))` when `a ≤ b ≤ 2a`. -/
theorem norm_iteratedFDeriv_heatKernel_convolution_sub_le_of_holderWith [CompleteSpace F]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M)
    {H α : ℝ≥0} (hH : HolderWith H α g) {m : ℕ} (hm : m ≠ 0) (x : E) :
    ‖iteratedFDeriv ℝ m (heatKernel b ⋆ g) x - iteratedFDeriv ℝ m (heatKernel a ⋆ g) x‖ ≤
      H * ∫ z, ‖iteratedFDeriv ℝ m (heatKernel b : E → ℝ) z -
        iteratedFDeriv ℝ m (heatKernel a) z‖ * ‖z‖ ^ (α : ℝ) := by
  have hw : Integrable fun z : E => ‖iteratedFDeriv ℝ m (heatKernel b : E → ℝ) z -
      iteratedFDeriv ℝ m (heatKernel a) z‖ * ‖z‖ ^ (α : ℝ) := by
    refine ((integrable_norm_iteratedFDeriv_heatKernel_mul_rpow hb m α.coe_nonneg).add
      (integrable_norm_iteratedFDeriv_heatKernel_mul_rpow ha m α.coe_nonneg)).mono' ?_
      (ae_of_all _ fun z => ?_)
    · exact ((((contDiff_heatKernel (k := ⊤) b).continuous_iteratedFDeriv le_top).sub
        ((contDiff_heatKernel (k := ⊤) a).continuous_iteratedFDeriv le_top)).norm.mul
          (continuous_norm.rpow_const fun _ => Or.inr α.coe_nonneg)).aestronglyMeasurable
    · rw [norm_mul, norm_norm, norm_of_nonneg (by positivity), Pi.add_apply, ← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
  rw [iteratedFDeriv_heatKernel_convolution_eq_integral_sub hb hg hM hm,
    iteratedFDeriv_heatKernel_convolution_eq_integral_sub ha hg hM hm,
    ← integral_sub (integrable_smulRight_iteratedFDeriv_heatKernel_sub hb hg hM m x)
      (integrable_smulRight_iteratedFDeriv_heatKernel_sub ha hg hM m x), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hw.const_mul _) (ae_of_all _ fun z => ?_)
  have hsub : (iteratedFDeriv ℝ m (heatKernel b) z).smulRight (g (x - z) - g x) -
      (iteratedFDeriv ℝ m (heatKernel a) z).smulRight (g (x - z) - g x) =
        (iteratedFDeriv ℝ m (heatKernel b) z - iteratedFDeriv ℝ m (heatKernel a) z).smulRight
          (g (x - z) - g x) := by
    ext v
    simp [sub_smul]
  rw [hsub]
  simpa using hH.norm_smulRight_sub_le _ (x - z) x

/-- **The Laplacian of a heat convolution.** For `t > 0` and `g` measurable and essentially
bounded, `Δ (K_t ⋆ g) = ΔK_t ⋆ g`. -/
theorem laplacian_heatKernel_convolution [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) :
    Δ (heatKernel t ⋆ g) x = (Δ (heatKernel t : E → ℝ) ⋆ g) x := by
  have hD₂ := integrable_iteratedFDeriv_heatKernel (E := E) ht 2
  -- The Laplacian is a continuous linear functional of the Hessian.
  rw [laplacian_eq_traceL_iteratedFDeriv, iteratedFDeriv_convolution_left_of_dominated
    (lsmul ℝ ℝ) (N := ⊤) (contDiff_heatKernel t)
    (fun k _ => exists_integrable_norm_iteratedFDeriv_heatKernel_add_le ht k 1) hg hM le_top,
    convolution_def, ← integral_comp_comm _
      (convolutionExists_of_integrable_of_ae_norm_le _ hD₂ hg hM x), convolution_def]
  congr 1 with y
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, lsmul_apply, Finset.sum_smul]
  simp

/-- **The heat equation.** For `t > 0` and `g` measurable and essentially bounded, the function
`u(s, x) = (K_s ⋆ g)(x)` satisfies `∂ₜu(t, x) = Δu(t, x)`. -/
theorem hasDerivAt_heatKernel_convolution [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) :
    HasDerivAt (fun s => (heatKernel s ⋆ g) x) (Δ (heatKernel t ⋆ g) x) t := by
  obtain ⟨B, hB₀, hB⟩ := exists_abs_laplacian_heatKernel_le (E := E) ht
  have hg' : ∀ᵐ y, ‖g (x - y)‖ ≤ M :=
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E) x).ae hM
  have hball : ∀ s ∈ ball t (t / 2), t / 2 < s ∧ s ≤ 2 * t := fun s hs => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hΔ : Continuous (Δ (heatKernel t : E → ℝ)) := by
    rw [show Δ (heatKernel t : E → ℝ) = fun y => (‖y‖ ^ 2 / (4 * t ^ 2) -
      finrank ℝ E / (2 * t)) * heatKernel t y from funext (laplacian_heatKernel t)]
    exact (((continuous_norm.pow 2).div_const _).sub continuous_const).mul
      (contDiff_heatKernel t (k := 0)).continuous
  rw [laplacian_heatKernel_convolution ht hg hM x]
  simp only [convolution_def]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t (half_pos ht))
    (F' := fun s y => lsmul ℝ ℝ (Δ (heatKernel s : E → ℝ) y) (g (x - y)))
    (bound := fun y => B * heatKernel (2 * (2 * t)) y * M)
    (Filter.Eventually.of_forall fun s => (contDiff_heatKernel s (k := 0)).continuous
      |>.aestronglyMeasurable.convolution_integrand_snd (lsmul ℝ ℝ) hg x)
    (convolutionExists_of_integrable_of_ae_norm_le _ (integrable_heatKernel ht) hg hM x)
    (hΔ.aestronglyMeasurable.convolution_integrand_snd (lsmul ℝ ℝ) hg x) ?_
    (((integrable_heatKernel (by positivity)).const_mul B).mul_const M) ?_).2
  · filter_upwards [hg'] with y hy s hs
    rw [lsmul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hB s (hball s hs).1 (hball s hs).2 y) hy (norm_nonneg _)
      (mul_nonneg hB₀ (heatKernel_pos (by positivity) y).le)
  · refine Filter.Eventually.of_forall fun y s hs => ?_
    simpa only [lsmul_apply] using
      (hasDerivAt_heatKernel (by linarith [(hball s hs).1]) y).smul_const (g (x - y))

/-- **The heat equation for `C²` data with compact support.** For `t > 0`, the function
`s ↦ (K_s ⋆ φ)(x)` has derivative `(K_t ⋆ Δ φ)(x)` at `t`: the Laplacian of the solution is the
heat convolution of the Laplacian of the datum. -/
theorem hasDerivAt_heatKernel_convolution_of_hasCompactSupport [CompleteSpace F] {φ : E → F}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => (heatKernel s ⋆ φ) x) ((heatKernel t ⋆ Δ φ) x) t := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have h := hasDerivAt_heatKernel_convolution ht hφ.continuous.aestronglyMeasurable
    (ae_of_all _ hC) x
  rwa [hc.laplacian_convolution_right _ (integrable_heatKernel ht).locallyIntegrable hφ] at h

/-- **Duhamel's formula for the heat equation.** For `φ` of class `C²` with compact support and
`t > 0`, `(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds` at every point `x`. -/
theorem heatKernel_convolution_sub_eq_integral [CompleteSpace F] {φ : E → F}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (ht : 0 < t) (x : E) :
    (heatKernel t ⋆ φ) x - φ x = ∫ s in 0..t, (heatKernel s ⋆ Δ φ) x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  obtain ⟨C₂, hC₂⟩ := hφ.continuous_laplacian.bounded_above_of_compact_support hc.laplacian
  -- The integrand is continuous at positive times, being differentiable there, and bounded.
  have hcont : ContinuousOn (fun s => (heatKernel s ⋆ Δ φ) x) (Ioi 0) := fun s hs =>
    (hasDerivAt_heatKernel_convolution hs hφ.continuous_laplacian.aestronglyMeasurable
      (ae_of_all _ hC₂) x).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s => (heatKernel s ⋆ Δ φ) x) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine (integrableOn_const (C := C₂) measure_Ioc_lt_top.ne).mono'
      ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_heatKernel_convolution_le hs.1 (ae_of_all _ hC₂) x
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun s hs => hasDerivAt_heatKernel_convolution_of_hasCompactSupport hφ hc hs.1 x) hint
    ?_ ?_).symm
  · exact (tendsto_heatKernel_convolution hφ.continuous.aestronglyMeasurable (ae_of_all _ hC)
      hφ.continuous.continuousAt).comp (Filter.tendsto_id.prodMk tendsto_const_nhds)
  · exact (hasDerivAt_heatKernel_convolution_of_hasCompactSupport hφ hc ht x).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds

/-- The heat convolution of a continuous function is jointly strongly measurable in time
and space. -/
theorem stronglyMeasurable_heatKernel_convolution (hg : Continuous g) :
    StronglyMeasurable fun z : ℝ × E => (heatKernel z.1 ⋆ g) z.2 := by
  have hK : Measurable fun q : ℝ × E => heatKernel q.1 q.2 := by
    simp only [heatKernel_apply]
    fun_prop
  simp only [convolution_def, lsmul_apply]
  refine StronglyMeasurable.integral_prod_right
    (f := fun (z : ℝ × E) (y : E) => heatKernel z.1 y • g (z.2 - y)) ?_
  exact (hK.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable.smul
    (hg.comp (continuous_fst.snd.sub continuous_snd)).stronglyMeasurable

end TauCeti
