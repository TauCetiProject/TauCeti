/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic
public import TauCeti.Analysis.Distribution.SchwartzKernel.Operations
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Checks for quantization and its kernels

This file computes small examples of the left quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`) and of
operators given by their kernels. Each pins down a convention or separates two notions that are
easy to conflate.

* **The identity.** The symbol `1` quantizes to the identity, so on the Gaussian
  `u(x) = exp(-x²)` it gives the value `1` at `x = 0`
  (`TauCeti.QuantizationExample.quantizeSchwartzValue_id_gaussian_zero`).
* **The sign and the `2π` rescaling.** The symbol `ξ` quantizes to `D = -i ∂`, so on the same
  Gaussian it gives `2 i x exp(-x²)`, with value `2i/e` at `x = 1`
  (`TauCeti.QuantizationExample.quantizeSchwartzValue_inner_gaussian`,
  `TauCeti.QuantizationExample.quantizeSchwartzValue_inner_gaussian_one`). A wrong sign of the
  phase or a missing rescaling of the frequency would change this value.
* **The zero symbol** gives the zero operator and the zero kernel; these are the library lemmas
  `TauCeti.quantizeSchwartzValue_zero_left` and `TauCeti.quantizationKernel_zero`.
* **The identity has no function kernel.** The kernel of `Op(1)` is the Dirac mass on the
  diagonal: in positive dimension no locally integrable function `k`, in particular no smooth or
  constant one, satisfies `u(x) = ∫ k(y) u(y) dy` for all Schwartz functions `u`
  (`TauCeti.QuantizationExample.not_exists_locallyIntegrable_kernel_id`).
* **The identity is properly supported.** Its symbol has propagation at most `ε` exactly when
  `ε > 0`, so its kernel is supported on the diagonal
  (`TauCeti.QuantizationExample.hasPropagationLE_const_id_iff`), and `Op(1)` preserves the support
  of every Schwartz function
  (`TauCeti.QuantizationExample.tsupport_quantizeSchwartzValue_const_id`).
* **The constant kernel `1` on `ℝ`.** The operator with Schwartz kernel `1` sends a test function
  `ψ` to the constant distribution `∫ ψ` (`TauCeti.QuantizationExample.kernelOperator_ofFun_one`).
  It is smoothing, but for `∫ ψ = 1` the image is the constant `1`, supported on all of `ℝ`: it
  does not preserve compact supports
  (`TauCeti.QuantizationExample.dsupport_kernelOperator_ofFun_one`).
* **The Gaussian kernel `exp(-(x - y)²)` on `ℝ`.** It is smooth, with value `1/e` at `(0, 1)`,
  but its support is all of `ℝ²`, so it is not properly supported: over the point `x = 0` its
  support is the whole line
  (`TauCeti.QuantizationExample.not_isCompact_support_gaussianKernel_inter_fst_preimage`). Its
  operator sends a nonzero nonnegative test function to a positive function, which is not
  compactly supported
  (`TauCeti.QuantizationExample.not_hasCompactSupport_integral_gaussianKernel_mul`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4) and (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §5.2.
-/

public section

open scoped SchwartzMap RealInnerProductSpace LineDeriv ContDiff Distributions
open MeasureTheory Complex TopologicalSpace

noncomputable section

namespace TauCeti.QuantizationExample

/-! ### Quantizations on the Gaussian -/

/-- The Gaussian `x ↦ exp(-x²)` on the line, as a Schwartz function. -/
def gaussian : 𝓢(ℝ, ℂ) :=
  SchwartzMap.gaussian (b := 1) (by simp)

/-- The value of the Gaussian at `x` is `exp(-x²)`. -/
theorem gaussian_apply (x : ℝ) : gaussian x = cexp (-(x : ℂ) ^ 2) := by
  simp [gaussian, SchwartzMap.gaussian_apply, Real.norm_eq_abs, ← ofReal_pow, sq_abs]

/-- The derivative of the Gaussian is `-2x exp(-x²)`. -/
theorem lineDerivOp_gaussian (x : ℝ) : ∂_{(1 : ℝ)} gaussian x = -2 * x * cexp (-(x : ℂ) ^ 2) := by
  have hx : HasDerivAt (fun y : ℝ ↦ -(y : ℂ) ^ 2) (-(2 * x)) x := by
    convert ((hasDerivAt_id x).ofReal_comp.pow 2).neg using 1
    · ext y
      simp
    · norm_num
  have h : HasDerivAt (gaussian : ℝ → ℂ) (cexp (-(x : ℂ) ^ 2) * -(2 * x)) x := by
    rw [funext gaussian_apply]
    exact hx.cexp
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv, h.deriv]
  ring

/-- The symbol `1` quantizes to the identity: on the Gaussian `exp(-x²)` its value at `0`
is `1`. -/
theorem quantizeSchwartzValue_id_gaussian_zero :
    quantizeSchwartzValue (fun _ ↦ ContinuousLinearMap.id ℂ ℂ) gaussian 0 = 1 := by
  simp [gaussian_apply]

/-- The symbol `ξ` quantizes to `D = -i ∂`: on the Gaussian, `Op(ξ) exp(-x²) = 2 i x exp(-x²)`. -/
theorem quantizeSchwartzValue_inner_gaussian (x : ℝ) :
    quantizeSchwartzValue (fun p ↦ (⟪p.2, (1 : ℝ)⟫ : ℂ) • ContinuousLinearMap.id ℂ ℂ)
      gaussian x = 2 * I * x * cexp (-(x : ℂ) ^ 2) := by
  rw [quantizeSchwartzValue_inner_eq_lineDerivOp, lineDerivOp_gaussian, smul_eq_mul]
  ring

/-- At `x = 1`, `Op(ξ) exp(-x²)` has the value `2i/e`, fixing the sign of the phase and the
`2π` rescaling of the frequency. -/
theorem quantizeSchwartzValue_inner_gaussian_one :
    quantizeSchwartzValue (fun p ↦ (⟪p.2, (1 : ℝ)⟫ : ℂ) • ContinuousLinearMap.id ℂ ℂ)
      gaussian 1 = 2 * I / cexp 1 := by
  rw [quantizeSchwartzValue_inner_gaussian]
  simp [Complex.exp_neg, div_eq_mul_inv]

/-! ### The identity -/

section Identity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **The identity has no function kernel.** In positive dimension the kernel of `Op(1)` at `x`
is the Dirac mass at `x`, not a locally integrable function: no locally integrable `k`, in
particular no smooth or constant kernel, gives `Op(1) u (x) = ∫ k(y) u(y) dy` for every Schwartz
function `u`. -/
theorem not_exists_locallyIntegrable_kernel_id [Nontrivial E] (x : E) :
    ¬∃ k : E → ℂ, LocallyIntegrable k ∧ ∀ u : 𝓢(E, ℂ),
      quantizeSchwartzValue (fun _ ↦ ContinuousLinearMap.id ℂ ℂ) u x = ∫ y, k y * u y := by
  rintro ⟨k, hk, hku⟩
  -- Testing against functions supported away from `x` shows that `k` vanishes off `x`.
  have hk0 : ∀ᵐ y, y ∈ ({x}ᶜ : Set E) → k y = 0 := by
    refine isOpen_compl_singleton.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hk.locallyIntegrableOn _) fun g hg hgc hgx ↦ ?_
    have hgc' : HasCompactSupport fun y ↦ (g y : ℂ) := hgc.comp_left ofReal_zero
    have hgd : ContDiff ℝ ∞ fun y ↦ (g y : ℂ) := ofRealCLM.contDiff.comp hg
    have h := hku (hgc'.toSchwartzMap hgd)
    rw [quantizeSchwartzValue_id] at h
    simp only [HasCompactSupport.toSchwartzMap_toFun,
      image_eq_zero_of_notMem_tsupport fun hx ↦ hgx hx rfl, ofReal_zero] at h
    simpa [Complex.real_smul, mul_comm] using h.symm
  -- Since `{x}` is a null set, `k` vanishes almost everywhere, which contradicts `u(x) ≠ 0`.
  have hk0' : k =ᵐ[volume] 0 := by
    filter_upwards [hk0, compl_mem_ae_iff.2 (measure_singleton x)] with y hy hyx
    exact hy hyx
  have h := hku (SchwartzMap.gaussian (V := E) (b := 1) (by simp))
  rw [quantizeSchwartzValue_id, integral_eq_zero_of_ae
    (hk0'.mono fun y hy ↦ by simp [hy])] at h
  rw [SchwartzMap.gaussian_apply] at h
  exact Complex.exp_ne_zero _ h

variable {n : ℕ} [CompleteSpace V]

/-- **The identity is supported on the diagonal.** On a nonzero fibre the constant symbol `1` has
propagation at most `ε` exactly when `ε > 0`: its kernel lies in every neighbourhood of the
diagonal, but the open ball of radius `0` is empty, and propagation `0` would make `Op(1)` the
zero operator. -/
theorem hasPropagationLE_const_id_iff [Nontrivial V] {ε : ℝ} :
    (Symbol.const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).HasPropagationLE ε ↔ 0 < ε := by
  refine ⟨fun h ↦ not_le.1 fun hε ↦ ?_, Symbol.hasPropagationLE_const _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hu := Symbol.hasPropagationLE_iff.1 h (SchwartzMap.postcompCLM
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v)
    (SchwartzMap.gaussian (V := CoordinateSpace n) (b := 1) (by simp))) 0
    fun y hy ↦ absurd hy (by simp [Metric.ball_eq_empty.2 hε])
  simp [funext (Symbol.coefficient_const (n := n) (ContinuousLinearMap.id ℂ V)),
    hv] at hu

/-- **The identity preserves supports.** `Op(1) u` has the same support as `u`. -/
theorem tsupport_quantizeSchwartzValue_const_id (u : 𝓢(CoordinateSpace n, V)) :
    tsupport (quantizeSchwartzValue
      (Symbol.const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).coefficient u) = tsupport u := by
  rw [funext (Symbol.coefficient_const (n := n) (ContinuousLinearMap.id ℂ V)),
    funext (quantizeSchwartzValue_id u)]

end Identity

/-! ### Two smooth kernels on the line -/

section Kernels

open Distribution Set

/-- The operator with Schwartz kernel `1` on `ℝ × ℝ` sends a test function `ψ` to the constant
distribution `∫ ψ`. -/
theorem kernelOperator_ofFun_one (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    kernelOperator (Ω := ⊤) (O := ⊤) (V := ⊤) (subset_univ _)
        (ofFun ⊤ (fun _ : ℝ × ℝ ↦ (1 : ℝ)) volume ⊤) ψ =
      (∫ y, ψ y) • ofFun ⊤ (fun _ : ℝ ↦ (1 : ℝ)) volume ⊤ := by
  rw [Measure.volume_eq_prod,
    kernelOperator_ofFun _ ((locallyIntegrable_const _).locallyIntegrableOn _)]
  ext φ
  rw [smul_apply, ofFun_apply ((locallyIntegrable_const _).locallyIntegrableOn _),
    ofFun_apply ((locallyIntegrable_const _).locallyIntegrableOn _)]
  simp [integral_mul_const, mul_comm]

/-- The constant kernel `1` sends a test function of integral `1` to the constant function `1`. -/
theorem kernelOperator_ofFun_one_of_integral_eq_one {ψ : 𝓓((⊤ : Opens ℝ), ℝ)}
    (hψ : ∫ y, ψ y = 1) :
    kernelOperator (Ω := ⊤) (O := ⊤) (V := ⊤) (subset_univ _)
        (ofFun ⊤ (fun _ : ℝ × ℝ ↦ (1 : ℝ)) volume ⊤) ψ =
      ofFun ⊤ (fun _ : ℝ ↦ (1 : ℝ)) volume ⊤ := by
  rw [kernelOperator_ofFun_one, hψ, one_smul]

/-- **The constant kernel does not preserve compact supports.** The image of a test function with
nonzero integral under the operator with kernel `1` is supported on all of `ℝ`. -/
theorem dsupport_kernelOperator_ofFun_one {ψ : 𝓓((⊤ : Opens ℝ), ℝ)} (hψ : ∫ y, ψ y ≠ 0) :
    dsupport (kernelOperator (Ω := ⊤) (O := ⊤) (V := ⊤) (subset_univ _)
      (ofFun ⊤ (fun _ : ℝ × ℝ ↦ (1 : ℝ)) volume ⊤) ψ) = univ := by
  rw [kernelOperator_ofFun_one, FunLike.coe_smul, dsupport_smul_of_ne_zero hψ]
  exact univ_subset_iff.1 (by
    simpa using subset_dsupport_ofFun_const (Ω := (⊤ : Opens ℝ)) (μ := volume) (n := ⊤)
      (one_ne_zero (α := ℝ)))

/-- The Gaussian kernel `exp(-(x - y)²)` on `ℝ × ℝ`. -/
def gaussianKernel (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(p.1 - p.2) ^ 2)

/-- The Gaussian kernel is smooth. -/
theorem contDiff_gaussianKernel : ContDiff ℝ ∞ gaussianKernel := by
  unfold gaussianKernel
  fun_prop

/-- The Gaussian kernel has the value `1/e` at `(0, 1)`. -/
theorem gaussianKernel_zero_one : gaussianKernel (0, 1) = (Real.exp 1)⁻¹ := by
  norm_num [gaussianKernel, Real.exp_neg]

/-- The Gaussian kernel vanishes nowhere. -/
theorem support_gaussianKernel : Function.support gaussianKernel = univ :=
  eq_univ_of_forall fun _ ↦ (Real.exp_pos _).ne'

/-- **The Gaussian kernel is not properly supported.** Over the point `x = 0` its support is the
whole line, which is not compact. -/
theorem not_isCompact_support_gaussianKernel_inter_fst_preimage :
    ¬IsCompact (Function.support gaussianKernel ∩ Prod.fst ⁻¹' {0}) := by
  intro h
  refine noncompact_univ ℝ ?_
  have himage : Prod.snd '' (Function.support gaussianKernel ∩ Prod.fst ⁻¹' {0}) = univ :=
    eq_univ_of_forall fun y ↦ ⟨(0, y), by simp [support_gaussianKernel], rfl⟩
  exact himage ▸ h.image continuous_snd

/-- The operator with the Gaussian kernel sends a nonzero nonnegative test function to a
positive function. -/
theorem integral_gaussianKernel_mul_pos {ψ : 𝓓((⊤ : Opens ℝ), ℝ)} (hψ : ∀ y, 0 ≤ ψ y)
    {y₀ : ℝ} (hy₀ : ψ y₀ ≠ 0) (x : ℝ) : 0 < ∫ y, gaussianKernel (x, y) * ψ y :=
  ((contDiff_gaussianKernel.continuous.comp (Continuous.prodMk_right x)).mul
      ψ.contDiff.continuous).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    ψ.hasCompactSupport.mul_left (fun y ↦ mul_nonneg (Real.exp_pos _).le (hψ y))
    (mul_ne_zero (Real.exp_pos _).ne' hy₀)

/-- **The Gaussian kernel does not preserve compact supports.** -/
theorem not_hasCompactSupport_integral_gaussianKernel_mul {ψ : 𝓓((⊤ : Opens ℝ), ℝ)}
    (hψ : ∀ y, 0 ≤ ψ y) {y₀ : ℝ} (hy₀ : ψ y₀ ≠ 0) :
    ¬HasCompactSupport fun x ↦ ∫ y, gaussianKernel (x, y) * ψ y := by
  intro h
  refine noncompact_univ ℝ (h.isCompact.of_isClosed_subset isClosed_univ fun x _ ↦ ?_)
  exact subset_tsupport _ (integral_gaussianKernel_mul_pos hψ hy₀ x).ne'

end Kernels

end TauCeti.QuantizationExample
