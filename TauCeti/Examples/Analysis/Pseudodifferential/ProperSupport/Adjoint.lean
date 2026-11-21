/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Adjoint.KernelCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.Pseudodifferential.Kernel
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Checks of the explicit properly cut-off adjoint

The examples distinguish conjugation, reversal, position growth and coefficient derivatives.
An imaginary cutoff on the zero-dimensional source gives opposite signs for the operator and
its adjoint, also for a nonzero vector in the infinite-dimensional Hilbert model l².
A nonlocal compact smoothing convolution detects reversal of an asymmetric real cutoff by a
strictly positive value versus zero. The coefficient exp(norm²) is not a uniform symbol.
Arbitrary positive differential orders include their lower-order coefficient corrections.
All operators use the original native test-function spaces and continuous maps.
-/

public section
noncomputable section

open MeasureTheory Real FourierTransform TopologicalSpace ComplexConjugate Filter
open scoped SchwartzMap RealInnerProductSpace ContDiff Distributions LineDeriv Topology

namespace TauCeti.Symbol.AdjointKernelCutoffExamples

section Models

variable {n : ℕ}

/-- The native Gaussian in a scalar operator coefficient model. -/
private def gaussianCoefficient : 𝓢(CoordinateSpace n, ℂ →L[ℂ] ℂ) :=
  SchwartzMap.postcompCLM
    (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).toLinearIsometry.toContinuousLinearMap
    (SchwartzMap.gaussian (b := (1 : ℂ)) (by norm_num))

/-- A smoothing native Gaussian symbol, available at every real order. -/
def gaussianSymbol (n : ℕ) (m : ℝ) : Symbol n ℂ ℂ m :=
  Symbol.ofSchwartzFrequency m gaussianCoefficient

/-- A concrete smooth, unbounded position coefficient with no temperate-growth assumption. -/
def exponentialSymbol (n : ℕ) : Symbol n ℂ ℂ 0 :=
  Symbol.cutoff ℂ (Real.contDiff_exp.comp (contDiff_norm_sq ℝ))

/-- Its coefficient grows as exp of the squared norm. -/
@[simp]
theorem coefficient_exponentialSymbol (x ξ : CoordinateSpace n) :
    (exponentialSymbol n).coefficient (x, ξ) =
      (Real.exp (‖x‖ ^ 2) : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  rw [exponentialSymbol, Symbol.coefficient_cutoff]
  exact (algebraMap_smul ℂ _ _).symm

end Models

section Multiplication

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The quantization client uses the original Schwartz input and spatial coefficient. -/
private theorem quantize_kernelCutoff_ofSpatial (χ : 𝓢(CoordinateSpace n, ℂ))
    (f : CoordinateSpace n → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (Symbol.kernelCutoff χ (Symbol.ofSpatial f hf)).coefficient u x =
      χ 0 • f x (u x) := by
  rw [quantizeSchwartzValue_congr_left (b := fun p ↦ χ 0 • f p.1)
    (fun ξ ↦ Symbol.coefficient_kernelCutoff_ofSpatial χ f hf x ξ)]
  exact quantizeSchwartzValue_comp_fst (fun y ↦ χ 0 • f y) u x

/-- The nonuniform exponential example acts on native tests by the smooth multiplier. -/
theorem quantize_exponentialSymbol {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ₀ : χ 0 = 1) {R : ℝ} (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) (x : CoordinateSpace n) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR (exponentialSymbol n)) u x =
        Real.exp (‖x‖ ^ 2) • u x := by
  rw [Symbol.quantizeTestFunctionCLM_apply]
  have hc (ξ : CoordinateSpace n) :
      (Symbol.kernelCutoff χ (exponentialSymbol n)).coefficient (x, ξ) =
        (Real.exp (‖x‖ ^ 2) : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
    rw [Symbol.coefficient_kernelCutoff]
    simp only [coefficient_exponentialSymbol]
    rw [integral_smul_const, SchwartzMap.integral_fourier_eq, hχ₀, one_smul]
  rw [quantizeSchwartzValue_congr_left
    (b := fun p ↦ (Real.exp (‖p.1‖ ^ 2) : ℂ) • ContinuousLinearMap.id ℂ ℂ) hc]
  have h := quantizeSchwartzValue_comp_fst
    (fun y : CoordinateSpace n ↦ (Real.exp (‖y‖ ^ 2) : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    (u.hasCompactSupport.toSchwartzMap u.contDiff) x
  rw [smul_apply, ContinuousLinearMap.id_apply,
    HasCompactSupport.toSchwartzMap_toFun] at h
  exact h.trans (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- The explicit adjoint on the nonuniform exponential coefficient is the same native multiplier.
No Schwartz endomorphism or temperate growth of the position coefficient is assumed. -/
theorem adjoint_exponentialSymbol {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχ₀ : χ 0 = 1) {R : ℝ}
    (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (v : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff hχ hχR (exponentialSymbol n)) v =
      TestFunction.smulLeftCLM (Real.contDiff_exp.comp (contDiff_norm_sq ℝ)) v := by
  apply TestFunction.eq_of_forall_integral_inner_eq (𝕜 := ℂ) (μ := volume)
  intro u
  rw [← Symbol.integral_inner_quantizeTestFunctionCLM_adjointKernelCutoff hχ hχR]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [quantize_exponentialSymbol hχ₀ hχR, TestFunction.smulLeftCLM_apply]
  simp only [Function.comp_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal]

/-- The exponential position coefficient is genuinely outside the uniform symbol class. -/
theorem not_isUniform_exponentialSymbol : ¬(exponentialSymbol 1).IsUniform := by
  intro h
  obtain ⟨C, hC, hb⟩ := h.exists_bound_coefficient
  let x : CoordinateSpace 1 := (C + 1) • EuclideanSpace.single 0 1
  have hx : ‖x‖ = C + 1 := by
    simp [x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0
      ≤ C + 1)]
  have hh := hb x 0
  simp only [coefficient_exponentialSymbol, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ContinuousLinearMap.norm_id,
    mul_one, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, zero_div, Real.rpow_zero] at hh
  have he := Real.add_one_le_exp (‖x‖ ^ 2)
  rw [hx] at he hh
  nlinarith

end Multiplication

section ZeroDimension

/-- The constant imaginary cutoff is compactly supported on the zero-dimensional model. -/
def imaginaryCutoff : 𝓢(CoordinateSpace 0, ℂ) :=
  (HasCompactSupport.of_compactSpace (f := fun _ : CoordinateSpace 0 ↦ Complex.I)).toSchwartzMap
    contDiff_const

/-- This cutoff is imaginary rather than real. -/
@[simp]
theorem imaginaryCutoff_apply (x : CoordinateSpace 0) : imaginaryCutoff x = Complex.I := by
  rw [imaginaryCutoff, HasCompactSupport.toSchwartzMap_toFun]

/-- Compactness here is literal compactness of the zero-dimensional source. -/
theorem compact_imaginaryCutoff : HasCompactSupport imaginaryCutoff :=
  HasCompactSupport.of_compactSpace _

/-- The support lies in the full unit propagation ball on the model. -/
theorem imaginaryCutoff_support : Function.support imaginaryCutoff ⊆ Metric.ball 0 1 := by
  intro x _
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The cutoff quantizes the scalar identity to multiplication by i. -/
theorem quantize_imaginaryCutoff
    (u : 𝓓((⊤ : Opens (CoordinateSpace 0)), V)) (x : CoordinateSpace 0) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_kernelCutoff imaginaryCutoff imaginaryCutoff_support
        (Symbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ V) contDiff_const)) u x =
      Complex.I • u x := by
  rw [Symbol.quantizeTestFunctionCLM_apply, quantize_kernelCutoff_ofSpatial,
    imaginaryCutoff_apply, ContinuousLinearMap.id_apply, HasCompactSupport.toSchwartzMap_toFun]

/-- The explicit left adjoint gives -i, so a missing cutoff conjugation would be detected. -/
theorem adjoint_imaginaryCutoff
    (v : 𝓓((⊤ : Opens (CoordinateSpace 0)), V)) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff compact_imaginaryCutoff
        imaginaryCutoff_support
        (Symbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ V) contDiff_const)) v =
      (-Complex.I) • v := by
  apply TestFunction.eq_of_forall_integral_inner_eq (𝕜 := ℂ) (μ := volume)
  intro u
  rw [← Symbol.integral_inner_quantizeTestFunctionCLM_adjointKernelCutoff
    compact_imaginaryCutoff imaginaryCutoff_support]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [quantize_imaginaryCutoff]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_I, smul_apply]

end ZeroDimension

section Edges

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A constant on the zero-dimensional source is a native compactly supported test. -/
def zeroDimensionalTest (v : V) : 𝓓((⊤ : Opens (CoordinateSpace 0)), V) where
  toFun := fun _ ↦ v
  contDiff' := contDiff_const
  hasCompactSupport' := HasCompactSupport.of_compactSpace _
  tsupport_subset' := Set.subset_univ _

omit [CompleteSpace V] in
/-- The zero-dimensional native test retains the chosen coefficient vector. -/
@[simp]
theorem zeroDimensionalTest_apply (v : V) (x : CoordinateSpace 0) :
    zeroDimensionalTest v x = v := by
  rfl

/-- A nonzero infinite-dimensional l² coefficient tests the adjoint sign. -/
theorem infiniteHilbert_adjoint_nonzero :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff compact_imaginaryCutoff
        imaginaryCutoff_support
        (Symbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ (lp (fun _ : ℕ ↦ ℂ) 2))
          contDiff_const))
      (zeroDimensionalTest (lp.single 2 0 (1 : ℂ))) ≠ 0 := by
  rw [adjoint_imaginaryCutoff]
  apply smul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  intro h
  have he := congrArg
    (fun u : 𝓓((⊤ : Opens (CoordinateSpace 0)), lp (fun _ : ℕ ↦ ℂ) 2) ↦ u 0) h
  -- The test constructor has the constant underlying function; this avoids lp instance
  -- inference through the generic evaluation rewrite.
  change lp.single 2 0 (1 : ℂ) = (0 : lp (fun _ : ℕ ↦ ℂ) 2) at he
  have hh := congrArg (fun v : lp (fun _ : ℕ ↦ ℂ) 2 ↦ v 0) he
  simp only [lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply, one_ne_zero] at hh

/-- Rank zero uses the zero-dimensional Hilbert coefficient and native operator. -/
theorem rankZero_adjoint
    (u : 𝓓((⊤ : Opens (CoordinateSpace 0)),
      EuclideanSpace ℂ (Fin 0))) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff compact_imaginaryCutoff
        imaginaryCutoff_support
        (Symbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 0)))
          contDiff_const)) u = 0 := by
  rw [adjoint_imaginaryCutoff]
  apply TestFunction.ext
  intro x
  exact Subsingleton.elim _ _

end Edges

section Convolution

/-- A compact smoothing kernel, constant one on a ball of radius two. -/
def kernelBump : ContDiffBump (0 : CoordinateSpace 1) := ⟨2, 3, by norm_num, by norm_num⟩

/-- The asymmetric cutoff has its support in a strictly positive interval. -/
def positiveBump : ContDiffBump (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := ⟨1 / 4, 1 / 2,
  by norm_num, by norm_num⟩

/-- A real compact bump in the native complex Schwartz carrier. -/
private def bumpSchwartz {c : CoordinateSpace 1} (b : ContDiffBump c) : 𝓢(CoordinateSpace 1, ℂ) :=
  (b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

/-- Actual values of a native bump after complexification of its scalar values. -/
@[simp]
private theorem bumpSchwartz_apply {c : CoordinateSpace 1} (b : ContDiffBump c)
    (x : CoordinateSpace 1) : bumpSchwartz b x = (b x : ℂ) := by
  rw [bumpSchwartz, HasCompactSupport.toSchwartzMap_toFun, Function.comp_apply,
    Complex.ofRealCLM_apply]

/-- The compact complex-valued convolution kernel. -/
def convolutionKernel : 𝓢(CoordinateSpace 1, ℂ) := bumpSchwartz kernelBump

/-- The real asymmetric cutoff, as a complex-valued Schwartz function. -/
def asymmetricCutoff : 𝓢(CoordinateSpace 1, ℂ) := bumpSchwartz positiveBump

/-- The complex kernel retains the real bump values. -/
@[simp]
theorem convolutionKernel_apply (x : CoordinateSpace 1) :
    convolutionKernel x = (kernelBump x : ℂ) := by
  exact bumpSchwartz_apply kernelBump x

/-- The asymmetric complex cutoff retains the positive real bump values. -/
@[simp]
theorem asymmetricCutoff_apply (x : CoordinateSpace 1) :
    asymmetricCutoff x = (positiveBump x : ℂ) := by
  exact bumpSchwartz_apply positiveBump x

/-- The native compact bump remains compact after scalar complexification. -/
private theorem compact_bumpSchwartz {c : CoordinateSpace 1} (b : ContDiffBump c) :
    HasCompactSupport (bumpSchwartz b) := by
  have h : (bumpSchwartz b : CoordinateSpace 1 → ℂ) = fun x ↦ (b x : ℂ) :=
    funext (bumpSchwartz_apply b)
  rw [h]
  exact b.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The convolution kernel has compact support. -/
theorem compact_convolutionKernel : HasCompactSupport convolutionKernel :=
  compact_bumpSchwartz kernelBump

/-- The asymmetric cutoff has compact support. -/
theorem compact_asymmetricCutoff : HasCompactSupport asymmetricCutoff :=
  compact_bumpSchwartz positiveBump

/-- The kernel is identically one on the indicated closed ball. -/
private theorem kernelBump_one {x : CoordinateSpace 1} (hx : ‖x‖ ≤ 2) : kernelBump x = 1 := by
  apply kernelBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, kernelBump] using hx

/-- At the centre the cutoff has a genuinely nonzero value. -/
@[simp]
private theorem positiveBump_e : positiveBump (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = 1 := by
  apply positiveBump.one_of_mem_closedBall
  simp [Metric.mem_closedBall, positiveBump]

/-- The exact open support ball of the asymmetric bump. -/
theorem support_positiveBump : Function.support positiveBump =
    Metric.ball (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (1 / 2) := by
  rw [positiveBump.support_eq]
  rfl

/-- The opposite half-line never meets the cutoff support. -/
private theorem positiveBump_neg_mul (x : CoordinateSpace 1) : positiveBump (-x) * positiveBump
  x = 0 := by
  by_cases hx : positiveBump x = 0
  · rw [hx, mul_zero]
  have hxp : x ∈ Metric.ball (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (1 / 2) := by
    rw [← support_positiveBump]
    exact hx
  have hdist : dist (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (-(EuclideanSpace.single (0 :
    Fin 1) (1 : ℝ))) = 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)),
      norm_smul, PiLp.norm_single, norm_one]
    norm_num
  have hd := Metric.ball_disjoint_ball (x := (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) (y :=
    -(EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    (δ := (1 / 2 : ℝ)) (ε := (1 / 2 : ℝ)) (by rw [hdist]; norm_num)
  have hn : -x ∉ Metric.ball (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (1 / 2) := by
    intro hn
    have hxneg : x ∈ Metric.ball (-(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) (1 / 2) := by
      have heq : x - -(EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = -(-x -
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) := by abel
      simpa only [Metric.mem_ball, dist_eq_norm, heq, norm_neg] using hn
    exact Set.disjoint_left.1 hd hxp hxneg
  have hz : positiveBump (-x) = 0 := by
    by_contra hz
    exact hn (by
      rw [← support_positiveBump]
      exact hz)
  rw [hz, zero_mul]

/-- The angular-frequency rescaling is an original continuous linear equivalence. -/
private def inverseAngularScale : CoordinateSpace 1 ≃L[ℝ] CoordinateSpace 1 :=
  (Units.mk0 ((2 * π)⁻¹) (inv_ne_zero Real.two_pi_pos.ne')) • ContinuousLinearEquiv.refl ℝ _

/-- The rescaling exactly cancels the native angular frequency. -/
private theorem inverseAngularScale_apply (ζ : CoordinateSpace 1) :
    inverseAngularScale ((2 * π) • ζ) = ζ := by
  -- The unit action on the identity equivalence is the original real scalar action.
  change (2 * π)⁻¹ • ((2 * π) • ζ) = ζ
  rw [smul_smul, inv_mul_cancel₀ Real.two_pi_pos.ne', one_smul]

/-- A native Schwartz frequency coefficient derived from the kernel by Fourier transform. -/
private def convolutionCoefficient : 𝓢(CoordinateSpace 1, ℂ →L[ℂ] ℂ) :=
  SchwartzMap.postcompCLM
    (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).toLinearIsometry.toContinuousLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ inverseAngularScale
      (𝓕 (convolutionKernel)))

/-- The frequency coefficient uses the Fourier transform at the inverse angular scale. -/
@[simp]
private theorem convolutionCoefficient_apply (ξ : CoordinateSpace 1) (z : ℂ) :
    convolutionCoefficient ξ z =
      𝓕 (convolutionKernel) (inverseAngularScale ξ) * z := by
  simp [convolutionCoefficient, SchwartzMap.postcompCLM_apply,
    ContinuousLinearMap.toSpanSingletonLIE_apply, mul_comm]

/-- This is an native symbol, rather than an assumed kernel representation. -/
def convolutionSymbol (m : ℝ) : Symbol 1 ℂ ℂ m := Symbol.ofSchwartzFrequency m
  convolutionCoefficient

/-- The concrete symbol is smoothing at every real order. -/
theorem isSmoothing_convolutionSymbol (m : ℝ) : (convolutionSymbol m).IsSmoothing := by
  unfold convolutionSymbol
  exact Symbol.isSmoothing_ofSchwartzFrequency m convolutionCoefficient

/-- Its frequency slices have the Schwartz integrability used in the kernel formula. -/
private theorem integrable_convolutionSymbol (m : ℝ) (x : CoordinateSpace 1) :
    Integrable (fun ξ ↦ (convolutionSymbol m).coefficient (x, ξ)) := by
  simpa only [convolutionSymbol, Symbol.coefficient_ofSchwartzFrequency] using
    (convolutionCoefficient.integrable (μ := volume))

/-- Quantization of the explicit Fourier-rescaled symbol has the stated nonlocal compact kernel. -/
theorem kernel_convolutionSymbol (m : ℝ) (x y : CoordinateSpace 1) (z : ℂ) :
    quantizationKernel (convolutionSymbol m).coefficient x y z =
      (kernelBump (x - y) : ℂ) * z := by
  rw [quantizationKernel_def,
    ContinuousLinearMap.integral_apply
      (integrable_quantizationKernel_integrand (integrable_convolutionSymbol m x) y)]
  have he (ζ : CoordinateSpace 1) :
      (𝐞 ⟪ζ, x - y⟫ • (convolutionSymbol m).coefficient (x, (2 * π) • ζ)) z =
        (𝐞 ⟪ζ, x - y⟫ • 𝓕 (convolutionKernel) ζ) * z := by
    rw [Circle.smul_def, Circle.smul_def, smul_apply]
    simp only [convolutionSymbol, Symbol.coefficient_ofSchwartzFrequency,
      convolutionCoefficient_apply, inverseAngularScale_apply, smul_eq_mul]
    exact (mul_assoc _ _ _).symm
  simp_rw [he]
  rw [integral_mul_const]
  have hF := congrArg (fun f : 𝓢(CoordinateSpace 1, ℂ) ↦ f (x - y))
    (show 𝓕⁻ (𝓕 (convolutionKernel) : 𝓢(CoordinateSpace 1, ℂ)) =
      convolutionKernel from fourierInv_fourier_eq _)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, convolutionKernel_apply] at hF
  exact congrArg (fun q : ℂ ↦ q * z) hF

/-- The native operator equals convolution against the compact nonlocal kernel. -/
theorem quantize_convolutionSymbol (m : ℝ) (u : 𝓢(CoordinateSpace 1, ℂ))
    (x : CoordinateSpace 1) :
    quantizeSchwartzValue (convolutionSymbol m).coefficient u x =
      ∫ y, (kernelBump (x - y) : ℂ) * u y := by
  rw [quantizeSchwartzValue_eq_integral_quantizationKernel (integrable_convolutionSymbol m x)]
  simp only [kernel_convolutionSymbol]

end Convolution

section Asymmetry

/-- The same positive bump is an original native test, not only a Schwartz function. -/
def positiveTest : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ) :=
  asymmetricCutoff.toTestFunction compact_asymmetricCutoff (Set.subset_univ _)

/-- The native test retains the original real bump values. -/
@[simp]
theorem positiveTest_apply (x : CoordinateSpace 1) : positiveTest x = (positiveBump x : ℂ) := by
  simp only [positiveTest, SchwartzMap.coe_toTestFunction, asymmetricCutoff_apply]

/-- The kernel-cutoff quantization is the stated absolutely convergent kernel integral. -/
theorem quantize_cutoff_convolution (χ : 𝓢(CoordinateSpace 1, ℂ)) (m : ℝ)
    (u : 𝓢(CoordinateSpace 1, ℂ)) (x : CoordinateSpace 1) :
    quantizeSchwartzValue (Symbol.kernelCutoff χ (convolutionSymbol m)).coefficient u x =
      ∫ y, χ (x - y) * (kernelBump (x - y) : ℂ) * u y := by
  rw [Symbol.quantizeSchwartzValue_kernelCutoff, quantize_convolutionSymbol]
  have ht : (fun y ↦ χ (x - y)).HasTemperateGrowth :=
    χ.hasTemperateGrowth.comp ((Function.HasTemperateGrowth.const x).sub
      Function.HasTemperateGrowth.id')
  simp only [SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul]
  congr 1
  funext y
  ring

/-- The unreversed cutoff gives exactly zero, because the test is on the opposite side. -/
theorem unreversed_convolution_zero (m : ℝ) :
    quantizeSchwartzValue
      (Symbol.kernelCutoff (asymmetricCutoff) (convolutionSymbol m)).coefficient
      (asymmetricCutoff) 0 = 0 := by
  rw [quantize_cutoff_convolution]
  convert integral_zero (CoordinateSpace 1) ℂ using 1
  congr 1
  funext y
  simp only [zero_sub, asymmetricCutoff_apply]
  calc _ = ((positiveBump (-y) * positiveBump y : ℝ) : ℂ) * kernelBump (-y) := by
            push_cast
            ring
    _ = 0 := by rw [positiveBump_neg_mul]; simp

/-- The broad compact kernel is one wherever the positive test can be nonzero. -/
private theorem kernelBump_one_of_positiveBump_ne_zero {y : CoordinateSpace 1}
    (hy : positiveBump y ≠ 0) : kernelBump (-y) = 1 := by
  have hd : dist y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) < 1 / 2 := by
    rw [← Metric.mem_ball, ← support_positiveBump]
    exact hy
  have hn : ‖y‖ < 3 / 2 := by
    have ht : ‖y‖ ≤ dist y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) +
      ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ := by
      simpa only [dist_zero_right] using dist_triangle y (EuclideanSpace.single (0 : Fin 1) (1
        : ℝ)) 0
    rw [PiLp.norm_single, norm_one] at ht
    linarith
  apply kernelBump_one
  rw [norm_neg]
  linarith

/-- The reversed real cutoff gives a strictly positive real value on this native test. -/
theorem reversed_convolution_pos (m : ℝ) :
    0 < (quantizeSchwartzValue
      (Symbol.kernelCutoff (SchwartzMap.conjnegCLM (asymmetricCutoff)) (convolutionSymbol
        m)).coefficient
      (asymmetricCutoff) 0).re := by
  rw [quantize_cutoff_convolution]
  have he (y : CoordinateSpace 1) :
      SchwartzMap.conjnegCLM (asymmetricCutoff) (0 - y) *
        (kernelBump (0 - y) : ℂ) * asymmetricCutoff y =
          ((positiveBump y ^ 2 : ℝ) : ℂ) := by
    simp only [SchwartzMap.conjnegCLM_apply, zero_sub, neg_neg, asymmetricCutoff_apply,
      Complex.conj_ofReal]
    by_cases hy : positiveBump y = 0
    · simp [hy]
    · rw [kernelBump_one_of_positiveBump_ne_zero hy]
      push_cast
      ring
  simp_rw [he]
  rw [integral_complex_ofReal]
  apply positiveBump.continuous.pow 2 |>.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (by
      simpa only [pow_two] using positiveBump.hasCompactSupport.mul_right
        (f' := (positiveBump : CoordinateSpace 1 → ℝ))) (fun y ↦ sq_nonneg _) (x :=
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
  simp

/-- The compact spatial pairing kernel is integrable for compact test inputs. -/
private theorem integrable_convolutionPair (χ : 𝓢(CoordinateSpace 1, ℂ))
    (u v : 𝓢(CoordinateSpace 1, ℂ)) (hu : HasCompactSupport u) (hv : HasCompactSupport v) :
    Integrable (fun p : CoordinateSpace 1 × CoordinateSpace 1 ↦
      conj (u p.1) * conj (χ (p.2 - p.1)) * (kernelBump (p.1 - p.2) : ℂ) * v p.2)
      (volume.prod volume) := by
  have hc : Continuous (fun p : CoordinateSpace 1 × CoordinateSpace 1 ↦
      conj (u p.1) * conj (χ (p.2 - p.1)) * (kernelBump (p.1 - p.2) : ℂ) * v p.2) := by
    have hk := kernelBump.continuous
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro' (hu.isCompact.prod hv.isCompact)
    (isClosed_closure.prod isClosed_closure)
  intro p hp
  by_cases hx : p.1 ∈ tsupport u
  · have hy : p.2 ∉ tsupport v := fun hy ↦ hp ⟨hx, hy⟩
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, map_zero, zero_mul, zero_mul, zero_mul]

/-- The smoothing convolution's adjoint reverses and conjugates this cutoff. -/
theorem integral_inner_convolution_cutoff (χ : 𝓢(CoordinateSpace 1, ℂ)) (m : ℝ)
    (u v : 𝓢(CoordinateSpace 1, ℂ)) (hu : HasCompactSupport u) (hv : HasCompactSupport v) :
    (∫ x, inner ℂ
      (quantizeSchwartzValue (Symbol.kernelCutoff χ (convolutionSymbol m)).coefficient u x)
      (v x)) =
    ∫ x, inner ℂ (u x)
      (quantizeSchwartzValue (Symbol.kernelCutoff (SchwartzMap.conjnegCLM χ) (convolutionSymbol
        m)).coefficient
        v x) := by
  have he₁ (x : CoordinateSpace 1) : inner ℂ
      (quantizeSchwartzValue (Symbol.kernelCutoff χ (convolutionSymbol m)).coefficient u x)
      (v x) =
      ∫ y, conj (u y) * conj (χ (x - y)) * (kernelBump (y - x) : ℂ) * v x := by
    rw [quantize_cutoff_convolution, RCLike.inner_apply', ← integral_conj, ← integral_mul_const]
    congr 1
    funext y
    rw [map_mul, map_mul, Complex.conj_ofReal]
    have he : x - y = -(y - x) := by abel
    rw [he, ContDiffBump.neg]
    ring
  have he₂ (x : CoordinateSpace 1) : inner ℂ (u x)
      (quantizeSchwartzValue (Symbol.kernelCutoff (SchwartzMap.conjnegCLM χ) (convolutionSymbol
        m)).coefficient
        v x) =
      ∫ y, conj (u x) * conj (χ (y - x)) * (kernelBump (x - y) : ℂ) * v y := by
    rw [quantize_cutoff_convolution, RCLike.inner_apply', ← integral_const_mul]
    congr 1
    funext y
    rw [SchwartzMap.conjnegCLM_apply, neg_sub]
    ring
  simp_rw [he₁, he₂]
  exact (integral_integral_swap (integrable_convolutionPair χ u v hu hv)).symm

/-- The explicit adjoint symbol equals reversed convolution on test functions. -/
theorem explicitAdjoint_convolution {χ : 𝓢(CoordinateSpace 1, ℂ)}
    (hχ : HasCompactSupport χ) {R : ℝ} (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (m : ℝ) (v : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
    Symbol.quantizeTestFunctionCLM (Symbol.hasNearDiagonalKernel_adjointKernelCutoff hχ hχR
      (convolutionSymbol m)) v =
      Symbol.quantizeTestFunctionCLM
        (Symbol.hasNearDiagonalKernel_kernelCutoff (SchwartzMap.conjnegCLM χ)
          (SchwartzMap.support_conjnegCLM_subset_ball hχR)
          (convolutionSymbol m)) v := by
  apply TestFunction.eq_of_forall_integral_inner_eq (𝕜 := ℂ) (μ := volume)
  intro u
  rw [← Symbol.integral_inner_quantizeTestFunctionCLM_adjointKernelCutoff hχ hχR]
  simpa only [Symbol.quantizeTestFunctionCLM_apply, quantizeSchwartzValue_def,
    SchwartzMap.fourier_coe, TestFunction.coe_toSchwartzMapCLM,
    funext (HasCompactSupport.toSchwartzMap_toFun u.hasCompactSupport u.contDiff),
    funext (HasCompactSupport.toSchwartzMap_toFun v.hasCompactSupport v.contDiff)] using
    integral_inner_convolution_cutoff χ m (TestFunction.toSchwartzMapCLM ℂ u)
      (TestFunction.toSchwartzMapCLM ℂ v)
      (TestFunction.hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) u)
      (TestFunction.hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) v)

/-- The asymmetric cutoff is supported in the open ball of radius two about zero. -/
theorem positiveCutoff_support :
    Function.support (asymmetricCutoff) ⊆ Metric.ball 0 2 := by
  intro y hy
  have hp : positiveBump y ≠ 0 := by
    have hy' : asymmetricCutoff y ≠ 0 := hy
    simpa only [asymmetricCutoff_apply, ne_eq, Complex.ofReal_eq_zero]
      using hy'
  have hd : dist y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) < 1 / 2 := by
    rw [← Metric.mem_ball, ← support_positiveBump]
    exact hp
  have ht : ‖y‖ ≤ dist y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) + ‖(EuclideanSpace.single
    (0 : Fin 1) (1 : ℝ))‖ := by
    simpa only [dist_zero_right] using dist_triangle y (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0
  rw [PiLp.norm_single, norm_one] at ht
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-- A strictly nonzero output of the adjoint symbol detects the reversal on a native test. -/
theorem explicitAdjoint_convolution_positive (m : ℝ) :
    0 < (Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff (compact_asymmetricCutoff)
        positiveCutoff_support
        (convolutionSymbol m)) positiveTest 0).re := by
  rw [explicitAdjoint_convolution (compact_asymmetricCutoff) positiveCutoff_support,
    Symbol.quantizeTestFunctionCLM_apply]
  have he : positiveTest.hasCompactSupport.toSchwartzMap positiveTest.contDiff =
      asymmetricCutoff := by
    apply SchwartzMap.ext
    intro y
    rw [HasCompactSupport.toSchwartzMap_toFun, positiveTest_apply, asymmetricCutoff_apply]
  rw [he]
  exact reversed_convolution_pos m

/-- These are distinct native quantizations: omitting reversal changes the operator. -/
theorem reversed_convolution_ne_unreversed (m : ℝ) :
    quantizeSchwartzValue
      (Symbol.kernelCutoff (SchwartzMap.conjnegCLM (asymmetricCutoff)) (convolutionSymbol
        m)).coefficient
      (asymmetricCutoff) 0 ≠
    quantizeSchwartzValue
      (Symbol.kernelCutoff (asymmetricCutoff) (convolutionSymbol m)).coefficient
      (asymmetricCutoff) 0 := by
  rw [unreversed_convolution_zero]
  intro hz
  have h := reversed_convolution_pos m
  rw [hz, Complex.zero_re] at h
  exact (lt_irrefl 0) h

end Asymmetry

section Differential

open TauCeti.Symbol.HasNearDiagonalKernel

/-- A native classical symbol for x times an arbitrary positive-order directional derivative. -/
def coordinateDerivSymbol (k : ℕ) : Symbol 1 ℂ ℂ (k + 1 : ℕ) :=
  (ClassicalSymbol.ofDifferentialSymbol (k + 1) ({()} : Finset Unit)
    (fun _ (_ : Fin (k + 1)) ↦ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    (fun _ x ↦ (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) x •
      ContinuousLinearMap.id ℂ ℂ)
    (fun _ _ ↦ (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff.smul
      contDiff_const) (fun _ _ ↦ le_rfl)).toSymbol

/-- The concrete native quantization is exactly x times the indicated derivative. -/
theorem quantize_coordinateDerivSymbol (k : ℕ) (u : 𝓢(CoordinateSpace 1, ℂ))
    (x : CoordinateSpace 1) :
    quantizeSchwartzValue (coordinateDerivSymbol k).coefficient u x =
      (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) x • ((∂_{(EuclideanSpace.single
        (0 : Fin 1) (1 : ℝ))})^[k + 1] u) x := by
  rw [coordinateDerivSymbol, ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol]
  simp only [Finset.sum_singleton, smul_apply, ContinuousLinearMap.id_apply,
    LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp]

/-- Locality holds for all coordinateDerivSymbol orders, on the full positive propagation ball. -/
theorem nearDiagonal_coordinateDerivSymbol (k : ℕ) {R : ℝ} (hR : 0 < R) :
    (coordinateDerivSymbol k).HasNearDiagonalKernel R := by
  apply Symbol.hasNearDiagonalKernel_iff.2
  intro u x hu
  rw [quantize_coordinateDerivSymbol]
  have hz : (u : CoordinateSpace 1 → ℂ) =ᶠ[𝓝 x] 0 :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds x hR) hu
  have hd := (hz.iteratedFDeriv ℝ (k + 1)).eq_of_nhds
  rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hd]
  simp

/-- Arbitrary positive orders have the coefficient derivative in their native adjoints. -/
private theorem adjoint_coordinateDerivSymbol (k : ℕ)
    (v : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
    Symbol.adjointTestFunctionCLM (nearDiagonal_coordinateDerivSymbol k zero_lt_one) v =
      (-1 : ℂ) ^ (k + 1) •
        (∂_{(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))})^[k + 1] (TestFunction.smulLeftCLM
          (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff v) := by
  apply TestFunction.eq_of_forall_integral_inner_eq (𝕜 := ℂ) (μ := volume)
  intro u
  rw [← Symbol.integral_inner_quantizeTestFunctionCLM]
  let us := TestFunction.toSchwartzMapCLM ℂ u
  let vs := TestFunction.toSchwartzMapCLM ℂ
    (TestFunction.smulLeftCLM (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff v)
  have huv : (∫ x, inner ℂ (((∂_{(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))})^[k + 1] us) x)
    (vs x)) =
      (-1 : ℂ) ^ (k + 1) * ∫ x, inner ℂ (us x) (((∂_{(EuclideanSpace.single (0 : Fin 1) (1 :
        ℝ))})^[k + 1] vs) x) := by
    rw [SchwartzMap.integral_inner_iterate_lineDerivOp_right_eq us vs
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (k + 1), ← mul_assoc, ← mul_pow]
    simp
  calc
    _ = ∫ x, inner ℂ (((∂_{(EuclideanSpace.single (0 : Fin 1) (1 : ℝ))})^[k + 1] us) x) (vs x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Symbol.quantizeTestFunctionCLM_apply, quantize_coordinateDerivSymbol]
      have hu : u.hasCompactSupport.toSchwartzMap u.contDiff = us := by
        apply SchwartzMap.ext
        intro y
        rw [HasCompactSupport.toSchwartzMap_toFun, TestFunction.toSchwartzMapCLM_apply]
      rw [hu]
      simp only [vs, TestFunction.toSchwartzMapCLM_apply, TestFunction.smulLeftCLM_apply]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal]
    _ = _ := huv
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← (Function.Semiconj.iterate_right
        (TestFunction.toSchwartzMapCLM_lineDerivOp (𝕜 := ℂ)
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) (k + 1))
        (TestFunction.smulLeftCLM
          (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff v)]
      simp only [us, TestFunction.toSchwartzMapCLM_apply, smul_apply, inner_smul_right]

/-- The native Schwartz Leibniz formula gives the coordinate correction on original tests. -/
private theorem iterate_coordinate_smul (k : ℕ)
    (v : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
    (∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[k + 1]
        (TestFunction.smulLeftCLM (innerSL ℝ
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff v) =
      TestFunction.smulLeftCLM (innerSL ℝ
          (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff
        ((∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[k + 1] v) +
      (k + 1 : ℝ) • (∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[k] v := by
  have he (u : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
      TestFunction.toSchwartzMapCLM ℂ (TestFunction.smulLeftCLM
        (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff u) =
      SchwartzMap.smulLeftCLM ℂ
        (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
        (TestFunction.toSchwartzMapCLM ℂ u) := by
    ext x
    simp only [TestFunction.toSchwartzMapCLM_apply, TestFunction.smulLeftCLM_apply,
      SchwartzMap.smulLeftCLM_apply_apply
        (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).hasTemperateGrowth]
  have hT (j : ℕ) (u : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :=
    (Function.Semiconj.iterate_right
      (TestFunction.toSchwartzMapCLM_lineDerivOp (𝕜 := ℂ)
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) j) u
  apply TestFunction.toSchwartzMapCLM_injective (𝕜 := ℂ)
  rw [hT, he]
  have h := SchwartzMap.iterate_lineDerivOp_smulLeftCLM_clm
    (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
    (TestFunction.toSchwartzMapCLM ℂ v)
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) k
  have hs (r : ℝ) (u : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
      TestFunction.toSchwartzMapCLM ℂ (r • u) = r • TestFunction.toSchwartzMapCLM ℂ u :=
    map_smul ((TestFunction.toSchwartzMapCLM ℂ).restrictScalars ℝ) r u
  simpa only [map_add, hs, hT, he,
    innerSL_apply_apply,
    real_inner_self_eq_norm_sq, PiLp.norm_single, norm_one, one_pow, mul_one] using h

/-- The explicit left symbol realizes every positive coordinateDerivSymbol order on native tests. -/
theorem explicitAdjoint_coordinateDerivSymbol (k : ℕ) {χ : 𝓢(CoordinateSpace 1, ℂ)}
    (hχ : HasCompactSupport χ) {R : ℝ} (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (hχ₁ : Set.EqOn (χ : CoordinateSpace 1 → ℂ) 1 (Metric.ball 0 1))
    (v : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff hχ hχR (coordinateDerivSymbol k)) v =
      (-1 : ℂ) ^ (k + 1) •
        (TestFunction.smulLeftCLM
            (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff
              ((∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[k + 1] v) +
          (k + 1 : ℝ) • (∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[k] v) := by
  rw [← adjointTestFunctionCLM_eq_quantizeTestFunctionCLM_adjointKernelCutoff
    (nearDiagonal_coordinateDerivSymbol k zero_lt_one) hχ hχR hχ₁, adjoint_coordinateDerivSymbol,
    iterate_coordinate_smul]

/-- The concrete compact kernel cutoff equals one on the entire unit propagation ball. -/
private theorem kernelCutoff_one_unitBall : Set.EqOn
    (convolutionKernel : CoordinateSpace 1 → ℂ) 1 (Metric.ball 0 1) := by
  intro x hx
  rw [convolutionKernel_apply, kernelBump_one]
  · rfl
  · have hx' : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith

/-- Its compact support is contained in the open ball of radius four. -/
theorem convolutionKernel_support_subset_ball_four :
    Function.support (convolutionKernel) ⊆ Metric.ball 0 4 := by
  intro x hx
  have hx' : kernelBump x ≠ 0 := by
    have hh : convolutionKernel x ≠ 0 := hx
    simpa only [convolutionKernel_apply, ne_eq, Complex.ofReal_eq_zero]
      using hh
  have hs := hx'
  rw [← Function.mem_support, kernelBump.support_eq] at hs
  exact Metric.ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4) hs

/-- A literal fourth-order client uses the complete compact cutoff and its propagation ball. -/
theorem fourthOrder_explicitAdjoint
    (v : 𝓓((⊤ : Opens (CoordinateSpace 1)), ℂ)) :
    Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_adjointKernelCutoff (compact_convolutionKernel)
        convolutionKernel_support_subset_ball_four
        (coordinateDerivSymbol 3)) v =
      TestFunction.smulLeftCLM
          (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))).contDiff
            ((∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[4] v) +
        (4 : ℝ) • (∂_{EuclideanSpace.single (0 : Fin 1) (1 : ℝ)})^[3] v := by
  have h := explicitAdjoint_coordinateDerivSymbol 3 (compact_convolutionKernel)
    convolutionKernel_support_subset_ball_four kernelCutoff_one_unitBall v
  norm_num at h ⊢
  exact h

/-- A smoothing Gaussian frequency symbol is consumed by the actual native adjoint equality. -/
example {n : ℕ} {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ)
    {R : ℝ} (hχR : Function.support χ ⊆ Metric.ball 0 R) (m : ℝ) :
    Symbol.adjointTestFunctionCLM
        (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR (gaussianSymbol n m)) =
      Symbol.quantizeTestFunctionCLM
        (Symbol.hasNearDiagonalKernel_adjointKernelCutoff hχ hχR (gaussianSymbol n m)) :=
  Symbol.adjointTestFunctionCLM_kernelCutoff hχ hχR (gaussianSymbol n m)

/-- The actual adjoint is zero on the empty compact support stage, with nonempty base allowed. -/
example {n : ℕ} {χ : 𝓢(CoordinateSpace n, ℂ)}
    {R : ℝ} (hχR : Function.support χ ⊆ Metric.ball 0 R) (m : ℝ) :
    Symbol.adjointSupportedInCLM
      (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR (gaussianSymbol n m)) ⊥ = 0 := by
  ext f x
  have hf : f = 0 := by
    apply ContDiffMapSupportedIn.ext
    intro y
    by_contra hy
    exact f.support_subset hy
  rw [hf, map_zero]
  rfl

end Differential

section Generality

/-- The real specialization has a nonzero value on the original positive native test. -/
example : TestFunction.rieszEquiv (𝕜 := ℝ)
    (TestFunction.postcompCLM Complex.reCLM positiveTest)
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (1 : ℝ) = 1 := by
  rw [TestFunction.rieszEquiv_apply, TestFunction.postcompCLM_apply, Function.comp_apply,
    positiveTest_apply, positiveBump_e]
  simp

/-- The real inverse accepts arbitrary native dual-valued continuous tests. -/
example (φ : 𝓓^{0}((⊤ : Opens ℝ), StrongDual ℝ ℝ)) (x y : ℝ) :
    inner ℝ ((TestFunction.rieszEquiv (𝕜 := ℝ)).symm φ x) y = φ x y :=
  TestFunction.rieszEquiv_symm_apply φ x y

/-- The recovery law applies to Banach coefficient models without an inner-product structure. -/
example {n : ℕ} {m R : ℝ}
    {a : Symbol n C(Set.Icc (0 : ℝ) 1, ℂ) C(Set.Icc (0 : ℝ) 1, ℂ) m}
    (ha : a.HasNearDiagonalKernel R) (χ : 𝓢(CoordinateSpace n, ℂ))
    (hχ : Set.EqOn (χ : CoordinateSpace n → ℂ) 1 (Metric.ball 0 R))
    (u : 𝓢(CoordinateSpace n, C(Set.Icc (0 : ℝ) 1, ℂ))) (x : CoordinateSpace n) :
    quantizeSchwartzValue (Symbol.kernelCutoff χ a).coefficient u x =
      quantizeSchwartzValue a.coefficient u x :=
  ha.quantizeSchwartzValue_kernelCutoff_eq χ hχ u x

end Generality

end TauCeti.Symbol.AdjointKernelCutoffExamples
