/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Moving a drift off a test function

Let `b` be a vector field smooth on an open set `Ω` of Euclidean space, with divergence
`div b = tr Db`. For a test function `φ` on `Ω` and `u ∈ W^{1,2}(Ω)`, integrating
`div (φ b) = φ div b + ⟪∇φ, b⟫` against `u` moves the derivative from `φ` onto `u`:

`∫_Ω ⟪b, ∇φ⟫ u = -∫_Ω (⟪b, ∇u⟫ + (div b) u) φ`.

In terms of energy forms, the drift `b` acting on the test function becomes the drift `-b` and the
mass `-div b` acting on `u` (`TauCeti.PDE.energyFormH1_drift_ofTestFunctionₗ`). No bound on `b`
is needed, since `φ` has compact support in `Ω`. A lower-order energy form against a test function
is the integral `∫_Ω (⟪b, ∇u⟫ + c u) φ` (`TauCeti.PDE.energyFormH1_zero_ofTestFunctionₗ`); for a
constant drift `e` and two test functions it is `∫_Ω (∂_e f) g`
(`TauCeti.PDE.energyFormH1_zero_const_ofTestFunctionₗ_ofTestFunctionₗ`).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace LineDeriv

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}

/-- The lower-order energy form of `u ∈ W^{1,2}(Ω)` against a test function `φ` is
`∫_Ω (⟪b, ∇u⟫ + c u) φ`. -/
theorem energyFormH1_zero_ofTestFunctionₗ (c : EuclideanSpace ℝ ι → ℝ) (u : W1p mu Omega 2)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 0 b c u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, (⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) * φ x ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := 2) φ).mono
    fun x hx ↦ ?_)
  simp only [Pi.zero_apply, energyIntegrand_apply, matrixBilinearForm_apply, Matrix.zero_mulVec,
    dotProduct_zero, driftForm_apply, jetField_apply, massForm_apply, hx]
  ring

/-- The energy form with only a constant drift `e`, between two test functions `f` and `g`, is
`∫_Ω (∂_e f) g`. -/
theorem energyFormH1_zero_const_ofTestFunctionₗ_ofTestFunctionₗ (e : EuclideanSpace ℝ ι)
    (f g : 𝓓(Omega, ℝ)) :
    energyFormH1 0 (fun _ ↦ e) 0 (W1p.ofTestFunctionₗ mu Omega 2 f)
        (W1p.ofTestFunctionₗ mu Omega 2 g) =
      ∫ x in Omega, (∂_{e} f) x * g x ∂mu := by
  rw [energyFormH1_zero_ofTestFunctionₗ]
  refine integral_congr_ae ((gradientTestFunctionLp_apply_ae (mu := mu) 2 f).mono fun x hx ↦ ?_)
  dsimp only
  rw [W1p.gradient_ofTestFunctionₗ, hx, real_inner_comm, inner_gradient_left,
    TestFunction.lineDerivOp_apply_eq_fderiv, Pi.zero_apply, zero_mul, add_zero]

/-- The drift form of a test function against `u`, as an integral over `Ω` involving the
divergence of `φ b`. -/
private theorem energyFormH1_drift_ofTestFunctionₗ_eq_integral (hb : ContDiffOn ℝ ∞ b Omega)
    (u : W1p mu Omega 2) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 0 b 0 (W1p.ofTestFunctionₗ mu Omega 2 φ) u =
      ∫ x in Omega, (TestFunction.divergenceCLM (smulTestField hb φ) x • W1p.value u x -
        φ x * LinearMap.trace ℝ (EuclideanSpace ℝ ι)
          (fderiv ℝ b x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) * W1p.value u x) ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae (((jetField_ofTestFunctionₗ_ae (mu := mu) (p := 2) φ).and
    (ae_restrict_mem Omega.isOpen.measurableSet)).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx.1, divergenceCLM_smulTestField hb φ hx.2]
  simp only [Pi.zero_apply, energyIntegrand_apply, matrixBilinearForm_apply, Matrix.zero_mulVec,
    dotProduct_zero, driftForm_apply, jetField_apply, massForm_apply, smul_eq_mul,
    real_inner_comm (b x)]
  ring

/-- The form with drift `-b` and mass `-div b` of `u` against a test function `φ`, as an integral
over `Ω`. -/
private theorem energyFormH1_neg_ofTestFunctionₗ_eq_integral (hb : ContDiffOn ℝ ∞ b Omega)
    (u : W1p mu Omega 2) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 0 (-b) (fun x ↦ -LinearMap.trace ℝ (EuclideanSpace ℝ ι)
        (fderiv ℝ b x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) u
        (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, (-innerSL ℝ (W1p.gradient u x) (smulTestField hb φ x) -
        φ x * LinearMap.trace ℝ (EuclideanSpace ℝ ι)
          (fderiv ℝ b x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) * W1p.value u x) ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae ((jetField_ofTestFunctionₗ_ae (mu := mu) (p := 2) φ).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx]
  simp only [Pi.zero_apply, Pi.neg_apply, energyIntegrand_apply, matrixBilinearForm_apply,
    Matrix.zero_mulVec, dotProduct_zero, driftForm_apply, jetField_apply, massForm_apply,
    innerSL_apply_apply, smulTestField_apply, inner_neg_left, inner_smul_right,
    real_inner_comm (b x)]
  ring

/-- **The drift on a test function, moved onto a Sobolev function.** For a vector field `b` smooth
on `Ω`, a test function `φ` on `Ω` and `u ∈ W^{1,2}(Ω)`,
`∫_Ω ⟪b, ∇φ⟫ u = ∫_Ω (⟪-b, ∇u⟫ - (div b) u) φ`, where `div b = tr Db`. -/
theorem energyFormH1_drift_ofTestFunctionₗ (hb : ContDiffOn ℝ ∞ b Omega) (u : W1p mu Omega 2)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 0 b 0 (W1p.ofTestFunctionₗ mu Omega 2 φ) u =
      energyFormH1 0 (-b) (fun x ↦ -LinearMap.trace ℝ (EuclideanSpace ℝ ι)
        (fderiv ℝ b x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) u
        (W1p.ofTestFunctionₗ mu Omega 2 φ) := by
  set Φ := smulTestField hb φ
  set tr : EuclideanSpace ℝ ι → ℝ := fun x ↦ LinearMap.trace ℝ (EuclideanSpace ℝ ι)
    (fderiv ℝ b x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
  have hu := W1p.hasWeakFDerivOn u
  have hkey := hu.integral_divergenceCLM_smul_eq_neg_integral Φ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Omega)
      (f := fun x ↦ TestFunction.divergenceCLM Φ x • W1p.value u x) fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx
        ((TestFunction.divergenceCLM Φ).tsupport_subset h), zero_smul],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Omega)
      (f := fun x ↦ innerSL ℝ (W1p.gradient u x) (Φ x)) fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (Φ.tsupport_subset h), map_zero]] at hkey
  have htr : ContinuousOn tr Omega :=
    (LinearMap.continuous_of_finiteDimensional (LinearMap.trace ℝ (EuclideanSpace ℝ ι) ∘ₗ
      ContinuousLinearMap.coeLM ℝ)).comp_continuousOn
      (hb.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp))
  have hφtr : Continuous fun x ↦ φ x * tr x :=
    ((contDiffOn_zero.2 htr).contDiff_smul_of_tsupport_subset Omega.isOpen
      (contDiffOn_zero.2 φ.continuous.continuousOn) φ.tsupport_subset).continuous
  have hA : Integrable (fun x ↦ TestFunction.divergenceCLM Φ x • W1p.value u x)
      (mu.restrict Omega) :=
    ((TestFunction.divergenceCLM Φ).integrable_smul hu.locallyIntegrableOn).restrict
  have hB : Integrable (fun x ↦ innerSL ℝ (W1p.gradient u x) (Φ x)) (mu.restrict Omega) := by
    have hΦ := (Φ.continuous.memLp_of_hasCompactSupport (μ := mu) (p := 2)
      Φ.hasCompactSupport).restrict Omega
    exact (L2.integrable_inner (𝕜 := ℝ) (W1p.gradient u) (hΦ.toLp _)).congr
      (hΦ.coeFn_toLp.mono fun x hx ↦ by simp only [hx, innerSL_apply_apply])
  have hC : Integrable (fun x ↦ φ x * tr x * W1p.value u x) (mu.restrict Omega) :=
    ((hφtr.memLp_of_hasCompactSupport (μ := mu) (p := 2)
      (φ.hasCompactSupport.mul_right)).restrict Omega).integrable_mul (Lp.memLp (W1p.value u))
  rw [energyFormH1_drift_ofTestFunctionₗ_eq_integral hb,
    energyFormH1_neg_ofTestFunctionₗ_eq_integral hb, integral_sub hA hC,
    integral_sub (f := fun x ↦ -innerSL ℝ (W1p.gradient u x) (Φ x)) hB.neg hC, integral_neg, hkey]

end TauCeti.PDE
