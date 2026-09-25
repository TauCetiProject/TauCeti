/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Test functions as elements of `Lp`

This file provides the generic bridge from compactly supported test functions on an open set to
`Lp` classes. A test function belongs to every `Lᵖ` space for any measure finite on compact sets.
The construction is used by the closed-graph presentations of weak Sobolev spaces.

The bridge is linear: `TauCeti.testFunctionLp_add` and `TauCeti.testFunctionLp_smul` record that
passing to the `Lᵖ` class commutes with the vector space structure of the test functions. For an
inner product space, `TauCeti.gradientTestFunctionLp` provides the parallel construction for the
gradient. These facts make the image of `C_c^∞(Ω)` in an `Lᵖ`-based function space a subspace.

On that subspace of `L²(Ω)`, a distributional derivative bounded by the `L²` norm of test functions
extends by Hahn–Banach to a bounded functional on `L²(Ω)`, and the negative of its Riesz
representative is a weak derivative:
`TauCeti.exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] {mu : Measure E} [IsFiniteMeasureOnCompacts mu] {Omega : Opens E}

/-- A test function on `Omega` lies in every `Lᵠ(Omega)`: it is continuous with compact support. -/
theorem memLp_testFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    MemLp (phi : E → ℝ) q (mu.restrict Omega) :=
  phi.continuous.memLp_of_hasCompactSupport phi.hasCompactSupport

/-- A test function on `Omega` as an element of `Lᵠ(Omega)`. -/
def testFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) : Lp ℝ q (mu.restrict Omega) :=
  (memLp_testFunction (mu := mu) q phi).toLp phi

@[simp]
theorem testFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, testFunctionLp (mu := mu) q phi x = phi x :=
  (memLp_testFunction (mu := mu) q phi).coeFn_toLp

/-- The norm of a test function's `Lᵖ` class is its `eLpNorm`, converted to `ℝ`. -/
theorem norm_testFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := mu) q phi‖ =
      (eLpNorm (phi : E → ℝ) q (mu.restrict Omega)).toReal :=
  Lp.norm_toLp _ _

/-- The extended norm of a test function's `Lᵖ` class is its `eLpNorm` for the *ambient* measure:
the function vanishes outside `Omega`, so the restriction may be dropped. -/
theorem enorm_testFunctionLp_eq_eLpNorm (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := mu) q phi‖ₑ = eLpNorm (phi : E → ℝ) q mu := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (testFunctionLp_apply_ae q phi),
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans phi.tsupport_subset)]

@[simp]
theorem testFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (phi + psi) =
      testFunctionLp (mu := mu) q phi + testFunctionLp (mu := mu) q psi := by
  rw [testFunctionLp, testFunctionLp, testFunctionLp, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (FunLike.coe_add phi psi) x

@[simp]
theorem testFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (c • phi) = c • testFunctionLp (mu := mu) q phi := by
  rw [testFunctionLp, testFunctionLp, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (FunLike.coe_smul c phi) x

section Injectivity

variable {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [OpensMeasurableSpace F] {nu : Measure F} [IsFiniteMeasureOnCompacts nu] [nu.IsOpenPosMeasure]
  {U : Opens F}

/-- Passing from a test function to its `Lᵠ` class is injective for a measure that is positive on
nonempty open sets, such as an additive Haar measure. -/
theorem testFunctionLp_injective (q : ENNReal) :
    Function.Injective (testFunctionLp (mu := nu) (Omega := U) q) := by
  intro phi psi hLp
  have hae : (phi : F → ℝ) =ᵐ[nu.restrict U] (psi : F → ℝ) := by
    filter_upwards [testFunctionLp_apply_ae (mu := nu) q phi,
      testFunctionLp_apply_ae (mu := nu) q psi] with x hx hy
    rw [← hx, ← hy, hLp]
  have hsubset : {x | (phi : F → ℝ) x ≠ psi x} ⊆ (U : Set F) := by
    intro x hx
    by_contra hxO
    exact hx (by rw [image_eq_zero_of_notMem_tsupport fun hc => hxO (phi.tsupport_subset hc),
      image_eq_zero_of_notMem_tsupport fun hc => hxO (psi.tsupport_subset hc)])
  have hzero : nu {x | (phi : F → ℝ) x ≠ psi x} = 0 := by
    have := ae_iff.1 hae
    rwa [Measure.restrict_apply' U.isOpen.measurableSet,
      Set.inter_eq_self_of_subset_left hsubset] at this
  have hempty := (isOpen_ne_fun phi.continuous psi.continuous).measure_eq_zero_iff nu |>.1 hzero
  exact TestFunction.ext fun x => not_not.1 fun hx => Set.eq_empty_iff_forall_notMem.1 hempty x hx

end Injectivity

section Representation

variable [mu.IsOpenPosMeasure] [IsLocallyFiniteMeasure (mu.restrict Omega)]

/-- **An `L²`-bounded distributional derivative is an `L²` weak derivative.** Let `u` be locally
integrable on `Omega`. If for some `C ≥ 0` every test function `phi` on `Omega` satisfies

`|∫ ∂_v phi * u| ≤ C ‖phi‖₂`,

then `u` has a weak derivative in the direction `v` on `Omega` that lies in `L²(Omega)` and has
norm at most `C`. -/
theorem exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le {u : E → ℝ}
    (hu : LocallyIntegrableOn u Omega mu) (v : E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ phi : 𝓓(Omega, ℝ),
      |∫ x, lineDeriv ℝ (phi : E → ℝ) x v * u x ∂mu| ≤ C * (eLpNorm (phi : E → ℝ) 2 mu).toReal) :
    ∃ g : Lp ℝ 2 (mu.restrict Omega), ‖g‖ ≤ C ∧ HasWeakLineDerivOn mu Omega u g v := by
  -- The test functions, as a subspace of `L²(Omega)`.
  let T : 𝓓(Omega, ℝ) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
    { toFun := testFunctionLp 2
      map_add' := testFunctionLp_add 2
      map_smul' := testFunctionLp_smul 2 }
  have hT : Function.Injective T := testFunctionLp_injective 2
  -- The pairing `phi ↦ ∫ ∂_v phi * u`, which the hypothesis bounds by the `L²` norm of `phi`.
  let ℓ : 𝓓(Omega, ℝ) →L[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) mu u).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v)
  have hℓ : ∀ phi, ℓ phi = ∫ x, lineDeriv ℝ (phi : E → ℝ) x v * u x ∂mu := fun phi => by
    simp [ℓ, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  let e := LinearEquiv.ofInjective T hT
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ := ℓ.toLinearMap ∘ₗ e.symm.toLinearMap
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ C * ‖s‖ := by
    intro s
    obtain ⟨phi, rfl⟩ := e.surjective s
    have hnorm : ‖e phi‖ = (eLpNorm (phi : E → ℝ) 2 mu).toReal := by
      rw [← Submodule.norm_coe, LinearEquiv.ofInjective_apply, ← toReal_enorm]
      exact congrArg ENNReal.toReal (enorm_testFunctionLp_eq_eLpNorm 2 phi)
    simpa [f₀, hℓ, hnorm] using hbound phi
  obtain ⟨g', hg'f, hg'norm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous C hf₀)
  refine ⟨(InnerProductSpace.toDual ℝ _).symm (-g'), ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, norm_neg, hg'norm]
    exact LinearMap.mkContinuous_norm_le _ hC hf₀
  · set g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (mu.restrict Omega))).symm (-g')
    have hg : LocallyIntegrableOn g Omega mu :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp g).locallyIntegrable (by norm_num))
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hu, hg, fun phi => ?_⟩
    have hg'phi : g' (T phi) = ℓ phi := by
      simpa [f₀, e, LinearEquiv.ofInjective_apply] using hg'f (e phi)
    have hinner : ⟪g, T phi⟫_ℝ = ∫ x, (phi : E → ℝ) x • g x ∂mu := by
      rw [L2.inner_def, ← setIntegral_smul_eq_integral_smul phi]
      refine integral_congr_ae ?_
      filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 phi] with x hx
      simp [T, hx]
    rw [← hinner, InnerProductSpace.toDual_symm_apply, neg_apply, hg'phi, hℓ, neg_neg]
    simp only [smul_eq_mul]

end Representation

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Omega : Opens E}

/-! ### The gradient of a test function -/

/-- The gradient of a test function is smooth. -/
theorem contDiff_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    ContDiff ℝ ∞ fun x => ∇ (phi : E → ℝ) x :=
  phi.contDiff.gradient_right (by simp)

/-- The gradient of a test function is continuous. -/
@[fun_prop]
theorem continuous_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    Continuous fun x => ∇ (phi : E → ℝ) x :=
  (contDiff_gradient_testFunction phi).continuous

/-- The gradient of a test function has compact support. -/
theorem hasCompactSupport_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    HasCompactSupport fun x => ∇ (phi : E → ℝ) x :=
  (phi.hasCompactSupport.fderiv ℝ).comp_left (map_zero _)

/-- The gradient of a test function on `Ω` vanishes outside `Ω`. -/
theorem support_gradient_testFunction_subset (phi : 𝓓(Omega, ℝ)) :
    Function.support (fun x => ∇ (phi : E → ℝ) x) ⊆ (Omega : Set E) :=
  (Function.support_comp_subset (map_zero (InnerProductSpace.toDual ℝ E).symm) _).trans <|
    (subset_tsupport _).trans <| (tsupport_fderiv_subset ℝ).trans phi.tsupport_subset

variable [MeasurableSpace E] [OpensMeasurableSpace E] {mu : Measure E}
  [IsFiniteMeasureOnCompacts mu]

/-- The gradient of a test function on `Ω` is continuous with compact support, so it lies in every
`Lᵠ(Ω)`. -/
theorem memLp_gradient_testFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    MemLp (fun x => ∇ (phi : E → ℝ) x) q (mu.restrict Omega) :=
  (continuous_gradient_testFunction phi).memLp_of_hasCompactSupport
    (hasCompactSupport_gradient_testFunction phi)

/-- The gradient of a test function on `Ω`, as an element of `Lᵠ(Ω, E)`. -/
def gradientTestFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) : Lp E q (mu.restrict Omega) :=
  (memLp_gradient_testFunction (mu := mu) q phi).toLp _

@[simp]
theorem gradientTestFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, gradientTestFunctionLp (mu := mu) q phi x = ∇ (phi : E → ℝ) x :=
  (memLp_gradient_testFunction (mu := mu) q phi).coeFn_toLp

/-- The norm of a test function gradient's `Lᵖ` class is its `eLpNorm`, converted to `ℝ`. -/
theorem norm_gradientTestFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := mu) q phi‖ =
      (eLpNorm (fun x => ∇ (phi : E → ℝ) x) q (mu.restrict Omega)).toReal :=
  Lp.norm_toLp _ _

/-- The extended norm of a test function gradient's `Lᵖ` class is the `eLpNorm` of its Fréchet
derivative for the *ambient* measure: the gradient vanishes outside `Omega`, so the restriction
may be dropped, and `‖∇ phi x‖ = ‖fderiv ℝ phi x‖`. -/
theorem enorm_gradientTestFunctionLp_eq_eLpNorm_fderiv (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := mu) q phi‖ₑ =
      eLpNorm (fderiv ℝ (phi : E → ℝ)) q mu := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (gradientTestFunctionLp_apply_ae q phi),
    eLpNorm_restrict_eq_of_support_subset (support_gradient_testFunction_subset phi),
    eLpNorm_congr_norm_ae
      (ae_of_all _ fun x => norm_gradient_eq_norm_fderiv (𝕜 := ℝ) (phi : E → ℝ) x)]

@[simp]
theorem gradientTestFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (phi + psi) =
      gradientTestFunctionLp (mu := mu) q phi + gradientTestFunctionLp (mu := mu) q psi := by
  rw [gradientTestFunctionLp, gradientTestFunctionLp, gradientTestFunctionLp,
    ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => gradient_add ((phi.contDiff.differentiable (by simp)) x)
    ((psi.contDiff.differentiable (by simp)) x)

@[simp]
theorem gradientTestFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (c • phi) =
      c • gradientTestFunctionLp (mu := mu) q phi := by
  rw [gradientTestFunctionLp, gradientTestFunctionLp, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => by simpa using gradient_const_smul (f := (phi : E → ℝ)) (x := x) c

end Gradient

end TauCeti
