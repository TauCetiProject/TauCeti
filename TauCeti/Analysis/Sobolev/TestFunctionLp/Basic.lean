/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import TauCeti.MeasureTheory.Function.Lp.Translation
public import TauCeti.Analysis.Distribution.TestFunction.Dilation
public import TauCeti.MeasureTheory.Function.Lp.Dilation
public import TauCeti.MeasureTheory.Measure.Haar.Restrict
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Holder

/-!
# Test functions as elements of `Lp`

This file provides the generic bridge from compactly supported test functions on an open set to
`Lp` classes. A test function belongs to every `Lᵖ` space for any measure finite on compact sets.
The construction is used by the closed-graph presentations of weak Sobolev spaces.

The bridge is linear: `TauCeti.testFunctionLp_add` and `TauCeti.testFunctionLp_smul` record that
passing to the `Lᵖ` class commutes with the vector space structure of the test functions, and
`TauCeti.testFunctionLpₗ` bundles it as a linear map. For an inner product space,
`TauCeti.gradientTestFunctionLp` and `TauCeti.gradientTestFunctionLpₗ` provide the parallel
construction for the gradient. These facts make the image of `C_c^∞(Ω)` in an `Lᵖ`-based function
space a subspace. On the whole space, passing a test function or its gradient to `Lᵖ`
commutes with translation, as recorded by `TauCeti.testFunctionLp_translateTestFunction` and
`TauCeti.gradientTestFunctionLp_translateTestFunction`, and turns dilation of test functions into
the normalized `Lᵖ` dilation `MeasureTheory.Measure.dilateLp`, up to an explicit power of the
factor, as recorded by `TauCeti.testFunctionLp_dilateTestFunction` and
`TauCeti.gradientTestFunctionLp_dilateTestFunction`.

A distributional derivative bounded by the `Lᵠ` norm of test functions extends by Hahn–Banach
to a bounded functional on `Lᵠ(Ω)` for every `q ≥ 1`. At `q = 2`, the negative of its Riesz
representative is a weak derivative:
`TauCeti.exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le`.
`ContDiffOn.enorm_integral_lineDeriv_smul_le` supplies the corresponding conjugate-exponent
test bound for a smooth map, using its actual `Lᵖ` derivative seminorm.
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
    eLpNorm_restrict_eq_of_support_subset phi.continuous.aestronglyMeasurable
      ((subset_tsupport _).trans phi.tsupport_subset)]

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

variable (mu Omega) in
/-- Passing from a test function on `Omega` to its class in `Lᵠ(Omega)`, as a linear map. -/
def testFunctionLpₗ (q : ENNReal) : 𝓓(Omega, ℝ) →ₗ[ℝ] Lp ℝ q (mu.restrict Omega) where
  toFun := testFunctionLp q
  map_add' := testFunctionLp_add q
  map_smul' := testFunctionLp_smul q

@[simp]
theorem testFunctionLpₗ_apply (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    testFunctionLpₗ mu Omega q phi = testFunctionLp q phi :=
  (rfl)

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

variable [IsLocallyFiniteMeasure (mu.restrict Omega)]

omit [IsLocallyFiniteMeasure (mu.restrict Omega)] in
/-- A distributional directional test bound extends to a continuous functional on `Lᵠ`
with the same bound, for every `q ≥ 1`. No σ-finiteness assumption is needed. -/
theorem exists_dual_norm_le_of_abs_integral_lineDeriv_mul_le_eLpNorm {q : ℝ≥0∞}
    [Fact (1 ≤ q)] {u : E → ℝ} (hu : LocallyIntegrableOn u Omega mu) (v : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ phi : 𝓓(Omega, ℝ),
      |∫ x, lineDeriv ℝ (phi : E → ℝ) x v * u x ∂mu| ≤
        C * (eLpNorm (phi : E → ℝ) q mu).toReal) :
    ∃ Λ : StrongDual ℝ (Lp ℝ q (mu.restrict Omega)), ‖Λ‖ ≤ C ∧
      ∀ phi : 𝓓(Omega, ℝ),
        Λ (testFunctionLp q phi) = ∫ x, lineDeriv ℝ (phi : E → ℝ) x v * u x ∂mu := by
  let ℓ : 𝓓(Omega, ℝ) →L[ℝ] ℝ :=
    (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ) mu u).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v)
  have hℓ (phi : 𝓓(Omega, ℝ)) :
      ℓ phi = ∫ x, lineDeriv ℝ (phi : E → ℝ) x v * u x ∂mu := by
    simp [ℓ, TestFunction.integralAgainstBilinCLM_eq_integral hu]
  let T := testFunctionLpₗ mu Omega q
  have hnorm (phi : 𝓓(Omega, ℝ)) :
      ‖T phi‖ = (eLpNorm (phi : E → ℝ) q mu).toReal := by
    rw [testFunctionLpₗ_apply, ← toReal_enorm]
    exact congrArg ENNReal.toReal (enorm_testFunctionLp_eq_eLpNorm q phi)
  have hker : LinearMap.ker T.rangeRestrict ≤ LinearMap.ker ℓ.toLinearMap := by
    rw [LinearMap.ker_rangeRestrict]
    intro phi hphi
    have h := hbound phi
    rw [← hnorm, LinearMap.mem_ker.mp hphi, norm_zero, mul_zero] at h
    rw [LinearMap.mem_ker]
    exact (hℓ phi).trans (abs_nonpos_iff.mp h)
  let f₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    T.rangeRestrict.liftOfSurjective T.surjective_rangeRestrict ⟨ℓ.toLinearMap, hker⟩
  have hf₀_apply (phi : 𝓓(Omega, ℝ)) : f₀ (T.rangeRestrict phi) = ℓ phi :=
    LinearMap.equivOfSurjective_apply T.surjective_rangeRestrict hker
  have hcoe (phi : 𝓓(Omega, ℝ)) :
      (T.rangeRestrict phi : Lp ℝ q (mu.restrict Omega)) = testFunctionLp q phi :=
    testFunctionLpₗ_apply q phi
  have hf₀ : ∀ s, ‖f₀ s‖ ≤ C * ‖s‖ := by
    intro s
    obtain ⟨phi, rfl⟩ := T.surjective_rangeRestrict s
    rw [hf₀_apply, Real.norm_eq_abs, hℓ, ← Submodule.norm_coe, hcoe]
    simpa only [testFunctionLpₗ_apply] using (hnorm phi ▸ hbound phi)
  obtain ⟨Λ, hΛ, hΛnorm⟩ := exists_extension_norm_eq _ (f₀.mkContinuous C hf₀)
  refine ⟨Λ, hΛnorm.trans_le (LinearMap.mkContinuous_norm_le _ hC hf₀), fun phi ↦ ?_⟩
  have h := hΛ (T.rangeRestrict phi)
  simpa only [hcoe, LinearMap.mkContinuous_apply, hf₀_apply, hℓ] using h

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
  obtain ⟨Λ, hΛnorm, hΛphi⟩ :=
    exists_dual_norm_le_of_abs_integral_lineDeriv_mul_le_eLpNorm hu v hC hbound
  let g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (mu.restrict Omega))).symm (-Λ)
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, LinearIsometryEquiv.norm_map, norm_neg] using hΛnorm
  · have hg : LocallyIntegrableOn g Omega mu := Lp.locallyIntegrableOn g (by norm_num)
    refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hu, hg, fun phi => ?_⟩
    have hinner : ⟪g, testFunctionLp 2 phi⟫_ℝ = ∫ x, (phi : E → ℝ) x • g x ∂mu := by
      rw [L2.inner_def, ← setIntegral_smul_eq_integral_smul phi]
      refine integral_congr_ae ?_
      filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 phi] with x hx
      simp [hx]
    rw [← hinner, InnerProductSpace.toDual_symm_apply, neg_apply, hΛphi, neg_neg]
    simp only [smul_eq_mul]

end Representation

section TestBound

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure]
  {p q : ℝ≥0∞} [p.HolderConjugate q]

omit [IsFiniteMeasureOnCompacts mu] in
/-- Integration by parts and Hölder's inequality bound the action of a function's weak directional
derivative on a test function by its `Lᵖ` derivative seminorm. The function need only be `C¹` on
the open test domain. -/
theorem _root_.ContDiffOn.enorm_integral_lineDeriv_smul_le {u : E → F}
    (hu : ContDiffOn ℝ 1 u Omega)
    (phi : 𝓓(Omega, ℝ)) (v : E) :
    ‖∫ x, lineDeriv ℝ (phi : E → ℝ) x v • u x ∂mu‖ₑ ≤
      eLpNorm (phi : E → ℝ) q mu * ‖v‖ₑ * eLpNorm (fderiv ℝ u) p (mu.restrict Omega) := by
  have hD : ContinuousOn (fderiv ℝ u) Omega :=
    hu.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl
  have hw : HasWeakFDerivOn mu Omega u (fderiv ℝ u) := hasWeakFDerivOn_of_differentiableOn
    (hD.locallyIntegrableOn Omega.isOpen.measurableSet) (fun x hx =>
      (hu.differentiableOn one_ne_zero x hx).differentiableAt (Omega.isOpen.mem_nhds hx))
  rw [(hw.hasWeakLineDerivOn v).integral_lineDeriv_smul_eq_neg_integral_smul phi, enorm_neg,
    ← setIntegral_smul_eq_integral_smul phi]
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ u x v) (mu.restrict Omega) :=
    (hD.clm_apply continuousOn_const).aestronglyMeasurable Omega.isOpen.measurableSet
  have hnorm : eLpNorm (fun x => fderiv ℝ u x v) p (mu.restrict Omega) ≤
      ‖v‖ₑ * eLpNorm (fderiv ℝ u) p (mu.restrict Omega) := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := ‖v‖) hmeas
      (ae_of_all _ fun x => by simpa only [mul_comm] using (fderiv ℝ u x).le_opNorm v) p
    rwa [ofReal_norm] at h
  calc ‖∫ x in Omega, (phi : E → ℝ) x • fderiv ℝ u x v ∂mu‖ₑ ≤
      eLpNorm (phi : E → ℝ) q (mu.restrict Omega) *
        eLpNorm (fun x => fderiv ℝ u x v) p (mu.restrict Omega) := enorm_integral_smul_le
    _ ≤ eLpNorm (phi : E → ℝ) q mu *
        (‖v‖ₑ * eLpNorm (fderiv ℝ u) p (mu.restrict Omega)) :=
          mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) hnorm
    _ = _ := (mul_assoc ..).symm

end TestBound

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
    phi.hasCompactSupport.gradient

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
  have hgrad : AEStronglyMeasurable (fun x => ∇ (phi : E → ℝ) x) mu :=
    ((continuous_gradient_testFunction phi).stronglyMeasurable_of_hasCompactSupport
      phi.hasCompactSupport.gradient).aestronglyMeasurable
  have hfderiv : AEStronglyMeasurable (fderiv ℝ (phi : E → ℝ)) mu :=
    ((contDiff_infty_iff_fderiv.mp phi.contDiff).2.continuous
      |>.stronglyMeasurable_of_hasCompactSupport
        (phi.hasCompactSupport.fderiv ℝ)).aestronglyMeasurable
  rw [Lp.enorm_def, eLpNorm_congr_ae (gradientTestFunctionLp_apply_ae q phi),
    eLpNorm_restrict_eq_of_support_subset hgrad (support_gradient_testFunction_subset phi),
    eLpNorm_congr_norm_ae hgrad hfderiv
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

/-- Passing from a test function on `Omega` to the class of its gradient in `Lᵠ(Omega, E)`, as a
linear map. -/
def gradientTestFunctionLpₗ (mu : Measure E) [IsFiniteMeasureOnCompacts mu] (Omega : Opens E)
    (q : ENNReal) :
    𝓓(Omega, ℝ) →ₗ[ℝ] Lp E q (mu.restrict Omega) where
  toFun := gradientTestFunctionLp q
  map_add' := gradientTestFunctionLp_add q
  map_smul' := gradientTestFunctionLp_smul q

@[simp]
theorem gradientTestFunctionLpₗ_apply (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLpₗ mu Omega q phi = gradientTestFunctionLp q phi :=
  (rfl)

end Gradient

/-! ### Translation on the whole space -/

section Translation

variable [MeasurableAdd E] [mu.IsAddRightInvariant] {q : ENNReal} [Fact (1 ≤ q)]

local instance : (mu.restrict (⊤ : Opens E)).IsAddRightInvariant := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (inferInstance : mu.IsAddRightInvariant)

/-- Passing a translated whole-space test function to `Lᵖ` translates its class. The sign
is reversed because `translateTestFunction h` evaluates at `x - h`, whereas `translateLp h`
evaluates at `x + h`. -/
@[simp]
theorem testFunctionLp_translateTestFunction (h : E) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    testFunctionLp (mu := mu) q
        (translateTestFunction (Omega := ⊤) (h := -h) (by intro x _; exact Opens.mem_top _) phi) =
      (mu.restrict (⊤ : Opens E)).translateLp q h (testFunctionLp q phi) := by
  apply Lp.ext
  filter_upwards [testFunctionLp_apply_ae (mu := mu) q
      (translateTestFunction (Omega := ⊤) (h := -h) (by intro x _; exact Opens.mem_top _) phi),
    Measure.coeFn_translateLp h (testFunctionLp (mu := mu) q phi),
    (measurePreserving_add_right (mu.restrict (⊤ : Opens E)) h).quasiMeasurePreserving.ae_eq_comp
      (testFunctionLp_apply_ae (mu := mu) q phi)] with x hx hy hz
  exact hx.trans ((translateTestFunction_apply _ phi x).trans
    ((congrArg phi (sub_neg_eq_add x h)).trans (hz.symm.trans hy.symm)))

end Translation

section GradientTranslation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [BorelSpace E] {mu : Measure E} [IsFiniteMeasureOnCompacts mu]
  [mu.IsAddRightInvariant] {q : ENNReal} [Fact (1 ≤ q)]

local instance : (mu.restrict (⊤ : Opens E)).IsAddRightInvariant := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (inferInstance : mu.IsAddRightInvariant)

/-- Taking the gradient's `Lᵖ` class commutes with whole-space translation. -/
@[simp]
theorem gradientTestFunctionLp_translateTestFunction (h : E) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    gradientTestFunctionLp (mu := mu) q
        (translateTestFunction (Omega := ⊤) (h := -h) (by intro x _; exact Opens.mem_top _) phi) =
      (mu.restrict (⊤ : Opens E)).translateLp q h (gradientTestFunctionLp q phi) := by
  apply Lp.ext
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q
      (translateTestFunction (Omega := ⊤) (h := -h) (by intro x _; exact Opens.mem_top _) phi),
    Measure.coeFn_translateLp h (gradientTestFunctionLp (mu := mu) q phi),
    (measurePreserving_add_right (mu.restrict (⊤ : Opens E)) h).quasiMeasurePreserving.ae_eq_comp
      (gradientTestFunctionLp_apply_ae (mu := mu) q phi)] with x hx hy hz
  rw [hx, hy, hz]
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [Function.comp_apply, toDual_gradient]
  exact (fderiv_translateTestFunction _ phi x).trans
    (congrArg (fderiv ℝ (phi : E → ℝ)) (sub_neg_eq_add x h))

end GradientTranslation

/-! ### Dilation on the whole space -/

section Dilation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {q : ENNReal}
  [Fact (1 ≤ q)] {r : ℝ}

open Module

/-- Passing a dilated whole-space test function `φ (r⁻¹ • ·)` to `Lᵖ` gives `r ^ (n / p)` times
the normalized dilation of its class, where `n` is the dimension of `E`. -/
@[simp]
theorem testFunctionLp_dilateTestFunction (hr : 0 < r)
    (hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E)) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    testFunctionLp (mu := mu) q (dilateTestFunction hr.ne' hVO phi) =
      r ^ ((finrank ℝ E : ℝ) / q.toReal) •
        (mu.restrict (⊤ : Opens E)).dilateLp q r hr (testFunctionLp q phi) := by
  apply Lp.ext
  filter_upwards [testFunctionLp_apply_ae (mu := mu) q (dilateTestFunction hr.ne' hVO phi),
    Lp.coeFn_smul (r ^ ((finrank ℝ E : ℝ) / q.toReal))
      ((mu.restrict (⊤ : Opens E)).dilateLp q r hr (testFunctionLp (mu := mu) q phi)),
    Measure.coeFn_dilateLp hr (testFunctionLp (mu := mu) q phi),
    (Measure.quasiMeasurePreserving_smul (mu.restrict (⊤ : Opens E))
      (inv_ne_zero hr.ne')).ae_eq_comp (testFunctionLp_apply_ae (mu := mu) q phi)]
    with x hx hy hz hw
  simp only [Function.comp_apply] at hw
  rw [hx, hy, Pi.smul_apply, hz, hw, dilateTestFunction_apply, smul_smul, ← Real.rpow_add hr,
    add_neg_cancel, Real.rpow_zero, one_smul]

end Dilation

section GradientDilation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {q : ENNReal}
  [Fact (1 ≤ q)] {r : ℝ}

open Module

/-- Passing the gradient of a dilated whole-space test function `φ (r⁻¹ • ·)` to `Lᵖ` gives
`r ^ (n / p - 1)` times the normalized dilation of the gradient's class, where `n` is the
dimension of `E`. -/
@[simp]
theorem gradientTestFunctionLp_dilateTestFunction (hr : 0 < r)
    (hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E)) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    gradientTestFunctionLp (mu := mu) q (dilateTestFunction hr.ne' hVO phi) =
      r ^ ((finrank ℝ E : ℝ) / q.toReal - 1) •
        (mu.restrict (⊤ : Opens E)).dilateLp q r hr (gradientTestFunctionLp q phi) := by
  apply Lp.ext
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q (dilateTestFunction hr.ne' hVO phi),
    Lp.coeFn_smul (r ^ ((finrank ℝ E : ℝ) / q.toReal - 1))
      ((mu.restrict (⊤ : Opens E)).dilateLp q r hr (gradientTestFunctionLp (mu := mu) q phi)),
    Measure.coeFn_dilateLp hr (gradientTestFunctionLp (mu := mu) q phi),
    (Measure.quasiMeasurePreserving_smul (mu.restrict (⊤ : Opens E))
      (inv_ne_zero hr.ne')).ae_eq_comp (gradientTestFunctionLp_apply_ae (mu := mu) q phi)]
    with x hx hy hz hw
  simp only [Function.comp_apply] at hw
  have hexp : (finrank ℝ E : ℝ) / q.toReal - 1 + -((finrank ℝ E : ℝ) / q.toReal) = -1 := by ring
  rw [hx, hy, Pi.smul_apply, hz, hw, gradient_dilateTestFunction, smul_smul, ← Real.rpow_add hr,
    hexp, Real.rpow_neg_one]

end GradientDilation

end TauCeti
