/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
public import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The homogeneous Sobolev space `D^{1,p}_0(Ω)`

This file constructs the homogeneous Sobolev space `D^{1,p}_0(Ω)`: the completion of the test
functions `C_c^∞(Ω)` for the gradient norm `‖∇φ‖_p` alone, with no `Lᵖ` norm of `φ` itself. On
the whole space `Ω = E`, with `p = 2` and `n = dim E ≥ 3`, this is the space `D^{1,2}(ℝⁿ)` on which
the sharp Sobolev inequality `aₙ ∫ |∇u|² ≥ Y(Sⁿ) ‖u‖²_{2n/(n-2)}` of the Yamabe problem is stated,
and on which its extremals, the bubbles, are classified. It is the natural domain of that
inequality rather than `W^{1,2}(ℝⁿ)`: neither side involves `‖u‖₂`, both are invariant under the
dilations `u ↦ λ^{(n-2)/2} u(λ ·)`, and the bubbles are not square integrable in dimensions `3`
and `4`.

## The construction

The gradient norm is a norm on `C_c^∞(Ω)`, so the completion is realized concretely as the closure
`TauCeti.d1p0Submodule` of the gradients `∇φ` of test functions in `Lᵖ(Ω, E)`. An element is
therefore recorded by its gradient field, the norm of `TauCeti.D1p0` is exactly the `Lᵖ` norm of
that gradient, the space is complete, and for `p = 2` it is a Hilbert space with inner product
`⟪u, v⟫ = ∫_Ω ⟪∇u, ∇v⟫`, inherited from `L²(Ω, E)`.

## The Sobolev embedding

That an element of the completion is a function at all is the content of the
Gagliardo--Nirenberg--Sobolev inequality `‖φ‖_{p⋆} ≤ C ‖∇φ‖_p`, for `1 ≤ p` and the Sobolev
conjugate `1/p⋆ + 1/n = 1/p` with `p⋆ ≠ ∞`. It extends `φ ↦ φ` to a continuous linear map
`TauCeti.D1p0.sobolevEmbeddingL : D^{1,p}_0(Ω) →L[ℝ] L^{p⋆}(Ω)`. The extension is not formal in
one respect: injectivity. An `L^{p⋆}` limit of test functions whose gradients converge in `Lᵖ`
has the limit of the gradients as its weak gradient
(`TauCeti.D1p0.hasWeakFDerivOn_sobolevEmbeddingL`), because the integration-by-parts identities
against a fixed test function pass to the limit in both exponents at once. Since weak gradients
are unique, a vanishing image forces a vanishing gradient, so the map is injective
(`TauCeti.D1p0.sobolevEmbeddingL_injective`): `D^{1,p}_0(Ω)` is a space of `L^{p⋆}` functions with
`Lᵖ` weak gradients, not merely an abstract completion.

## Main declarations

* `TauCeti.d1p0Submodule` and `TauCeti.D1p0`: the space `D^{1,p}_0(Ω)`, complete for the
  gradient norm, with the dense linear embedding `TauCeti.D1p0.ofTestFunctionₗ` of the test
  functions (`TauCeti.D1p0.denseRange_ofTestFunctionₗ`, `TauCeti.D1p0.norm_ofTestFunctionₗ`).
* `TauCeti.D1p0.inner_def` and `TauCeti.D1p0.inner_ofTestFunctionₗ`: the Hilbert space structure
  of `D^{1,2}_0(Ω)`.
* `TauCeti.D1p0.sobolevEmbeddingL`: the Sobolev embedding `D^{1,p}_0(Ω) →L[ℝ] L^{p⋆}(Ω)`, with
  `TauCeti.D1p0.sobolevEmbeddingL_ofTestFunctionₗ` (it is the identity on test functions),
  `TauCeti.D1p0.norm_sobolevEmbeddingL_le` (the Gagliardo--Nirenberg--Sobolev bound),
  `TauCeti.D1p0.hasWeakFDerivOn_sobolevEmbeddingL` (the element is the weak gradient of its
  image) and `TauCeti.D1p0.sobolevEmbeddingL_injective`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, AMS (2001),
  Sections 8.2 and 8.3, for the homogeneous space `D¹(ℝⁿ)` of functions vanishing at infinity with
  square-integrable gradient, and Sobolev's inequality on it.
* M. Struwe, *Variational Methods*, 4th ed., Springer (2008), for `D^{1,2}_0(Ω)` as the completion
  of `C_c^∞(Ω)` in the Dirichlet norm.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91, for
  the role of this space in the Yamabe problem.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} {Omega : Opens E} {p : ENNReal}
  [Fact (1 ≤ p)]

/-! ### The space `D^{1,p}_0(Ω)` -/

section Space

variable [IsFiniteMeasureOnCompacts mu]

/-- **The homogeneous Sobolev space `D^{1,p}_0(Ω)`**, as a closed subspace of `Lᵖ(Ω, E)`: the
closure of the gradients `∇φ` of the test functions `φ ∈ C_c^∞(Ω)`. It is the completion of
`C_c^∞(Ω)` for the gradient norm, each element being recorded by its gradient field. -/
def d1p0Submodule (mu : Measure E) [IsFiniteMeasureOnCompacts mu] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : ClosedSubmodule ℝ (Lp E p (mu.restrict Omega)) :=
  (LinearMap.range (gradientTestFunctionLpₗ mu Omega p)).closure

/-- `D^{1,p}_0(Ω)` is the closure of the set of gradients of test functions. -/
theorem coe_d1p0Submodule :
    (d1p0Submodule mu Omega p : Set (Lp E p (mu.restrict Omega))) =
      closure (Set.range (gradientTestFunctionLp (mu := mu) (Omega := Omega) p)) := by
  rw [d1p0Submodule, Submodule.coe_closure, LinearMap.coe_range]
  congr 2
  exact funext (gradientTestFunctionLpₗ_apply p)

/-- **The homogeneous Sobolev space `D^{1,p}_0(Ω)`**, the completion of the test functions
`C_c^∞(Ω)` for the gradient norm `‖∇φ‖_p`. An element is its gradient field in `Lᵖ(Ω, E)`; the
function it represents is its image under `TauCeti.D1p0.sobolevEmbeddingL`. -/
abbrev D1p0 (mu : Measure E) [IsFiniteMeasureOnCompacts mu] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] := (d1p0Submodule mu Omega p).toSubmodule

/-- Shortcut instance for the norm of `D^{1,p}_0(Ω)`, inherited from `Lᵖ(Ω, E)`. Instance search
can time out on it while the measure and the open set are still metavariables. -/
instance D1p0.instNormedAddCommGroup : NormedAddCommGroup (D1p0 mu Omega p) := inferInstance

/-- Shortcut instance for the scalar action of `D^{1,p}_0(Ω)`, inherited from `Lᵖ(Ω, E)`. -/
instance D1p0.instNormedSpace : NormedSpace ℝ (D1p0 mu Omega p) := inferInstance

/-- `D^{1,p}_0(Ω)` is complete: it is a closed subspace of the complete space `Lᵖ(Ω, E)`. -/
instance : CompleteSpace (D1p0 mu Omega p) :=
  (d1p0Submodule mu Omega p).isClosed.completeSpace_coe

/-- **The test functions inside `D^{1,p}_0(Ω)`**: the linear embedding sending `φ ∈ C_c^∞(Ω)` to
its gradient `∇φ`. -/
def D1p0.ofTestFunctionₗ (mu : Measure E) [IsFiniteMeasureOnCompacts mu] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] : 𝓓(Omega, ℝ) →ₗ[ℝ] D1p0 mu Omega p where
  toFun phi := ⟨gradientTestFunctionLp p phi,
    Submodule.mem_closure_iff.2
      (Submodule.le_topologicalClosure _ ⟨phi, gradientTestFunctionLpₗ_apply p phi⟩)⟩
  map_add' phi psi := Subtype.ext (gradientTestFunctionLp_add p phi psi)
  map_smul' c phi := Subtype.ext (gradientTestFunctionLp_smul p c phi)

@[simp]
theorem D1p0.coe_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    (D1p0.ofTestFunctionₗ mu Omega p phi : Lp E p (mu.restrict Omega)) =
      gradientTestFunctionLp p phi := by
  simp [D1p0.ofTestFunctionₗ]

/-- The norm of a test function in `D^{1,p}_0(Ω)` is the `Lᵖ` norm of its derivative. -/
theorem D1p0.norm_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    ‖D1p0.ofTestFunctionₗ mu Omega p phi‖ = (eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu).toReal := by
  rw [← Submodule.norm_coe, D1p0.coe_ofTestFunctionₗ, ← toReal_enorm,
    enorm_gradientTestFunctionLp_eq_eLpNorm_fderiv]

/-- The test functions are dense in `D^{1,p}_0(Ω)`. -/
theorem D1p0.denseRange_ofTestFunctionₗ : DenseRange (D1p0.ofTestFunctionₗ mu Omega p) := by
  intro u
  have hu : (u : Lp E p (mu.restrict Omega)) ∈ (d1p0Submodule mu Omega p : Set _) := u.2
  rw [coe_d1p0Submodule] at hu
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage,
    ← Set.range_comp]
  convert hu using 3
  exact funext D1p0.coe_ofTestFunctionₗ

/-! ### The Hilbert space `D^{1,2}_0(Ω)` -/

/-- The inner product of `D^{1,2}_0(Ω)` is the Dirichlet inner product `∫_Ω ⟪∇u, ∇v⟫`. -/
theorem D1p0.inner_def (u v : D1p0 mu Omega 2) :
    ⟪u, v⟫_ℝ = ∫ x in Omega, ⟪(u : Lp E 2 (mu.restrict Omega)) x,
      (v : Lp E 2 (mu.restrict Omega)) x⟫_ℝ ∂mu := by
  rw [Submodule.coe_inner, L2.inner_def]

/-- On test functions, the inner product of `D^{1,2}_0(Ω)` is `∫ ⟪∇φ, ∇ψ⟫`. -/
theorem D1p0.inner_ofTestFunctionₗ (phi psi : 𝓓(Omega, ℝ)) :
    ⟪D1p0.ofTestFunctionₗ mu Omega 2 phi, D1p0.ofTestFunctionₗ mu Omega 2 psi⟫_ℝ =
      ∫ x, ⟪∇ (phi : E → ℝ) x, ∇ (psi : E → ℝ) x⟫_ℝ ∂mu := by
  rw [D1p0.inner_def]
  refine (integral_congr_ae ?_).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_)
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 phi,
      gradientTestFunctionLp_apply_ae (mu := mu) 2 psi] with x hphi hpsi
    rw [D1p0.coe_ofTestFunctionₗ, D1p0.coe_ofTestFunctionₗ, hphi, hpsi]
  · rw [Function.notMem_support.1 fun h => hx (support_gradient_testFunction_subset phi h),
      inner_zero_left]

end Space

/-! ### The Sobolev embedding `D^{1,p}_0(Ω) ↪ L^{p⋆}(Ω)` -/

variable [mu.IsAddHaarMeasure] {pstar : ENNReal}

/-- **The Sobolev embedding `D^{1,p}_0(Ω) → L^{p⋆}(Ω)`**, for `1 ≤ p` and the Sobolev conjugate
`1/p⋆ + 1/n = 1/p`: the extension by continuity of `φ ↦ φ` from the test functions, along the
Gagliardo--Nirenberg--Sobolev inequality. It sends an element of `D^{1,p}_0(Ω)` to the function
whose weak gradient it is (`TauCeti.D1p0.hasWeakFDerivOn_sobolevEmbeddingL`), and it is injective
(`TauCeti.D1p0.sobolevEmbeddingL_injective`). The results about it assume `p⋆ ≠ ∞`, that is
`p < n`; without it no such bound holds. -/
def D1p0.sobolevEmbeddingL (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    D1p0 mu Omega p →L[ℝ] Lp ℝ pstar (mu.restrict Omega) :=
  letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  (testFunctionLpₗ mu Omega pstar).extendOfNorm (D1p0.ofTestFunctionₗ mu Omega p)

/-- The Gagliardo--Nirenberg--Sobolev bound in the form consumed by
`LinearMap.extendOfNorm`. -/
private theorem D1p0.norm_testFunctionLp_le (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLpₗ mu Omega pstar phi‖ ≤
      SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖D1p0.ofTestFunctionₗ mu Omega p phi‖ := by
  rw [testFunctionLpₗ_apply, ← Submodule.norm_coe, D1p0.coe_ofTestFunctionₗ]
  exact norm_testFunctionLp_le_mul_norm_gradientTestFunctionLp hpstar hexp phi

/-- The Sobolev embedding is the identity on test functions: it sends the gradient `∇φ` of a test
function to the class of `φ` itself. -/
@[simp]
theorem D1p0.sobolevEmbeddingL_ofTestFunctionₗ (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (phi : 𝓓(Omega, ℝ)) :
    D1p0.sobolevEmbeddingL hexp (D1p0.ofTestFunctionₗ mu Omega p phi) =
      testFunctionLp pstar phi := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  exact (LinearMap.extendOfNorm_eq (D1p0.denseRange_ofTestFunctionₗ (mu := mu) (Omega := Omega))
    ⟨_, D1p0.norm_testFunctionLp_le hpstar hexp⟩ phi).trans (testFunctionLpₗ_apply pstar phi)

/-- **The Gagliardo--Nirenberg--Sobolev inequality on `D^{1,p}_0(Ω)`**: `‖u‖_{p⋆} ≤ C ‖∇u‖_p`, with
Mathlib's constant `MeasureTheory.SNormLESNormFDerivOfEqConst`, which depends only on `E`, `mu`
and `p`. -/
theorem D1p0.norm_sobolevEmbeddingL_le (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : D1p0 mu Omega p) :
    ‖D1p0.sobolevEmbeddingL hexp u‖ ≤ SNormLESNormFDerivOfEqConst ℝ mu p.toReal * ‖u‖ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  exact LinearMap.norm_extendOfNorm_apply_le
    (D1p0.denseRange_ofTestFunctionₗ (mu := mu) (Omega := Omega)) _
    (D1p0.norm_testFunctionLp_le hpstar hexp) u

/-- The pairing of `u ∈ D^{1,p}_0(Ω)` against a test function `φ` in a direction `w` that
expresses the weak-derivative identity `∫ (∂_w φ) u = -∫ φ ⟪∇u, w⟫` is a continuous function
of `u`, once `u` is read in `L^{p⋆}(Ω)` through the Sobolev embedding. -/
private theorem D1p0.continuous_weakDerivPairing (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (phi : 𝓓(Omega, ℝ)) (w : E) :
    Continuous fun u : D1p0 mu Omega p =>
      (∫ x in Omega, lineDeriv ℝ (phi : E → ℝ) x w * D1p0.sobolevEmbeddingL hexp u x ∂mu) +
        ∫ x in Omega, phi x * ⟪(u : Lp E p (mu.restrict Omega)) x, w⟫_ℝ ∂mu := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  let q := ENNReal.conjExponent p
  let qstar := ENNReal.conjExponent pstar
  let _ : q.HolderConjugate p := ENNReal.HolderConjugate.symm
  let _ : qstar.HolderConjugate pstar := ENNReal.HolderConjugate.symm
  let _ : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let _ : Fact (1 ≤ qstar) := ⟨ENNReal.HolderConjugate.one_le _ pstar⟩
  let dphi : 𝓓(Omega, ℝ) := TestFunction.lineDerivCLM ℝ w phi
  have hdphi : (dphi : E → ℝ) = fun x => lineDeriv ℝ (phi : E → ℝ) x w :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  let B : ℝ →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight (innerSL ℝ w)
  let Φ : D1p0 mu Omega p →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (mu.restrict Omega) qstar pstar
        (testFunctionLp qstar dphi)).comp (D1p0.sobolevEmbeddingL hexp) +
      (B.lpPairing (mu.restrict Omega) q p (testFunctionLp q phi)).comp
        (D1p0 mu Omega p).subtypeL
  refine Φ.continuous.congr fun u => ?_
  simp only [Φ, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral, Submodule.subtypeL_apply]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := mu) qstar dphi] with x hx
    rw [ContinuousLinearMap.mul_apply', hx, hdphi]
  · refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := mu) q phi] with x hx
    simp [B, hx, real_inner_comm]

/-- **An element of `D^{1,p}_0(Ω)` is the weak gradient of its image under the Sobolev
embedding.** For `u ∈ D^{1,p}_0(Ω)`, the function `u` in `L^{p⋆}(Ω)` has the recorded gradient
field `∇u ∈ Lᵖ(Ω, E)` as its weak gradient on `Ω`. -/
theorem D1p0.hasWeakFDerivOn_sobolevEmbeddingL (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : D1p0 mu Omega p) :
    HasWeakFDerivOn mu Omega (D1p0.sobolevEmbeddingL hexp u)
      fun x => innerSL ℝ ((u : Lp E p (mu.restrict Omega)) x) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  -- The integration-by-parts identities hold on the dense set of test functions, and are closed.
  have hibp : ∀ (phi : 𝓓(Omega, ℝ)) (w : E),
      (∫ x in Omega, lineDeriv ℝ (phi : E → ℝ) x w * D1p0.sobolevEmbeddingL hexp u x ∂mu) +
        ∫ x in Omega, phi x * ⟪(u : Lp E p (mu.restrict Omega)) x, w⟫_ℝ ∂mu = 0 := by
    intro phi w
    refine (D1p0.denseRange_ofTestFunctionₗ (mu := mu) (Omega := Omega)).induction_on u
      (isClosed_eq (D1p0.continuous_weakDerivPairing hexp phi w) continuous_const) fun psi => ?_
    have h := ((hasWeakFDerivOn_testFunction (μ := mu) psi).hasWeakLineDerivOn
      w).integral_lineDeriv_smul_eq_neg_integral_smul phi
    rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      ← setIntegral_smul_eq_integral_smul] at h
    rw [D1p0.sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp, D1p0.coe_ofTestFunctionₗ,
      ← eq_neg_iff_add_eq_zero]
    convert h using 1
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet,
        testFunctionLp_apply_ae (mu := mu) pstar psi] with x _ hx
      rw [hx, smul_eq_mul]
    · congr 1
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) p psi] with x hx
      rw [hx, innerSL_apply_apply, smul_eq_mul]
  rw [hasWeakFDerivOn_iff]
  intro w
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, Lp.locallyIntegrableOn _ Fact.out, ?_, fun phi => ?_⟩
  · apply locallyIntegrableOn_of_locallyIntegrable_restrict
    exact ((Lp.memLp (u : Lp E p (mu.restrict Omega))).continuousLinearMap_comp
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (innerSL ℝ))).locallyIntegrable Fact.out
  · rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      ← setIntegral_smul_eq_integral_smul, eq_neg_iff_add_eq_zero]
    simpa only [smul_eq_mul, innerSL_apply_apply] using hibp phi w

/-- **The Sobolev embedding of `D^{1,p}_0(Ω)` is injective**: an element of the completion is
determined by the `L^{p⋆}` function it represents. So `D^{1,p}_0(Ω)` is a space of functions,
those `u ∈ L^{p⋆}(Ω)` arising as limits of test functions whose gradients converge in `Lᵖ`. -/
theorem D1p0.sobolevEmbeddingL_injective (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) :
    Function.Injective (D1p0.sobolevEmbeddingL (mu := mu) (Omega := Omega) (p := p) hexp) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  have hzero : (D1p0.sobolevEmbeddingL hexp u : E → ℝ) =ᵐ[mu.restrict Omega] 0 := by
    rw [hu]
    exact Lp.coeFn_zero _ _ _
  have hae := ((D1p0.hasWeakFDerivOn_sobolevEmbeddingL hpstar hexp u).congr_ae hzero).ae_eq
    (hasWeakFDerivOn_zero (μ := mu) (Ω := Omega))
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero E p (mu.restrict Omega)] with x hx h0
  rw [Submodule.coe_zero, h0, Pi.zero_apply, ← norm_eq_zero, ← innerSL_apply_norm ℝ, hx,
    Pi.zero_apply, norm_zero]

end TauCeti
