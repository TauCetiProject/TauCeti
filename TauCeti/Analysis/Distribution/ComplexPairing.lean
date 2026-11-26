/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Complex-valued distributions on complex-valued test functions

Mathlib's distributions `𝓓'(Ω, F)` are continuous linear maps on *real-valued* test functions.
A complex-valued distribution `T : 𝓓'(Ω, ℂ)` extends uniquely to a complex-linear map on
complex-valued test functions, by

`T (φ) = T (re ∘ φ) + i T (im ∘ φ)`.

This is how a complex-valued distribution is paired with a complex kernel, such as the Cauchy
kernel `t ↦ χ t / (t - z)` whose pairing with a distribution on `ℝ` is the Cauchy transform. This
file defines the extension `Distribution.complexPairing` and transfers to it the two basic
estimates used when the test function varies: the pairing depends only on the germ of the test
function along the support of `T`, and it has finite order on each compact set. Complex
conjugation of the values, `mapCLM conjCLE`, is an involution on complex distributions, and
continuous linear maps of the values act functorially.

## Main declarations

* `Distribution.complexPairing`: the complex-linear extension of `T : 𝓓'^{n}(Ω, ℂ)` to complex
  test functions, as a continuous complex-linear map.
* `Distribution.complexPairing_postcompCLM_ofRealCLM`: on real test functions it is `T`.
* `Distribution.complexPairing_lineDerivOp`: it turns derivatives of `T` into derivatives of the
  test function, `(∂_{v} T) φ = - T (∂_{v} φ)`.
* `Distribution.complexPairing_mapCLM_ofRealCLM_delta`: for the complex point mass at `x` it is
  evaluation at `x`.
* `Distribution.complexPairing_eq_integral`, `Distribution.complexPairing_ofFun`: where `T` is
  integration against a locally integrable function, so is its extension.
* `Distribution.complexPairing_eq_of_eventuallyEq`: it depends only on the germ of the test
  function along `dsupport T`.
* `Distribution.exists_norm_complexPairing_le`: it has finite order on each compact set.
* `Distribution.mul_norm_complexPairing_tsum_smul`: a nonnegative weight of the value of a
  distribution on a series of test functions in `𝓓_K` moves into the coefficients of the series.
* `Distribution.mapCLM_conj_mapCLM_conj`: conjugating a complex distribution twice gives it
  back.
* `Distribution.mapCLM_id`, `Distribution.mapCLM_mapCLM`: continuous linear maps of the values
  act functorially.
* `Distribution.mapCLM_restrictScalars_eq_smul`, `Distribution.mapCLM_restrictScalars_smul`,
  `Distribution.mapCLM_restrictScalars_symm_mapCLM`: complex-linear maps of the values; on
  complex distributions they are scalar multiplications, they commute with complex scalar
  multiples, and complex isomorphisms are undone by their inverses.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction LineDeriv
open scoped Distributions Topology

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}

/-- The **complex-linear extension** of a complex-valued distribution to complex-valued test
functions: `φ ↦ T (re ∘ φ) + i T (im ∘ φ)`. -/
def complexPairing (T : 𝓓'^{n}(Ω, ℂ)) : 𝓓^{n}(Ω, ℂ) →L[ℂ] ℂ where
  toFun φ := T (postcompCLM (𝕜 := ℝ) reCLM φ) + I * T (postcompCLM (𝕜 := ℝ) imCLM φ)
  map_add' φ ψ := by
    simp only [map_add]
    ring
  map_smul' c φ := by
    simp only [postcompCLM_reCLM_smul, postcompCLM_imCLM_smul, map_sub, map_add, map_smul,
      RingHom.id_apply, real_smul]
    conv_rhs => rw [← re_add_im c]
    ring_nf
    rw [I_sq]
    ring
  cont := by
    fun_prop

theorem complexPairing_apply (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω, ℂ)) :
    T.complexPairing φ =
      T (postcompCLM (𝕜 := ℝ) reCLM φ) + I * T (postcompCLM (𝕜 := ℝ) imCLM φ) :=
  (rfl)

/-- On real test functions, viewed as complex test functions, the complex-linear extension of `T`
is `T` itself. -/
@[simp]
theorem complexPairing_postcompCLM_ofRealCLM (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω, ℝ)) :
    T.complexPairing (postcompCLM (𝕜 := ℝ) ofRealCLM φ) = T φ := by
  simp [complexPairing_apply]

@[simp]
theorem complexPairing_zero (φ : 𝓓^{n}(Ω, ℂ)) : (0 : 𝓓'^{n}(Ω, ℂ)).complexPairing φ = 0 := by
  simp [complexPairing_apply]

@[simp]
theorem complexPairing_add (T S : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω, ℂ)) :
    (T + S).complexPairing φ = T.complexPairing φ + S.complexPairing φ := by
  simp only [complexPairing_apply]
  simp
  ring

@[simp]
theorem complexPairing_smul (c : ℂ) (T : 𝓓'^{n}(Ω, ℂ)) (φ : 𝓓^{n}(Ω, ℂ)) :
    (c • T).complexPairing φ = c * T.complexPairing φ := by
  simp only [complexPairing_apply]
  simp
  ring

/-- For a fixed complex test function `φ`, the pairing `T ↦ T φ` is continuous in the
distribution `T`. -/
theorem continuous_complexPairing_apply (φ : 𝓓^{n}(Ω, ℂ)) :
    Continuous fun T : 𝓓'^{n}(Ω, ℂ) ↦ T.complexPairing φ := by
  simp only [complexPairing_apply]
  fun_prop

/-- The complex-linear extension of a derivative of `T` is minus the extension of `T` applied to
the derivative of the test function: `(∂_{v} T) φ = - T (∂_{v} φ)` on complex test functions. -/
theorem complexPairing_lineDerivOp (T : 𝓓'(Ω, ℂ)) (v : E) (φ : 𝓓(Ω, ℂ)) :
    (∂_{v} T).complexPairing φ = -T.complexPairing (∂_{v} φ) := by
  simp only [complexPairing_apply, lineDerivOp_apply_apply, map_neg,
    TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, lineDerivCLM_postcompCLM]
  ring

/-- The complex-linear extension of the complex point mass at `x` evaluates a complex test
function at `x`. -/
@[simp]
theorem complexPairing_mapCLM_ofRealCLM_delta (x : E) (φ : 𝓓^{n}(Ω, ℂ)) :
    (mapCLM ofRealCLM (delta x : 𝓓'^{n}(Ω, ℝ))).complexPairing φ = φ x := by
  simp only [complexPairing_apply, mapCLM_apply, delta_apply, postcompCLM_apply,
    Function.comp_apply, ofRealCLM_apply, reCLM_apply, imCLM_apply]
  rw [mul_comm]
  exact re_add_im (φ x)

/-- If `T` is integration against a function `f` locally integrable on a set `U`, on real
test functions supported in `U`, then its complex-linear extension is integration against `f` on
complex test functions supported in `U`. -/
theorem complexPairing_eq_integral [MeasurableSpace E] [OpensMeasurableSpace E]
    {T : 𝓓'^{n}(Ω, ℂ)} {U : Set E} {f : E → ℂ} {μ : MeasureTheory.Measure E}
    (hf : MeasureTheory.LocallyIntegrableOn f U μ)
    (hT : ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ x, φ x • f x ∂μ) {φ : 𝓓^{n}(Ω, ℂ)}
    (hφ : tsupport φ ⊆ U) : T.complexPairing φ = ∫ x, φ x * f x ∂μ := by
  have hpart (L : ℂ →L[ℝ] ℝ) : tsupport (postcompCLM (𝕜 := ℝ) L φ) ⊆ U := by
    rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero L) φ).trans hφ
  -- `f` is integrable against a real test function supported in `U`.
  have hint (L : ℂ →L[ℝ] ℝ) :
      MeasureTheory.Integrable (fun x => postcompCLM (𝕜 := ℝ) L φ x • f x) μ :=
    hf.integrable_smul_left_of_hasCompactSupport
      (postcompCLM (𝕜 := ℝ) L φ).continuous.continuousOn
      (postcompCLM (𝕜 := ℝ) L φ).hasCompactSupport (hpart L)
  rw [complexPairing_apply, hT _ (hpart reCLM), hT _ (hpart imCLM),
    ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_add (hint reCLM) ((hint imCLM).const_mul I)]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [postcompCLM_apply, Function.comp_apply, reCLM_apply, imCLM_apply, real_smul]
  conv_rhs => rw [← re_add_im (φ x)]
  ring

/-- On a locally integrable function `f`, the complex-linear extension of the distribution
`ofFun Ω f μ n` is integration against `f`. -/
theorem complexPairing_ofFun [MeasurableSpace E] [OpensMeasurableSpace E] {f : E → ℂ}
    {μ : MeasureTheory.Measure E} (hf : MeasureTheory.LocallyIntegrableOn f Ω μ)
    (φ : 𝓓^{n}(Ω, ℂ)) :
    (ofFun Ω f μ n).complexPairing φ = ∫ x, φ x * f x ∂μ :=
  complexPairing_eq_integral hf (fun _ _ => ofFun_apply hf) φ.tsupport_subset

/-- **The complex-linear extension has finite order on each compact set.** For a compact `K ⊆ Ω`
there are an order `N` and a constant `C` such that `‖T.complexPairing φ‖ ≤ C * M` for every
complex test function `φ` supported in `K` whose derivatives of order at most `N` are all bounded
by `M`. -/
theorem exists_norm_complexPairing_le (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hK : (K : Set E) ⊆ Ω) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ K → ∀ M, 0 ≤ M →
      (∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ M) → ‖T.complexPairing φ‖ ≤ C * M := by
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le hK
  refine ⟨N, 2 * C, by positivity, fun φ hφ M hM hφM => ?_⟩
  -- The real and imaginary parts of `φ` satisfy the same support condition and bounds.
  have hpart (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) : ‖T (postcompCLM (𝕜 := ℝ) L φ)‖ ≤ C * M := by
    refine hT _ ?_ M hM fun i hi x => ?_
    · rw [postcompCLM_apply]
      exact (tsupport_comp_subset (map_zero L) φ).trans hφ
    · rw [postcompCLM_apply]
      calc ‖iteratedFDeriv ℝ i (L ∘ φ) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i φ x‖ :=
            L.norm_iteratedFDeriv_comp_left (φ.contDiff.contDiffAt) (by exact_mod_cast le_top)
        _ ≤ 1 * M := mul_le_mul hL (hφM i hi x) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
  calc ‖T.complexPairing φ‖ ≤ ‖T (postcompCLM (𝕜 := ℝ) reCLM φ)‖ +
        ‖I * T (postcompCLM (𝕜 := ℝ) imCLM φ)‖ := norm_add_le _ _
    _ ≤ C * M + C * M := by
        rw [norm_mul, norm_I, one_mul]
        exact add_le_add (hpart _ Complex.reCLM_norm.le) (hpart _ Complex.imCLM_norm.le)
    _ = 2 * C * M := by ring

/-- Conjugating a complex distribution twice gives it back. -/
@[simp]
theorem mapCLM_conj_mapCLM_conj (T : 𝓓'^{n}(Ω, ℂ)) :
    mapCLM conjCLE.toContinuousLinearMap (mapCLM conjCLE.toContinuousLinearMap T) = T := by
  ext φ
  simp [mapCLM_apply]

/-- The complex-linear extension of `T` depends only on the germ of the test function along the
support of `T`. -/
theorem complexPairing_eq_of_eventuallyEq (T : 𝓓'^{n}(Ω, ℂ)) {φ ψ : 𝓓^{n}(Ω, ℂ)}
    (h : (φ : E → ℂ) =ᶠ[𝓝ˢ (dsupport T)] ψ) : T.complexPairing φ = T.complexPairing ψ := by
  rw [complexPairing_apply, complexPairing_apply,
    map_eq_map_of_eventuallyEq T (φ := postcompCLM (𝕜 := ℝ) reCLM φ)
      (ψ := postcompCLM (𝕜 := ℝ) reCLM ψ)
      (by simpa only [postcompCLM_apply] using h.fun_comp reCLM),
    map_eq_map_of_eventuallyEq T (φ := postcompCLM (𝕜 := ℝ) imCLM φ)
      (ψ := postcompCLM (𝕜 := ℝ) imCLM ψ)
      (by simpa only [postcompCLM_apply] using h.fun_comp imCLM)]

/-! ### Continuous linear maps of the values -/

section MapCLM

variable {F F' F'' : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [AddCommGroup F'] [Module ℝ F']
  [TopologicalSpace F'] [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [AddCommGroup F'']
  [Module ℝ F''] [TopologicalSpace F''] [IsTopologicalAddGroup F''] [ContinuousSMul ℝ F'']

/-- The identity of the values acts trivially on `T`. -/
@[simp]
theorem mapCLM_id (T : 𝓓'^{n}(Ω, F)) : mapCLM (ContinuousLinearMap.id ℝ F) T = T := by
  ext φ
  simp

/-- Applying `B` and then `A` to the values is applying `A ∘ B`. -/
theorem mapCLM_mapCLM (A : F' →L[ℝ] F'') (B : F →L[ℝ] F') (T : 𝓓'^{n}(Ω, F)) :
    mapCLM A (mapCLM B T) = mapCLM (A.comp B) T := by
  ext φ
  simp

end MapCLM

/-! ### Complex-linear maps of the values -/

section ComplexValues

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
  [NormedSpace ℂ F']

/-- A complex-linear functional `ℓ` on `ℂ` is multiplication by `ℓ 1`, so applying it to the
values of a complex distribution `T` gives the scalar multiple `ℓ 1 • T`. -/
theorem mapCLM_restrictScalars_eq_smul (ℓ : ℂ →L[ℂ] ℂ) (T : 𝓓'^{n}(Ω, ℂ)) :
    mapCLM (ℓ.restrictScalars ℝ) T = ℓ 1 • T := by
  ext φ
  simpa [mul_comm] using ℓ.map_smul (T φ) (1 : ℂ)

/-- Applying a complex isomorphism `A` of the values and then its inverse gives back `T`. -/
@[simp]
theorem mapCLM_restrictScalars_symm_mapCLM (A : F ≃L[ℂ] F') (T : 𝓓'^{n}(Ω, F)) :
    mapCLM ((A.symm : F' →L[ℂ] F).restrictScalars ℝ)
      (mapCLM ((A : F →L[ℂ] F').restrictScalars ℝ) T) = T := by
  rw [mapCLM_mapCLM]
  ext φ
  simp

/-- A complex-linear map of the values commutes with complex scalar multiplication. -/
@[simp]
theorem mapCLM_restrictScalars_smul (A : F →L[ℂ] F') (c : ℂ) (T : 𝓓'^{n}(Ω, F)) :
    mapCLM (A.restrictScalars ℝ) (c • T) = c • mapCLM (A.restrictScalars ℝ) T := by
  ext φ
  simp

end ComplexValues

section Series

/-- The weight `w ≥ 0` of the pairing of a distribution with a series in `𝓓_K` moves into the
coefficients of the series. -/
theorem mul_norm_complexPairing_tsum_smul (T : 𝓓'(Ω, ℂ)) {K : Compacts E}
    (hKΩ : (K : Set E) ⊆ Ω) {ι : Type*} {c : ι → ℂ} {v : ι → 𝓓_{K}(E, ℂ)} {w : ℝ}
    (hw : 0 ≤ w) (hc : Summable fun m ↦ c m • v m) :
    w * ‖T.complexPairing (TestFunction.ofSupportedIn hKΩ (∑' m, c m • v m))‖ =
      ‖T.complexPairing (TestFunction.ofSupportedIn hKΩ (∑' m, ((w : ℂ) * c m) • v m))‖ := by
  simp_rw [mul_smul]
  rw [hc.tsum_const_smul, ← TestFunction.coe_ofSupportedInCLM (𝕜 := ℂ) hKΩ, map_smul, map_smul,
    smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]

end Series

end Distribution
