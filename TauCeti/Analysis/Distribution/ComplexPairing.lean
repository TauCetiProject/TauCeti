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
function along the support of `T`, and it has finite order on each compact set.

## Main declarations

* `Distribution.complexPairing`: the complex-linear extension of `T : 𝓓'^{n}(Ω, ℂ)` to complex
  test functions, as a continuous complex-linear map.
* `Distribution.complexPairing_postcompCLM_ofRealCLM`: on real test functions it is `T`.
* `Distribution.complexPairing_mapCLM_ofRealCLM_delta`: for the complex point mass at `x` it is
  evaluation at `x`.
* `Distribution.complexPairing_eq_integral`, `Distribution.complexPairing_ofFun`: where `T` is
  integration against a locally integrable function, so is its extension.
* `Distribution.complexPairing_eq_of_eventuallyEq`: it depends only on the germ of the test
  function along `dsupport T`.
* `Distribution.exists_norm_complexPairing_le`: it has finite order on each compact set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction
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
    have hre : postcompCLM (𝕜 := ℝ) reCLM (c • φ) =
        c.re • postcompCLM (𝕜 := ℝ) reCLM φ - c.im • postcompCLM (𝕜 := ℝ) imCLM φ := by
      ext t
      simp
    have him : postcompCLM (𝕜 := ℝ) imCLM (c • φ) =
        c.re • postcompCLM (𝕜 := ℝ) imCLM φ + c.im • postcompCLM (𝕜 := ℝ) reCLM φ := by
      ext t
      simp
    simp only [hre, him, map_sub, map_add, map_smul, RingHom.id_apply, real_smul]
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
  have hre : postcompCLM (𝕜 := ℝ) reCLM (postcompCLM (𝕜 := ℝ) ofRealCLM φ) = φ := by
    ext t
    simp
  have him : postcompCLM (𝕜 := ℝ) imCLM (postcompCLM (𝕜 := ℝ) ofRealCLM φ) = 0 := by
    ext t
    simp
  simp [complexPairing_apply, hre, him]

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

/-- The complex-linear extension of the complex point mass at `x` evaluates a complex test
function at `x`. -/
@[simp]
theorem complexPairing_mapCLM_ofRealCLM_delta (x : E) (φ : 𝓓^{n}(Ω, ℂ)) :
    (mapCLM ofRealCLM (delta x : 𝓓'^{n}(Ω, ℝ))).complexPairing φ = φ x := by
  simp only [complexPairing_apply, mapCLM_apply, delta_apply, postcompCLM_apply,
    Function.comp_apply, ofRealCLM_apply, reCLM_apply, imCLM_apply]
  rw [mul_comm]
  exact re_add_im (φ x)

/-- If `T` is integration against a function `f` locally integrable on an open set `U`, on real
test functions supported in `U`, then its complex-linear extension is integration against `f` on
complex test functions supported in `U`. -/
theorem complexPairing_eq_integral [MeasurableSpace E] [OpensMeasurableSpace E]
    {T : 𝓓'^{n}(Ω, ℂ)} {U : Set E} (hU : IsOpen U) {f : E → ℂ} {μ : MeasureTheory.Measure E}
    (hf : MeasureTheory.LocallyIntegrableOn f U μ)
    (hT : ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ x, φ x • f x ∂μ) {φ : 𝓓^{n}(Ω, ℂ)}
    (hφ : tsupport φ ⊆ U) : T.complexPairing φ = ∫ x, φ x * f x ∂μ := by
  have hpart (L : ℂ →L[ℝ] ℝ) : tsupport (postcompCLM (𝕜 := ℝ) L φ) ⊆ U := by
    rw [postcompCLM_apply]
    exact (tsupport_comp_subset (map_zero L) φ).trans hφ
  -- A real test function supported in `U` is a test function on `U`, so `f` is integrable
  -- against it.
  have hint (L : ℂ →L[ℝ] ℝ) :
      MeasureTheory.Integrable (fun x => postcompCLM (𝕜 := ℝ) L φ x • f x) μ :=
    TestFunction.integrable_smul (Ω := ⟨U, hU⟩)
      ⟨postcompCLM (𝕜 := ℝ) L φ, (postcompCLM (𝕜 := ℝ) L φ).contDiff,
        (postcompCLM (𝕜 := ℝ) L φ).hasCompactSupport, hpart L⟩ hf
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
  complexPairing_eq_integral Ω.isOpen hf (fun _ _ => ofFun_apply hf) φ.tsupport_subset

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

variable [FiniteDimensional ℝ E]

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

end Distribution
