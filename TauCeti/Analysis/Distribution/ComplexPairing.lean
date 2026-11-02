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
