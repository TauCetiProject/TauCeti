/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Coordinate slices of Schwartz functions

Fixing the first variable of a Schwartz function on `P × E` gives a Schwartz function on `E`.
The restriction is a continuous linear map `SchwartzMap.sliceRightCLM`, and its Schwartz
seminorms are bounded independently of the frozen variable. More strongly, each seminorm of
the slice decays faster than any power of the norm of the frozen variable.

These estimates allow one-dimensional Fourier and Poisson summation theorems to be applied
coordinate by coordinate. To slice a function on a Euclidean space, first use
`SchwartzMap.compCLMOfContinuousLinearEquiv` with a fixed splitting into a product of the frozen
coordinates and the remaining coordinate. The bounds here are uniform in the frozen
coordinates, including when either factor has dimension zero.

The derivative calculation uses `ContDiff.iteratedFDeriv_prod_right`: the derivatives of a slice
are restrictions of the total derivatives to directions in the second factor. The product norm
dominates both coordinate norms, which gives the mixed decay estimate without a loss of constants.

## Main declarations

* `SchwartzMap.sliceRightCLM`: restriction to the second variable as a continuous linear map.
* `SchwartzMap.seminorm_sliceRightCLM_le`: a bound uniform in the first variable.
* `SchwartzMap.norm_pow_mul_seminorm_sliceRightCLM_le`: rapid decay of slice seminorms in the
  first variable.
-/

public section

open scoped SchwartzMap

namespace SchwartzMap

variable {𝕜 P E F : Type*} [NormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Partial derivatives of a Schwartz function have mixed polynomial decay in the frozen and
remaining variables, with a constant independent of both variables. -/
theorem norm_pow_mul_norm_iteratedFDeriv_prod_right_le (f : 𝓢(P × E, F))
    (l k n : ℕ) (p : P) (x : E) :
    ‖p‖ ^ l * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x‖) ≤
      SchwartzMap.seminorm 𝕜 (l + k) n f := by
  have hderiv : ‖iteratedFDeriv ℝ n (fun y ↦ f (p, y)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (p, x)‖ := by
    rw [_root_.ContDiff.iteratedFDeriv_prod_right (f.smooth ⊤) n (by simp)]
    exact (iteratedFDeriv ℝ n f (p, x)).norm_compContinuous_linearIsometry_le
      (fun _ ↦ LinearIsometry.inr ℝ P E)
  calc
    _ ≤ ‖(p, x)‖ ^ l * (‖(p, x)‖ ^ k * ‖iteratedFDeriv ℝ n f (p, x)‖) := by
      gcongr
      · exact norm_fst_le (p, x)
      · exact norm_snd_le (p, x)
    _ = ‖(p, x)‖ ^ (l + k) * ‖iteratedFDeriv ℝ n f (p, x)‖ := by rw [pow_add]; ring
    _ ≤ _ := f.le_seminorm 𝕜 (l + k) n (p, x)

/-- Fix the first variable of a Schwartz function on a product, as a continuous linear map
between Schwartz spaces. -/
noncomputable def sliceRightCLM (𝕜 : Type*) [NormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] (p : P) :
    𝓢(P × E, F) →L[𝕜] 𝓢(E, F) :=
  mkCLM (fun f x ↦ f (p, x)) (by intros; rfl) (by intros; rfl)
    (fun f ↦ (f.smooth ⊤).comp (contDiff_const.prodMk contDiff_id)) fun ⟨k, n⟩ ↦ by
      refine ⟨{(k, n)}, 1, zero_le_one, fun f x ↦ ?_⟩
      simpa using norm_pow_mul_norm_iteratedFDeriv_prod_right_le (𝕜 := 𝕜) f 0 k n p x

@[simp]
theorem sliceRightCLM_apply (p : P) (f : 𝓢(P × E, F)) (x : E) :
    sliceRightCLM 𝕜 p f x = f (p, x) :=
  (rfl)

theorem coe_sliceRightCLM (p : P) (f : 𝓢(P × E, F)) :
    ⇑(sliceRightCLM 𝕜 p f) = fun x ↦ f (p, x) :=
  funext (sliceRightCLM_apply p f)

/-- Differentiating a coordinate slice restricts the total derivative to directions in the
second factor. -/
theorem iteratedFDeriv_sliceRightCLM (f : 𝓢(P × E, F)) (p : P) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (sliceRightCLM 𝕜 p f) x =
      (iteratedFDeriv ℝ n f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ P E) := by
  rw [coe_sliceRightCLM]
  exact _root_.ContDiff.iteratedFDeriv_prod_right (f.smooth ⊤) n (by simp) p x

/-- Every Schwartz seminorm of a coordinate slice decays faster than any power in the frozen
variable. The bound uses a single seminorm of the original function. -/
theorem norm_pow_mul_seminorm_sliceRightCLM_le (f : 𝓢(P × E, F))
    (l k n : ℕ) (p : P) :
    ‖p‖ ^ l * SchwartzMap.seminorm 𝕜 k n (sliceRightCLM 𝕜 p f) ≤
      SchwartzMap.seminorm 𝕜 (l + k) n f := by
  by_cases hp : ‖p‖ ^ l = 0
  · simp [hp]
  have hp' : 0 < ‖p‖ ^ l := lt_of_le_of_ne (by positivity) (Ne.symm hp)
  rw [mul_comm, ← le_div_iff₀ hp']
  refine (sliceRightCLM 𝕜 p f).seminorm_le_bound 𝕜 k n (by positivity) fun x ↦ ?_
  rw [le_div_iff₀ hp', mul_comm]
  simpa only [coe_sliceRightCLM] using
    norm_pow_mul_norm_iteratedFDeriv_prod_right_le (𝕜 := 𝕜) f l k n p x

/-- Schwartz seminorms of slices are bounded uniformly in the frozen variable. -/
theorem seminorm_sliceRightCLM_le (f : 𝓢(P × E, F)) (k n : ℕ) (p : P) :
    SchwartzMap.seminorm 𝕜 k n (sliceRightCLM 𝕜 p f) ≤ SchwartzMap.seminorm 𝕜 k n f := by
  simpa using norm_pow_mul_seminorm_sliceRightCLM_le f 0 k n p

end SchwartzMap
