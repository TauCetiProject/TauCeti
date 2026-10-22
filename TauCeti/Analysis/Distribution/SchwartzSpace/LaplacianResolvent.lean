/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
public import TauCeti.Analysis.Normed.Module.Complexification

/-!
# The resolvent of the Laplacian on Schwartz space

For `c > 0` the shifted Laplacian `-Δ + c` is a bijection of Schwartz space. With Mathlib's
normalization of the Fourier transform, `𝓕 (Δ f) ξ = -(2π)² ‖ξ‖² 𝓕 f ξ`, so `-Δ + c` is the Fourier
multiplier with symbol `(2π)² ‖ξ‖² + c`. This symbol is bounded below by `c`, and its reciprocal
`((2π)² ‖ξ‖² + c)⁻¹` has temperate growth, so the Fourier multiplier with the reciprocal symbol is
a continuous inverse of `-Δ + c` on Schwartz functions with values in a complex Banach space.

For Schwartz functions with values in a real Banach space `G`, the Fourier transform is not
available directly, since it takes values in a complex space. We embed the values in the
complexification `TauCeti.Complexification G`, apply the complex inverse, and take real parts.
Since the Laplacian commutes with these real-linear maps, the result is a continuous real-linear
inverse `SchwartzMap.laplacianResolvent c` of `-Δ + c` on `𝓢(E, G)`, which is the resolvent
`(c - Δ)⁻¹` of the Laplacian at `c`.

Inverting `-Δ + c` is the basic step in inverting constant-coefficient first-order operators `L`
satisfying a Weitzenböck identity `L* L = L L* = -Δ + c`: then `L⁻¹ = L* (-Δ + c)⁻¹`.

## Main declarations

* `TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add`: the symbol `(a ‖ξ‖² + c)⁻¹`, for `a ≥ 0` and
  `c > 0`, has temperate growth.
* `SchwartzMap.neg_laplacian_fourierMultiplierCLM_add_smul` and
  `SchwartzMap.fourierMultiplierCLM_neg_laplacian_add_smul`: the Fourier multiplier with symbol
  `((2π)² ‖ξ‖² + c)⁻¹` is a two-sided inverse of `-Δ + c` on complex Schwartz space.
* `SchwartzMap.laplacianResolvent c`: the inverse of `-Δ + c` on Schwartz functions with values in
  a real Banach space, characterized by
  `SchwartzMap.neg_laplacian_laplacianResolvent_add_smul` and
  `SchwartzMap.laplacianResolvent_neg_laplacian_add_smul`.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 3, §1 (the Fourier transform on Schwartz
  space and constant-coefficient operators).
-/

public section

noncomputable section

open scoped SchwartzMap Laplacian Real

namespace TauCeti

/-- The symbol `ξ ↦ (a ‖ξ‖² + c)⁻¹`, for `a ≥ 0` and `c > 0`, has temperate growth. It is a
rescaling of the Bessel potential `(1 + ‖ξ‖²)⁻¹`. -/
theorem hasTemperateGrowth_inv_mul_norm_sq_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    (fun ξ : E ↦ (a * ‖ξ‖ ^ 2 + c)⁻¹).HasTemperateGrowth := by
  have h := ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-1)).comp
    (√(a / c) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth).mul
    (Function.HasTemperateGrowth.const c⁻¹)
  convert h using 1
  ext ξ
  have : 0 < a * ‖ξ‖ ^ 2 + c := by positivity
  simp only [Pi.mul_apply, Function.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, norm_smul, Real.rpow_neg_one, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_nonneg ha hc.le)]
  field_simp
  ring

end TauCeti

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Complex

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℂ 𝕜 F]

variable [CompleteSpace F]

/-- The Fourier multiplier with symbol `((2π)² ‖ξ‖² + c)⁻¹` is a right inverse of `-Δ + c`. -/
@[simp]
theorem neg_laplacian_fourierMultiplierCLM_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢(E, F)) :
    -Δ (fourierMultiplierCLM F (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹) f) +
      c • fourierMultiplierCLM F (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹) f = f := by
  set g : E → ℝ := fun ξ ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹
  have hg : g.HasTemperateGrowth :=
    TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add (by positivity) hc
  have hn : (fun ξ : E ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by fun_prop
  have hsum : (2 * π) ^ 2 • ((fun ξ : E ↦ ‖ξ‖ ^ 2) * g) + c • g = fun _ ↦ 1 := by
    ext ξ
    have : 0 < (2 * π) ^ 2 * ‖ξ‖ ^ 2 + c := by positivity
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, g]
    field_simp
  have h₁ : ((2 * π) ^ 2 • ((fun ξ : E ↦ ‖ξ‖ ^ 2) * g)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).smul (hn.mul hg)
  have h₂ : (c • g).HasTemperateGrowth := (Function.HasTemperateGrowth.const _).smul hg
  have hop : fourierMultiplierCLM F ((2 * π) ^ 2 • ((fun ξ : E ↦ ‖ξ‖ ^ 2) * g) + c • g) =
      ContinuousLinearMap.id ℝ 𝓢(E, F) := by
    simp [hsum]
  rw [fourierMultiplierCLM_add h₁ h₂, fourierMultiplierCLM_smul (hn.mul hg),
    fourierMultiplierCLM_smul hg] at hop
  simpa [laplacian_eq_fourierMultiplierCLM, fourierMultiplierCLM_fourierMultiplierCLM_apply hn hg]
    using congr($hop f)

/-- The Fourier multiplier with symbol `((2π)² ‖ξ‖² + c)⁻¹` is a left inverse of `-Δ + c`. -/
@[simp]
theorem fourierMultiplierCLM_neg_laplacian_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹) (-Δ f + c • f) = f := by
  rw [map_add, map_neg, map_smul, fourierMultiplierCLM_laplacian
    (TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add (by positivity) hc)]
  exact neg_laplacian_fourierMultiplierCLM_add_smul hc f

end Complex

section Real

open TauCeti.Complexification

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **resolvent of the Laplacian** `(c - Δ)⁻¹` on Schwartz functions with values in a real
Banach space `G`. For `c > 0` it is the two-sided inverse of `-Δ + c`
(`neg_laplacian_laplacianResolvent_add_smul` and `laplacianResolvent_neg_laplacian_add_smul`). It
is the real part of the Fourier multiplier with symbol `((2π)² ‖ξ‖² + c)⁻¹`, applied to the
complexification `TauCeti.Complexification G` of the values. For `c ≤ 0` the value is not
meaningful. -/
def laplacianResolvent (c : ℝ) : 𝓢(E, G) →L[ℝ] 𝓢(E, G) :=
  postcompCLM (reCLM G) ∘L
    fourierMultiplierCLM (TauCeti.Complexification G)
      (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹) ∘L
    postcompCLM (ofRealLI G).toContinuousLinearMap

private theorem laplacianResolvent_apply (c : ℝ) (f : 𝓢(E, G)) :
    laplacianResolvent c f =
      (fourierMultiplierCLM (TauCeti.Complexification G)
        (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹)
        (f.postcompCLM (ofRealLI G).toContinuousLinearMap)).postcompCLM (reCLM G) :=
  rfl

variable [CompleteSpace G]

/-- The resolvent of the Laplacian is a right inverse of `-Δ + c`, for `c > 0`. -/
@[simp]
theorem neg_laplacian_laplacianResolvent_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢(E, G)) :
    -Δ (laplacianResolvent c f) + c • laplacianResolvent c f = f := by
  -- Project the complex inverse identity to real values, then normalize the linear maps.
  have hcomplex := neg_laplacian_fourierMultiplierCLM_add_smul hc
    (f.postcompCLM (ofRealLI G).toContinuousLinearMap)
  have hreal := congrArg (postcompCLM (reCLM G)) hcomplex
  ext x
  simpa only [laplacianResolvent_apply, TauCeti.laplacian_postcompCLM, map_add, map_neg,
    map_smul, postcompCLM_postcompCLM, reCLM_comp_ofRealLI, postcompCLM_apply,
    ContinuousLinearMap.id_apply] using congrArg (fun u : 𝓢(E, G) ↦ u x) hreal

/-- The resolvent of the Laplacian commutes with the Laplacian. -/
theorem laplacianResolvent_laplacian {c : ℝ} (hc : 0 < c) (f : 𝓢(E, G)) :
    laplacianResolvent c (Δ f) = Δ (laplacianResolvent c f) := by
  have hcomplex := fourierMultiplierCLM_laplacian
    (TauCeti.hasTemperateGrowth_inv_mul_norm_sq_add (E := E) (a := (2 * π) ^ 2)
      (c := c) (by positivity) hc)
    (f.postcompCLM (ofRealLI G).toContinuousLinearMap)
  have hreal := congrArg (postcompCLM (reCLM G)) hcomplex
  simpa only [laplacianResolvent_apply, TauCeti.laplacian_postcompCLM] using hreal

/-- The resolvent of the Laplacian is a left inverse of `-Δ + c`, for `c > 0`. -/
@[simp]
theorem laplacianResolvent_neg_laplacian_add_smul {c : ℝ} (hc : 0 < c) (f : 𝓢(E, G)) :
    laplacianResolvent c (-Δ f + c • f) = f := by
  rw [map_add, map_neg, map_smul, laplacianResolvent_laplacian hc]
  exact neg_laplacian_laplacianResolvent_add_smul hc f

end Real

/-- On complex-valued Schwartz space, the real resolvent is the Fourier multiplier with
symbol `((2π)² ‖ξ‖² + c)⁻¹`. -/
theorem laplacianResolvent_eq_fourierMultiplierCLM
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {c : ℝ} (hc : 0 < c) (f : 𝓢(E, G)) :
    laplacianResolvent c f =
      fourierMultiplierCLM G (fun ξ : E ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2 + c)⁻¹) f := by
  have h := congrArg (laplacianResolvent (G := G) c)
    (neg_laplacian_fourierMultiplierCLM_add_smul hc f)
  rw [laplacianResolvent_neg_laplacian_add_smul hc] at h
  exact h.symm


end SchwartzMap
