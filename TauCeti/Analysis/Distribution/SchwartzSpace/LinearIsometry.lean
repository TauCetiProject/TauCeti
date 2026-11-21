/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Linear isometries of Schwartz functions

Let `E` be a finite-dimensional real inner product space and `A` a linear isometry onto `E`.
Composition with `A` commutes with the Fourier transform and its inverse, `𝓕 (f ∘ A) = 𝓕 f ∘ A`
(`SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv`). So it carries the
Fourier multiplier with symbol `g` to the one with symbol `g ∘ A`; in particular it commutes with
every Fourier multiplier whose symbol is invariant under `A`, such as the Bessel potentials
`⟨ξ⟩ ^ s`. The Jacobian of `A⁻¹` has absolute value `1`, so the pushforward of Schwartz densities
along a linear isometry `A` of `E` is composition with `A⁻¹`. These are the Schwartz-space inputs
for the action of linear isometries on tempered distributions and on the Bessel-potential spaces
`H^{s,p}`.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_compCLMOfContinuousLinearEquiv_linearIsometryEquiv`: the
  Fourier multiplier with symbol `g ∘ A` applied to `f ∘ A` is `(T_g f) ∘ A`.
* `SchwartzMap.pushforwardCLM_linearIsometryEquiv`: the pushforward of Schwartz densities along a
  linear isometry `A` is composition with `A⁻¹`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Proposition 2.2.11 (the Fourier transform
  commutes with orthogonal changes of variables).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LinearEquiv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A linear equivalence out of a finite-dimensional space, as a bijection, has temperate
growth. -/
theorem hasTemperateGrowth_toEquiv (e : V ≃ₗ[ℝ] W) : (e.toEquiv : V → W).HasTemperateGrowth :=
  e.toContinuousLinearEquiv.hasTemperateGrowth

/-- The inverse of a linear equivalence out of a finite-dimensional space, as a bijection, has
temperate growth. -/
theorem hasTemperateGrowth_toEquiv_symm (e : V ≃ₗ[ℝ] W) :
    (e.toEquiv.symm : W → V).HasTemperateGrowth :=
  e.toContinuousLinearEquiv.symm.hasTemperateGrowth

end LinearEquiv

namespace ContinuousLinearEquiv

variable {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Precomposing with a continuous linear equivalence preserves and reflects temperate growth. -/
theorem hasTemperateGrowth_comp_iff (e : D ≃L[ℝ] V) {g : V → W} :
    (g ∘ e).HasTemperateGrowth ↔ g.HasTemperateGrowth :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp e.symm.hasTemperateGrowth,
    fun h ↦ h.comp e.hasTemperateGrowth⟩

end ContinuousLinearEquiv

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace SchwartzMap

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pushforward of Schwartz densities along a linear isometry `A` is composition with `A⁻¹`:
the Jacobian factor `|det A⁻¹|` is `1`. -/
@[simp]
theorem pushforwardCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (f : 𝓢(E, F)) :
    pushforwardCLM ℂ A.toLinearEquiv.toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm f =
      compCLMOfContinuousLinearEquiv ℂ A.symm.toContinuousLinearEquiv f := by
  ext y
  have hdet : |(fderiv ℝ (A.toLinearEquiv.toEquiv.symm : E → E) y).det| = 1 := by
    have hA : (A.toLinearEquiv.toEquiv.symm : E → E) = A.symm := by
      ext x
      simp
    rw [hA, A.symm.fderiv, ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
    exact A.symm.toLinearIsometry.normDet_eq_one
  rw [pushforwardCLM_apply, hdet]
  simp

/-- Composition with a linear isometry equivalence `A` intertwines Fourier multipliers, carrying
the symbol `g` to `g ∘ A`: `T_{g ∘ A} (f ∘ A) = (T_g f) ∘ A`. In particular a Fourier multiplier
whose symbol is invariant under a linear isometry of `E` commutes with composition with it. -/
theorem fourierMultiplierCLM_compCLMOfContinuousLinearEquiv_linearIsometryEquiv {D : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D]
    [BorelSpace D] (A : D ≃ₗᵢ[ℝ] E) (g : E → ℂ) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (g ∘ A) (compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (fourierMultiplierCLM F g f) := by
  by_cases hg : g.HasTemperateGrowth
  · have hgA' : (g ∘ A).HasTemperateGrowth :=
      A.toContinuousLinearEquiv.hasTemperateGrowth_comp_iff.mpr hg
    have hgA : (g ∘ A) ∘ A.toContinuousLinearEquiv.symm = g := by
      ext x
      simp
    rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
      fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv,
      smulLeftCLM_compCLMOfContinuousLinearEquiv ℂ hgA', hgA,
      fourierInv_compCLMOfContinuousLinearEquiv_linearIsometryEquiv]
  · have hgA : ¬(g ∘ A).HasTemperateGrowth :=
      A.toContinuousLinearEquiv.hasTemperateGrowth_comp_iff.not.mpr hg
    simp [fourierMultiplierCLM_apply, smulLeftCLM, hg, hgA]

end SchwartzMap
