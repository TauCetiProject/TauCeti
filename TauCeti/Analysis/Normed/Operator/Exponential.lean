/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Exponentials of bounded operators

This file records facts about the exponential of a continuous linear endomorphism of a normed
space. The norm bounds for exponentials in a general normed algebra live in
`TauCeti/Analysis/Normed/Algebra/Exponential.lean`.

## Main results

* `ContinuousLinearMap.exp_add_smul`, `ContinuousLinearMap.exp_add_smul_apply`: exponentials of
  scalar multiples of a bounded operator compose additively.
* `ContinuousLinearMap.exp_apply_of_apply_eq_smul`: the exponential of an operator acts on an
  eigenvector by the scalar exponential of the eigenvalue.
* `ContinuousLinearMap.spectrum_exp`: the spectral mapping theorem for the exponential of an
  operator on a finite-dimensional complex normed space, `σ(exp B) = exp (σ(B))`.
* `ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral`: the Duhamel identity
  `exp (t • B) x - x = ∫₀ᵗ exp (u • B) (B x) du` for the orbits of a real bounded operator.
-/

public section

open NormedSpace

namespace TauCeti

section Operator

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- Exponentials of scalar multiples of the same bounded operator split over addition. -/
theorem _root_.ContinuousLinearMap.exp_add_smul (A : X →L[𝕜] X) (s t : 𝕜) :
    exp ((s + t) • A) = (exp (s • A)).comp (exp (t • A)) := by
  let +nondep : NormedAlgebra ℚ (X →L[𝕜] X) := .restrictScalars ℚ 𝕜 _
  exact (NormedSpace.exp_add_smul A s t).trans (ContinuousLinearMap.mul_def _ _)

/-- Pointwise form of `ContinuousLinearMap.exp_add_smul`:
`exp ((s + t) • A) x = exp (s • A) (exp (t • A) x)`. -/
theorem _root_.ContinuousLinearMap.exp_add_smul_apply (A : X →L[𝕜] X) (s t : 𝕜) (x : X) :
    exp ((s + t) • A) x = exp (s • A) (exp (t • A) x) := by
  rw [ContinuousLinearMap.exp_add_smul, ContinuousLinearMap.comp_apply]

/-- **The exponential of an operator acts exponentially on an eigenvector.** If `B x = μ • x`,
then `exp B x = exp μ • x`. The statement also covers `x = 0`, without requiring a bundled
`Module.End.HasEigenvector` witness. -/
theorem _root_.ContinuousLinearMap.exp_apply_of_apply_eq_smul (B : X →L[𝕜] X) {x : X} {μ : 𝕜}
    (hx : B x = μ • x) : exp B x = exp μ • x := by
  have hpow (n : ℕ) : (B ^ n) x = μ ^ n • x := by
    induction n with
    | zero => simp
    | succ n hn => rw [pow_succ, mul_apply_eq_comp, hx, map_smul, hn, smul_smul, ← pow_succ']
  have hop := (exp_series_hasSum_exp' (𝕂 := 𝕜) B).mapL (ContinuousLinearMap.apply 𝕜 X x)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, hpow, smul_smul] at hop
  have hscalar := (exp_series_hasSum_exp' (𝕂 := 𝕜) μ).smul_const x
  simp only [smul_eq_mul] at hscalar
  exact hop.unique hscalar

end Operator

section SpectrumExp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **The spectral mapping theorem for the exponential**, in finite dimensions: the spectrum of
`exp B` is the image of the spectrum of `B` under the exponential. The inclusion
`exp (σ(B)) ⊆ σ(exp B)` holds in every complex Banach algebra (`spectrum.exp_mem_exp`). -/
theorem _root_.ContinuousLinearMap.spectrum_exp (B : V →L[ℂ] V) :
    spectrum ℂ (exp B) = exp '' spectrum ℂ B := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  refine Set.Subset.antisymm (fun μ hμ ↦ ?_) ?_
  -- The eigenspace of `exp B` for `μ` is preserved by `B`, which commutes with `exp B`. An
  -- eigenvector of `B` in it, with eigenvalue `c`, shows `μ = exp c`.
  · rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
    set E := Module.End.eigenspace ((exp B : V →L[ℂ] V) : Module.End ℂ V) μ
    have hmaps : ∀ v ∈ E, (B : Module.End ℂ V) v ∈ E := by
      intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      simp only [ContinuousLinearMap.coe_coe] at hv ⊢
      rw [← mul_apply_eq_comp, ← (Commute.refl B).exp_right.eq, mul_apply_eq_comp, hv, map_smul]
    have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.2 hμ
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((B : Module.End ℂ V).restrict hmaps)
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hBw : B (w : V) = c • (w : V) := by
      simpa [LinearMap.restrict_apply, Subtype.ext_iff] using hw.apply_eq_smul
    have hexpw : exp B (w : V) = μ • (w : V) := by
      simpa using Module.End.mem_eigenspace_iff.1 w.2
    have hw0 : (w : V) ≠ 0 := by simpa using hw.2
    refine ⟨c, ?_, smul_left_injective ℂ hw0
      ((ContinuousLinearMap.exp_apply_of_apply_eq_smul B hBw).symm.trans hexpw)⟩
    rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum]
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hBw, hw0⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact spectrum.exp_mem_exp B hz

end SpectrumExp

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **The Duhamel identity for the exponential of a bounded operator.** For `B : X →L[ℝ] X`,
`exp (t B) x - x = ∫₀ᵗ exp (u B) (B x) du`.

This is the fundamental theorem of calculus applied to the differentiable orbit
`u ↦ exp (u B) x`, whose derivative is the continuous function `u ↦ exp (u B) (B x)`. -/
theorem _root_.ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral
    (B : X →L[ℝ] X) (t : ℝ) (x : X) :
    exp (t • B) x - x = ∫ u in (0 : ℝ)..t, exp (u • B) (B x) := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ => exp (v • B) x) (exp (u • B) (B x)) u := by
    intro u
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const B u).clm_apply (hasDerivAt_const u x)
  have hcont : Continuous fun u : ℝ => exp (u • B) (B x) :=
    (differentiable_exp_smul_const ℝ B).continuous.clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 t)]
  simp

end Real

end TauCeti

end
