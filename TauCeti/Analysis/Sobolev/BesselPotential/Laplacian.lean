/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Elliptic regularity of `-Δ + c` for classical functions

Let `E` be a finite-dimensional real inner product space and `c > 0`. On tempered distributions,
`-Δ + c` is an isomorphism `H^(s+2) ≃ H^s` for every real `s`
(`TemperedDistribution.memSobolev_add_two_iff_neg_laplacian_add_smul`). This file transfers that
statement to classical functions: a real `C²` function `f ∈ L²(E)` whose classical
`-Δ f + c f` lies in the real Bessel-potential space `H^s` lies in `H^(s+2)`
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_neg_laplacian_add_smul`).

No decay of the derivatives of `f` is assumed: the classical Laplacian of a `C²` function is its
distributional Laplacian (`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`), and a
tempered distribution is determined by its values on compactly supported real test functions
(`TemperedDistribution.ext_real`), against which the integrations by parts have no boundary
terms. This is the form in which the regularity of `-Δ + c` applies to solutions of semilinear
equations `Δ f = c f + N(f)` known only to be smooth and square integrable, by bootstrapping in
the Sobolev scale.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
* M. E. Taylor, *Partial Differential Equations I*, Chapter 4.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TopologicalSpace
open scoped Laplacian SchwartzMap Distributions ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Elliptic regularity of `-Δ + c` for classical functions.** For `c > 0`, a real `C²`
function `f ∈ L²(E)` whose classical `-Δ f + c f` lies in `H^s` lies in `H^(s+2)`. -/
theorem mem_realSobolevFunctions_add_two_of_neg_laplacian_add_smul {c s : ℝ} (hc : 0 < c)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hL : MemLp f 2 volume)
    (h : (fun x ↦ -Δ f x + c * f x) ∈ realSobolevFunctions E s 2) :
    f ∈ realSobolevFunctions E (s + 2) 2 := by
  obtain ⟨w, hwf, hw⟩ := mem_realSobolevFunctions.1 h
  refine mem_realSobolevFunctions.2 ⟨hL.toLp f, hL.coeFn_toLp, ?_⟩
  rw [memSobolev_add_two_iff_neg_laplacian_add_smul hc]
  convert hw using 1
  refine ext_real fun φ hφ ↦ ?_
  -- Green's identity against `φ`, regarded as a test function on the whole space.
  let ψ : 𝓓((⊤ : Opens E), ℝ) := ⟨φ, φ.smooth ⊤, hφ, by simp⟩
  have hgreen := ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume)
    (hf.contDiffOn (s := ((⊤ : Opens E) : Set E))) ψ
  change ∫ x, Δ (φ : E → ℝ) x * f x = ∫ x, φ x * Δ f x at hgreen
  have hΔφ : Continuous (Δ (φ : E → ℝ)) :=
    ((φ.smooth ⊤).of_le (by simp)).continuous_laplacian
  have hi₁ : Integrable (fun x ↦ Δ (φ : E → ℝ) x * f x) volume :=
    (hΔφ.mul hf.continuous).integrable_of_hasCompactSupport hφ.laplacian.mul_right
  have hi₂ : Integrable (fun x ↦ φ x * f x) volume :=
    (φ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hφ.mul_right
  have hi₃ : Integrable (fun x ↦ φ x * Δ f x) volume :=
    (φ.continuous.mul hf.continuous_laplacian).integrable_of_hasCompactSupport hφ.mul_right
  have hΔ : ∀ x, (Δ (φ.postcompCLM Complex.ofRealCLM)) x = (Δ (φ : E → ℝ) x : ℂ) := by
    intro x
    rw [TauCeti.laplacian_postcompCLM, SchwartzMap.postcompCLM_apply, SchwartzMap.laplacian_apply]
    rfl
  simp only [add_apply, neg_apply,
    smul_apply, laplacian_apply_apply, Lp.toTemperedDistribution_apply, hΔ,
    SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  have hfu := Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) (hL.toLp f)
  have e₁ : ∫ x, (Δ (φ : E → ℝ) x : ℂ) • Complex.ofRealCLM.compLp (hL.toLp f) x =
      ((∫ x, Δ (φ : E → ℝ) x * f x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hfu, hL.coeFn_toLp] with x h₁ h₂
    rw [h₁, Complex.ofRealCLM_apply, h₂, smul_eq_mul, Complex.ofReal_mul]
  have e₂ : ∫ x, (φ x : ℂ) • Complex.ofRealCLM.compLp (hL.toLp f) x =
      ((∫ x, φ x * f x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hfu, hL.coeFn_toLp] with x h₁ h₂
    rw [h₁, Complex.ofRealCLM_apply, h₂, smul_eq_mul, Complex.ofReal_mul]
  have e₃ : ∫ x, (φ x : ℂ) • Complex.ofRealCLM.compLp w x =
      ((∫ x, φ x * (-Δ f x + c * f x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) w, hwf] with x h₁ h₂
    rw [h₁, Complex.ofRealCLM_apply, h₂, smul_eq_mul, Complex.ofReal_mul]
  have e₄ : ∫ x, φ x * (-Δ f x + c * f x) = -(∫ x, φ x * Δ f x) + c * ∫ x, φ x * f x := by
    rw [← integral_neg, ← integral_const_mul,
      ← integral_add (f := fun x ↦ -(φ x * Δ f x)) hi₃.neg (hi₂.const_mul c)]
    congr 1
    ext x
    ring
  rw [e₁, e₂, e₃, e₄, hgreen, Complex.real_smul]
  push_cast
  ring

end TemperedDistribution
