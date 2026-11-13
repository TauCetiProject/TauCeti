/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
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
  simp only [ψ, TestFunction.coe_mk, smul_eq_mul] at hgreen
  have hi₂ : Integrable (fun x ↦ φ x * f x) volume :=
    (φ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hφ.mul_right
  have hi₃ : Integrable (fun x ↦ φ x * Δ f x) volume :=
    (φ.continuous.mul hf.continuous_laplacian).integrable_of_hasCompactSupport hφ.mul_right
  -- Pairing a real test function with the distribution of a real `L²` representative.
  have hpair {g : E → ℝ} {u : Lp ℝ 2 volume} (hu : u =ᵐ[volume] g) (χ : 𝓢(E, ℝ)) :
      ((Complex.ofRealCLM.compLp u : Lp ℂ 2 volume) : 𝓢'(E, ℂ))
          (χ.postcompCLM Complex.ofRealCLM) = ((∫ x, χ x * g x : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM,
      integral_congr_ae (hu.mono fun x hx ↦ by rw [hx])]
  rw [add_apply, neg_apply, smul_apply, laplacian_apply_apply, TauCeti.laplacian_postcompCLM,
    hpair hL.coeFn_toLp, hpair hL.coeFn_toLp, hpair hwf]
  simp only [SchwartzMap.laplacian_apply]
  have e₄ : ∫ x, φ x * (-Δ f x + c * f x) = -(∫ x, φ x * Δ f x) + c * ∫ x, φ x * f x := by
    rw [← integral_neg, ← integral_const_mul,
      ← integral_add (f := fun x ↦ -(φ x * Δ f x)) hi₃.neg (hi₂.const_mul c)]
    congr 1
    ext x
    ring
  rw [e₄, hgreen, Complex.real_smul]
  push_cast
  ring

end TemperedDistribution
