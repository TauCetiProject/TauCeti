/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Normed.Module.Trace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence

/-!
# The Laplacian of a `W^{2,p}` function

For `u ∈ W^{2,p}(Ω)` on an open set `Ω` of a finite-dimensional real inner product space, the
weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` is an `Lᵖ` field of endomorphisms, and its trace
is the Laplacian of `u` in the sense of distributions: for every test function `φ` on `Ω`,

`∫ Δφ • u = ∫ φ • tr D²u`.

Consequently the two notions of a solution of `Δu = f` coincide in `W^{2,p}(Ω)`: for locally
integrable `f`, the weak formulation `∫ Δφ • u = ∫ φ • f` for all test functions `φ` holds exactly
when `u` is a strong solution, `tr D²u = f` almost everywhere in `Ω`. This is the form in which
`Lᵖ` estimates for the second derivatives, which are stated through the Laplacian, apply to
solutions of Poisson's equation given in either formulation.

No boundedness or boundary regularity of `Ω` is used.

## Main declarations

* `TauCeti.Wkp.integral_laplacian_smul_value_eq`: the distributional Laplacian of a `W^{2,p}`
  function is the trace of its weak Hessian.
* `TauCeti.Wkp.forall_integral_laplacian_smul_value_eq_iff`: weak and strong solutions of
  `Δu = f` agree in `W^{2,p}(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §9.4.
-/

public section

namespace TauCeti.Wkp

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **The distributional Laplacian of a `W^{2,p}` function is the trace of its weak Hessian**:
`∫ Δφ • u = ∫ φ • tr D²u` for every test function `φ` on `Ω`. -/
theorem integral_laplacian_smul_value_eq (u : Wkp mu Omega p 2) (φ : 𝓓(Omega, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • value 2 u x ∂mu =
      ∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (iteratedGradient 1 u x) ∂mu := by
  rw [value_succ]
  exact (hasWeakFDerivOn_value (lowerOrder 1 u)).integral_laplacian_smul_eq_integral_smul_trace
    (hasWeakFDerivOn_iteratedGradient 0 u) φ

/-- **Weak and strong solutions of `Δu = f` agree in `W^{2,p}(Ω)`.** For `u ∈ W^{2,p}(Ω)` and `f`
locally integrable on `Ω`, `∫ Δφ • u = ∫ φ • f` holds for every test function `φ` on `Ω` if and
only if the trace of the weak Hessian of `u` is `f` almost everywhere in `Ω`. -/
theorem forall_integral_laplacian_smul_value_eq_iff (u : Wkp mu Omega p 2) {f : E → ℝ}
    (hf : LocallyIntegrableOn f Omega mu) :
    (∀ φ : 𝓓(Omega, ℝ),
        ∫ x, Δ (φ : E → ℝ) x • value 2 u x ∂mu = ∫ x, (φ : E → ℝ) x • f x ∂mu) ↔
      (fun x => LinearMap.trace ℝ E (iteratedGradient 1 u x)) =ᵐ[mu.restrict Omega] f := by
  -- The trace of the weak Hessian is locally integrable on `Ω`, as the weak Hessian is.
  have htr : LocallyIntegrableOn (fun x => LinearMap.trace ℝ E (iteratedGradient 1 u x))
      Omega mu := fun x hx => by
    obtain ⟨t, ht, hint⟩ := (hasWeakFDerivOn_iteratedGradient 0 u).locallyIntegrableOn_deriv x hx
    exact ⟨t, ht, by simpa only [IntegrableOn, Function.comp_def, traceCLM_apply] using
      (traceCLM ℝ E).integrable_comp hint⟩
  simp_rw [integral_laplacian_smul_value_eq]
  constructor
  · intro h
    have hzero := Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (htr.sub hf)
      fun g hg hgc hgs => by
        set φ : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
        have hi₁ : Integrable (fun x => g x • LinearMap.trace ℝ E (iteratedGradient 1 u x)) mu := by
          simpa [φ] using integrable_smul_of_locallyIntegrableOn htr φ
        have hi₂ : Integrable (fun x => g x • f x) mu := by
          simpa [φ] using integrable_smul_of_locallyIntegrableOn hf φ
        simp only [Pi.sub_apply, smul_sub]
        rw [integral_sub hi₁ hi₂, sub_eq_zero]
        simpa [φ] using h φ
    rw [Filter.EventuallyEq, ae_restrict_iff' Omega.isOpen.measurableSet]
    filter_upwards [hzero] with x hx hxΩ
    exact sub_eq_zero.1 (hx hxΩ)
  · intro h φ
    rw [← setIntegral_smul_eq_integral_smul, ← setIntegral_smul_eq_integral_smul (w := f)]
    exact integral_congr_ae (h.mono fun x hx => congrArg ((φ : E → ℝ) x • ·) hx)

end TauCeti.Wkp
