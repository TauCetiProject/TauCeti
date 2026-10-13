/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# The weak divergence of a weakly differentiable vector field

Let `g : E → E` be a vector field on an open set `Ω` of a finite-dimensional real inner product
space, with weak derivative `G : E → E →L[ℝ] E`. Its divergence is the trace of its derivative,
and this holds in the weak sense: for every test function `φ` on `Ω`,

`∫ ⟪∇φ, g⟫ = -∫ φ • tr G`.

Applied to the weak gradient `g` of a scalar function `u`, together with
`TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_neg_integral_inner`, this says that the
distributional Laplacian of a twice weakly differentiable function is the trace of its weak
Hessian: `∫ Δφ • u = ∫ φ • tr G`. This identity is what makes the weak formulation
`∫ Δφ • u = ∫ φ • f` of Poisson's equation `Δu = f` agree with the strong one, `tr G = f` almost
everywhere, for twice weakly differentiable `u`.

No boundedness or boundary regularity of `Ω` is used, and the measure need not be a Haar measure:
both identities come from the defining integration-by-parts identities of weak derivatives.

## Main declarations

* `TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`: the weak
  divergence of a weakly differentiable vector field is the trace of its weak derivative.
* `TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace`: the distributional
  Laplacian of a twice weakly differentiable function is the trace of its weak Hessian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.1 and §6.3.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}

/-- **The weak divergence is the trace of the weak derivative.** If the vector field `g` has weak
derivative `G` on `Ω`, then for every test function `φ` on `Ω`,
`∫ ⟪∇φ, g⟫ ∂μ = -∫ φ • tr G ∂μ`. -/
theorem HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace
    [OpensMeasurableSpace E] {g : E → E} {G : E → E →L[ℝ] E} (h : HasWeakFDerivOn μ Ω g G)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ =
      -∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  -- The component `⟪bᵢ, g⟫` has weak derivative `⟪bᵢ, G bᵢ⟫` in the direction `bᵢ`.
  have hdir : ∀ i, HasWeakLineDerivOn μ Ω (fun x => ⟪b i, g x⟫_ℝ)
      (fun x => ⟪b i, G x (b i)⟫_ℝ) (b i) := fun i => by
    simpa only [innerSL_apply_apply] using
      (h.hasWeakLineDerivOn (b i)).clm_comp (innerSL ℝ (b i))
  have hline : ∀ x v, lineDeriv ℝ (φ : E → ℝ) x v = fderiv ℝ (φ : E → ℝ) x v := fun x v =>
    (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
  calc ∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ
      = ∑ i, ∫ x, lineDeriv ℝ (φ : E → ℝ) x (b i) • ⟪b i, g x⟫_ℝ ∂μ := by
        rw [← integral_finsetSum _ fun i _ =>
          integrable_lineDeriv_smul_of_locallyIntegrableOn (hdir i).locallyIntegrableOn φ (b i)]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hline, smul_eq_mul, ← toDual_gradient, toDual_apply_apply]
        exact (b.sum_inner_mul_inner _ _).symm
    _ = ∑ i, -∫ x, (φ : E → ℝ) x • ⟪b i, G x (b i)⟫_ℝ ∂μ :=
        Finset.sum_congr rfl fun i _ => (hdir i).integral_lineDeriv_smul_eq_neg_integral_smul φ
    _ = -∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          integrable_smul_of_locallyIntegrableOn (hdir i).locallyIntegrableOn_deriv φ]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]

/-- **The distributional Laplacian is the trace of the weak Hessian.** If `u` has weak gradient
`g` on `Ω` and `g` has weak derivative `G` there, then for every test function `φ` on `Ω`,
`∫ Δφ • u ∂μ = ∫ φ • tr G ∂μ`. -/
theorem HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace [BorelSpace E]
    {u : E → ℝ} {g : E → E} {G : E → E →L[ℝ] E}
    (hu : HasWeakFDerivOn μ Ω u fun x => innerSL ℝ (g x)) (hg : HasWeakFDerivOn μ Ω g G)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = ∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
  rw [hu.integral_laplacian_smul_eq_neg_integral_inner φ,
    hg.integral_inner_gradient_eq_neg_integral_smul_trace φ, neg_neg]

end TauCeti
