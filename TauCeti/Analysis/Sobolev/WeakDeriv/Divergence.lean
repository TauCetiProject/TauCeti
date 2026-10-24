/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
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

Dually, a weakly differentiable function `u : E → F` with weak derivative `U` pairs with the
divergence of a test vector field `φ` as `∫ div φ • u = -∫ U φ`. This identity only needs a
finite-dimensional real normed domain and a real normed codomain. For scalar `u`, it is the
identity behind total variation, a supremum of the left-hand side over `‖φ‖ ≤ 1`. Against an
additive Haar measure, taking `u = 1` gives `∫ div φ = 0`.

No boundedness or boundary regularity of `Ω` is used. Except for `∫ div φ = 0`, which needs an
additive Haar measure, the measure need not be a Haar measure: the trace identity, the Laplacian
identity and the pairing `∫ div φ • u = -∫ U φ` all come from the defining integration-by-parts
identities of weak derivatives.

## Main declarations

* `TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`: the weak
  divergence of a weakly differentiable vector field is the trace of its weak derivative.
* `TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace`: the distributional
  Laplacian of a twice weakly differentiable function is the trace of its weak Hessian.
* `TauCeti.HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral`: a weakly differentiable
  function pairs with the divergence of a test vector field through its weak derivative.
* `TestFunction.integral_divergenceCLM_eq_zero`: the divergence of a test vector field has
  integral zero against an additive Haar measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.1 and §6.3.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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
theorem HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace [OpensMeasurableSpace E]
    {u : E → ℝ} {g : E → E} {G : E → E →L[ℝ] E}
    (hu : HasWeakFDerivOn μ Ω u fun x => innerSL ℝ (g x)) (hg : HasWeakFDerivOn μ Ω g G)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = ∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
  rw [hu.integral_laplacian_smul_eq_neg_integral_inner φ,
    hg.integral_inner_gradient_eq_neg_integral_smul_trace φ, neg_neg]

end InnerProductSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Integration by parts against a divergence.** If `u : E → F` has weak derivative `U` on
`Ω`, then for every test vector field `φ` on `Ω`, `∫ div φ • u ∂μ = -∫ U φ ∂μ`. -/
theorem HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral [OpensMeasurableSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) (φ : 𝓓(Ω, E)) :
    ∫ x, TestFunction.divergenceCLM φ x • u x ∂μ = -∫ x, U x (φ x) ∂μ := by
  have := h.completeSpace
  let b := Module.finBasis ℝ E
  -- Coordinate functions replace inner products, so no inner product on `E` is needed.
  let ψ : Fin (Module.finrank ℝ E) → 𝓓(Ω, ℝ) := fun i =>
    TestFunction.postcompCLM (LinearMap.toContinuousLinearMap (b.coord i)) φ
  have hψ (i) : (ψ i : E → ℝ) = fun y => b.repr (φ y) i := by
    ext y
    simp [ψ]
  have hdiv (x) : TestFunction.divergenceCLM φ x =
      ∑ i, lineDeriv ℝ (ψ i : E → ℝ) x (b i) := by
    rw [TestFunction.divergenceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd := (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp x
      (φ.contDiff.differentiable (by simp) x).hasFDerivAt
    simpa [hψ, LinearMap.toMatrix_apply, Function.comp_def] using
      (hd.hasLineDerivAt (b i)).lineDeriv.symm
  calc ∫ x, TestFunction.divergenceCLM φ x • u x ∂μ
      = ∑ i, ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) • u x ∂μ := by
        simp_rw [hdiv, Finset.sum_smul]
        exact integral_finsetSum _ fun i _ =>
          integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn (ψ i) (b i)
    _ = ∑ i, -∫ x, (ψ i : E → ℝ) x • U x (b i) ∂μ := Finset.sum_congr rfl fun i _ =>
        (h.hasWeakLineDerivOn (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
    _ = -∫ x, U x (φ x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          integrable_smul_of_locallyIntegrableOn
            (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv (ψ i)]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hψ]
        simpa only [map_sum, map_smul] using congrArg (U x) (b.sum_repr (φ x))

/-- The divergence of a test vector field has integral zero against an additive Haar measure:
`∫ div φ ∂μ = 0`. -/
theorem _root_.TestFunction.integral_divergenceCLM_eq_zero [BorelSpace E] [μ.IsAddHaarMeasure]
    (φ : 𝓓(Ω, E)) : ∫ x, TestFunction.divergenceCLM φ x ∂μ = 0 := by
  have h : HasWeakFDerivOn μ Ω (fun _ => (1 : ℝ)) 0 := hasWeakFDerivOn_iff.mpr fun v => by
    simpa using hasWeakLineDerivOn_const (μ := μ) (Ω := Ω) (v := v) (1 : ℝ)
  simpa using h.integral_divergenceCLM_smul_eq_neg_integral φ

end TauCeti
