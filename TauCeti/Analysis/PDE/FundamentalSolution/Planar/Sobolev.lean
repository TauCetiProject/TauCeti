/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Sobolev
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

/-!
# The planar Newtonian potential of `Lᵖ` data lies in `W^{2,p}_loc`

Let `G = TauCeti.planarNewtonianKernel`, `G(z) = -(2π)⁻¹ log ‖z‖`, be the Newtonian kernel of the
plane `ℂ`, let `1 < p < ∞` and let `f ∈ Lᵖ(ℂ)` have compact support. This file proves that the
Newtonian potential `G ⋆ f` has second weak derivatives in `Lᵖ` on every bounded open set `U`: it
is the value of an element `w` of `W^{2,p}(U)`, and `w` solves Poisson's equation `-Δw = f`
strongly, the trace of its weak Hessian being `-f` almost everywhere in `U`
(`TauCeti.exists_wkp_two_value_ae_eq_planarNewtonianKernel_convolution`). No continuity of `f` is
assumed.

This is dimension two of the regularity half of the constant-coefficient Calderón–Zygmund theory
of the Laplacian. The power-law kernel `TauCeti.newtonianKernel n` covers `n = 1` and `n ≥ 3`
(`TauCeti.exists_wkp_two_value_ae_eq_newtonianKernel_convolution`); in the plane the fundamental
solution is logarithmic. Both are cases of `TauCeti.exists_wkp_two_value_ae_eq_convolution`: the
logarithmic kernel and its derivative are locally integrable
(`TauCeti.locallyIntegrable_planarNewtonianKernel`,
`TauCeti.locallyIntegrable_fderiv_planarNewtonianKernel`), integration by parts against it holds
across the pole (`TauCeti.integral_planarNewtonianKernel_sub_mul_fderiv_eq_neg_fderiv_mul`), and
`-ΔG = δ` (`TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped Convolution

/-- **The planar Newtonian potential of `Lᵖ` data lies in `W^{2,p}_loc`.** Let `1 < p < ∞` and let
`f ∈ Lᵖ(ℂ)` have compact support. On every bounded open set `U ⊆ ℂ`, the Newtonian potential
`G ⋆ f` of the logarithmic kernel `G(z) = -(2π)⁻¹ log ‖z‖` is the value of an element `w` of
`W^{2,p}(U)`, and `w` solves Poisson's equation `-Δw = f` strongly: the trace of its weak Hessian
is `-f` almost everywhere in `U`. -/
theorem exists_wkp_two_value_ae_eq_planarNewtonianKernel_convolution {p : ENNReal}
    [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) {f : ℂ → ℝ} (hf : MemLp f p)
    (hfc : HasCompactSupport f) {U : Opens ℂ} (hU : Bornology.IsBounded (U : Set ℂ)) :
    ∃ w : Wkp volume U p 2,
      (Wkp.value 2 w : ℂ → ℝ) =ᵐ[volume.restrict U] planarNewtonianKernel ⋆ f ∧
      (fun x ↦ LinearMap.trace ℝ ℂ (Wkp.iteratedGradient 1 w x)) =ᵐ[volume.restrict U] -f :=
  exists_wkp_two_value_ae_eq_convolution locallyIntegrable_planarNewtonianKernel
    locallyIntegrable_fderiv_planarNewtonianKernel
    (fun _ hg hgc v t ↦ by
      simpa only [mul_comm] using
        integral_planarNewtonianKernel_sub_mul_fderiv_eq_neg_fderiv_mul hg hgc v t)
    (fun _ hφ hφc t ↦ integral_laplacian_mul_planarNewtonianKernel_sub (hφ.of_le (by simp)) hφc t)
    hp hp_top hf hfc hU

end TauCeti
