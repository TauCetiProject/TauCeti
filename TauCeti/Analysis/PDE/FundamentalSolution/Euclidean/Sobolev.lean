/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Sobolev
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution

/-!
# The Newtonian potential of `Lᵖ` data lies in `W^{2,p}_loc`

Let `n = 1` or `n ≥ 3`, let `Gₙ = TauCeti.newtonianKernel n` be the Newtonian kernel of `ℝⁿ`, let
`1 < p < ∞` and let `f ∈ Lᵖ(ℝⁿ)` have compact support. This file proves that the Newtonian
potential `Gₙ ⋆ f` has second weak derivatives in `Lᵖ` on every bounded open set `U`: it is the
value of an element `w` of `W^{2,p}(U)`, and `w` solves Poisson's equation `-Δw = f` strongly, the
trace of its weak Hessian being `-f` almost everywhere in `U`
(`TauCeti.exists_wkp_two_value_ae_eq_newtonianKernel_convolution`). This is the regularity half
of the constant-coefficient Calderón–Zygmund theory of the Laplacian.

This is the case `K = Gₙ` of `TauCeti.exists_wkp_two_value_ae_eq_convolution`, which applies to
every locally integrable fundamental solution of `-Δ` with a locally integrable weak derivative.
The kernel `Gₙ` and its derivative are locally integrable
(`TauCeti.locallyIntegrable_newtonianKernel`, `TauCeti.locallyIntegrable_fderiv_newtonianKernel`),
integration by parts against it holds across the pole
(`TauCeti.integral_fderiv_mul_newtonianKernel_sub`), and `-ΔGₙ = δ`
(`TauCeti.integral_laplacian_mul_newtonianKernel_sub`). The planar counterpart, with the
logarithmic kernel on `ℂ`, is
`TauCeti.exists_wkp_two_value_ae_eq_planarNewtonianKernel_convolution`.

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

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **The Newtonian potential of `Lᵖ` data lies in `W^{2,p}_loc`.** Let `n = 1` or `n ≥ 3`, let
`1 < p < ∞`, and let `f ∈ Lᵖ(ℝⁿ)` have compact support. On every bounded open set `U`, the
Newtonian potential `Gₙ ⋆ f` is the value of an element `w` of `W^{2,p}(U)`, and `w` solves
Poisson's equation `-Δw = f` strongly: the trace of its weak Hessian is `-f` almost everywhere in
`U`. -/
theorem exists_wkp_two_value_ae_eq_newtonianKernel_convolution (hn : n ≠ 2) (hn0 : n ≠ 0)
    {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) (hf : MemLp f p)
    (hfc : HasCompactSupport f) {U : Opens (EuclideanSpace ℝ (Fin n))}
    (hU : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ w : Wkp volume U p 2,
      (Wkp.value 2 w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict U]
        newtonianKernel n ⋆ f ∧
      (fun x ↦ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (Wkp.iteratedGradient 1 w x))
        =ᵐ[volume.restrict U] -f :=
  exists_wkp_two_value_ae_eq_convolution (locallyIntegrable_newtonianKernel n)
    (locallyIntegrable_fderiv_newtonianKernel n)
    (fun _ hg hgc v t ↦ integral_fderiv_mul_newtonianKernel_sub hg hgc v t)
    (fun _ hφ hφc t ↦ integral_laplacian_mul_newtonianKernel_sub hn hn0 (hφ.of_le (by simp)) hφc t)
    hp hp_top hf hfc hU

end TauCeti
