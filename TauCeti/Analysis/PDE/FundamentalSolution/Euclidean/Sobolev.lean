/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Convolution.CompactSupport
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.WeakSolution
import TauCeti.Analysis.PDE.Regularity.Hessian.Poisson

/-!
# The Newtonian potential of `Lᵖ` data lies in `W^{2,p}_loc`

Let `n = 1` or `n ≥ 3`, let `Gₙ = TauCeti.newtonianKernel n` be the Newtonian kernel of `ℝⁿ`, let
`1 < p < ∞` and let `f ∈ Lᵖ(ℝⁿ)` have compact support. This file proves that the Newtonian
potential `Gₙ ⋆ f` has second weak derivatives in `Lᵖ` on every bounded open set `U`: it is the
value of an element `w` of `W^{2,p}(U)`, and `w` solves Poisson's equation `-Δw = f` strongly, the
trace of its weak Hessian being `-f` almost everywhere in `U`
(`TauCeti.exists_wkp_two_value_ae_eq_newtonianKernel_convolution`). This is the regularity half
of the constant-coefficient Calderón–Zygmund theory of the Laplacian.

The potential is weakly differentiable with gradient `∇Gₙ ⋆ f`
(`TauCeti.hasWeakFDerivOn_newtonianKernel_convolution`), and both it and its gradient lie in `Lᵖ`
on bounded sets by Young's inequality, since `Gₙ` and `∇Gₙ` are locally integrable
(`HasCompactSupport.memLp_convolution_right_of_isBounded`). So it lies in `W^{1,p}` of a ball
containing `U`, where it solves `-Δ(Gₙ ⋆ f) = f` in the sense of distributions
(`TauCeti.integral_laplacian_mul_newtonianKernel_convolution`). Interior `W^{2,p}` regularity for
Poisson's equation (`TauCeti.W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq`)
then gives the second derivatives on `U`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.3.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Distributions Laplacian

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
        =ᵐ[volume.restrict U] -f := by
  -- Work on a ball `Ω` whose interior contains the closure of `U`.
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  let Ω : Opens (EuclideanSpace ℝ (Fin n)) := ⟨ball 0 (R + 1), isOpen_ball⟩
  have hUΩ : closure (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Ω :=
    (closure_minimal hR isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  have hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin n))) := isBounded_ball
  -- `f` is integrable, being `Lᵖ` on the compact set carrying it.
  have hfi : Integrable f := (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
    ((hf.locallyIntegrable hp.le).integrableOn_isCompact hfc.isCompact)
  -- The potential lies in `W^{1,p}(Ω)`, with weak gradient `∇Gₙ ⋆ f`.
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    (hfc.memLp_convolution_right_of_isBounded _ (locallyIntegrable_newtonianKernel n) hf hp.le hΩ)
    (hfc.memLp_convolution_right_of_isBounded _ (locallyIntegrable_fderiv_newtonianKernel n) hf
      hp.le hΩ)
    (hasWeakFDerivOn_newtonianKernel_convolution hfi hfc Ω)
  -- It solves `Δu = -f` against the test functions on `Ω`.
  have heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • W1p.value u x =
      ∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • (-f) x := fun φ ↦ by
    have hu' := (ae_restrict_iff' Ω.isOpen.measurableSet).1 hu
    calc ∫ x, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • W1p.value u x
        = ∫ x, Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x * (newtonianKernel n ⋆ f) x := by
          refine integral_congr_ae (hu'.mono fun x hx ↦ ?_)
          by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          · simp only [smul_eq_mul, hx hxΩ]
          · have hΔ : Δ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 :=
              laplacian_of_notMem_tsupport fun h ↦ hxΩ (φ.tsupport_subset h)
            simp [hΔ]
      _ = -∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x * f x :=
          integral_laplacian_mul_newtonianKernel_convolution hn hn0 hfi hfc
            (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
      _ = ∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x • (-f) x := by
          simp [← integral_neg]
  obtain ⟨w, hwv, hwtr⟩ := W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq hp
    hp_top (hU.isCompact_closure) hUΩ u (hf.neg.restrict _) heq
  exact ⟨w, hwv.trans (ae_restrict_of_ae_restrict_of_subset
    (subset_closure.trans hUΩ) hu), hwtr⟩

end TauCeti
