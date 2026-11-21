/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Convolution.CompactSupport
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.PDE.Regularity.Hessian.Poisson
import TauCeti.Analysis.Sobolev.WeakDeriv.Convolution

/-!
# Potentials of a fundamental solution of the Laplacian lie in `W^{2,p}_loc`

Let `E` be a finite-dimensional real inner product space and let `K : E → ℝ` be a fundamental
solution of `-Δ` with a weak derivative `K'`, both locally integrable: integration by parts
against `K` holds across its singularity,

`∫ ∂ᵥg (x) K(x - t) dx = -∫ g(x) K'(x - t) v dx`,

and `-ΔK = δ`, in the form `∫ Δφ (x) K(x - t) dx = -φ(t)`, for every pole `t`, every `C¹`
function `g` and every smooth function `φ` with compact support. This file proves that for
`1 < p < ∞` and `f ∈ Lᵖ(E)` with compact support the potential `K ⋆ f` has second weak derivatives
in `Lᵖ` on every bounded open set `U`: it is the value of an element `w` of `W^{2,p}(U)`, and `w`
solves Poisson's equation `-Δw = f` strongly, the trace of its weak Hessian being `-f` almost
everywhere in `U` (`TauCeti.exists_wkp_two_value_ae_eq_convolution`).

The Newtonian kernels are such fundamental solutions, in the form `TauCeti.newtonianKernel n` on
`ℝⁿ` for `n ≠ 0, 2` and `TauCeti.planarNewtonianKernel` on `ℂ`. The corresponding statements are
`TauCeti.exists_wkp_two_value_ae_eq_newtonianKernel_convolution` and
`TauCeti.exists_wkp_two_value_ae_eq_planarNewtonianKernel_convolution`. Together they are the
regularity half of the constant-coefficient Calderón–Zygmund theory of the Laplacian in every
positive dimension.

## The argument

The potential is weakly differentiable with gradient `K' ⋆ f`
(`TauCeti.hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub`), and both it and its
gradient lie in `Lᵖ` on bounded sets by Young's inequality
(`HasCompactSupport.memLp_convolution_right_of_isBounded`). So it lies in `W^{1,p}` of a ball
containing `U`. Pairing it with `Δφ` and exchanging the integrals
moves the Laplacian onto the kernel, where `-ΔK = δ` gives `-Δ(K ⋆ f) = f` in the sense of
distributions (`TauCeti.integral_laplacian_mul_convolution_of_forall_integral_laplacian_mul_sub`).
Interior `W^{2,p}` regularity for Poisson's equation
(`TauCeti.W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq`) then gives the second
derivatives on `U`.

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
open scoped Convolution ContDiff Distributions Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The potential of a fundamental solution of `-Δ` lies in `W^{2,p}_loc`.** Let `K` be locally
integrable with locally integrable weak derivative `K'`, in the sense that
`∫ ∂ᵥg (x) K(x - t) dx = -∫ g(x) K'(x - t) v dx` for every `C¹` function `g` with compact support,
and let `-ΔK = δ`: `∫ Δφ (x) K(x - t) dx = -φ(t)` for every smooth `φ` with compact support.
Let `1 < p < ∞` and let `f ∈ Lᵖ(E)` have compact support. On every bounded open set `U`, the
potential `K ⋆ f` is the value of an element `w` of `W^{2,p}(U)`, and `w` solves Poisson's equation
`-Δw = f` strongly: the trace of its weak Hessian is `-f` almost everywhere in `U`. -/
theorem exists_wkp_two_value_ae_eq_convolution {K : E → ℝ} {K' : E → E →L[ℝ] ℝ}
    (hK : LocallyIntegrable K) (hK' : LocallyIntegrable K')
    (hibp : ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ v t,
      ∫ x, fderiv ℝ g x v * K (x - t) = -∫ x, g x * K' (x - t) v)
    (hΔ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ t,
      ∫ x, Δ φ x * K (x - t) = -φ t)
    {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) {f : E → ℝ} (hf : MemLp f p)
    (hfc : HasCompactSupport f) {U : Opens E} (hU : Bornology.IsBounded (U : Set E)) :
    ∃ w : Wkp volume U p 2,
      (Wkp.value 2 w : E → ℝ) =ᵐ[volume.restrict U] K ⋆ f ∧
      (fun x ↦ LinearMap.trace ℝ E (Wkp.iteratedGradient 1 w x)) =ᵐ[volume.restrict U] -f := by
  -- Work on a ball `Ω` whose interior contains the closure of `U`.
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  let Ω : Opens E := ⟨ball 0 (R + 1), isOpen_ball⟩
  have hUΩ : closure (U : Set E) ⊆ Ω :=
    (closure_minimal hR isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  -- `f` is integrable, being `Lᵖ` on the compact set carrying it.
  have hfi : Integrable f := (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
    ((hf.locallyIntegrable hp.le).integrableOn_isCompact hfc.isCompact)
  -- The potential lies in `W^{1,p}(Ω)`, with weak gradient `K' ⋆ f`.
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    (hfc.memLp_convolution_right_of_isBounded _ hK hf hp.le isBounded_ball)
    (hfc.memLp_convolution_right_of_isBounded _ hK' hf hp.le isBounded_ball)
    (hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub hK hK' hibp hfi hfc Ω)
  -- It solves `Δu = -f` against the test functions on `Ω`.
  have heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • W1p.value u x =
      ∫ x, (φ : E → ℝ) x • (-f) x := fun φ ↦ by
    have hu' := (ae_restrict_iff' Ω.isOpen.measurableSet).1 hu
    have hφ : ContDiff ℝ 2 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
    calc ∫ x, Δ (φ : E → ℝ) x • W1p.value u x = ∫ x, Δ (φ : E → ℝ) x * (K ⋆ f) x := by
          refine integral_congr_ae (hu'.mono fun x hx ↦ ?_)
          by_cases hxΩ : x ∈ (Ω : Set E)
          · simp only [smul_eq_mul, hx hxΩ]
          · have hΔφ : Δ (φ : E → ℝ) x = 0 :=
              laplacian_of_notMem_tsupport fun h ↦ hxΩ (φ.tsupport_subset h)
            simp [hΔφ]
      _ = -∫ x, (φ : E → ℝ) x * f x :=
          integral_laplacian_mul_convolution_of_forall_integral_laplacian_mul_sub hK hφ
            φ.hasCompactSupport (hΔ _ φ.contDiff φ.hasCompactSupport) hfi hfc
      _ = ∫ x, (φ : E → ℝ) x • (-f) x := by
          simp [integral_neg]
  obtain ⟨w, hwv, hwtr⟩ := W1p.exists_wkp_two_value_ae_eq_of_integral_laplacian_smul_eq hp
    hp_top hU.isCompact_closure hUΩ u (hf.neg.restrict _) heq
  exact ⟨w, hwv.trans (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUΩ) hu), hwtr⟩

end TauCeti
