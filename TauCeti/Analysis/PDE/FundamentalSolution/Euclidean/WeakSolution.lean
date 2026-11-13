/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.CompactSupport
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
import TauCeti.Analysis.PDE.WeakLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Convolution

/-!
# The Newtonian potential of square-integrable data

Let `n ≥ 3`, let `Gₙ = TauCeti.newtonianKernel n` be the Newtonian kernel of `ℝⁿ`, and let `f` be
integrable with compact support. The Newtonian potential `Gₙ ⋆ f`,
`(Gₙ ⋆ f) x = ∫ Gₙ(x - y) f(y) dy`, of a `C²` function `f` is a classical solution of Poisson's
equation `-Δu = f` (`TauCeti.laplacian_newtonianKernel_convolution`). This file shows that for
rough data it is a weak solution:

* `Gₙ ⋆ f` is weakly differentiable on every open set, with weak derivative `∇Gₙ ⋆ f`, the
  convolution of `f` with the locally integrable derivative of the kernel
  (`TauCeti.hasWeakFDerivOn_newtonianKernel_convolution`);
* `-Δ(Gₙ ⋆ f) = f` in the sense of distributions: `∫ Δφ (Gₙ ⋆ f) = -∫ φ f` for every `C²`
  function `φ` with compact support (`TauCeti.integral_laplacian_mul_newtonianKernel_convolution`);
* if `f ∈ L²`, then on every bounded open set `Ω` the potential lies in `H¹(Ω)` and satisfies
  `∫_Ω ∇v · ∇(Gₙ ⋆ f) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`
  (`TauCeti.PDE.exists_value_ae_eq_newtonianKernel_convolution_and_energyFormH1_eq`).

The last statement gives the **Green representation of the weak Dirichlet solution for `L²`
data**. Let `u ∈ H¹₀(Ω)` be the weak solution of `-Δu = f` in `Ω`, `u = 0` on `∂Ω`, given by the
Lax--Milgram theorem. The difference `Gₙ ⋆ f - u` lies in `H¹(Ω)` and solves `Δh = 0` weakly, so by
Weyl's lemma it agrees almost everywhere with a harmonic function `h`, and

`u = Gₙ ⋆ f - h` almost everywhere on `Ω`

(`TauCeti.PDE.IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq_of_memLp`). Since
`u ∈ H¹₀(Ω)`, the harmonic correction `h` has the boundary values of the Newtonian potential, as
the theorem also states: `h - Gₙ ⋆ f ∈ H¹₀(Ω)`, which is the trace condition `h = Gₙ ⋆ f` on `∂Ω`
when `Ω` is a bounded Lipschitz domain
(`TauCeti.W1p.mem_w1p0Submodule_iff_frontierTrace_eq_zero`). So `h` is the
harmonic replacement of `Gₙ ⋆ f`, which is unique
(`TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq`). For `C²` data with
compact support and `Ω` a ball the same representation holds with `h` continuous up to the
sphere and equal to `Gₙ ⋆ f` there
(`TauCeti.PDE.IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq`); here neither
smoothness of the data nor regularity of `∂Ω` is used.

## The argument

The kernel is locally integrable with locally integrable derivative
(`TauCeti.locallyIntegrable_newtonianKernel`, `TauCeti.locallyIntegrable_fderiv_newtonianKernel`),
and integration by parts against it holds across the pole
(`TauCeti.integral_fderiv_mul_newtonianKernel_sub`). Pairing the potential with a test function
`ψ` and exchanging the integrals
(`MeasureTheory.integral_mul_convolution_eq_integral_mul_integral_left_comp_sub`),

`∫ ψ (Gₙ ⋆ f) = ∫ f(y) (∫ ψ(x) Gₙ(x - y) dx) dy`,

moves every derivative from the potential onto the kernel with pole `y`. With `ψ = ∂ᵥφ` this gives
the weak derivative (`TauCeti.hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub`),
and with `ψ = Δφ` the distributional identity `-ΔGₙ = δ`
(`TauCeti.integral_laplacian_mul_newtonianKernel_sub`) gives Poisson's equation. Square
integrability on bounded sets is Young's inequality applied to the kernel cut off to a ball
(`HasCompactSupport.memLp_convolution_right_of_isBounded`). Poisson's equation against the test
functions on `Ω` then gives the weak formulation against `H¹₀(Ω)`
(`TauCeti.PDE.energyFormH1_one_zero_zero_eq_setIntegral_of_forall_integral_laplacian_smul_eq`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.2.1 (the Newtonian potential)
  and Section 6.2 (weak solutions).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.1 (the gradient of the Newtonian potential is the potential of the kernel's gradient).
* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Theorem 6.21 (the Newtonian potential of locally
  integrable data solves Poisson's equation in the sense of distributions).
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace ContinuousLinearMap
open scoped Convolution Distributions Gradient InnerProductSpace

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **The Newtonian potential is weakly differentiable.** In every dimension, for `f` integrable
with compact support, the derivative of the Newtonian potential `Gₙ ⋆ f` on every open set is,
weakly, the convolution `∇Gₙ ⋆ f`, `x ↦ ∫ f(x - y) • DGₙ(y) dy`, of `f` with the locally
integrable derivative of the kernel. -/
theorem hasWeakFDerivOn_newtonianKernel_convolution (hf : Integrable f)
    (hfc : HasCompactSupport f) (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    HasWeakFDerivOn volume Ω (newtonianKernel n ⋆ f)
      (fderiv ℝ (newtonianKernel n) ⋆[(lsmul ℝ ℝ).flip] f) :=
  hasWeakFDerivOn_convolution_of_forall_integral_fderiv_mul_sub
    (locallyIntegrable_newtonianKernel n) (locallyIntegrable_fderiv_newtonianKernel n)
    (fun _ hg hgc v t ↦ integral_fderiv_mul_newtonianKernel_sub hg hgc v t) hf hfc Ω

/-- **The Newtonian potential solves Poisson's equation in the sense of distributions.** For
`n ≥ 3` and `f` integrable with compact support, `-Δ(Gₙ ⋆ f) = f` weakly: for every `C²` function
`φ` with compact support, `∫ Δφ (Gₙ ⋆ f) = -∫ φ f`. -/
theorem integral_laplacian_mul_newtonianKernel_convolution (hn : 3 ≤ n) (hf : Integrable f)
    (hfc : HasCompactSupport f) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, Δ φ x * (newtonianKernel n ⋆ f) x = -∫ x, φ x * f x := by
  rw [integral_mul_convolution_eq_integral_mul_integral_left_comp_sub hφ.continuous_laplacian
    hφc.laplacian (locallyIntegrable_newtonianKernel n) hf hfc, ← integral_neg]
  simp_rw [integral_laplacian_mul_newtonianKernel_sub (by omega) (by omega) hφ hφc, mul_neg,
    mul_comm]

namespace PDE

/-- **The Newtonian potential of `L²` data is a weak solution of Poisson's equation in `H¹`.** Let
`n ≥ 3`, let `Ω ⊆ ℝⁿ` be a bounded open set and let `f ∈ L²(ℝⁿ)` have compact support. Then the
Newtonian potential `Gₙ ⋆ f` is represented on `Ω` by an element `w` of `H¹(Ω)`, whose weak
gradient is the convolution `∇Gₙ ⋆ f`, and `w` solves `-Δw = f` weakly in `Ω`:
`∫_Ω ∇v · ∇w = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. No boundary condition is imposed on `w`. -/
theorem exists_value_ae_eq_newtonianKernel_convolution_and_energyFormH1_eq (hn : 3 ≤ n)
    {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin n))))
    (hf : MemLp f 2) (hfc : HasCompactSupport f) :
    ∃ w : W1p volume Omega 2,
      W1p.value w =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))]
        newtonianKernel n ⋆ f ∧
      W1p.gradient w =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))]
        (fun x ↦ (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          ((fderiv ℝ (newtonianKernel n) ⋆[(lsmul ℝ ℝ).flip] f) x)) ∧
      ∀ v : W1p0 volume Omega 2, energyFormH1 (fun _ => 1) 0 0 w (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x := by
  -- `f` is integrable, being square integrable on the compact set carrying it.
  have hfi : Integrable f := (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
    ((hf.locallyIntegrable one_le_two).integrableOn_isCompact hfc.isCompact)
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    (hfc.memLp_convolution_right_of_isBounded _ (locallyIntegrable_newtonianKernel n) hf
      one_le_two hOmega)
    (hfc.memLp_convolution_right_of_isBounded _ (locallyIntegrable_fderiv_newtonianKernel n) hf
      one_le_two hOmega)
    (hasWeakFDerivOn_newtonianKernel_convolution hfi hfc Omega)
  refine ⟨w, hwv, hwg,
    energyFormH1_one_zero_zero_eq_setIntegral_of_forall_integral_laplacian_smul_eq hwv
      (hf.restrict _) fun φ ↦ ?_⟩
  simpa only [smul_eq_mul] using integral_laplacian_mul_newtonianKernel_convolution hn hfi hfc
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

/-- **The Green representation of the weak Dirichlet solution for `L²` data.** Let `n ≥ 3`, let
`Ω ⊆ ℝⁿ` be a bounded open set, let `f ∈ L²(ℝⁿ)` have compact support and let `g ∈ L²(Ω)` agree
with `f` on `Ω`. If `u ∈ H¹₀(Ω)` is the weak solution of `-Δu = g` in `Ω`, `u = 0` on `∂Ω`, then
`u` is the Newtonian potential corrected by a harmonic function: there is `h`, harmonic on `Ω`,
with `u = Gₙ ⋆ f - h` almost everywhere on `Ω`, and `h` has the boundary values of `Gₙ ⋆ f` in the
Sobolev sense: both lie in `H¹(Ω)`, represented by some `w` and `H`, with `w - H ∈ H¹₀(Ω)`. -/
theorem IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq_of_memLp (hn : 3 ≤ n)
    {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin n))))
    (hf : MemLp f 2) (hfc : HasCompactSupport f)
    {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n))))}
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))] f)
    {u : W1p0 volume Omega 2} (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ, HarmonicOnNhd h Omega ∧
      (∃ w H : W1p volume Omega 2,
        W1p.value w =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))]
          newtonianKernel n ⋆ f ∧
        W1p.value H =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))] h ∧
        w - H ∈ w1p0Submodule volume Omega 2) ∧
      W1p.value (u : W1p volume Omega 2)
        =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))]
          newtonianKernel n ⋆ f - h := by
  obtain ⟨w, hwv, -, hw⟩ :=
    exists_value_ae_eq_newtonianKernel_convolution_and_energyFormH1_eq hn hOmega hf hfc
  -- The difference `w - u` of the potential and the solution is weakly harmonic.
  have hH : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 (w - (u : W1p volume Omega 2)) (v : W1p volume Omega 2) = 0 :=
        fun v ↦ by
    rw [energyFormH1_sub_left (memLp_energyIntegrand_const_zero_zero 1), hw v,
      (isWeakSolutionDirichlet_iff g u).1 hu v, sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  obtain ⟨h, hh, hHh⟩ := exists_harmonicOnNhd_ae_eq_of_forall_energyFormH1_eq_zero fun φ ↦
    hH ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  refine ⟨h, hh, ⟨w, w - u, hwv, hHh, by rw [sub_sub_cancel]; exact u.2⟩, ?_⟩
  filter_upwards [W1p.value_sub_ae w (u : W1p volume Omega 2), hwv, hHh] with x h₁ h₂ h₃
  rw [Pi.sub_apply, ← h₂, ← h₃, h₁, Pi.sub_apply, sub_sub_cancel]

end PDE

end TauCeti
