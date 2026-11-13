/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Green's identity for `H¹` functions and distributional solutions of Poisson's equation

Let `Ω ⊆ ℝⁿ` be open and let `u ∈ H¹(Ω)`. Against a test function `φ` on `Ω`, the energy form of
`-Δ` is Green's identity `∫_Ω ∇φ · ∇u = -∫ Δφ u`, with no boundary condition on `u`. Since the
test functions are dense in `H¹₀(Ω)`, a distributional solution `u ∈ H¹(Ω)` of `-Δu = f`, with
`f ∈ L²(Ω)`, is therefore a weak solution: `∫_Ω ∇v · ∇u = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.

## Main declarations

* `TauCeti.PDE.energyFormH1_one_zero_zero_ofTestFunctionₗ_eq_neg_integral_laplacian_smul`: Green's
  identity `∫_Ω ∇φ · ∇u = -∫ Δφ u` for `u ∈ H¹(Ω)` and a test function `φ`.
* `TauCeti.PDE.energyFormH1_one_zero_zero_eq_setIntegral_of_forall_integral_laplacian_smul_eq`:
  if `u ∈ H¹(Ω)` solves `-Δu = f` in the sense of distributions on `Ω`, with `f ∈ L²(Ω)`, then
  `∫_Ω ∇v · ∇u = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.
* `TauCeti.PDE.isWeakSolutionDirichlet_one_zero_zero_iff_forall_setIntegral_laplacian_mul_eq`:
  `u ∈ H¹₀(Ω)` is a weak solution of `-Δu = f` exactly when `-Δu = f` in the sense of
  distributions on `Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.1.2 (the weak formulation).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open InnerProductSpace Laplacian _root_.MeasureTheory TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι → ℝ}

/-- **Green's identity against a test function.** Let `u ∈ H¹(Ω)` agree almost everywhere on `Ω`
with a function `w`. For a test function `φ` on `Ω`, the energy form of `-Δ` is
`∫_Ω ∇φ · ∇u = -∫ Δφ w`. No boundary condition is imposed on `u`. -/
theorem energyFormH1_one_zero_zero_ofTestFunctionₗ_eq_neg_integral_laplacian_smul [DecidableEq ι]
    {u : W1p mu Omega 2} (hu : W1p.value u =ᵐ[mu.restrict Omega] w) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) x • w x ∂mu := by
  rw [((W1p.hasWeakFDerivOn u).congr_ae hu).integral_laplacian_smul_eq_neg_integral_inner φ,
    neg_neg, energyFormH1_one_zero_zero_apply]
  simp_rw [real_inner_comm (W1p.gradient u _)]
  rw [← φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
  rw [W1p.gradient_ofTestFunctionₗ, hx]
  exact (EuclideanSpace.inner_eq_star_dotProduct _ _).symm

/-- **Distributional solutions of Poisson's equation are weak solutions.** Let `u ∈ H¹(Ω)` agree
almost everywhere on `Ω` with a function `w`, and let `f ∈ L²(Ω)`. If `-Δw = f` in the sense of
distributions on `Ω`, that is `∫ Δφ w = -∫ φ f` for every test function `φ` on `Ω`, then
`∫_Ω ∇v · ∇u = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. No boundary condition is imposed on `u`. -/
theorem energyFormH1_one_zero_zero_eq_setIntegral_of_forall_integral_laplacian_smul_eq
    [DecidableEq ι] {u : W1p mu Omega 2} (hu : W1p.value u =ᵐ[mu.restrict Omega] w)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega))
    (hw : ∀ φ : 𝓓(Omega, ℝ), ∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) x • w x ∂mu =
      -∫ x, (φ : EuclideanSpace ℝ ι → ℝ) x • f x ∂mu)
    (v : W1p0 mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hF := hf.coeFn_toLp
  refine ((forall_energyFormH1_eq_setIntegral_iff_forall_testFunction
    (memLp_energyIntegrand_const_zero_zero 1) (hf.toLp f) u).2
    (fun φ => ?_) v).trans (integral_congr_ae ?_)
  · rw [energyFormH1_one_zero_zero_ofTestFunctionₗ_eq_neg_integral_laplacian_smul hu, hw, neg_neg,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [φ.zero_on_compl hx]]
    refine integral_congr_ae ?_
    filter_upwards [hF] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  · filter_upwards [hF] with x hx
    rw [hx]

/-- **Weak and distributional solutions of Poisson's equation agree on `H¹₀(Ω)`.** For
`u ∈ H¹₀(Ω)` and `f ∈ L²(Ω)`, `u` is a weak solution of `-Δu = f` with Dirichlet boundary
condition exactly when `-Δu = f` in the sense of distributions on `Ω`, that is
`-∫_Ω Δφ u = ∫_Ω f φ` for every test function `φ` on `Ω`. -/
theorem isWeakSolutionDirichlet_one_zero_zero_iff_forall_setIntegral_laplacian_mul_eq
    [DecidableEq ι] (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u ↔
      ∀ φ : 𝓓(Omega, ℝ), -∫ x in Omega, Δ (φ : EuclideanSpace ℝ ι → ℝ) x *
        W1p.value (u : W1p mu Omega 2) x ∂mu = ∫ x in Omega, f x * φ x ∂mu := by
  rw [isWeakSolutionDirichlet_iff_forall_testFunction (memLp_energyIntegrand_const_zero_zero 1)]
  refine forall_congr' fun φ => ?_
  -- The integral of `Δφ • u` over the whole space only sees `Ω`, which carries `Δφ`.
  rw [energyFormH1_one_zero_zero_ofTestFunctionₗ_eq_neg_integral_laplacian_smul
    Filter.EventuallyEq.rfl φ, ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h' =>
        hx (φ.tsupport_subset (tsupport_laplacian_subset _ h')), zero_smul]]
  simp_rw [smul_eq_mul]

end PDE

end TauCeti
