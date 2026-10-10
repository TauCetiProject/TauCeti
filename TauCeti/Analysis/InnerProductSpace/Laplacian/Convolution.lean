/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian of a convolution

On a finite-dimensional real inner product space, convolution with a locally integrable function
commutes with the Laplacian on `C²` functions with compact support:

`Δ (f ⋆ g) = f ⋆ Δ g`.

Each second directional derivative passes onto `g` by the rule `∂ᵥ (f ⋆ g) = f ⋆ ∂ᵥ g`
(`HasCompactSupport.fderiv_convolution_right_apply`), and the Laplacian is their sum along an
orthonormal basis (`TauCeti.laplacian_eq_sum_fderiv_fderiv_apply`).

This is how a convolution against a fundamental solution, such as the Newtonian potential, is
shown to solve Poisson's equation: the Laplacian moves onto the smooth compactly supported
factor, where the distributional identity for the kernel applies
(`TauCeti.laplacian_convolution_eq_neg_of_integral_laplacian_mul`).

## Main declarations

* `HasCompactSupport.laplacian_convolution_right`: `Δ (f ⋆[L, μ] g) = f ⋆[L, μ] Δ g`.
* `TauCeti.laplacian_convolution_eq_neg_of_integral_laplacian_mul`: if `-ΔK = δ` in the sense of
  distributions, then `-Δ (K ⋆ f) = f` for every `C²` function `f` with compact support.
-/

public section

open ContinuousLinearMap InnerProductSpace Laplacian MeasureTheory
open scoped Convolution

variable {E E₀ E' F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E₀} {g : E → E'}

/-- **The Laplacian of a convolution.** If `f` is locally integrable and `g` is `C²` with compact
support, then `Δ (f ⋆ g) = f ⋆ Δ g`. -/
theorem HasCompactSupport.laplacian_convolution_right (L : E₀ →L[ℝ] E' →L[ℝ] F)
    (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ) (hg : ContDiff ℝ 2 g) :
    Δ (f ⋆[L, μ] g) = f ⋆[L, μ] Δ g := by
  set b := stdOrthonormalBasis ℝ E
  -- The directional derivatives of `g` are again compactly supported, and `C¹`.
  have hdir : ∀ v : E, HasCompactSupport (fun y => fderiv ℝ g y v) ∧
      ContDiff ℝ 1 (fun y => fderiv ℝ g y v) := fun v =>
    ⟨(hcg.fderiv (𝕜 := ℝ)).comp_left (g := fun A : E →L[ℝ] E' => A v) (zero_apply v),
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const⟩
  -- Each second directional derivative of `f ⋆ g` is the convolution of `f` with that of `g`.
  have hterm : ∀ x v, fderiv ℝ (fun y => fderiv ℝ (f ⋆[L, μ] g) y v) x v =
      (f ⋆[L, μ] fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v) x := fun x v => by
    rw [funext fun y => hcg.fderiv_convolution_right_apply L hf (hg.of_le (by norm_num)) y v,
      (hdir v).1.fderiv_convolution_right_apply L hf (hdir v).2 x v]
  funext x
  have hu : DifferentiableAt ℝ (fderiv ℝ (f ⋆[L, μ] g)) x :=
    ((hcg.contDiff_convolution_right L hf hg).fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero x
  have hint : ∀ i ∈ Finset.univ, Integrable
      (fun t => L (f t) (fderiv ℝ (fun z => fderiv ℝ g z (b i)) (x - t) (b i))) μ := fun i _ =>
    ((hdir (b i)).1.fderiv (𝕜 := ℝ)).comp_left (g := fun A : E →L[ℝ] E' => A (b i))
      (zero_apply _) |>.convolutionExists_right L hf
      (((hdir (b i)).2.continuous_fderiv one_ne_zero).clm_apply continuous_const) x
  simp_rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply b hu, hterm, convolution_def]
  rw [← integral_finsetSum _ hint]
  congr 1 with t
  rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply b
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero (x - t)), map_sum]

namespace TauCeti

/-- **Convolution with a fundamental solution solves Poisson's equation.** Let `K` be locally
integrable with `-ΔK = δ` in the sense of distributions, tested against real `C²` functions with
compact support: `∫ Δφ(y) K(x - y) dy = -φ x` for every such `φ` and every `x`. Then for every
`f` of class `C²` with compact support, `Δ (K ⋆ f) = -f`. -/
theorem laplacian_convolution_eq_neg_of_integral_laplacian_mul [μ.IsNegInvariant]
    [CompleteSpace F] {K : E → ℝ} {f : E → F} (hK : LocallyIntegrable K μ)
    (hKΔ : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ x,
      ∫ y, Δ φ y * K (x - y) ∂μ = -φ x)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : Δ (K ⋆[lsmul ℝ ℝ, μ] f) = -f := by
  rw [hc.laplacian_convolution_right _ hK hf]
  funext x
  have hΔc : HasCompactSupport (Δ f) :=
    hc.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset f))
  have hΔcont : Continuous (Δ f) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    have := hf.continuous_iteratedFDeriv (m := 2) le_rfl
    fun_prop
  have hint := hΔc.convolutionExists_right (lsmul ℝ ℝ) hK hΔcont x
  -- Test against every continuous linear functional `φ`, which reduces to real values.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ => ?_
  have hφf : ContDiff ℝ 2 (φ ∘ f) := φ.contDiff.comp hf
  calc φ ((K ⋆[lsmul ℝ ℝ, μ] Δ f) x)
      = ∫ t, K t * φ (Δ f (x - t)) ∂μ := by
        rw [convolution_def, ← φ.integral_comp_comm hint]
        simp
    _ = ∫ y, Δ (φ ∘ f) y * K (x - y) ∂μ := by
        rw [← integral_sub_left_eq_self _ μ x]
        congr 1 with y
        rw [sub_sub_cancel, hf.contDiffAt.laplacian_CLM_comp_left, Function.comp_apply, mul_comm]
    _ = φ ((-f) x) := by
        rw [hKΔ _ hφf (hc.comp_left φ.map_zero) x]
        simp

end TauCeti
