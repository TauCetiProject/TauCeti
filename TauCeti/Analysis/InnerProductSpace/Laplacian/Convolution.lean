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
factor, where the distributional identity for the kernel applies.

## Main declarations

* `HasCompactSupport.laplacian_convolution_right`: `Δ (f ⋆[L, μ] g) = f ⋆[L, μ] Δ g`.
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
