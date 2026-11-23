/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Convex.Strong
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Smooth approximation preserving uniform concavity

Positive normalized convolution preserves a uniform concavity modulus on a convex set when
all translated sampling points lie in the original domain. Only existence of the convolution
at points of the smaller set is required.

A single buffered-domain mollification construction gives smooth approximations with the
original Lipschitz constant, arbitrary strict uniform error and the original concavity modulus
on the smaller domain. McShane extension handles data defined only on the larger domain.
For signed strong concavity, the pointwise second-derivative criterion gives classical Hessian
upper bounds on buffered convex domains, including when the original data are nonsmooth.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set ContinuousLinearMap MeasureTheory Metric
open scoped Convolution NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Convolution

variable [MeasurableSpace E] {μ : Measure E}

/-- Nonnegative integral-one convolution preserves a uniform concavity modulus wherever
its translated sampling points lie in the original domain. Existence is needed only on `s`. -/
theorem UniformConcaveOn.convolution_lsmul {ρ f : E → ℝ} {ψ : ℝ → ℝ} {s T : Set E}
    (hconc : UniformConcaveOn T ψ f) (hρ0 : ∀ t, 0 ≤ ρ t) (hρ1 : ∫ t, ρ t ∂μ = 1)
    (hs : Convex ℝ s) (hf : ∀ x ∈ s, ConvolutionExistsAt ρ f x (lsmul ℝ ℝ) μ)
    (hsub : ∀ t ∈ Function.support ρ, ∀ x ∈ s, x - t ∈ T) :
    UniformConcaveOn s ψ (ρ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hi (x : E) (hx : x ∈ s) : Integrable (fun t ↦ ρ t * f (x - t)) μ := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using hf x hx
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := hs hx hy ha hb hab
  have hil := ((hi x hx).const_mul a).add ((hi y hy).const_mul b)
  have hic := (integrable_of_integral_eq_one hρ1).mul_const (a * b * ψ ‖x - y‖)
  have hsplit : (fun t ↦ ρ t *
      (a * f (x - t) + b * f (y - t) + a * b * ψ ‖x - y‖)) =
      ((fun t ↦ a * (ρ t * f (x - t))) +
        (fun t ↦ b * (ρ t * f (y - t)))) + fun t ↦ ρ t * (a * b * ψ ‖x - y‖) := by
    ext t
    simp only [Pi.add_apply]
    ring
  have hl : Integrable (fun t ↦ ρ t *
      (a * f (x - t) + b * f (y - t) + a * b * ψ ‖x - y‖)) μ := by
    rw [hsplit]
    exact hil.add hic
  have hle : (∫ t, ρ t *
      (a * f (x - t) + b * f (y - t) + a * b * ψ ‖x - y‖) ∂μ) ≤
      ∫ t, ρ t * f ((a • x + b • y) - t) ∂μ := by
    apply integral_mono hl (hi _ hxy)
    intro t
    by_cases ht : t ∈ Function.support ρ
    · exact mul_le_mul_of_nonneg_left
        ((hconc.comp_sub hs t (hsub t ht)).2 hx hy ha hb hab) (hρ0 t)
    · simp only [Function.notMem_support.mp ht, zero_mul, le_refl]
  calc
    a * (ρ ⋆[lsmul ℝ ℝ, μ] f) x + b * (ρ ⋆[lsmul ℝ ℝ, μ] f) y +
        a * b * ψ ‖x - y‖ = ∫ t, ρ t *
          (a * f (x - t) + b * f (y - t) + a * b * ψ ‖x - y‖) ∂μ := by
      simp only [convolution_def, lsmul_apply, smul_eq_mul]
      rw [hsplit, integral_add' hil hic,
        integral_add' ((hi x hx).const_mul a) ((hi y hy).const_mul b)]
      simp [integral_const_mul, integral_mul_const, hρ1]
    _ ≤ ∫ t, ρ t * f ((a • x + b • y) - t) ∂μ := hle
    _ = (ρ ⋆[lsmul ℝ ℝ, μ] f) (a • x + b • y) := by
      simp only [convolution_def, lsmul_apply, smul_eq_mul]

/-- A normalized bump preserves uniform concavity using only local measure finiteness and
positivity on nonempty open sets; no Haar invariance is required. -/
theorem UniformConcaveOn.normed_convolution [FiniteDimensional ℝ E] [BorelSpace E]
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : E → ℝ} {ψ : ℝ → ℝ} {s T : Set E}
    (hconc : UniformConcaveOn T ψ f) (φ : ContDiffBump (0 : E)) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, ConvolutionExistsAt (φ.normed μ) f x (lsmul ℝ ℝ) μ)
    (hsub : ∀ t ∈ ball (0 : E) φ.rOut, ∀ x ∈ s, x - t ∈ T) :
    UniformConcaveOn s ψ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  hconc.convolution_lsmul φ.nonneg_normed φ.integral_normed hs hf
    (fun t ht ↦ hsub t (φ.support_normed_eq (μ := μ) ▸ ht))

end Convolution

variable [FiniteDimensional ℝ E]

/-- Buffered convex domains admit smooth approximations retaining the Lipschitz constant
and uniform concavity modulus, with strict uniform error on the entire space. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_lt_uniformConcaveOn
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {s T : Set E} {ψ : ℝ → ℝ}
    (hs : Convex ℝ s) (hconc : UniformConcaveOn T ψ f)
    {δ : ℝ} (hδ : 0 < δ) (hsub : thickening δ s ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) < ε) ∧ UniformConcaveOn s ψ u := by
  borelize E
  obtain ⟨φ, hrOut, hsmooth, hLip, herr⟩ := hf.exists_contDiffBump_normed_convolution hδ hε
  have hi := (φ.hasCompactSupport_normed (μ := Measure.addHaar)).convolutionExists_left
    (lsmul ℝ ℝ) (φ.continuous_normed (μ := Measure.addHaar))
    (hf.continuous.locallyIntegrable (μ := Measure.addHaar))
  refine ⟨φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f,
    hsmooth, hLip, herr, hconc.normed_convolution φ hs (fun x _ ↦ hi x) ?_⟩
  intro t ht x hx
  apply hsub
  refine mem_thickening_iff.2 ⟨x, hx, ?_⟩
  rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact (mem_ball_zero_iff.1 ht).trans_le hrOut

/-- Lipschitz data on a buffered domain admit smooth global Lipschitz approximations,
strictly close on that domain and uniformly concave on the prescribed smaller convex set. -/
theorem LipschitzOnWith.exists_contDiff_lipschitzWith_dist_lt_uniformConcaveOn
    {f : E → ℝ} {K : ℝ≥0} {s T : Set E} (hf : LipschitzOnWith K f T)
    {ψ : ℝ → ℝ} (hs : Convex ℝ s) (hconc : UniformConcaveOn T ψ f)
    {δ : ℝ} (hδ : 0 < δ) (hsub : thickening δ s ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ T, dist (u x) (f x) < ε) ∧ UniformConcaveOn s ψ u := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hc : UniformConcaveOn T ψ F := hconc.congr heq
  obtain ⟨u, hu, hLu, herr, hcu⟩ :=
    hF.exists_contDiff_lipschitzWith_dist_lt_uniformConcaveOn hs hc hδ hsub hε
  exact ⟨u, hu, hLu, fun x hx ↦ by simpa only [heq hx] using herr x, hcu⟩

/-- Buffered strongly concave Lipschitz data admit a smooth global Lipschitz approximant
with strict error on the original domain and a Hessian upper bound on the smaller convex set. -/
theorem LipschitzOnWith.exists_contDiff_lipschitzWith_dist_lt_fderiv_fderiv_le
    {f : E → ℝ} {K : ℝ≥0} {s T : Set E} {m : ℝ} (hf : LipschitzOnWith K f T)
    (hs : Convex ℝ s) (hconc : StrongConcaveOn T m f)
    {δ : ℝ} (hδ : 0 < δ) (hsub : thickening δ s ⊆ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x ∈ T, dist (u x) (f x) < ε) ∧ StrongConcaveOn s m u ∧ ∀ x ∈ s, ∀ v : E,
        fderiv ℝ (fderiv ℝ u) x v v ≤ -m * ‖v‖ ^ 2 := by
  have hhalf : 0 < δ / 2 := half_pos hδ
  have hbuffer : thickening (δ / 2) (thickening (δ / 2) s) ⊆ T := by
    apply Subset.trans (thickening_thickening_subset _ _ _)
    simpa only [add_halves] using hsub
  obtain ⟨u, hu, hLu, herr, hcu⟩ :=
    hf.exists_contDiff_lipschitzWith_dist_lt_uniformConcaveOn (hs.thickening _)
      (TauCeti.strongConcaveOn_iff_uniformConcaveOn.mp hconc) hhalf hbuffer hε
  have hcu := TauCeti.strongConcaveOn_iff_uniformConcaveOn.mpr hcu
  have hss : s ⊆ thickening (δ / 2) s := self_subset_thickening hhalf s
  have hcs : StrongConcaveOn s m u := hcu.subset hss hs
  refine ⟨u, hu, hLu, herr, hcs, fun x hx v ↦ ?_⟩
  exact StrongConcaveOn.fderiv_fderiv_self_le hcu (isOpen_thickening.mem_nhds (hss hx))
    (Filter.Eventually.of_forall fun y ↦ hu.differentiable (by simp) y)
    (((hu.of_le (by simp) : ContDiff ℝ 2 u).contDiffAt.fderiv_right (m := 1)
      le_rfl).differentiableAt one_ne_zero) v
