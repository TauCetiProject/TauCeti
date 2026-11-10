/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform derivative convergence after composition with a right inverse

Uniform derivative convergence remains uniform after composition with a fixed right inverse
whose derivative is bounded on the set in question. No completeness is required.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology

/-- Composing a family whose derivatives converge uniformly with a right inverse gives
uniform convergence of the composite derivatives to the identity, provided the derivative
of the right inverse is bounded. -/
theorem TendstoUniformlyOn.fderiv_comp_eq_id
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} {l : Filter ι} {K : Set F} {f : E → F} {g : F → E} {fseq : ι → E → F}
    (h : TendstoUniformlyOn (fun k ↦ fderiv 𝕜 (fseq k)) (fderiv 𝕜 f) l (g '' K))
    (hf : ∀ x ∈ K, DifferentiableAt 𝕜 f (g x))
    (hg : ∀ x ∈ K, DifferentiableAt 𝕜 g x)
    (hs : ∀ᶠ k in l, ∀ x ∈ K, DifferentiableAt 𝕜 (fseq k) (g x))
    (hfg : ∀ x ∈ K, f ∘ g =ᶠ[𝓝 x] id) {B : ℝ}
    (hB : ∀ x ∈ K, ‖fderiv 𝕜 g x‖ ≤ B) :
    TendstoUniformlyOn (fun k ↦ fderiv 𝕜 (fseq k ∘ g))
      (fun _ ↦ ContinuousLinearMap.id 𝕜 F) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hden : 0 < max B 0 + 1 := by positivity
  filter_upwards [hs, Metric.tendstoUniformlyOn_iff.mp h _ (div_pos hε hden)]
    with k hk hsmall x hx
  have hder : (fderiv 𝕜 f (g x)).comp (fderiv 𝕜 g x) = ContinuousLinearMap.id 𝕜 F := by
    rw [← fderiv_comp x (hf x hx) (hg x hx), (hfg x hx).fderiv_eq, fderiv_id]
  rw [dist_eq_norm, norm_sub_rev, fderiv_comp x (hk x hx) (hg x hx),
    ← hder, ← ContinuousLinearMap.sub_comp]
  have hd : ‖fderiv 𝕜 (fseq k) (g x) - fderiv 𝕜 f (g x)‖ < ε / (max B 0 + 1) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hsmall _ (mem_image_of_mem g hx)
  calc
    _ ≤ ‖fderiv 𝕜 (fseq k) (g x) - fderiv 𝕜 f (g x)‖ * ‖fderiv 𝕜 g x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv 𝕜 (fseq k) (g x) - fderiv 𝕜 f (g x)‖ * (max B 0 + 1) := by
      gcongr
      exact (hB x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
    _ < ε := (lt_div_iff₀ hden).mp hd
