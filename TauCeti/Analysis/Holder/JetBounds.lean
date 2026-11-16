/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Hölder bounds for local derivative fields

On an open convex set, bounds for a derivative field and its next derivative give a Hölder
bound for every exponent at most one. Thus local `C^{k,α}` data need a separate Hölder
hypothesis only at their top derivative. Currying preserves these bounds exactly. On an open set
that need not be convex, one more derivative makes the top derivative Hölder on every compact
subset.
-/

public section

open Set Topology
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace TauCeti

/-- Currying preserves the Hölder bound of the top derivative exactly. -/
theorem holderOnWith_iteratedFDeriv_succ_iff {f : E → F} {s : Set E} {j : ℕ}
    {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ (j + 1) f) s ↔
      HolderOnWith H α (iteratedFDeriv ℝ j (fderiv ℝ f)) s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- The order-zero derivative field has the same Hölder constant as the original function. -/
theorem holderOnWith_iteratedFDeriv_zero_iff {f : E → F} {s : Set E} {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv ℝ 0 f) s ↔ HolderOnWith H α f s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- Every derivative field below the top order is Hölder, controlled by the uniform bound on
that field and its next derivative. No Hölder assumption on lower derivatives is needed. -/
theorem _root_.ContDiffOn.holderOnWith_iteratedFDeriv_of_lt {k j : ℕ} {s : Set E}
    {f : E → F} {M L α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : IsOpen s)
    (hconv : Convex ℝ s) (hj : j < k) (hα : α ≤ 1)
    (hb : ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hnext : ∀ x ∈ s, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    HolderOnWith (L + 2 * M) α (iteratedFDeriv ℝ j f) s := by
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x := fun x hx =>
    (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have hder : ∀ x ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖₊ ≤ L := by
    intro x hx
    exact_mod_cast (norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f) (n := j) (x := x)) ▸
      hnext x hx
  have hlip := Convex.lipschitzOnWith_of_nnNorm_fderiv_le hdiff hder hconv
  exact hlip.holderOnWith_of_norm_le hb hα

/-- For a map of class `C^{k+1}` on an open set `s`, the `k`-th derivative is `α`-Hölder on each
compact subset of `s`, for every `α ≤ 1`. -/
theorem _root_.ContDiffOn.exists_holderOnWith_iteratedFDeriv {k : ℕ} {s K : Set E} {f : E → F}
    {α : ℝ≥0} (hf : ContDiffOn ℝ (k + 1) f s) (hs : IsOpen s) (hα : α ≤ 1) (hK : IsCompact K)
    (hKs : K ⊆ s) : ∃ C, HolderOnWith C α (iteratedFDeriv ℝ k f) K := by
  have hloc (x : E) (hx : x ∈ K) :
      ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α (iteratedFDeriv ℝ k f) (Metric.ball x r) := by
    have h1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k f) x :=
      (hf.contDiffAt (hs.mem_nhds (hKs hx))).iteratedFDeriv_right (add_comm _ _).le
    obtain ⟨L, t, ht, hLt⟩ := h1.exists_lipschitzOnWith
    have hb : ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv ℝ k f y‖ < ‖iteratedFDeriv ℝ k f x‖ + 1 :=
      h1.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hb)
    refine ⟨r, hr, L + 2 * (‖iteratedFDeriv ℝ k f x‖₊ + 1), ?_⟩
    exact (hLt.mono fun y hy ↦ (hrt hy).1).holderOnWith_of_norm_le
      (fun y hy ↦ by simpa using (hrt hy).2.le) hα
  obtain ⟨δ, hδ, L, -, hL, -⟩ := hK.exists_holderOnWith_thickening_and_norm_le hloc
  exact ⟨L, hL.mono (Metric.self_subset_thickening hδ K)⟩

end TauCeti
