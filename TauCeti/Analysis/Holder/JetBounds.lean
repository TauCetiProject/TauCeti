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

/-!
# Hölder bounds for local derivative fields

On an open convex set, bounds for a derivative field and its next derivative give a Hölder
bound for every exponent at most one. Thus local `C^{k,α}` data need a separate Hölder
hypothesis only at their top derivative. Over any nontrivially normed field, currying preserves
these bounds exactly, and every iterated derivative of a constant function is constant, hence
Hölder with any constant and exponent (`TauCeti.holderWith_iteratedFDeriv_const`,
`TauCeti.holderOnWith_iteratedFDeriv_const`).
-/

public section

open Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace TauCeti

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Currying preserves the Hölder bound of the top derivative exactly. -/
theorem holderOnWith_iteratedFDeriv_succ_iff {f : E → F} {s : Set E} {j : ℕ}
    {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv 𝕜 (j + 1) f) s ↔
      HolderOnWith H α (iteratedFDeriv 𝕜 j (fderiv 𝕜 f)) s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- The order-zero derivative field has the same Hölder constant as the original function. -/
theorem holderOnWith_iteratedFDeriv_zero_iff {f : E → F} {s : Set E} {H α : ℝ≥0} :
    HolderOnWith H α (iteratedFDeriv 𝕜 0 f) s ↔ HolderOnWith H α f s := by
  simp only [holderOnWith_iff_dist_le, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.dist_map]

/-- Every iterated derivative of a constant function is constant, hence globally Hölder with any
constant `C` and exponent `α`. -/
theorem holderWith_iteratedFDeriv_const {C α : ℝ≥0} (n : ℕ) (c : F) :
    HolderWith C α (iteratedFDeriv 𝕜 n (fun _ : E ↦ c)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [iteratedFDeriv_zero_eq_comp, Function.comp_def]
    exact HolderWith.const
  · rw [iteratedFDeriv_const_of_ne hn]
    exact HolderWith.zero

/-- Every iterated derivative of a constant function is Hölder with any constant `C` and exponent
`α` on any set `s`. -/
theorem holderOnWith_iteratedFDeriv_const {C α : ℝ≥0} {s : Set E} (n : ℕ) (c : F) :
    HolderOnWith C α (iteratedFDeriv 𝕜 n (fun _ : E ↦ c)) s :=
  (holderWith_iteratedFDeriv_const n c).holderOnWith s

end Field

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

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

end TauCeti
