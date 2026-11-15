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
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Hölder bounds for local derivative fields

On an open convex set, bounds for a derivative field and its next derivative give a Hölder
bound for every exponent at most one. Thus local `C^{k,α}` data need a separate Hölder
hypothesis only at their top derivative. Currying preserves these bounds exactly, and Hölder
bounds on the derivatives of two maps of the same order add up to one for their sum.
-/

public section

open Set
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

/-- If `f` and `g` are `C^n` at every point of `s` and their `n`-th derivatives are `r`-Hölder on
`s`, then so is the `n`-th derivative of `f + g`, with the sum of the constants. -/
theorem _root_.HolderOnWith.iteratedFDeriv_add {𝕜 G H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H] {n : ℕ}
    {r C C' : ℝ≥0} {f g : G → H} {s : Set G} (hf : HolderOnWith C r (iteratedFDeriv 𝕜 n f) s)
    (hg : HolderOnWith C' r (iteratedFDeriv 𝕜 n g) s) (hfs : ∀ x ∈ s, ContDiffAt 𝕜 n f x)
    (hgs : ∀ x ∈ s, ContDiffAt 𝕜 n g x) :
    HolderOnWith (C + C') r (iteratedFDeriv 𝕜 n (f + g)) s :=
  (hf.add hg).congr fun x hx => (iteratedFDeriv_add_apply (hfs x hx) (hgs x hx)).symm

end TauCeti
