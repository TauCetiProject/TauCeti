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
hypothesis only at their top derivative. On the whole space, a uniform bound on the next
derivative makes a derivative field Lipschitz (`ContDiff.lipschitzWith_iteratedFDeriv`).
Currying preserves these bounds exactly. On an open set that need not be convex, a `C^1` map is
locally Lipschitz, hence Hölder on every compact subset, so one more derivative makes the top
derivative Hölder there.
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

/-- A derivative field below the top order whose next derivative is bounded by `L` everywhere is
`L`-Lipschitz. -/
theorem _root_.ContDiff.lipschitzWith_iteratedFDeriv {k j : ℕ} {f : E → F} {L : ℝ≥0}
    (hf : ContDiff ℝ k f) (hj : j < k) (hnext : ∀ x, ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L) :
    LipschitzWith L (iteratedFDeriv ℝ j f) :=
  lipschitzWith_of_nnNorm_fderiv_le (hf.differentiable_iteratedFDeriv (by exact_mod_cast hj))
    fun x ↦ by
      have h := hnext x
      rw [← norm_fderiv_iteratedFDeriv] at h
      exact_mod_cast h

/-- A map of class `C^1` on an open set `s` is locally Lipschitz on `s`. Compare Mathlib's
`ContDiffOn.locallyLipschitzOn`, which assumes `s` convex instead of open. -/
theorem _root_.ContDiffOn.locallyLipschitzOn_of_isOpen {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {s : Set E'} {g : E' → F'} (hg : ContDiffOn 𝕂 1 g s) (hs : IsOpen s) :
    LocallyLipschitzOn s g := by
  intro x hx
  obtain ⟨L, t, ht, hLt⟩ := (hg.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hLt⟩

/-- A map of class `C^1` on an open set `s` is `α`-Hölder on each compact subset of `s`, for every
`α ≤ 1`. Compare `ContDiffOn.exists_holderOnWith`, for a compact convex set. -/
theorem _root_.ContDiffOn.exists_holderOnWith_of_isOpen {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {s K : Set E'} {g : E' → F'} {α : ℝ≥0} (hg : ContDiffOn 𝕂 1 g s) (hs : IsOpen s)
    (hα : α ≤ 1) (hK : IsCompact K) (hKs : K ⊆ s) : ∃ C, HolderOnWith C α g K :=
  (hg.locallyLipschitzOn_of_isOpen hs).exists_holderOnWith_of_isCompact hα hK hKs

/-- For a map of class `C^{k+1}` on an open set `s`, the `k`-th derivative is `α`-Hölder on each
compact subset of `s`, for every `α ≤ 1`. -/
theorem _root_.ContDiffOn.exists_holderOnWith_iteratedFDeriv {𝕂 E' F' : Type*} [RCLike 𝕂]
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F'] [NormedSpace 𝕂 F']
    {k : ℕ} {s K : Set E'} {f : E' → F'} {α : ℝ≥0} (hf : ContDiffOn 𝕂 (k + 1) f s)
    (hs : IsOpen s) (hα : α ≤ 1) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ C, HolderOnWith C α (iteratedFDeriv 𝕂 k f) K :=
  ContDiffOn.exists_holderOnWith_of_isOpen (fun _ hx ↦
    ((hf.contDiffAt (hs.mem_nhds hx)).iteratedFDeriv_right (add_comm _ _).le).contDiffWithinAt)
    hs hα hK hKs

end TauCeti
