/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Translating `C^n` functions on balls and `C^n` charts

Translating the argument of a function `f` by `a` moves the ball on which `f` is `C^n`:
if `f` is `C^n` on `ball x R`, then `y ↦ f (y + a)` is `C^n` on `ball (x - a) R`. The case
`a = x` recentres a ball computation at the origin. In the same way, a `C^n` chart defined on
displacements from a point `x` is recentred into a chart around `x`.

## Main declarations

* `ContDiffOn.comp_add_right_ball`: translation of a `C^n` function on a ball.
* `TauCeti.exists_chart_comp_sub`: a `C^n` chart `q` with `0` in its source, precomposed with
  `w ↦ w - x`, is a `C^n` chart around `x` with the same derivative.
-/

public section

namespace ContDiffOn

open Metric

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F} {x : E} {R : ℝ}

/-- If `f` is `C^n` on the ball `ball x R`, then its translate `y ↦ f (y + a)` is `C^n` on the
translated ball `ball (x - a) R`. -/
theorem comp_add_right_ball (hf : ContDiffOn 𝕜 n f (ball x R)) (a : E) :
    ContDiffOn 𝕜 n (fun y ↦ f (y + a)) (ball (x - a) R) :=
  hf.comp (contDiffOn_id.add contDiffOn_const) (preimage_add_right_ball a x R).superset

end ContDiffOn

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

/-- **Recentring a chart.** Let `q` be a `C^n` chart with `C^n` inverse, with `0` in its source
and derivative `A` at `0`. Precomposing `q` with the translation `w ↦ w - x` and restricting it to
an open set `V` containing `x` gives a `C^n` chart around `x`, with `C^n` inverse and derivative
`A` at `x`. It cuts out a set `S` by `e z ∈ L` as soon as, on `V`, the set `S` is cut out by
`q (w - x) ∈ L`. -/
theorem exists_chart_comp_sub {q : OpenPartialHomeomorph E F} {A : E →L[𝕜] F} {x : E}
    (hq0 : 0 ∈ q.source) (hqd : HasFDerivAt q A 0)
    (hqC : ∀ z ∈ q.source, ContDiffAt 𝕜 n q z) (hqCs : ∀ z ∈ q.target, ContDiffAt 𝕜 n q.symm z)
    {S V : Set E} {L : Set F} (hVo : IsOpen V) (hxV : x ∈ V)
    (hVS : ∀ w ∈ V, w - x ∈ q.source → (w ∈ S ↔ q (w - x) ∈ L)) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ HasFDerivAt e A x ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      ∀ z ∈ e.source, z ∈ S ↔ e z ∈ L := by
  let e := ((Homeomorph.subRight x).toOpenPartialHomeomorph.restrOpen V hVo).trans q
  have hesource : e.source = {z | z ∈ V ∧ z - x ∈ q.source} := by
    ext z
    simp [e]
  have he : (e : E → F) = fun z ↦ q (z - x) := by
    ext z
    simp [e]
  have hes : (e.symm : F → E) = fun z ↦ q.symm z + x := by
    ext z
    simp [e]
  refine ⟨e, by rw [hesource]; exact ⟨hxV, by rwa [sub_self]⟩, ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [he]
    have hqd' : HasFDerivAt q A (x - x) := by rwa [sub_self]
    have hsub : HasFDerivAt (fun z : E ↦ z - x) (ContinuousLinearMap.id 𝕜 E) x :=
      (hasFDerivAt_id x).sub_const x
    simpa [Function.comp_def] using hqd'.comp (f := fun z : E ↦ z - x) x hsub
  · rw [hesource] at hz
    rw [he]
    exact (hqC _ hz.2).comp z (contDiffAt_id.sub contDiffAt_const)
  · rw [OpenPartialHomeomorph.trans_target] at hz
    rw [hes]
    exact (hqCs z hz.1).add contDiffAt_const
  · rw [hesource] at hz
    rw [he]
    exact hVS z hz.1 hz.2

end TauCeti
