/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Uniformly smooth functions on a set

`TauCeti.UniformContDiffOn 𝕜 s n Y G` says that a function `G : X → Y` between normed spaces is
`n` times differentiable at every point of `s`, with all derivatives up to order `n - 1` bounded
on `s` and the `n`-th derivative uniformly continuous on `s`. The derivatives are carried along as
functions `X → (X →L[𝕜] ⋯ →L[𝕜] Y)` rather than as iterated Fréchet derivatives, so a proof by
induction on `n` applies the case `n` to the derivative of `G`.

This is the regularity needed for superposition operators on bounded continuous functions: the
uniform control is what makes the derivative of `f ↦ G ∘ f` converge at all the points `f t` at
once.

## Main declarations

* `TauCeti.UniformContDiffOn`: the definition, with `TauCeti.uniformContDiffOn_zero_iff` and
  `TauCeti.uniformContDiffOn_succ_iff` unfolding it.
* `TauCeti.UniformContDiffOn.uniformContinuousOn` and `TauCeti.UniformContDiffOn.continuousOn`:
  such a function is uniformly continuous, hence continuous, on `s`.
* `ContDiff.uniformContDiffOn`: a `C^n` function is uniformly `C^n` on a compact set.
-/

public section

universe u

open Set

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {X : Type u} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] (s : Set X)

/-- A function `G : X → Y` is **uniformly `C^n` on `s`** if it is uniformly continuous on `s`, and
for `n + 1` it also has a derivative `G' x` at every point `x` of `s`, bounded on `s`, such that
`G'` is uniformly `C^n` on `s`. -/
def UniformContDiffOn : (n : ℕ) → (Y : Type u) → [NormedAddCommGroup Y] → [NormedSpace 𝕜 Y] →
    (X → Y) → Prop
  | 0 => @fun _ _ _ G ↦ UniformContinuousOn G s
  | n + 1 => @fun Y _ _ G ↦ UniformContinuousOn G s ∧
    ∃ G' : X → X →L[𝕜] Y, (∀ x ∈ s, HasFDerivAt G (G' x) x) ∧
      (∃ C, ∀ x ∈ s, ‖G' x‖ ≤ C) ∧ UniformContDiffOn n (X →L[𝕜] Y) G'

variable {𝕜 s} {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y}

/-- Uniform `C^0` regularity is uniform continuity. -/
theorem uniformContDiffOn_zero_iff : UniformContDiffOn 𝕜 s 0 Y G ↔ UniformContinuousOn G s :=
  Iff.rfl

/-- Uniform `C^{n+1}` regularity: uniform continuity, and a derivative that is bounded on `s` and
uniformly `C^n`. -/
theorem uniformContDiffOn_succ_iff {n : ℕ} :
    UniformContDiffOn 𝕜 s (n + 1) Y G ↔ UniformContinuousOn G s ∧
      ∃ G' : X → X →L[𝕜] Y, (∀ x ∈ s, HasFDerivAt G (G' x) x) ∧ (∃ C, ∀ x ∈ s, ‖G' x‖ ≤ C) ∧
        UniformContDiffOn 𝕜 s n (X →L[𝕜] Y) G' :=
  Iff.rfl

/-- A uniformly `C^n` function is uniformly continuous on `s`. -/
theorem UniformContDiffOn.uniformContinuousOn {n : ℕ} (h : UniformContDiffOn 𝕜 s n Y G) :
    UniformContinuousOn G s := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

/-- A uniformly `C^n` function is continuous on `s`. -/
theorem UniformContDiffOn.continuousOn {n : ℕ} (h : UniformContDiffOn 𝕜 s n Y G) :
    ContinuousOn G s :=
  h.uniformContinuousOn.continuousOn

/-- **A smooth function is uniformly smooth on a compact set.** If `G` is `C^n` and `s` is compact,
then `G` is uniformly `C^n` on `s`: every derivative is continuous, hence bounded and uniformly
continuous on `s`. -/
theorem _root_.ContDiff.uniformContDiffOn (hs : IsCompact s) (n : ℕ) :
    ∀ {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y},
      ContDiff 𝕜 n G → UniformContDiffOn 𝕜 s n Y G := by
  induction n with
  | zero =>
    intro Y _ _ G hG
    exact hs.uniformContinuousOn_of_continuous hG.continuous.continuousOn
  | succ n ih =>
    intro Y _ _ G hG
    have hdiff : Differentiable 𝕜 G := hG.differentiable (by simp)
    have hG' : ContDiff 𝕜 n (fderiv 𝕜 G) := hG.fderiv_right (m := n) (by simp)
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hG'.continuous.continuousOn
    exact ⟨hs.uniformContinuousOn_of_continuous hG.continuous.continuousOn, fderiv 𝕜 G,
      fun x _ ↦ (hdiff x).hasFDerivAt, ⟨C, hC⟩, ih hG'⟩

end TauCeti
