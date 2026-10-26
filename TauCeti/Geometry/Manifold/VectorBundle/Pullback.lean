/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Regularity of maps into pullback bundles

A map into the total space of a pullback bundle is smooth exactly when its projection to the new
base and its lift to the original total space are smooth. This is the smooth analogue of the
initial-topology description of a pullback bundle.

The criterion lets a map into a pullback bundle be checked without unfolding the pulled-back
trivializations. It is particularly useful for tangent maps whose base points agree through a
commuting square.

The criterion applies to fibre bundles with a normed model fibre; the fibres themselves need
only be nonempty topological spaces, without an additive or vector-space structure.
-/

public section

open Bundle
open scoped Manifold

namespace Bundle.Pullback

variable {𝕜 F EM EM' EX H H' HX B B' X K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM']
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace HX]
  {I : ModelWithCorners 𝕜 EM H} {I' : ModelWithCorners 𝕜 EM' H'}
  {IX : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B']
  [TopologicalSpace X] [ChartedSpace HX X]
  {E : B → Type*} [∀ x, Nonempty (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [FunLike K B' B] [ContinuousMapClass K B' B] {n : WithTop ℕ∞}

/-- A map into a pullback bundle is `C^n` at a point exactly when its base projection and its
lift to the original total space are `C^n` there. -/
theorem contMDiffAt_iff (f : K) {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} {x : X}
    (hf : ContMDiffAt I' I n f (q x).proj) :
    ContMDiffAt IX (I'.prod 𝓘(𝕜, F)) n q x ↔
      ContMDiffAt IX I' n (fun y => (q y).proj) x ∧
        ContMDiffAt IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) x := by
  simp only [Bundle.contMDiffAt_totalSpace, trivializationAt,
    FiberBundle.pullback_trivializationAt', Trivialization.pullback_apply, Pullback.lift_proj]
  exact ⟨fun ⟨hq, hcoord⟩ => ⟨hq, hf.comp x hq, hcoord⟩,
    fun ⟨hq, _, hcoord⟩ => ⟨hq, hcoord⟩⟩

/-- A map into a pullback bundle is `C^n` exactly when its base projection and its lift to the
original total space are `C^n`. -/
theorem contMDiff_iff (f : K) (hf : ContMDiff I' I n f)
    {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} :
    ContMDiff IX (I'.prod 𝓘(𝕜, F)) n q ↔
      ContMDiff IX I' n (fun y => (q y).proj) ∧
        ContMDiff IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) := by
  simp only [ContMDiff, ← forall_and]
  exact forall_congr' fun x => contMDiffAt_iff f hf.contMDiffAt

end Bundle.Pullback
