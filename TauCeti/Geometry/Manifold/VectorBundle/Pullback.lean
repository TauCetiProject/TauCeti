/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# Regularity of maps into pullback bundles

A map into the total space of a pullback bundle is smooth exactly when its projection to the new
base and its lift to the original total space are smooth. This is the smooth analogue of the
initial-topology description of a pullback bundle.

The criterion lets a map into a pullback bundle be checked without unfolding the pulled-back
trivializations. It is particularly useful for tangent maps whose base points agree through a
commuting square.
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
  {E : B → Type*} [∀ x, AddCommMonoid (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [FunLike K B' B] [ContinuousMapClass K B' B] {n : WithTop ℕ∞}

/-- A map into a pullback bundle is `C^n` at a point exactly when its base projection and its
lift to the original total space are `C^n` there. -/
theorem contMDiffAt_iff (f : K) (hf : ContMDiff I' I n f)
    {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} {x : X} :
    ContMDiffAt IX (I'.prod 𝓘(𝕜, F)) n q x ↔
      ContMDiffAt IX I' n (fun y => (q y).proj) x ∧
        ContMDiffAt IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) x := by
  rw [Bundle.contMDiffAt_totalSpace]
  constructor
  · rintro ⟨hq, hcoord⟩
    refine ⟨hq, Bundle.contMDiffAt_totalSpace.mpr ⟨hf.contMDiffAt.comp x hq, ?_⟩⟩
    change ContMDiffAt IX 𝓘(𝕜, F) n
      (fun y => ((trivializationAt F E (f (q x).proj)).pullback f (q y)).2) x at hcoord
    simpa only [Trivialization.pullback_apply, Pullback.lift_proj] using hcoord
  · rintro ⟨hq, hlift⟩
    refine ⟨hq, ?_⟩
    have hcoord := (Bundle.contMDiffAt_totalSpace.mp hlift).2
    change ContMDiffAt IX 𝓘(𝕜, F) n
      (fun y => ((trivializationAt F E (f (q x).proj)).pullback f (q y)).2) x
    simpa only [Trivialization.pullback_apply, Pullback.lift_proj] using hcoord

/-- A map into a pullback bundle is `C^n` exactly when its base projection and its lift to the
original total space are `C^n`. -/
theorem contMDiff_iff (f : K) (hf : ContMDiff I' I n f)
    {q : X → TotalSpace F ((f : B' → B) *ᵖ E)} :
    ContMDiff IX (I'.prod 𝓘(𝕜, F)) n q ↔
      ContMDiff IX I' n (fun y => (q y).proj) ∧
        ContMDiff IX (I.prod 𝓘(𝕜, F)) n
          (fun y => Pullback.lift f (q y)) := by
  simp only [ContMDiff, contMDiffAt_iff f hf, forall_and]

end Bundle.Pullback
