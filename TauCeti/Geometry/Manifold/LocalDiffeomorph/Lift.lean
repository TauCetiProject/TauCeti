/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth lifts through local diffeomorphisms

A continuous lift of a `C^n` map through a `C^n` local diffeomorphism is `C^n`.
The pointwise statement only requires a local diffeomorphism at the value of the lift.
The relative version applies to arbitrary subsets, including at boundary and corner points.
These criteria allow smoothness to be checked in the base of a smooth covering map.

The argument uses Mathlib's `IsLocalDiffeomorphAt.localInverse` and its local inverse laws.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 4,
  "Smooth Covering Maps".
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} {f : N → M} {s : Set N} {x : N}

/-- A lift continuous within a set is `C^n` there if its composite is `C^n` and the projection
is a `C^n` local diffeomorphism at the value of the lift. -/
theorem contMDiffWithinAt_of_comp_isLocalDiffeomorphAt (p : M → P)
    (hp : IsLocalDiffeomorphAt I K n p (f x)) (hf : ContinuousWithinAt f s x)
    (hpf : ContMDiffWithinAt J K n (p ∘ f) s x) : ContMDiffWithinAt J I n f s x := by
  have h := hp.contMDiffAt_localInverse.comp_contMDiffWithinAt x hpf
  refine h.congr_of_eventuallyEq ?_ ?_
  · exact (hp.localInverse_eventuallyEq_left.comp_tendsto hf).symm
  · exact (hp.localInverse_left_inv hp.localInverse_mem_target).symm

/-- A continuous lift at a point through a local diffeomorphism is `C^n` at that point
whenever its composite is `C^n`. -/
theorem contMDiffAt_of_comp_isLocalDiffeomorphAt (p : M → P)
    (hp : IsLocalDiffeomorphAt I K n p (f x)) (hf : ContinuousAt f x)
    (hpf : ContMDiffAt J K n (p ∘ f) x) : ContMDiffAt J I n f x := by
  rw [← contMDiffWithinAt_univ] at hpf ⊢
  exact contMDiffWithinAt_of_comp_isLocalDiffeomorphAt p hp hf.continuousWithinAt hpf

/-- A continuous lift on a set through a local diffeomorphism is `C^n` on the set
whenever its composite is `C^n` there. -/
theorem contMDiffOn_of_comp_isLocalDiffeomorph (p : M → P)
    (hp : IsLocalDiffeomorph I K n p) (hf : ContinuousOn f s)
    (hpf : ContMDiffOn J K n (p ∘ f) s) : ContMDiffOn J I n f s :=
  fun x hx ↦ contMDiffWithinAt_of_comp_isLocalDiffeomorphAt p (hp (f x)) (hf x hx) (hpf x hx)

/-- A continuous lift through a local diffeomorphism is `C^n` whenever its composite is `C^n`. -/
theorem contMDiff_of_comp_isLocalDiffeomorph (p : M → P)
    (hp : IsLocalDiffeomorph I K n p) (hf : Continuous f)
    (hpf : ContMDiff J K n (p ∘ f)) : ContMDiff J I n f :=
  fun x ↦ contMDiffAt_of_comp_isLocalDiffeomorphAt p (hp (f x)) hf.continuousAt hpf.contMDiffAt

end TauCeti
