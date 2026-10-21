/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Cancelling local diffeomorphisms from compositions

A continuous map into a manifold is `C^n` if its composite with a `C^n` local diffeomorphism is
`C^n`. This file provides pointwise-within, on-set, and global versions of this cancellation
principle.

## Main results

* `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`: pointwise-within cancellation.
* `ContMDiffOn.of_comp_isLocalDiffeomorph`: on-set cancellation.
* `ContMDiff.of_comp_isLocalDiffeomorph`: global cancellation.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {p : M → B} {f : N → M}

/-- A continuous map is `C^n` within a set at a point when its composite with a map that is a
`C^n` local diffeomorphism at the image point is `C^n` there. -/
theorem _root_.ContMDiffWithinAt.of_comp_isLocalDiffeomorph {s : Set N} {y : N}
    (hp : IsLocalDiffeomorphAt I J n p (f y)) (hf : ContinuousWithinAt f s y)
    (hpf : ContMDiffWithinAt I' J n (p ∘ f) s y) : ContMDiffWithinAt I' I n f s y := by
  have hcomp : ContMDiffWithinAt I' I n (hp.localInverse ∘ (p ∘ f)) s y :=
    hp.contMDiffAt_localInverse.comp_contMDiffWithinAt y hpf
  have heq : Filter.EventuallyEq (nhdsWithin y s) (hp.localInverse ∘ (p ∘ f)) f := by
    exact hp.localInverse_eventuallyEq_left.comp_tendsto hf
  exact hcomp.congr_of_eventuallyEq heq.symm
    (hp.localInverse_left_inv hp.localInverse_mem_target).symm

/-- A continuous map on a set is `C^n` there when its composite with a `C^n` local diffeomorphism
is `C^n` on that set. -/
theorem _root_.ContMDiffOn.of_comp_isLocalDiffeomorph (hp : IsLocalDiffeomorph I J n p)
    {s : Set N} (hf : ContinuousOn f s) (hpf : ContMDiffOn I' J n (p ∘ f) s) :
    ContMDiffOn I' I n f s :=
  fun y hy ↦ (hpf y hy).of_comp_isLocalDiffeomorph (hp (f y)) (hf y hy)

/-- A continuous map is `C^n` when its composite with a `C^n` local diffeomorphism is `C^n`. -/
theorem _root_.ContMDiff.of_comp_isLocalDiffeomorph (hp : IsLocalDiffeomorph I J n p)
    (hf : Continuous f) (hpf : ContMDiff I' J n (p ∘ f)) : ContMDiff I' I n f := by
  rw [← contMDiffOn_univ]
  exact hpf.contMDiffOn.of_comp_isLocalDiffeomorph hp hf.continuousOn

end TauCeti
