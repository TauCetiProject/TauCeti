/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import TauCeti.Order.Monotone.InvFunOn

/-!
# Derivative of the inverse of a strictly monotone real function

Let `f : ℝ → ℝ` be continuous and strictly monotone on a neighbourhood `s` of `x`, with nonzero
derivative `f'` at `x`. Then `f '' s` is a neighbourhood of `f x`, so the inverse
`invFunOn f s` is continuous at `f x` and has derivative `f'⁻¹` there
(`StrictMonoOn.hasDerivAt_invFunOn`).
-/

public section

open Filter Function Set Topology

/-- The inverse `invFunOn f s` of a function `f : ℝ → ℝ` that is continuous and strictly monotone
on a neighbourhood `s` of `x`, with nonzero derivative `f'` at `x`, has derivative `f'⁻¹` at
`f x`. -/
theorem StrictMonoOn.hasDerivAt_invFunOn {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}
    (hf : StrictMonoOn f s) (hcont : ContinuousOn f s) (hs : s ∈ 𝓝 x) (hderiv : HasDerivAt f f' x)
    (hf' : f' ≠ 0) : HasDerivAt (Function.invFunOn f s) f'⁻¹ (f x) := by
  have hx : x ∈ s := mem_of_mem_nhds hs
  have hinv : LeftInvOn (Function.invFunOn f s) f s := hf.injOn.leftInvOn_invFunOn
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hs
  obtain ⟨a, hla, hax⟩ := exists_between hl
  obtain ⟨b, hxb, hbu⟩ := exists_between hu
  have hab : Icc a b ⊆ s := fun y hy ↦ hsub ⟨hla.trans_le hy.1, hy.2.trans_lt hbu⟩
  have hnhds : f '' s ∈ 𝓝 (f x) :=
    mem_of_superset (Icc_mem_nhds (hf (hab ⟨le_rfl, (hax.trans hxb).le⟩) hx hax)
      (hf hx (hab ⟨(hax.trans hxb).le, le_rfl⟩) hxb))
      ((intermediate_value_Icc (hax.trans hxb).le (hcont.mono hab)).trans (image_mono hab))
  refine HasDerivAt.of_local_left_inverse ?_ (by rwa [hinv hx]) hf' ?_
  · refine hf.invFunOn.continuousAt_of_image_mem_nhds hnhds ?_
    rwa [hinv.image_image, hinv hx]
  · filter_upwards [hnhds]
    rintro _ ⟨y, hy, rfl⟩
    rw [hinv hy]
