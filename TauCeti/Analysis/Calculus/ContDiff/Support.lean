/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth multiplication supported in an open set

Multiplying a function smooth on an open set by a smooth scalar function whose topological
support lies in that set gives a globally smooth function.
-/

public section

open Set
open scoped Topology

/-- A smooth scalar multiplier supported in an open smoothness domain gives a globally smooth
product. No regularity of the other factor is required outside that domain. -/
theorem ContDiff.smul_of_tsupport_subset {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {φ : E → 𝕜} {f : E → F} {U : Set E}
    (hφ : ContDiff 𝕜 n φ) (hf : ContDiffOn 𝕜 n f U) (hU : IsOpen U)
    (hs : tsupport φ ⊆ U) : ContDiff 𝕜 n (fun x ↦ φ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.smul ((hf x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp hx
    have heq : (fun y ↦ φ y • f y) =ᶠ[𝓝 x] fun _ ↦ (0 : F) := by
      filter_upwards [hzero] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq
