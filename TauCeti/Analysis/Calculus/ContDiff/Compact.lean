/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Compactness.Compact

/-!
# Eventual differentiability on compact sets

Local eventual `C^n` regularity admits a common eventual threshold on a compact set.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- A compact subset admits one eventual threshold for pointwise `C^n` regularity when each
point has an eventually `C^n` neighborhood. -/
theorem IsCompact.eventually_forall_contDiffAt_of_eventually_contDiffOn
    {K : Set E} {ι : Type*} {l : Filter ι} {f : ι → E → F} (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ k in l, ContDiffOn 𝕜 n (f k) V) :
    ∀ᶠ k in l, ∀ x ∈ K, ContDiffAt 𝕜 n (f k) x := by
  refine hK.induction_on (p := fun S ↦ ∀ᶠ k in l,
    ∀ x ∈ S, ContDiffAt 𝕜 n (f k) x) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (by simp)
  · intro S T hST hT
    exact hT.mono fun _ hk x hx ↦ hk x (hST hx)
  · intro S T hS hT
    filter_upwards [hS, hT] with k hkS hkT x hx
    exact hx.elim (hkS x) (hkT x)
  · intro x hx
    obtain ⟨V, hV, hxV, hVsmooth⟩ := hlocal x hx
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV),
      hVsmooth.mono fun _ hk _ hy ↦ hk.contDiffAt (hV.mem_nhds hy)⟩
