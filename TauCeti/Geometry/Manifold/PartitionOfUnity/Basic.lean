/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Finite-order regularity for manifold partitions of unity

A `BumpCovering` whose functions are all `C^n` (`n : ℕ∞ω`) produces a `C^n` partition of unity
(`BumpCovering.contMDiff_toPartitionOfUnity_of_contMDiff`), without assuming `C^∞` regularity,
`σ`-compactness, or finite-dimensionality of the model space.
-/

public section

open Function Set
open scoped ContDiff Manifold

section BumpCovering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If every function in a `BumpCovering` is `C^n`, each weight of its associated partition of
unity is `C^n`. Adapted from Mathlib's `BumpCovering.contMDiff_toPartitionOfUnity`, generalized
from `C^∞` to `C^n`. -/
theorem BumpCovering.contMDiff_toPartitionOfUnity_of_contMDiff {ι : Type*} {s : Set M} {n : ℕ∞ω}
    (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) (i : ι) :
    ContMDiff I 𝓘(ℝ) n (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ ↦ contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

end BumpCovering
