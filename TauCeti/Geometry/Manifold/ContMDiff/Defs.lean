/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# The set of points where a map is `C^n`

For `n ≠ ∞`, a map between manifolds is `C^n` at a point if and only if it is `C^n` on a
neighbourhood of that point (`contMDiffAt_iff_contMDiffAt_nhds`), so the set of points where it
is `C^n` is open.  This file records that openness.

## Main results

* `TauCeti.isOpen_setOfPred_contMDiffAt`: for `n ≠ ∞`, the set of points where a map is `C^n` is
  open.
-/

public section

open scoped ContDiff

namespace TauCeti

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω} {f : M → M'}

/-- For `n ≠ ∞`, the set of points where a map is `C^n` is open.  This fails for `n = ∞`, where
the neighbourhood on which `f` is `C^k` may shrink with `k`. -/
theorem isOpen_setOfPred_contMDiffAt [IsManifold I n M] [IsManifold I' n M'] (hn : n ≠ ∞) :
    IsOpen {x | ContMDiffAt I I' n f x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ (contMDiffAt_iff_contMDiffAt_nhds hn).1 hx

end TauCeti

end
