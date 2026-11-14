/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The open set where a map is `C^n`

For an order `n ≠ ∞`, that is a finite order or the analytic order `n = ω`, being `C^n` at a
point propagates to a neighbourhood of that point (`ContDiffAt.eventually`), so the points at
which a map is `C^n` form an open set, on which the map is `C^n`. Hence a map which is `C^n` at
every point of a set is `C^n` on an open superset of that set. This fails for `n = ∞`, where the
neighbourhood on which the map is `C^m` may shrink as `m` grows.

## Main declarations

* `TauCeti.isOpen_setOf_contDiffAt`: for `n ≠ ∞`, the points at which `f` is `C^n` form an
  open set.
* `TauCeti.exists_isOpen_superset_contDiffOn`: for `n ≠ ∞`, a map which is `C^n` at every
  point of `s` is `C^n` on an open superset of `s`.
-/

public section

namespace TauCeti

open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f : E → F} {s : Set E}

/-- For `n ≠ ∞`, the points at which `f` is `C^n` form an open set. -/
theorem isOpen_setOf_contDiffAt (hn : n ≠ ∞) : IsOpen {x | ContDiffAt 𝕜 n f x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ hx.eventually hn

/-- For `n ≠ ∞`, a map which is `C^n` at every point of `s` is `C^n` on an open superset
of `s`. -/
theorem exists_isOpen_superset_contDiffOn (hn : n ≠ ∞) (hf : ∀ x ∈ s, ContDiffAt 𝕜 n f x) :
    ∃ U, IsOpen U ∧ s ⊆ U ∧ ContDiffOn 𝕜 n f U :=
  ⟨{x | ContDiffAt 𝕜 n f x}, isOpen_setOf_contDiffAt hn, hf, fun _ hx ↦ hx.contDiffWithinAt⟩

end TauCeti
