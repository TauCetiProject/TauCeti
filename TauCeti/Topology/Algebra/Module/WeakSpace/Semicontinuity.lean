/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Weak lower semicontinuity

This module proves ambient sequential weak closedness of sublevels `{u ∈ S | E u ≤ b}` of a
sequentially weakly lower semicontinuous function on a sequentially weakly closed set
(`TauCeti.isSeqClosed_toWeakSpace_sublevel`).
-/

public section

open Set

namespace TauCeti

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- On a sequentially weakly closed set `S`, every sublevel `{u ∈ S | E u ≤ b}` of a
sequentially weakly lower semicontinuous function `E` is sequentially weakly closed. -/
theorem isSeqClosed_toWeakSpace_sublevel {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (b : β) : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  rw [heq]
  exact hE.isSeqClosed_sublevel hS b

end TauCeti
