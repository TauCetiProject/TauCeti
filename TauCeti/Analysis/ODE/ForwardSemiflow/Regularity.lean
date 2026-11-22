/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.ForwardSemiflow.Basic
public import TauCeti.Analysis.ODE.Regularity

/-!
# Time regularity of forward semiflow trajectories

Proves `LocallyLipschitzOn.contDiffOn_forwardSemiflow_time`: for a locally Lipschitz `C^m` vector
field on an arbitrary state set `S`, each individual trajectory of `TauCeti.forwardSemiflow` is
`C^(m + 1)` on its maximal forward interval.
-/

public section

open Filter Set
open scoped ContDiff

namespace LocallyLipschitzOn

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a locally Lipschitz `C^m` field `X` (`m : ℕ∞`) on `S`, each individual trajectory of
`forwardSemiflow X S` is `C^(m + 1)` on its maximal forward interval. -/
theorem contDiffOn_forwardSemiflow_time {m : ℕ∞} {S : Set E} {X : E → E}
    (hX_lip : LocallyLipschitzOn S X) (hX : ContDiffOn ℝ m X S) (x : E) :
    ContDiffOn ℝ (m + 1) (fun t ↦ forwardSemiflow X S t x)
      (forwardSemiflowInterval X S x) := by
  intro t ht
  obtain ⟨b, htb, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
  exact (contDiffOn_succ_of_hasDerivWithinAt_comp (uniqueDiffOn_Ico 0 b) hX
    (fun _ hs ↦ forwardSemiflow_mem (hsub hs))
    (fun _ hs ↦ hX_lip.hasDerivWithinAt_forwardSemiflow_Ico hsub hs) t
    ⟨nonneg_of_mem_forwardSemiflowInterval ht, htb⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio b, isOpen_Iio, htb, fun _ hs ↦ ⟨nonneg_of_mem_forwardSemiflowInterval hs.2, hs.1⟩⟩

end LocallyLipschitzOn
