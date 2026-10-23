/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Monotone convergence on a closed half-line

A function that is monotone and bounded above on a closed half-line `[a, ∞)` tends at infinity to
its supremum over that half-line, and dually for antitone functions bounded below. These are the
half-line forms of Mathlib's `tendsto_atTop_ciSup` and `tendsto_atTop_ciInf`, which ask for
monotonicity on the whole domain. They apply, for instance, to a quantity monotone along a
trajectory that is only defined, or only monotone, in forward time.

## Main results

* `TauCeti.tendsto_atTop_ciSup_of_monotoneOn_Ici` — a function monotone and bounded above on
  `[a, ∞)` tends to its supremum there.
* `TauCeti.tendsto_atTop_ciInf_of_antitoneOn_Ici` — a function antitone and bounded below on
  `[a, ∞)` tends to its infimum there.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι α : Type*} [Preorder ι] [IsDirectedOrder ι] [TopologicalSpace α] {f : ι → α} {a : ι}

/-- **Monotone convergence on a half-line.** A function monotone and bounded above on `[a, ∞)`
tends at infinity to its supremum over `[a, ∞)`. -/
theorem tendsto_atTop_ciSup_of_monotoneOn_Ici [ConditionallyCompletePartialOrderSup α]
    [SupConvergenceClass α] (hf : MonotoneOn f (Ici a)) (hbdd : BddAbove (f '' Ici a)) :
    Tendsto f atTop (𝓝 (⨆ t : Ici a, f t)) :=
  tendsto_comp_val_Ici_atTop.mp <|
    tendsto_atTop_ciSup (fun s t hst ↦ hf s.2 t.2 hst) (by rwa [← image_eq_range])

/-- **Antitone convergence on a half-line.** A function antitone and bounded below on `[a, ∞)`
tends at infinity to its infimum over `[a, ∞)`. -/
theorem tendsto_atTop_ciInf_of_antitoneOn_Ici [ConditionallyCompletePartialOrderInf α]
    [InfConvergenceClass α] (hf : AntitoneOn f (Ici a)) (hbdd : BddBelow (f '' Ici a)) :
    Tendsto f atTop (𝓝 (⨅ t : Ici a, f t)) :=
  tendsto_comp_val_Ici_atTop.mp <|
    tendsto_atTop_ciInf (fun s t hst ↦ hf s.2 t.2 hst) (by rwa [← image_eq_range])

end TauCeti
