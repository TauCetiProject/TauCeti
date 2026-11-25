/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Limits of periodic functions

A pointwise limit of functions with a common period `c`, valued in a Hausdorff space, again has
period `c` (`TauCeti.periodic_of_tendsto`): the equation `F i (x + c) = F i x` passes to the limit
by the uniqueness of limits. For instance, a limit of maps `ℝ × ℝ → V` with `1`-periodic loops has
`1`-periodic loops, and the loop to which the loops of a cylinder converge at one of its ends is
`1`-periodic.
-/

public section

open Filter Topology Function

namespace TauCeti

/-- A pointwise limit of functions with period `c`, valued in a Hausdorff space, has period `c`.
It suffices that the functions eventually have period `c`. -/
theorem periodic_of_tendsto {ι α β : Type*} [Add α] [TopologicalSpace β] [T2Space β]
    {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β} {c : α}
    (hF : ∀ᶠ i in l, Periodic (F i) c) (hf : ∀ x, Tendsto (fun i ↦ F i x) l (𝓝 (f x))) :
    Periodic f c := fun x ↦
  tendsto_nhds_unique ((hf (x + c)).congr' (hF.mono fun _ hi ↦ hi x)) (hf x)

end TauCeti
