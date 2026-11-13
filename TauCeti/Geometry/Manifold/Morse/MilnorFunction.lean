/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.LowerOn
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Critical points of a function lowered on disjoint open sets

Milnor's proof of the cell attachment theorem (Theorem 3.2 of *Morse Theory*) replaces a function
`f` near each critical point by `F = f - μ(‖u‖² + 2‖v‖²)`, lowered by a cutoff in a chart and equal
to `f` elsewhere (`TauCeti.lowerOn`). Bott's attachment of negative disc bundles runs the same
construction fibrewise in normal forms over critical submanifolds. This file records the part of
the critical-point argument that does not depend on the chart model: outside the sets `U i` on
which `f` is lowered, critical points of the lowered function are critical points of `f`.

## Main results

* `TauCeti.mfderiv_lowerOn_ne_zero_of_forall_notMem`: outside the `U i`, the lowered function has
  no critical points with values in a set `s` if `f` has none outside the `U i` with values in `s`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

open Function Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {M ι : Type*} {U K : ι → Set M} {g : ι → M → ℝ} {f : M → ℝ} {x : M} [Fintype ι]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Outside the sets `U i`, the lowered function has no critical points with values in `s`,
provided the critical points of `f` with values in `s` lie in the `U i`. -/
theorem mfderiv_lowerOn_ne_zero_of_forall_notMem (hgK : ∀ i, EqOn (g i) 0 (U i \ K i))
    (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K i ⊆ U i) {s : Set ℝ}
    (hcrit : criticalPoints I f ∩ f ⁻¹' s ⊆ ⋃ i, U i) (hx : ∀ i, x ∉ U i)
    (hxs : lowerOn U g f x ∈ s) : mfderiv I 𝓘(ℝ) (lowerOn U g f) x ≠ 0 := by
  have hxK : x ∉ ⋃ i, K i := fun h ↦
    have ⟨i, hi⟩ := mem_iUnion.1 h
    hx i (hKU i hi)
  rw [(lowerOn_eventuallyEq hgK hK hxK).mfderiv_eq]
  intro h0
  rw [lowerOn_of_forall_notMem hx] at hxs
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, hxs⟩)
  exact hx i hi

end TauCeti
