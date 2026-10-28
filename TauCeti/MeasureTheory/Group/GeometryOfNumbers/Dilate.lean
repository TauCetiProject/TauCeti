/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRight
import TauCeti.Analysis.Convex.Basic
import TauCeti.Analysis.Convex.Gauge
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Lattice points in the dilates of a compact convex set

Let `L` be a discrete `ℤ`-submodule of a finite-dimensional real normed space `E`, and let `s` be
a compact convex neighbourhood of `0`. The lattice points `r • s ∩ L` of the dilates of `s` grow
with `r`, and they are right-continuous in `r`: just above any `r₀ ≥ 0` they are exactly the
lattice points of `r₀ • s` (`MeasureTheory.eventually_smul_inter_eq`). Indeed, the lattice points
of `(r₀ + 1) • s` form a finite set, and each of them outside `r₀ • s` has gauge strictly above
`r₀`.

Consequently, for each `i`, the set of dilation factors `r ≥ 0` for which `r • s ∩ L` spans a real
subspace of dimension greater than `i` is closed
(`MeasureTheory.isClosed_setOf_lt_setFinrank_smul_inter`). The `i`-th successive minimum of `s`
with respect to `L` is the infimum of this set, so closedness says that the infimum is attained
whenever the set is nonempty (for instance when `i` is below the rank of `L`): the dilate of `s`
by its `i`-th successive minimum then already contains `i + 1` independent lattice vectors.

The name and statement of `MeasureTheory.isClosed_setOf_lt_setFinrank_smul_inter` follow
Mathlib's successive-minima proposal (mathlib4 PR 35812 by Alex J. Best, Yaël Dillies and
Kevin H. Wilson, file `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` at revision `8423d1c`),
without its hypothesis that `i` is below the rank of `L`. The proof here goes through
`MeasureTheory.eventually_smul_inter_eq` rather than through sequences of independent families.
-/

public section

open Filter Module Topology
open scoped NNReal Pointwise

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] {s : Set E}

/-- Let `s` be a compact convex neighbourhood of `0` and `L` a discrete `ℤ`-submodule. For
`r₀ ≥ 0`, every dilate `r • s` with `r ≥ r₀` close enough to `r₀` contains exactly the same
lattice points as `r₀ • s`. -/
theorem eventually_smul_inter_eq (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0)
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) : ∀ᶠ r in 𝓝[≥] r₀, r • s ∩ L = r₀ • s ∩ L := by
  have h0 : (0 : E) ∈ s := mem_of_mem_nhds hs₀
  -- The lattice points of `(r₀ + 1) • s` that are not in `r₀ • s` form a finite set `T`.
  set T := ((r₀ + 1) • s ∩ L) \ (r₀ • s)
  have hT : T.Finite :=
    (AddSubgroup.finite_inter L.toAddSubgroup (hs.isBounded.smul₀ (r₀ + 1))).sdiff
  -- Each point of `T` has gauge greater than `r₀`, because `r₀ • s` is the gauge sublevel.
  have hgauge (x : E) (hx : x ∈ T) : r₀ < gauge s x := by
    by_contra! h
    have hx' : x ∈ {x | gauge s x ≤ r₀} := h
    rw [TauCeti.setOfPred_gauge_le_eq_closure_smul hsc
      (NormedSpace.isVonNBounded_of_isBounded ℝ hs.isBounded) hs₀ hr₀,
      (hs.smul r₀).isClosed.closure_eq] at hx'
    exact hx.2 hx'
  have hev : ∀ᶠ r in 𝓝[≥] r₀, r < r₀ + 1 ∧ ∀ x ∈ T, r < gauge s x :=
    nhdsWithin_le_nhds <| (eventually_lt_nhds (lt_add_one r₀)).and <|
      hT.eventually_all.2 fun x hx ↦ eventually_lt_nhds (hgauge x hx)
  filter_upwards [hev, self_mem_nhdsWithin] with r ⟨hr1, hrT⟩ (hr : r₀ ≤ r)
  refine Set.Subset.antisymm (fun x ⟨hxs, hxL⟩ ↦ ⟨?_, hxL⟩)
    (Set.inter_subset_inter_left _ (hsc.smul_mono_of_zero_mem h0 hr₀ hr))
  by_contra hx
  exact (gauge_le_of_mem (hr₀.trans hr) hxs).not_gt <| hrT x
    ⟨⟨hsc.smul_mono_of_zero_mem h0 (hr₀.trans hr) hr1.le hxs, hxL⟩, hx⟩

/-- Let `s` be a compact convex neighbourhood of `0` and `L` a discrete `ℤ`-submodule. For each
`i`, the set of dilation factors `r ≥ 0` for which the lattice points of `r • s` span a real
subspace of dimension greater than `i` is closed. Its infimum is the `i`-th successive minimum of
`s` with respect to `L`, which is therefore attained whenever the set is nonempty. -/
theorem isClosed_setOf_lt_setFinrank_smul_inter (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) {i : ℕ} : IsClosed {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)} := by
  have h0 : (0 : E) ∈ s := mem_of_mem_nhds hs₀
  have hsmul (r : ℝ≥0) : r • s = (r : ℝ) • s := by
    ext x
    simp [Set.mem_smul_set, NNReal.smul_def]
  -- The complement is open: below a point of the complement the rank can only drop, and just
  -- above it the lattice points do not change.
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro r₀ hr₀
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hr₀
  rw [← nhdsLE_sup_nhdsGE, mem_sup]
  constructor
  · filter_upwards [self_mem_nhdsWithin] with r (hr : r ≤ r₀)
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    refine le_trans (Set.finrank_mono (Set.inter_subset_inter_left _ ?_)) hr₀
    rw [hsmul, hsmul]
    exact hsc.smul_mono_of_zero_mem h0 r.2 hr
  · have hcoe : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[≥] r₀) (𝓝[≥] (r₀ : ℝ)) :=
      NNReal.continuous_coe.continuousWithinAt.tendsto_nhdsWithin fun _ hr ↦
        NNReal.coe_le_coe.2 hr
    filter_upwards [hcoe.eventually (eventually_smul_inter_eq (L := L) hsc hs hs₀ r₀.2)] with r hr
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rwa [hsmul, hr, ← hsmul]

end MeasureTheory
