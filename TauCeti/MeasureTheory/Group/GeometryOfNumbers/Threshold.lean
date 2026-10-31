/-
Copyright (c) 2021 Alex J. Best, 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Body
import TauCeti.Analysis.Convex.Gauge
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Closed rank thresholds for lattice dilates

For a compact convex neighbourhood `s` of zero and a discrete integer submodule `L`, the
nonnegative dilation factors `r` for which `r • s ∩ L` spans more than `i` real dimensions form
a closed set. This is the closedness needed to attain an infimum defining a successive minimum.
The lattice need not span the ambient space, and no bound on `i` is necessary: above the rank,
the threshold set is empty.

The statement and finite-family argument follow Kevin H. Wilson's successive-minima proposal,
Mathlib PR #35812, revision `8423d1c878e50d8504a230ffd9b6ec76ce6a08eb`,
`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`,
`MeasureTheory.isClosed_setOf_lt_setFinrank_smul_inter` (Apache-2.0; authors Alex J. Best,
Yaël Dillies, Kevin H. Wilson). Here gauge bounds confine the witnesses to a single finite set,
and positive definiteness of the gauge handles a possible zero limit.
-/

public section

open Module Submodule Set Filter
open scoped Pointwise Topology NNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] {s : Set E} {i : ℕ}

/-- For a compact convex neighbourhood of zero, the dilation factors whose lattice intersection
has real rank greater than `i` form a closed subset of `ℝ≥0`. No fullness of the lattice or
restriction on the index is required. -/
theorem isClosed_setOf_lt_setFinrank_smul_inter (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) :
    IsClosed {r : ℝ≥0 | i < Set.finrank ℝ (r • s ∩ L)} := by
  apply IsSeqClosed.isClosed
  intro r r₀ hr hlim
  -- Eventually all witness families lie in a single finite lattice intersection.
  have hbounded := hlim.eventually_le_const (lt_add_of_pos_right r₀ one_pos)
  have hfinite : ((r₀ + 1) • s ∩ L).Finite := by
    simpa only [NNReal.smul_def, Submodule.coe_toAddSubgroup] using
      AddSubgroup.finite_inter L.toAddSubgroup
      (hs.isBounded.smul₀ ((r₀ + 1 : ℝ≥0) : ℝ))
  let S := {v : Fin (i + 1) → E | ∀ j, v j ∈ (r₀ + 1) • s ∩ L}
  have hS : S.Finite := Set.Finite.pi' fun _ ↦ hfinite
  have hw (n : ℕ) : ∃ v : Fin (i + 1) → E,
      LinearIndependent ℝ v ∧ ∀ j, v j ∈ r n • s ∩ L :=
    Submodule.le_finrank_span_iff_exists_linearIndependent.1 (Nat.succ_le_of_lt (hr n))
  choose v hvli hv using hw
  have hevent : ∀ᶠ n in atTop, v n ∈ S := by
    filter_upwards [hbounded] with n hn j
    refine ⟨?_, (hv n j).2⟩
    have hg := (gauge_le_of_mem (r n).coe_nonneg (hv n j).1).trans
      (NNReal.coe_le_coe.mpr hn)
    simpa only [hs.isClosed.closure_eq, NNReal.smul_def] using
      (gauge_le_iff_mem_smul_closure hsc hs₀ (by positivity)).1 hg
  obtain ⟨w, _, hfreq⟩ : ∃ w ∈ S, ∃ᶠ n in atTop, v n = w :=
    hS.frequently_exists.mp (hevent.frequently.mono fun n hn ↦ ⟨v n, hn, rfl⟩)
  have hwli : LinearIndependent ℝ w := by
    obtain ⟨n, rfl⟩ := hfreq.exists
    exact hvli n
  have hwL (j) : w j ∈ L := by
    obtain ⟨n, rfl⟩ := hfreq.exists
    exact (hv n j).2
  -- A recurring independent family retains the limiting gauge bounds.
  have hwg (j) : gauge s (w j) ≤ r₀ := by
    apply ge_of_tendsto_of_frequently ((NNReal.continuous_coe.tendsto r₀).comp hlim)
    exact hfreq.mono fun n hn ↦ hn ▸ gauge_le_of_mem (r n).coe_nonneg (hv n j).1
  have hr₀ : 0 < (r₀ : ℝ) :=
    ((gauge_pos (absorbent_nhds_zero hs₀)
      ((NormedSpace.isVonNBounded_iff ℝ).2 hs.isBounded)).2
      (hwli.ne_zero 0)).trans_le (hwg 0)
  refine Nat.lt_of_succ_le <| Submodule.le_finrank_span_iff_exists_linearIndependent.2
    ⟨w, hwli, fun j ↦ ⟨?_, hwL j⟩⟩
  simpa [hs.isClosed.closure_eq, NNReal.smul_def] using
    (gauge_le_iff_mem_smul_closure hsc hs₀ hr₀).1 (hwg j)

end MeasureTheory
