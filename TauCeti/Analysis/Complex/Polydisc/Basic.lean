/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Sets.Opens

/-!
# Open polydiscs

For a finite index type `ι`, the open polydisc `TauCeti.polydisc c r` in `ι → ℂ` with centre `c`
and polyradius `r` is the product of the open discs `B(c i, r i)`, bundled as an open subset. As an
open subset of `ι → ℂ` it is an open complex submanifold, the domain of the Dolbeault–Grothendieck
lemma on polydiscs. It is empty when some radius is nonpositive, and it is the one-point space
`ι → ℂ` when `ι` is empty.
-/

public section

noncomputable section

open Set Metric

namespace TauCeti

variable {ι : Type*} [Finite ι]

/-- The open polydisc in `ι → ℂ` with centre `c` and polyradius `r`: the product of the open discs
`B(c i, r i)`, as an open subset. It is empty when some `r i ≤ 0`. -/
def polydisc (c : ι → ℂ) (r : ι → ℝ) : TopologicalSpace.Opens (ι → ℂ) :=
  ⟨univ.pi fun i ↦ ball (c i) (r i), isOpen_set_pi finite_univ fun _ _ ↦ isOpen_ball⟩

@[simp]
theorem coe_polydisc (c : ι → ℂ) (r : ι → ℝ) :
    (polydisc c r : Set (ι → ℂ)) = univ.pi fun i ↦ ball (c i) (r i) :=
  (rfl)

@[simp]
theorem mem_polydisc {c z : ι → ℂ} {r : ι → ℝ} :
    z ∈ polydisc c r ↔ ∀ i, z i ∈ ball (c i) (r i) := by
  rw [← SetLike.mem_coe, coe_polydisc, mem_univ_pi]

/-- A polydisc is empty exactly when one of its radii is nonpositive. -/
@[simp]
theorem polydisc_eq_bot_iff {c : ι → ℂ} {r : ι → ℝ} :
    polydisc c r = ⊥ ↔ ∃ i, r i ≤ 0 := by
  rw [← TopologicalSpace.Opens.coe_inj, coe_polydisc, TopologicalSpace.Opens.coe_bot,
    Set.pi_eq_empty_iff']
  simp only [mem_univ, true_and, Metric.ball_eq_empty]

/-- Increasing the radii gives an inclusion of concentric polydiscs. -/
theorem polydisc_mono {c : ι → ℂ} {r' r : ι → ℝ} (h : r' ≤ r) :
    polydisc c r' ≤ polydisc c r := by
  apply SetLike.coe_subset_coe.1
  rw [coe_polydisc, coe_polydisc]
  exact Set.pi_mono fun i _ ↦ Metric.ball_subset_ball (h i)

end TauCeti
