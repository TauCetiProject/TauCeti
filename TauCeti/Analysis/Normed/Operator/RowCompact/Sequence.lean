/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Common row majorants for convergent sequences

A norm-convergent sequence of row-compact maps between model spaces has a common nonnegative
null row majorant, including its limit. This permits estimates depending on row decay to be
applied uniformly to such sequences.
-/

public section

namespace TauCeti

open Filter Finset Topology ContinuousLinearMap
open scoped ZeroAtInfty RingOpNorm

variable {I J R : Type*} [TopologicalSpace I] [TopologicalSpace J]
  [DiscreteTopology J] [DecidableEq J] [SeminormedRing R] [NormedRing.IsTate R]
  {u : C₀(J, R) →L[R] C₀(I, R)} {v : ℕ → C₀(J, R) →L[R] C₀(I, R)}

/-- A norm-convergent sequence of row-compact maps and its limit admit a common
nonnegative null row majorant. Neither completeness nor ultrametricity is required.
In particular the limit's row decay need not be assumed separately. -/
theorem exists_common_row_majorant_of_tendsto_ringOpNorm
    (h : Tendsto (fun n ↦ ‖u - v n‖) atTop (𝓝 0))
    (hv : ∀ n, (v n).IsRowCompact) :
    ∃ r : I → ℝ, (∀ i, 0 ≤ r i) ∧ Tendsto r cofinite (𝓝 0) ∧
      (∀ i j, ‖u.matrixCoeff i j‖ ≤ r i) ∧
      (∀ n i j, ‖(v n).matrixCoeff i j‖ ≤ r i) := by
  have hu : u.IsRowCompact := isRowCompact_of_tendsto h (Eventually.of_forall hv)
  have hrow (n : ℕ) (i : I) : (v n).rowNorm i ≤ ‖u - v n‖ + u.rowNorm i := by
    simpa only [← neg_sub u (v n), ringOpNorm_neg] using
      (v n).rowNorm_le_ringOpNorm_sub_add u i
  obtain ⟨C, hC⟩ := h.bddAbove_range
  have hbdd (i : I) : BddAbove (Set.range fun n ↦ (v n).rowNorm i) :=
    ⟨C + ‖u‖, by
      rintro _ ⟨n, rfl⟩
      exact (hrow n i).trans (add_le_add (hC ⟨n, rfl⟩) (u.rowNorm_le_ringOpNorm i))⟩
  let r := fun i ↦ max (u.rowNorm i) (⨆ n, (v n).rowNorm i)
  have hr₀ (i : I) : 0 ≤ r i := (u.rowNorm_nonneg i).trans (le_max_left _ _)
  refine ⟨r, hr₀, ?_, (fun i j ↦ (u.norm_matrixCoeff_le_rowNorm i j).trans
    (le_max_left _ _)), fun n i j ↦ ((v n).norm_matrixCoeff_le_rowNorm i j).trans
      ((le_ciSup (hbdd i) n).trans (le_max_right _ _))⟩
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun i ↦ ha.trans_le (hr₀ i),
    fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_lt_const (by positivity : 0 < ε / 4))
  have hhead : ∀ᶠ i in cofinite, ∀ n ∈ range N, (v n).rowNorm i < ε / 2 :=
    (eventually_all_finset _).2 fun n _ ↦
      (hv n).tendsto_rowNorm.eventually_lt_const (half_pos hε)
  filter_upwards [hhead, hu.tendsto_rowNorm.eventually_lt_const
    (by positivity : 0 < ε / 4)] with i hi hui
  have hall (n : ℕ) : (v n).rowNorm i ≤ ε / 2 := by
    by_cases hn : n < N
    · exact (hi n (mem_range.mpr hn)).le
    · have := hN n (by omega)
      linarith [hrow n i]
  exact lt_of_le_of_lt (max_le (by linarith) (ciSup_le hall)) (half_lt_self hε)

end TauCeti
