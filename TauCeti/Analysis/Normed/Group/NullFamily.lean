/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Norm estimates for null families in ultrametric groups

A family tending to zero along the cofinite filter is bounded. If one of its terms has nonzero
norm, its largest norm is attained: outside a finite set every term is smaller than that fixed
term, and a largest term can be chosen inside the finite exceptional set. This turns the
non-strict ultrametric bound for infinite sums into two useful sharp statements.

First, if every term of a summable family has norm strictly less than a positive bound `B`, then
the sum also has norm strictly less than `B`. Second, if one term has norm strictly larger than
every other term, then the sum has exactly the norm of that dominant term. The statements include
empty families and the zero family; the latter is separated before invoking attainment.

Mathlib supplies the equivalence between summability and cofinite decay in a complete
nonarchimedean group, as well as the non-strict bound
`IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`. The results here isolate the finiteness
argument needed to make those bounds strict.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {ι E : Type*} [SeminormedAddCommGroup E]

/-- A family tending to zero along the cofinite filter and having a term of nonzero norm has a
term whose norm dominates the norms of all its terms. -/
theorem exists_forall_norm_le_of_tendsto_cofinite_zero {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) (hne : ∃ i, ‖f i‖ ≠ 0) :
    ∃ i, ∀ j, ‖f j‖ ≤ ‖f i‖ := by
  obtain ⟨i₀, hi₀⟩ := hne
  have hi₀pos : 0 < ‖f i₀‖ := lt_of_le_of_ne (norm_nonneg _) hi₀.symm
  have hnorm : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0) := by
    simpa only [norm_zero] using hf.norm
  have heventually : ∀ᶠ i in cofinite, ‖f i‖ < ‖f i₀‖ := by
    exact hnorm.eventually_lt_const hi₀pos
  have hfinite : {i | ‖f i₀‖ ≤ ‖f i‖}.Finite := by
    simpa only [eventually_cofinite, not_lt] using heventually
  let s : Finset ι := hfinite.toFinset
  have hi₀s : i₀ ∈ s := by simp [s]
  obtain ⟨i, -, hmax⟩ := s.exists_max_image (fun j ↦ ‖f j‖) ⟨i₀, hi₀s⟩
  refine ⟨i, fun j ↦ ?_⟩
  by_cases hj : ‖f i₀‖ ≤ ‖f j‖
  · exact hmax j (by simpa [s] using hj)
  · exact (le_of_lt (lt_of_not_ge hj)).trans (hmax i₀ hi₀s)

/-- A family tending to zero along the cofinite filter and having a term of nonzero norm attains
the supremum of the norms of its terms. -/
theorem exists_norm_eq_ciSup_of_tendsto_cofinite_zero {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) (hne : ∃ i, ‖f i‖ ≠ 0) :
    ∃ i, ‖f i‖ = ⨆ j, ‖f j‖ := by
  obtain ⟨i, hi⟩ := exists_forall_norm_le_of_tendsto_cofinite_zero hf hne
  let _ : Nonempty ι := ⟨i⟩
  have hbdd : BddAbove (Set.range fun j ↦ ‖f j‖) := hf.norm.bddAbove_range_of_cofinite
  exact ⟨i, le_antisymm (le_ciSup hbdd i) (ciSup_le hi)⟩

/-- In an ultrametric group, the sum of a summable family whose terms all have norm strictly less
than a positive bound `B` also has norm strictly less than `B`.

This includes empty families and identically zero families. -/
theorem norm_tsum_lt_of_summable_of_forall_lt [IsUltrametricDist E] {f : ι → E}
    (hf : Summable f) {B : ℝ} (hB : 0 < B) (h : ∀ i, ‖f i‖ < B) :
    ‖∑' i, f i‖ < B := by
  by_cases hnormzero : ∀ i, ‖f i‖ = 0
  · have hle : ‖∑' i, f i‖ ≤ 0 :=
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg le_rfl fun i ↦ (hnormzero i).le
    exact hle.trans_lt hB
  · push Not at hnormzero
    obtain ⟨i, hi⟩ := exists_forall_norm_le_of_tendsto_cofinite_zero
      hf.tendsto_cofinite_zero hnormzero
    exact (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) hi).trans_lt (h i)

/-- In an ultrametric group, a summable family with a unique dominant term has sum of the same
norm as that term. The hypothesis is phrased at the distinguished index: every other term has
strictly smaller norm. -/
theorem norm_tsum_eq_of_forall_norm_lt [T2Space E] [IsUltrametricDist E] {f : ι → E}
    (hf : Summable f) (i : ι) (hi : ∀ j, j ≠ i → ‖f j‖ < ‖f i‖) :
    ‖∑' j, f j‖ = ‖f i‖ := by
  classical
  by_cases hfi : ‖f i‖ = 0
  · have hle : ∀ j, ‖f j‖ ≤ 0 := by
      intro j
      by_cases hji : j = i
      · simp [hji, hfi]
      · exact (hi j hji).le.trans_eq hfi
    rw [hfi]
    exact le_antisymm
      (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg le_rfl hle) (norm_nonneg _)
  · let g : ι → E := fun j ↦ if j = i then 0 else f j
    have hfi_pos : 0 < ‖f i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfi)
    have hg : Summable g := hf.congr_cofinite <| (eventually_cofinite_ne i).mono fun j hj ↦ by
      simp [g, hj]
    have hglt : ‖∑' j, g j‖ < ‖f i‖ :=
      norm_tsum_lt_of_summable_of_forall_lt hg hfi_pos fun j ↦ by
        by_cases hji : j = i
        · simp [g, hji, hfi_pos]
        · simpa [g, hji] using hi j hji
    rw [hf.tsum_eq_add_tsum_ite i]
    have hg_eq : (fun j ↦ if j = i then 0 else f j) = g := rfl
    rw [hg_eq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hglt.ne', max_eq_left hglt.le]

end TauCeti
