/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Norm estimates for null families in ultrametric groups

A family tending to zero along the cofinite filter is bounded. On a nonempty index type its
largest norm is attained, including when every term has norm zero. This turns the non-strict
ultrametric bound for infinite sums into two useful sharp statements.

For a family `f` with sum `a` in a seminormed ultrametric group,
`HasSum.norm_lt_of_forall_norm_lt` shows that if every term has norm strictly less than a positive
bound `B`, then `‖a‖ < B`. The strict bound includes empty families and families whose terms all
have norm zero. The result `HasSum.norm_eq_of_forall_norm_lt` says that if one term has norm
strictly larger than every other term, then `a` has exactly the norm of that dominant term. Both
estimates apply to every `HasSum` limit without completeness or Hausdorff assumptions.

Mathlib supplies the finite-sum estimate
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` and the term-removal identity
`hasSum_ite_sub_hasSum`. The results here extend finite-sum bounds to strict bounds and
dominant-term equalities for `HasSum` limits.
-/

public section

open Filter
open scoped Topology

variable {ι E : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup E]

/-- A family on a nonempty index type tending to zero along the cofinite filter has a term whose
norm dominates the norms of all its terms. -/
theorem Filter.Tendsto.exists_forall_norm_le [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i, ∀ j, ‖f j‖ ≤ ‖f i‖ := by
  by_cases hne : ∃ i, ‖f i‖ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hne
    have hi₀pos : 0 < ‖f i₀‖ := lt_of_le_of_ne (norm_nonneg _) hi₀.symm
    have hnorm : Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0) := by
      simpa only [norm_zero] using hf.norm
    have hfinite : {i | ‖f i₀‖ ≤ ‖f i‖}.Finite := by
      simpa only [eventually_cofinite, not_lt] using hnorm.eventually_lt_const hi₀pos
    obtain ⟨i, _, hmax⟩ := Set.exists_max_image _ (fun j ↦ ‖f j‖) hfinite ⟨i₀, by simp⟩
    refine ⟨i, fun j ↦ ?_⟩
    by_cases hj : ‖f i₀‖ ≤ ‖f j‖
    · exact hmax j hj
    · exact (le_of_not_ge hj).trans (hmax i₀ (by simp))
  · push Not at hne
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, fun j ↦ by simp [hne]⟩

/-- A family on a nonempty index type tending to zero along the cofinite filter attains the
supremum of the norms of its terms. -/
theorem Filter.Tendsto.exists_norm_eq_ciSup [Nonempty ι] {f : ι → E}
    (hf : Tendsto f cofinite (𝓝 0)) : ∃ i, ‖f i‖ = ⨆ j, ‖f j‖ := by
  obtain ⟨i, hi⟩ := hf.exists_forall_norm_le
  have hbdd : BddAbove (Set.range fun j ↦ ‖f j‖) := hf.norm.bddAbove_range_of_cofinite
  exact ⟨i, le_antisymm (le_ciSup hbdd i) (ciSup_le hi)⟩

end SeminormedAddGroup

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] [IsUltrametricDist E]

/-- In an ultrametric group, any sum of a family whose terms all have norm strictly less than a
positive bound `B` also has norm strictly less than `B`.

This includes empty families and families whose terms all have norm zero. -/
theorem HasSum.norm_lt_of_forall_norm_lt {f : ι → E} {a : E} (hf : HasSum f a)
    {B : ℝ} (hB : 0 < B) (h : ∀ i, ‖f i‖ < B) : ‖a‖ < B := by
  cases isEmpty_or_nonempty ι
  · have ha : ‖a‖ ≤ 0 :=
      le_of_tendsto' hf.norm fun s ↦ by simp [Finset.eq_empty_of_isEmpty]
    exact ha.trans_lt hB
  · obtain ⟨i, hi⟩ := hf.summable.tendsto_cofinite_zero.exists_forall_norm_le
    exact (le_of_tendsto' hf.norm fun s ↦
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ ↦ hi j).trans_lt
        (h i)

/-- In an ultrametric group, any sum of a family with a unique dominant term has the same norm as
that term. Every other term must have strictly smaller norm than the distinguished term. -/
theorem HasSum.norm_eq_of_forall_norm_lt {f : ι → E} {a : E} (hf : HasSum f a)
    (i : ι) (hi : ∀ j, j ≠ i → ‖f j‖ < ‖f i‖) : ‖a‖ = ‖f i‖ := by
  classical
  by_cases hfi : ‖f i‖ = 0
  · have hle : ∀ j, ‖f j‖ ≤ 0 := by
      intro j
      by_cases hji : j = i
      · simp [hji, hfi]
      · exact (hi j hji).le.trans_eq hfi
    rw [hfi]
    exact le_antisymm (le_of_tendsto' hf.norm fun s ↦
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg le_rfl fun j _ ↦ hle j) (norm_nonneg _)
  · have hfi_pos : 0 < ‖f i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfi)
    have hglt : ‖a - f i‖ < ‖f i‖ :=
      (hasSum_ite_sub_hasSum hf i).norm_lt_of_forall_norm_lt hfi_pos fun j ↦ by
        by_cases hji : j = i
        · simp [hji, hfi_pos]
        · simpa [hji] using hi j hji
    calc
      ‖a‖ = ‖(a - f i) + f i‖ := by rw [sub_add_cancel]
      _ = ‖f i‖ := by
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hglt.ne, max_eq_right hglt.le]

end SeminormedAddCommGroup
