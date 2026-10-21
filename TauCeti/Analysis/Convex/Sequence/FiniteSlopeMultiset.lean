/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.Analysis.Convex.Sequence.SlopeData
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite slope multisets

The finite slopes of a convex height sequence are the slopes of all of its unit edges,
counted with multiplicity. This file packages that invariant on `FiniteSlopeData`, the
canonical presentation of a nonempty convex height sequence with finite domain.

The multiset has cardinality equal to the horizontal length of the polygon. Its sum is the
difference between the endpoint heights. The multiplicity of a real slope `σ` is the width of
the finite face of slope `σ`, so a singleton face contributes multiplicity zero.

## Main results

* `FiniteSlopeData.slopeMultiset`: the multiset of unit slopes.
* `FiniteSlopeData.count_slopeMultiset`: multiplicities count unit edges of a given slope.
* `FiniteSlopeData.card_slopeMultiset`: its cardinality is the horizontal length.
* `FiniteSlopeData.sum_slopeMultiset`: its sum is the total height change.
* `FiniteSlopeData.count_slopeMultiset_of_isFiniteFace`: the multiplicity of a slope is the
  width of the finite face of that slope.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

open Finset

namespace TauCeti

namespace FiniteSlopeData

variable {Γ : Type*} [Preorder Γ]

/-- The multiset of the slopes of the unit edges of finite slope data.

Each `i : Fin length` contributes one copy of `slope i`, so repeated slopes retain their
multiplicity. In particular, slope data of length zero has the empty slope multiset. -/
def slopeMultiset (d : FiniteSlopeData Γ) : Multiset Γ :=
  List.ofFn d.slope

/-- The slope multiset lists the slopes of the unit edges from left to right. -/
theorem slopeMultiset_def (d : FiniteSlopeData Γ) : d.slopeMultiset = List.ofFn d.slope :=
  (rfl)

/-- A value occurs in the slope multiset exactly when it is the slope of a unit edge. -/
@[simp]
theorem mem_slopeMultiset {d : FiniteSlopeData Γ} {m : Γ} :
    m ∈ d.slopeMultiset ↔ ∃ i : Fin d.length, d.slope i = m := by
  simp [slopeMultiset]

/-- The slope multiset is empty exactly when the represented polygon is a singleton. -/
@[simp]
theorem slopeMultiset_eq_zero_iff {d : FiniteSlopeData Γ} :
    d.slopeMultiset = 0 ↔ d.length = 0 := by
  simp [slopeMultiset]

/-- The number of finite unit slopes is the horizontal length of the polygon. -/
@[simp]
theorem card_slopeMultiset (d : FiniteSlopeData Γ) :
    d.slopeMultiset.card = d.length := by
  simp [slopeMultiset]

/-- The multiplicity of a value in the slope multiset is the number of unit edges with that
slope. -/
@[simp]
theorem count_slopeMultiset [DecidableEq Γ] (d : FiniteSlopeData Γ) (m : Γ) :
    d.slopeMultiset.count m = #{i | d.slope i = m} := by
  rw [slopeMultiset, ← Fin.univ_val_map, Multiset.count_map]
  simp [eq_comm, Finset.card, Finset.filter_val]

section AddCommMonoid

variable {Γ' : Type*} [Preorder Γ'] [AddCommMonoid Γ] [AddCommMonoid Γ']

/-- The slope multiset of transported slope data is the image of the slope multiset. -/
@[simp]
theorem slopeMultiset_map (d : FiniteSlopeData Γ) (f : Γ →+o Γ') :
    (d.map f).slopeMultiset = d.slopeMultiset.map f := by
  simp [slopeMultiset, Function.comp_def]

/-- The sum of the finite slopes is the sum over the unit edges. -/
theorem sum_slopeMultiset_eq_sum (d : FiniteSlopeData Γ) :
    d.slopeMultiset.sum = ∑ i, d.slope i := by
  simp [slopeMultiset, List.sum_ofFn]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup Γ]

/-- The sum of the finite slopes is the difference between the endpoint heights. -/
theorem sum_slopeMultiset (d : FiniteSlopeData Γ) :
    d.slopeMultiset.sum =
      (d.heights (d.start + d.length)).untop₀ - (d.heights d.start).untop₀ := by
  rw [d.heights_start_add_length, d.heights_start, d.sum_slopeMultiset_eq_sum]
  simp

end AddCommGroup

/-- A polygon represented by real finite slope data has a finite face at every real slope. -/
theorem exists_isFiniteFace_heights (d : FiniteSlopeData ℝ) (σ : ℝ) :
    ∃ l u : ℕ, IsFiniteFace d.heights σ l u :=
  d.isConvexSeq_heights.exists_isFiniteFace_of_finiteDomain_eq_Icc
    (Nat.le_add_right _ _) (fun _ ↦ d.heights_ne_top_iff) σ

/-- The multiplicity of a real slope `σ` in the slope multiset is the width `u - l` of the
finite face of slope `σ`. The endpoints `l` and `u` are absolute indices. -/
theorem count_slopeMultiset_of_isFiniteFace (d : FiniteSlopeData ℝ) {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace d.heights σ l u) : d.slopeMultiset.count σ = u - l := by
  classical
  have hl := (d.heights_ne_top_iff (n := l)).mp hf.left_ne_top
  have hu := (d.heights_ne_top_iff (n := u)).mp hf.right_ne_top
  have hlu := hf.left_le_right
  rw [count_slopeMultiset, ← Nat.card_Ico]
  refine Finset.card_bij (fun i _ ↦ d.start + i) (fun i hi ↦ ?_)
    (fun i _ j _ hij ↦ Fin.ext (by simpa using hij)) (fun n hn ↦ ?_)
  · rw [Finset.mem_filter_univ] at hi
    have hedge : d.start + (i : ℕ) ∈ finiteEdges d.heights := by
      simp only [mem_finiteEdges, ne_eq, heights_eq_top_iff, not_or, not_lt]
      omega
    rw [← d.unitSlope_heights] at hi
    rw [Finset.mem_Ico]
    by_contra hnot
    rcases not_and_or.mp hnot with hil | hiu
    · exact (hf.unitSlope_lt d.isConvexSeq_heights hedge (not_le.mp hil)).ne hi
    · exact (hf.lt_unitSlope d.isConvexSeq_heights hedge (not_lt.mp hiu)).ne' hi
  · rw [Finset.mem_Ico] at hn
    refine ⟨⟨n - d.start, by omega⟩, ?_, by dsimp only; omega⟩
    rw [Finset.mem_filter_univ, ← d.unitSlope_heights]
    exact hf.unitSlope_eq (by dsimp only; omega) (by dsimp only; omega)

end FiniteSlopeData

end TauCeti
