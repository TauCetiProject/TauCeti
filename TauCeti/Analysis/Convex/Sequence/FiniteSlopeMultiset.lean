/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort

/-!
# Finite slope multisets

The finite slopes of a convex height sequence are the slopes of all of its unit edges,
counted with multiplicity. This file packages that invariant on `FiniteSlopeData`, the
canonical presentation of a nonempty convex height sequence with finite domain.

The multiset has cardinality equal to the horizontal length of the polygon. Its sum is the
difference between the endpoint heights.

## Main results

* `FiniteSlopeData.slopeMultiset`: the multiset of unit slopes.
* `FiniteSlopeData.count_slopeMultiset`: multiplicities count unit edges of a given slope.
* `FiniteSlopeData.card_slopeMultiset`: its cardinality is the horizontal length.
* `FiniteSlopeData.sum_slopeMultiset`: its sum is the total height change.

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

/-- The slope multiset consists of the slopes indexed by the unit edges. -/
theorem slopeMultiset_def (d : FiniteSlopeData Γ) :
    d.slopeMultiset = (List.ofFn d.slope : Multiset Γ) := (rfl)

/-- A nondecreasing unit-slope presentation is determined by its anchor and slope multiset.
In particular, different subdivisions of equal slopes do not give different unit data. -/
theorem eq_of_multiset_eq {Γ : Type*} [LinearOrder Γ] {d e : FiniteSlopeData Γ}
    (hs : d.start = e.start) (hy : d.initialHeight = e.initialHeight)
    (hm : d.slopeMultiset = e.slopeMultiset) : d = e := by
  simp only [slopeMultiset_def] at hm
  have hl := (Multiset.coe_eq_coe.mp hm).eq_of_pairwise'
    d.monotone.sortedLE_ofFn.pairwise e.monotone.sortedLE_ofFn.pairwise
  obtain ⟨s, y, n, f, hf⟩ := d
  obtain ⟨s', y', n', f', hf'⟩ := e
  dsimp only at hs hy hl
  subst s' y'
  have hn := congrArg List.length hl
  simp only [List.length_ofFn] at hn
  subst n'
  have hff := List.ofFn_injective hl
  subst f'
  rfl

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

end FiniteSlopeData

end TauCeti
