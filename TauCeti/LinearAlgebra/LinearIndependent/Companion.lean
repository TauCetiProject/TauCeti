/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# A common independent companion

In a left vector space of rank greater than one over a division ring, any two nonzero vectors
have a common vector
independent of each. This includes infinite-dimensional spaces and the field with two elements.
The construction first chooses a vector independent of the first input; either it works for
the second input as well, or its sum with the first input works for both.

This is the linear-algebra step in comparing translations of Abel-map images using independent
pairs of sections.
-/

public section

namespace TauCeti

variable {baseField vectorSpace : Type*} [DivisionRing baseField]
  [AddCommGroup vectorSpace] [Module baseField vectorSpace]

/-- Two nonzero vectors in dimension at least two have a common independent
companion, without any assumption on the cardinality of the field. -/
theorem exists_linearIndependent_pair_companion
    (dimension : 1 < Module.rank baseField vectorSpace)
    {first second : vectorSpace} (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0) :
    ∃ companion : vectorSpace, LinearIndependent baseField ![first, companion] ∧
      LinearIndependent baseField ![second, companion] := by
  have pair_iff {u v : vectorSpace} (hu : u ≠ 0) :
      LinearIndependent baseField ![u, v] ↔ v ∉ Submodule.span baseField {u} := by
    rw [LinearIndependent.pair_iff' hu, Submodule.mem_span_singleton]
    simp only [not_exists]
  obtain ⟨independentVector, independent⟩ :=
    exists_linearIndependent_pair_of_one_lt_rank dimension first_nonzero
  have outside_first : independentVector ∉ Submodule.span baseField {first} :=
    (pair_iff first_nonzero).mp independent
  by_cases mem_second : independentVector ∈ Submodule.span baseField {second}
  · refine ⟨first + independentVector, ?_, ?_⟩
    · exact LinearIndependent.pair_add_right_iff.mpr independent
    · apply (pair_iff second_nonzero).mpr
      intro sum_mem
      have first_mem : first ∈ Submodule.span baseField {second} := by
        simpa using (Submodule.span baseField {second}).sub_mem sum_mem mem_second
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp first_mem
      have ha₀ : a ≠ 0 := by
        rintro rfl
        exact first_nonzero (by simpa using ha.symm)
      apply outside_first
      have hsecond : second ∈ Submodule.span baseField {first} :=
        (Submodule.span baseField {first}).smul_mem_iff ha₀ |>.mp
          (ha.symm ▸ Submodule.mem_span_singleton_self first)
      exact Submodule.mem_span_singleton_trans mem_second hsecond
  · exact ⟨independentVector, independent,
      (pair_iff second_nonzero).mpr mem_second⟩

end TauCeti
