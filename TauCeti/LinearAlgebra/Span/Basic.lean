/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Exchanging a generator in a finite span

A generator with a unit coefficient in a linear combination can be replaced by that combination
without changing the span.
-/

public section

namespace TauCeti.Submodule

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- If one coefficient of `x` in a finite span is a unit, then `x` can replace that generator. -/
theorem span_insert_erase_eq_span_of_isUnit [DecidableEq M] {s : Finset M} {i x : M}
    {f : M → A} (hi : i ∈ s) (hf : ∑ a ∈ s, f a • a = x) (hfi : IsUnit (f i)) :
    _root_.Submodule.span A ((insert x (s.erase i)) : Set M) =
      _root_.Submodule.span A (s : Set M) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff] at hy
    rcases hy with rfl | hy
    · rw [← hf]
      exact (_root_.Submodule.span A (s : Set M)).sum_mem fun a ha ↦
        (_root_.Submodule.span A (s : Set M)).smul_mem _
          (Submodule.subset_span (Finset.mem_coe.mpr ha))
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hy))
  · rw [Submodule.span_le]
    intro y hy
    by_cases h : y = i
    · subst y
      have hsum : f i • i + ∑ a ∈ s.erase i, f a • a = x := by
        rw [Finset.add_sum_erase _ (fun a ↦ f a • a) hi, hf]
      have hmem : f i • i ∈ _root_.Submodule.span A ((insert x (s.erase i)) : Set M) := by
        have hxmem : x ∈ _root_.Submodule.span A ((insert x (s.erase i)) : Set M) :=
          Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl))
        have hsmem : (∑ a ∈ s.erase i, f a • a) ∈
            _root_.Submodule.span A ((insert x (s.erase i)) : Set M) :=
          (_root_.Submodule.span A ((insert x (s.erase i)) : Set M)).sum_mem fun a ha ↦
            (_root_.Submodule.span A ((insert x (s.erase i)) : Set M)).smul_mem _
              (Submodule.subset_span (Set.mem_insert_of_mem x (Finset.mem_coe.mpr ha)))
        have hsub : x - (∑ a ∈ s.erase i, f a • a) ∈
            _root_.Submodule.span A ((insert x (s.erase i)) : Set M) :=
          _root_.Submodule.sub_mem (_root_.Submodule.span A ((insert x (s.erase i)) : Set M))
            hxmem hsmem
        rwa [eq_sub_of_add_eq hsum]
      exact ((_root_.Submodule.span A ((insert x (s.erase i)) : Set M)).smul_mem_iff_of_isUnit
        hfi).mp hmem
    · exact Submodule.subset_span (Set.mem_insert_of_mem x
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hy⟩)))

end TauCeti.Submodule
