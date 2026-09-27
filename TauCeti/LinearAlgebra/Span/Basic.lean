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
  have hx : x ∈ _root_.Submodule.span A (s : Set M) :=
    hf ▸ sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)
  have hi' : i ∈ _root_.Submodule.span A (insert x (s.erase i : Set M)) := by
    refine (Submodule.smul_mem_iff_of_isUnit _ hfi).mp (Submodule.mem_span_insert.mpr
      ⟨1, -∑ a ∈ s.erase i, f a • a,
        neg_mem (sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)), ?_⟩)
    rw [one_smul, ← hf, ← Finset.add_sum_erase _ _ hi, add_neg_cancel_right]
  calc _ = _root_.Submodule.span A (insert i (insert x (s.erase i : Set M))) :=
        (Submodule.span_insert_eq_span hi').symm
    _ = _root_.Submodule.span A (insert x (s : Set M)) := by
      rw [Set.insert_comm, ← Finset.coe_insert, Finset.insert_erase hi]
    _ = _ := Submodule.span_insert_eq_span hx

end TauCeti.Submodule
