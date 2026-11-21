/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Unitriangular changes of a family

Let `x` and `z` be families of vectors indexed by a well-founded order, such that every `z j` is
`x j` plus a combination of the earlier `x l`. Such corrections occur when a basis is improved one
vector at a time, as in Evertse's lemma. Then `z` spans what `x` spans
(`Submodule.span_range_eq_span_range_of_sub_mem_span`), and a finite such `z` is linearly
independent when `x` is (`LinearIndependent.of_sub_mem_span`), over any nontrivial ring with the
Orzech property, in particular over every field.
-/

public section

open Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Preorder ι] {x z : ι → M}

/-- Two families span the same submodule when every `z j` is `x j` plus a combination of the
earlier `x l`. -/
theorem Submodule.span_range_eq_span_range_of_sub_mem_span [WellFoundedLT ι]
    (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) :
    span R (Set.range z) = span R (Set.range x) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    have hmem := add_mem (span_mono (Set.image_subset_range x _) (h j))
      (subset_span (R := R) (Set.mem_range_self j))
    rwa [sub_add_cancel] at hmem
  · rintro _ ⟨j, rfl⟩
    have hj : z j - x j ∈ span R (z '' Set.Iio j) := span_image_Iio_eq_span_image_Iio h j ▸ h j
    have hmem := sub_mem (subset_span (R := R) (Set.mem_range_self (f := z) j))
      (span_mono (Set.image_subset_range z _) hj)
    rwa [sub_sub_cancel] at hmem

/-- A finite family in which every `z j` is `x j` plus a combination of the earlier `x l` is
linearly independent when `x` is. -/
theorem LinearIndependent.of_sub_mem_span [OrzechProperty R] [Nontrivial R] [Finite ι]
    (hx : LinearIndependent R x) (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) :
    LinearIndependent R z := by
  have := Fintype.ofFinite ι
  rw [linearIndependent_iff_card_eq_finrank_span] at hx ⊢
  rwa [Set.finrank, span_range_eq_span_range_of_sub_mem_span h]
