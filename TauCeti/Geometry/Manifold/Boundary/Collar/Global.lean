/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic.NormNum

/-!
# Global collar data

This file records the global object supplied by a collar theorem.  Local collar charts are useful
for proving the theorem, but gluing constructions need one map on the whole boundary.  The
definition is deliberately topological and independent of a choice of manifold model; smooth and
PL collar theorems can add the corresponding regularity to the same data.

The parameter is the half-open interval `[0,1)`.  Thus a collar is an open embedding of
`N × Ico 0 1` whose zero slice is the given embedding.  The small API below is the part consumed by
gluing: restriction along an open subset of the boundary, and the injectivity and zero-slice
consequences.

The collar-neighborhood formulation follows J. Lee, *Introduction to Smooth Manifolds*, 2nd ed.,
Theorem 9.25; this declaration is its topological abstraction.
-/

public section

namespace TauCeti

open Set Topology

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  {f : N → M} {c : N × Ico (0 : ℝ) 1 → M}

/-- A global collar of `f` is an open embedding of the boundary times `[0,1)` whose zero slice is
`f`.  The parameter is a subtype, so the endpoint `1` is excluded by construction. -/
structure IsGlobalCollar (f : N → M) (c : N × Ico (0 : ℝ) 1 → M) : Prop where
  isOpenEmbedding : IsOpenEmbedding c
  apply_zero : ∀ x, c (x, ⟨0, by norm_num⟩) = f x

/-- A map admits a global collar. -/
def GloballyCollared (f : N → M) : Prop := ∃ c, IsGlobalCollar f c

/-- The product collar is a canonical example of global collar data. -/
theorem globallyCollared_prodMk_zero :
    GloballyCollared
      ((fun x : N => (x, ⟨0, by norm_num⟩)) : N → N × Ico (0 : ℝ) 1) := by
  refine ⟨(id : N × Ico (0 : ℝ) 1 → N × Ico (0 : ℝ) 1), ⟨IsOpenEmbedding.id, ?_⟩⟩
  intro x
  rfl

namespace IsGlobalCollar

variable (h : IsGlobalCollar f c)
include h

/-- The boundary map of a global collar is an embedding. -/
theorem isEmbedding : IsEmbedding f := by
  have heq : f = c ∘ fun x : N => (x, ⟨0, by norm_num⟩) := by
    funext x
    exact (h.apply_zero x).symm
  rw [heq]
  exact h.isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkLeft _)

/-- The boundary map of a global collar is injective. -/
theorem injective : Function.Injective f := h.isEmbedding.injective

/-- The boundary map of a global collar is continuous. -/
theorem continuous : Continuous f := h.isEmbedding.continuous

/-- The boundary image lies in the image of the collar. -/
theorem range_subset_range : range f ⊆ range c := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, ⟨0, by norm_num⟩), h.apply_zero x⟩

/-- The zero slice of a collar has exactly the boundary image as its range. -/
theorem image_prod_univ_singleton_zero :
    c '' (univ ×ˢ ({⟨0, by norm_num⟩} : Set (Ico (0 : ℝ) 1))) = range f := by
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    exact ⟨x, (h.apply_zero x).symm.trans (congrArg c (congrArg (fun z => (x, z)) ht.symm))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, ⟨0, by norm_num⟩), ⟨mem_univ _, mem_singleton _⟩, h.apply_zero x⟩

/-- Restricting a collar along an open subset of its base preserves collar data. -/
theorem restrict {U : Set N} (hU : IsOpen U) :
    IsGlobalCollar (f ∘ ((↑) : U → N))
      (c ∘ Prod.map ((↑) : U → N) id) := by
  refine ⟨h.isOpenEmbedding.comp (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id), ?_⟩
  intro x
  exact h.apply_zero x

end IsGlobalCollar

end TauCeti
