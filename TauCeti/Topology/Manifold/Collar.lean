/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

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

theorem isGlobalCollar_iff : GloballyCollared f ↔ ∃ c, IsGlobalCollar f c := Iff.rfl

namespace IsGlobalCollar

variable (h : IsGlobalCollar f c)
include h

theorem isEmbedding : IsEmbedding f := by
  have heq : f = c ∘ fun x : N => (x, ⟨0, by norm_num⟩) := by
    funext x
    exact (h.apply_zero x).symm
  rw [heq]
  exact h.isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkLeft _)

theorem injective : Function.Injective f := h.isEmbedding.injective

theorem continuous : Continuous f := h.isEmbedding.continuous

theorem range_subset : range f ⊆ range c := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, ⟨0, by norm_num⟩), h.apply_zero x⟩

/-- Restricting a collar along an open subset of its base preserves collar data. -/
theorem restrict {U : Set N} (hU : IsOpen U) :
    IsGlobalCollar (f ∘ ((↑) : U → N))
      (c ∘ Prod.map ((↑) : U → N) id) := by
  refine ⟨h.isOpenEmbedding.comp (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id), ?_⟩
  intro x
  exact h.apply_zero x

end IsGlobalCollar

end TauCeti
