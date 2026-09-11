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
gluing: restriction to a smaller interval, restriction along an open subset of the boundary, and
the injectivity and zero-slice consequences.
-/

public section

namespace TauCeti

open Set

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

/-- Restricting the collar to a smaller half-open interval preserves collar data. -/
theorem restrict_interval {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IsGlobalCollar f (c ∘ fun p : N × Ico (0 : ℝ) a =>
      (p.1, ⟨p.2.1, le_trans p.2.2 ha1⟩)) := by
  let e : N × Ico (0 : ℝ) a → N × Ico (0 : ℝ) 1 := fun p =>
    (p.1, ⟨p.2.1, lt_of_lt_of_le p.2.2 ha1⟩)
  have he : IsOpenEmbedding e := by
    refine (IsOpenEmbedding.id.prodMap ?_).comp ?_
    · exact IsOpenEmbedding.subtypeVal
    · exact IsOpenEmbedding.id
  refine ⟨c ∘ e, h.isOpenEmbedding.comp he, ?_⟩
  intro x
  exact h.apply_zero x

/-- Restricting a collar along an open subset of its base preserves collar data. -/
theorem restrict {U : Set N} (hU : IsOpen U) :
    IsGlobalCollar (f ∘ ((↑) : U → N))
      (c ∘ Prod.map ((↑) : U → N) id) := by
  refine ⟨c ∘ Prod.map ((↑) : U → N) id, ?_, ?_⟩
  · exact h.isOpenEmbedding.comp (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id)
  · intro x
    exact h.apply_zero x

end IsGlobalCollar

end TauCeti
