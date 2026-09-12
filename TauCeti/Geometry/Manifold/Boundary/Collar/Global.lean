/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Maps.Basic
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
Theorem 9.25; this declaration is its topological abstraction.  The API adapts the existing
`TauCeti.Geometry.Manifold.LocallyFlat.Bicollar` formalization by replacing `ℝ` with `Ico 0 1`.
-/

public section

namespace TauCeti

open Set Topology

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  {f : N → M} {c : N × Ico (0 : ℝ) 1 → M}

/-- A global collar of `f` is an open embedding of the boundary times `[0,1)` whose zero slice is
`f`.  The parameter is a subtype, so the endpoint `1` is excluded by construction. -/
structure IsCollar (f : N → M) (c : N × Ico (0 : ℝ) 1 → M) : Prop where
  isOpenEmbedding : IsOpenEmbedding c
  apply_zero : ∀ x, c (x, ⟨0, by norm_num⟩) = f x

/-- A map admits a global collar. -/
def IsCollared (f : N → M) : Prop := ∃ c, IsCollar f c

/-- The identity map on the product is the canonical collar of its zero slice. -/
theorem isCollar_prodMkLeft :
    IsCollar ((fun x : N => (x, ⟨0, by norm_num⟩)) : N → N × Ico (0 : ℝ) 1)
      (id : N × Ico (0 : ℝ) 1 → N × Ico (0 : ℝ) 1) := by
  refine ⟨IsOpenEmbedding.id, ?_⟩
  intro x
  rfl

/-- The canonical product zero slice admits a collar. -/
theorem isCollared_prodMkLeft :
    IsCollared ((fun x : N => (x, ⟨0, by norm_num⟩)) : N → N × Ico (0 : ℝ) 1) :=
  ⟨_, isCollar_prodMkLeft⟩

/-- An existential collar is precisely a map together with collar data. -/
theorem isCollared_iff : IsCollared f ↔ ∃ c, IsCollar f c := Iff.rfl

namespace IsCollar

variable (h : IsCollar f c)
include h

/-- A collar witness implies that its boundary map admits a collar. -/
theorem isCollared : IsCollared f := ⟨c, h⟩

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

/-- The boundary image lies in the image of the collar map. -/
theorem range_subset_range : range f ⊆ range c := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, ⟨0, by norm_num⟩), h.apply_zero x⟩

/-- The zero slice of a collar has exactly the boundary image as its range. -/
theorem image_prod_singleton_zero :
    c '' (univ ×ˢ ({⟨0, by norm_num⟩} : Set (Ico (0 : ℝ) 1))) = range f := by
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    exact ⟨x, (h.apply_zero x).symm.trans (congrArg c (congrArg (fun z => (x, z)) ht.symm))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, ⟨0, by norm_num⟩), ⟨mem_univ _, mem_singleton _⟩, h.apply_zero x⟩

/-- The collar map's preimage of the boundary is exactly its zero slice. -/
@[simp] theorem preimage_range :
    c ⁻¹' range f = univ ×ˢ ({⟨0, by norm_num⟩} : Set (Ico (0 : ℝ) 1)) := by
  ext ⟨x, t⟩
  constructor
  · rintro ⟨y, hy⟩
    have hxy : c (x, t) = c (y, ⟨0, by norm_num⟩) := hy.symm.trans (h.apply_zero y).symm
    have hprod := h.isOpenEmbedding.injective hxy
    exact ⟨mem_univ _, mem_singleton_iff.mpr (congrArg Prod.snd hprod)⟩
  · rintro ⟨_, ht⟩
    rw [mem_singleton_iff] at ht
    change c (x, t) ∈ range f
    have ht' : t = ⟨0, by norm_num⟩ := ht
    rw [ht']
    exact ⟨x, (h.apply_zero x).symm⟩

/-- Reparametrizing the boundary of a collar by a homeomorphism preserves it. -/
theorem comp_homeomorph (e : P ≃ₜ N) :
    IsCollar (f ∘ e) (c ∘ Prod.map e id) := by
  refine ⟨h.isOpenEmbedding.comp (e.isOpenEmbedding.prodMap IsOpenEmbedding.id), ?_⟩
  intro x
  simpa [Function.comp_apply] using h.apply_zero (e x)

/-- Open embeddings of the ambient space carry collars to collars. -/
theorem isOpenEmbedding_comp {g : M → P} (hg : IsOpenEmbedding g) :
    IsCollar (g ∘ f) (g ∘ c) where
  isOpenEmbedding := hg.comp h.isOpenEmbedding
  apply_zero x := by
    simpa only [Function.comp_apply] using congrArg g (h.apply_zero x)

/-- Restricting a collar along an open subset of its base preserves collar data. -/
theorem restrict {U : Set N} (hU : IsOpen U) :
    IsCollar (f ∘ ((↑) : U → N))
      (c ∘ Prod.map ((↑) : U → N) id) := by
  refine ⟨h.isOpenEmbedding.comp (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id), ?_⟩
  intro x
  simpa only [Function.comp_apply, Prod.map_apply, id_eq] using h.apply_zero (x : N)

end IsCollar

namespace IsCollared

/-- A map admitting a collar is an embedding. -/
theorem isEmbedding (h : IsCollared f) : IsEmbedding f :=
  let ⟨_, hc⟩ := h; hc.isEmbedding

/-- A collared map remains collared on every open subset of its domain. -/
theorem restrict (h : IsCollared f) {U : Set N} (hU : IsOpen U) :
    IsCollared (f ∘ ((↑) : U → N)) :=
  let ⟨_, hc⟩ := h; (hc.restrict hU).isCollared

/-- Open embeddings of the ambient space preserve the existence of a collar. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsCollared f) (hg : IsOpenEmbedding g) :
    IsCollared (g ∘ f) :=
  let ⟨_, hc⟩ := h; (hc.isOpenEmbedding_comp hg).isCollared

/-- Reparametrizing the domain by a homeomorphism preserves the existence of a collar. -/
theorem comp_homeomorph (h : IsCollared f) (e : P ≃ₜ N) : IsCollared (f ∘ e) :=
  let ⟨_, hc⟩ := h; (hc.comp_homeomorph e).isCollared

end IsCollared

end TauCeti
