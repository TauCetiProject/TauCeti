/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
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
  rw [Set.prod_singleton, Set.image_image, Set.image_univ]
  exact congrArg Set.range (funext h.apply_zero)

/-- The collar map's preimage of the boundary is exactly its zero slice. -/
@[simp] theorem preimage_range :
    c ⁻¹' range f = univ ×ˢ ({⟨0, by norm_num⟩} : Set (Ico (0 : ℝ) 1)) := by
  rw [← h.image_prod_singleton_zero, h.isOpenEmbedding.injective.preimage_image]

/-- Pulling back the boundary parameter along an open embedding preserves collar data. -/
theorem comp_isOpenEmbedding {e : P → N} (he : IsOpenEmbedding e) :
    IsCollar (f ∘ e) (c ∘ Prod.map e id) := by
  refine ⟨h.isOpenEmbedding.comp (he.prodMap IsOpenEmbedding.id), ?_⟩
  intro x
  simpa [Function.comp_apply] using h.apply_zero (e x)

/-- Reparametrizing the depth coordinate by an open embedding that fixes zero preserves a
collar. -/
theorem reparam_isOpenEmbedding {e : Ico (0 : ℝ) 1 → Ico (0 : ℝ) 1}
    (he : IsOpenEmbedding e) (he_zero : e ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) :
    IsCollar f (c ∘ Prod.map id e) := by
  refine ⟨h.isOpenEmbedding.comp (IsOpenEmbedding.id.prodMap he), ?_⟩
  intro x
  simpa [Function.comp_apply, he_zero] using h.apply_zero x

/-- Shrinking the depth of a collar by a factor in `(0,1]` preserves collar data. -/
theorem scale (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
    IsCollar f (c ∘ Prod.map id fun t : Ico (0 : ℝ) 1 =>
      ⟨r * t, mul_nonneg hr.1.le t.2.1,
        (mul_le_of_le_one_left t.2.1 hr.2).trans_lt t.2.2⟩) := by
  let er : Ico (0 : ℝ) 1 ≃ₜ Ico (0 : ℝ) r :=
    (Homeomorph.mulLeft₀ r hr.1.ne').sets <| by
      ext x
      have hx := Set.ext_iff.mp
        ((OrderIso.mulLeft₀ r hr.1).toOrderEmbedding.preimage_Ico (0 : ℝ) 1) x
      simpa only [Set.mem_preimage, Homeomorph.coe_mulLeft₀,
        OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply, mul_zero, mul_one] using hx.symm
  have hsubset : Ico (0 : ℝ) r ⊆ Ico (0 : ℝ) 1 := Set.Ico_subset_Ico_right hr.2
  have hopen : IsOpen {x : Ico (0 : ℝ) 1 | (x : ℝ) ∈ Ico (0 : ℝ) r} := by
    have heq : {x : Ico (0 : ℝ) 1 | (x : ℝ) ∈ Ico (0 : ℝ) r} =
        ((↑) : Ico (0 : ℝ) 1 → ℝ) ⁻¹' Iio r := by
      ext x
      simp [x.2.1]
    rw [heq]
    exact isOpen_Iio.preimage continuous_subtype_val
  have he : IsOpenEmbedding (Set.inclusion hsubset ∘ er) :=
    (IsOpenEmbedding.inclusion hsubset hopen).comp er.isOpenEmbedding
  have er_coe (x : Ico (0 : ℝ) 1) : (er x : ℝ) = r * x :=
    congrFun (Homeomorph.coe_mulLeft₀ r hr.1.ne') x
  have he_zero :
      (Set.inclusion hsubset ∘ er) ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simpa only [Function.comp_apply, Set.inclusion_mk, mul_zero] using
      er_coe ⟨0, by norm_num⟩
  have he_eq : (Set.inclusion hsubset ∘ er) = fun t : Ico (0 : ℝ) 1 =>
      ⟨r * t, mul_nonneg hr.1.le t.2.1,
        (mul_le_of_le_one_left t.2.1 hr.2).trans_lt t.2.2⟩ := by
    funext t
    apply Subtype.ext
    simpa only [Function.comp_apply, Set.inclusion_mk] using er_coe t
  convert h.reparam_isOpenEmbedding he he_zero using 1
  exact congrArg (fun e => c ∘ Prod.map id e) he_eq.symm

/-- Reparametrizing the boundary of a collar by a homeomorphism preserves it. -/
theorem comp_homeomorph (e : P ≃ₜ N) :
    IsCollar (f ∘ e) (c ∘ Prod.map e id) :=
  h.comp_isOpenEmbedding e.isOpenEmbedding

/-- Open embeddings of the ambient space carry collars to collars. -/
theorem isOpenEmbedding_comp {g : M → P} (hg : IsOpenEmbedding g) :
    IsCollar (g ∘ f) (g ∘ c) where
  isOpenEmbedding := hg.comp h.isOpenEmbedding
  apply_zero x := by
    simpa only [Function.comp_apply] using congrArg g (h.apply_zero x)

/-- Restricting a collar along an open subset of its base preserves collar data. -/
theorem restrict {U : Set N} (hU : IsOpen U) :
    IsCollar (f ∘ ((↑) : U → N))
      (c ∘ Prod.map ((↑) : U → N) id) :=
  h.comp_isOpenEmbedding hU.isOpenEmbedding_subtypeVal

end IsCollar

namespace IsCollared

/-- A map admitting a collar is an embedding. -/
theorem isEmbedding (h : IsCollared f) : IsEmbedding f :=
  let ⟨_, hc⟩ := h; hc.isEmbedding

/-- Precomposing a collared map with an open embedding preserves the existence of a collar. -/
theorem comp_isOpenEmbedding (h : IsCollared f) {e : P → N} (he : IsOpenEmbedding e) :
    IsCollared (f ∘ e) :=
  let ⟨_, hc⟩ := h; (hc.comp_isOpenEmbedding he).isCollared

/-- A collared map remains collared on every open subset of its domain. -/
theorem restrict (h : IsCollared f) {U : Set N} (hU : IsOpen U) :
    IsCollared (f ∘ ((↑) : U → N)) :=
  h.comp_isOpenEmbedding hU.isOpenEmbedding_subtypeVal

/-- Open embeddings of the ambient space preserve the existence of a collar. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsCollared f) (hg : IsOpenEmbedding g) :
    IsCollared (g ∘ f) :=
  let ⟨_, hc⟩ := h; (hc.isOpenEmbedding_comp hg).isCollared

/-- Reparametrizing the domain by a homeomorphism preserves the existence of a collar. -/
theorem comp_homeomorph (h : IsCollared f) (e : P ≃ₜ N) : IsCollared (f ∘ e) :=
  h.comp_isOpenEmbedding e.isOpenEmbedding

end IsCollared

end TauCeti
