/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.Data.Set.Card

/-!
# Lozenge tilings of regions

A lozenge is the union of the two faces containing an edge, its inner edge; its type is the
direction of the inner edge. A tiling of a region `R` is a set `M` of edges, each with both of its
faces in `R`, such that every face of `R` contains exactly one edge of `M`: the lozenges of the
edges of `M` partition `R`. A free tiling only asks the edges of `M` to be edges of `R`; its
lozenges may stick out of `R` by one face. A plane tiling is a tiling of `Set.univ`.

## Main definitions

* `TauCeti.IsTiling`: `M` is a tiling of the region `R`.
* `TauCeti.IsFreeTiling`: `M` is a free tiling of `R`.
* `TauCeti.lozengeProtoset`: the three lozenges at the origin, as a Mathlib protoset under the
  translations `Multiplicative (ℤ × ℤ)`.
* `TauCeti.TriEdge.toPlacedTile`, `TauCeti.TriEdge.equivPlacedTile`: the bijection from edges onto
  the placed tiles of `lozengeProtoset`.

## Main statements

* `TauCeti.isTiling_iff_lozenges`: `M` is a tiling of `R` exactly when the lozenges of its edges
  lie in `R`, are pairwise disjoint and cover `R`.
* `TauCeti.IsTiling.card_eq_two_mul_ncard`, `TauCeti.IsTiling.card_filter_isWhite_eq_ncard`,
  `TauCeti.IsTiling.card_filter_isWhite_eq_card_filter_not`: a finite tileable region has
  `|R| = 2 |M|` and as many white as black faces.
* `TauCeti.IsTiling.isFreeTiling_inter_regionEdges`: the restriction of a plane tiling to the
  edges of `R` is a free tiling of `R`.
* `TauCeti.IsFreeTiling.isTiling_iff`: a free tiling is a tiling exactly when it contains no
  boundary edge.
* `TauCeti.isTiling_vadd_iff`, `TauCeti.isTiling_rot_iff`: translations and `ρ` map tilings to
  tilings of the image region.
* `TauCeti.isTiling_iff_placedTile`: tilings are the families of placed tiles of
  `lozengeProtoset` lying in `R`, pairwise disjoint and covering `R`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

open Pointwise

namespace TauCeti

/-- `IsTiling R M`: every edge of `M` has both of its faces in the region `R`, and every face of
`R` contains exactly one edge of `M`. A plane tiling is a tiling of `Set.univ`. -/
def IsTiling (R : Set TriFace) (M : Set TriEdge) : Prop :=
  (∀ e ∈ M, ∀ f : TriFace, e ∈ f.edges → f ∈ R) ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges

/-- `IsFreeTiling R M`: every edge of `M` is an edge of a face of `R`, and every face of `R`
contains exactly one edge of `M`. -/
def IsFreeTiling (R : Set TriFace) (M : Set TriEdge) : Prop :=
  M ⊆ regionEdges R ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges

variable {R : Set TriFace} {M : Set TriEdge} {e : TriEdge} {f : TriFace}

theorem isTiling_def : IsTiling R M ↔
    (∀ e ∈ M, ∀ f : TriFace, e ∈ f.edges → f ∈ R) ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges := Iff.rfl

theorem isFreeTiling_def :
    IsFreeTiling R M ↔ M ⊆ regionEdges R ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges := Iff.rfl

theorem isTiling_iff_subset_interiorEdges :
    IsTiling R M ↔ M ⊆ interiorEdges R ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges := by
  simp only [IsTiling, Set.subset_def, mem_interiorEdges]

/-- A plane tiling is a set of edges meeting every face in exactly one edge. -/
theorem isTiling_univ_iff :
    IsTiling Set.univ M ↔ ∀ f : TriFace, ∃! e, e ∈ M ∧ e ∈ f.edges := by
  simp [IsTiling]

namespace IsTiling

theorem subset_interiorEdges (h : IsTiling R M) : M ⊆ interiorEdges R :=
  fun e he => mem_interiorEdges.2 (h.1 e he)

theorem existsUnique (h : IsTiling R M) (hf : f ∈ R) : ∃! e, e ∈ M ∧ e ∈ f.edges := h.2 f hf

/-- Both faces of an edge of a tiling lie in the region. -/
theorem mem_of_mem_edges (h : IsTiling R M) (he : e ∈ M) (hf : e ∈ f.edges) : f ∈ R :=
  h.1 e he f hf

theorem whiteFace_mem (h : IsTiling R M) (he : e ∈ M) : e.whiteFace ∈ R :=
  h.1 e he _ e.mem_whiteFace_edges

theorem blackFace_mem (h : IsTiling R M) (he : e ∈ M) : e.blackFace ∈ R :=
  h.1 e he _ e.mem_blackFace_edges

/-- Every tiling is a free tiling. -/
theorem isFreeTiling (h : IsTiling R M) : IsFreeTiling R M :=
  ⟨h.subset_interiorEdges.trans interiorEdges_subset_regionEdges, h.2⟩

/-- Two edges of a tiling lying in a common face are equal. -/
theorem eq_of_mem_edges (h : IsTiling R M) {e e' : TriEdge} (he : e ∈ M) (he' : e' ∈ M)
    (hef : e ∈ f.edges) (he'f : e' ∈ f.edges) : e = e' :=
  (h.2 f (h.1 e he f hef)).unique ⟨he, hef⟩ ⟨he', he'f⟩

end IsTiling

/-- **Tilings partition the region.** `M` is a tiling of `R` exactly when the lozenges of the
edges of `M` lie in `R`, are pairwise disjoint and cover `R`. -/
theorem isTiling_iff_lozenges :
    IsTiling R M ↔ (∀ e ∈ M, (e.faces : Set TriFace) ⊆ R) ∧
      M.PairwiseDisjoint (fun e => (e.faces : Set TriFace)) ∧
      R ⊆ ⋃ e ∈ M, (e.faces : Set TriFace) := by
  constructor
  · intro h
    refine ⟨fun e he f hf => h.1 e he f (TriEdge.mem_faces.1 hf),
      fun e he e' he' hne => Set.disjoint_left.2 fun f hf hf' => hne ?_, fun f hf => ?_⟩
    · exact h.eq_of_mem_edges he he' (TriEdge.mem_faces.1 hf) (TriEdge.mem_faces.1 hf')
    · obtain ⟨e, ⟨he, hef⟩, -⟩ := h.2 f hf
      exact Set.mem_biUnion he (TriEdge.mem_faces.2 hef)
  · rintro ⟨hsub, hdisj, hcov⟩
    refine ⟨fun e he f hf => hsub e he (TriEdge.mem_faces.2 hf), fun f hf => ?_⟩
    obtain ⟨e, he, hfe⟩ := Set.mem_iUnion₂.1 (hcov hf)
    refine ⟨e, ⟨he, TriEdge.mem_faces.1 hfe⟩, fun e' ⟨he', hfe'⟩ => ?_⟩
    by_contra hne
    exact Set.disjoint_left.1 (hdisj he' he hne) (TriEdge.mem_faces.2 hfe') hfe

/-! ### Finite tileable regions -/

namespace IsTiling

variable {R : Finset TriFace}

theorem finite (h : IsTiling (R : Set TriFace) M) : M.Finite :=
  (R.biUnion TriFace.edges).finite_toSet.subset fun e he => by
    simpa using ⟨e.whiteFace, h.whiteFace_mem he, e.mem_whiteFace_edges⟩

/-- A finite tileable region has twice as many faces as its tilings have lozenges. -/
theorem card_eq_two_mul_ncard (h : IsTiling (R : Set TriFace) M) : R.card = 2 * M.ncard := by
  classical
  have hR : R = h.finite.toFinset.biUnion TriEdge.faces := by
    ext f
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, TriEdge.mem_faces]
    refine ⟨fun hf => ?_, fun ⟨e, he, hfe⟩ => h.1 e he f hfe⟩
    obtain ⟨e, ⟨he, hfe⟩, -⟩ := h.2 f hf
    exact ⟨e, he, hfe⟩
  have hdisj := (isTiling_iff_lozenges.1 h).2.1
  rw [hR, Finset.card_biUnion fun e he e' he' hne => Finset.disjoint_coe.1
    (hdisj (h.finite.mem_toFinset.1 he) (h.finite.mem_toFinset.1 he') hne),
    Finset.sum_const_nat fun e _ => e.card_faces, Set.ncard_eq_toFinset_card M h.finite, mul_comm]

/-- In a finite tileable region, each tiling has one lozenge per white face. -/
theorem card_filter_isWhite_eq_ncard (h : IsTiling (R : Set TriFace) M) :
    (R.filter fun f => f.isWhite = true).card = M.ncard := by
  classical
  have hR : R.filter (fun f => f.isWhite = true) = h.finite.toFinset.image TriEdge.whiteFace := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset]
    refine ⟨fun ⟨hf, hw⟩ => ?_, ?_⟩
    · obtain ⟨e, ⟨he, hfe⟩, -⟩ := h.2 f hf
      exact ⟨e, he, (TriEdge.eq_whiteFace_of_mem_edges hfe hw).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h.whiteFace_mem he, e.whiteFace_isWhite⟩
  rw [hR, Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card M h.finite]
  intro e he e' he' hee
  exact h.eq_of_mem_edges (h.finite.mem_toFinset.1 he) (h.finite.mem_toFinset.1 he')
    e.mem_whiteFace_edges (hee ▸ e'.mem_whiteFace_edges)

/-- In a finite tileable region, each tiling has one lozenge per black face. -/
theorem card_filter_isWhite_eq_false_eq_ncard (h : IsTiling (R : Set TriFace) M) :
    (R.filter fun f => f.isWhite = false).card = M.ncard := by
  classical
  have hR : R.filter (fun f => f.isWhite = false) = h.finite.toFinset.image TriEdge.blackFace := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset]
    refine ⟨fun ⟨hf, hw⟩ => ?_, ?_⟩
    · obtain ⟨e, ⟨he, hfe⟩, -⟩ := h.2 f hf
      exact ⟨e, he, (TriEdge.eq_blackFace_of_mem_edges hfe hw).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h.blackFace_mem he, e.blackFace_isWhite⟩
  rw [hR, Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card M h.finite]
  intro e he e' he' hee
  exact h.eq_of_mem_edges (h.finite.mem_toFinset.1 he) (h.finite.mem_toFinset.1 he')
    e.mem_blackFace_edges (hee ▸ e'.mem_blackFace_edges)

/-- A finite tileable region has as many white as black faces. -/
theorem card_filter_isWhite_eq_card_filter_not (h : IsTiling (R : Set TriFace) M) :
    (R.filter fun f => f.isWhite = true).card = (R.filter fun f => f.isWhite = false).card := by
  rw [h.card_filter_isWhite_eq_ncard, h.card_filter_isWhite_eq_false_eq_ncard]

end IsTiling

/-! ### Free tilings -/

/-- The restriction of a plane tiling to the edges of a region is a free tiling of the region. -/
theorem IsTiling.isFreeTiling_inter_regionEdges (h : IsTiling Set.univ M) (R : Set TriFace) :
    IsFreeTiling R (M ∩ regionEdges R) := by
  refine ⟨Set.inter_subset_right, fun f hf => ?_⟩
  obtain ⟨e, ⟨he, hfe⟩, huniq⟩ := h.2 f (Set.mem_univ f)
  exact ⟨e, ⟨⟨he, mem_regionEdges.2 ⟨f, hf, hfe⟩⟩, hfe⟩,
    fun e' he' => huniq e' ⟨he'.1.1, he'.2⟩⟩

/-- A free tiling is a tiling exactly when it contains no boundary edge. -/
theorem IsFreeTiling.isTiling_iff (h : IsFreeTiling R M) :
    IsTiling R M ↔ Disjoint M (boundaryEdges R) := by
  refine ⟨fun ht => Set.disjoint_left.2 fun e he hb =>
    (notMem_boundaryEdges_iff (mem_boundaryEdges.1 hb).1).2 (ht.subset_interiorEdges he) hb,
    fun hd => ⟨?_, h.2⟩⟩
  intro e he
  exact mem_interiorEdges.1
    ((notMem_boundaryEdges_iff (h.1 he)).1 (Set.disjoint_left.1 hd he))

/-! ### Symmetries -/

private theorem isTiling_image (φ : Equiv.Perm TriFace) (ψ : Equiv.Perm TriEdge)
    (hψ : ∀ e f, ψ e ∈ (φ f).edges ↔ e ∈ f.edges) :
    IsTiling (φ '' R) (ψ '' M) ↔ IsTiling R M := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun e he f hf => ?_, fun f hf => ?_⟩
    · simpa [φ.injective.mem_set_image] using
        h₁ (ψ e) (Set.mem_image_of_mem ψ he) (φ f) ((hψ e f).2 hf)
    · refine (ψ.existsUnique_congr fun {e} => ?_).2 (h₂ (φ f) (Set.mem_image_of_mem φ hf))
      rw [ψ.injective.mem_set_image, hψ]
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩ g hg
      obtain ⟨f, rfl⟩ := φ.surjective g
      exact Set.mem_image_of_mem φ (h₁ e he f ((hψ e f).1 hg))
    · rintro _ ⟨f, hf, rfl⟩
      refine (ψ.existsUnique_congr fun {e} => ?_).1 (h₂ f hf)
      rw [ψ.injective.mem_set_image, hψ]

/-- Translations map tilings of `R` to tilings of the translated region. -/
@[simp] theorem isTiling_vadd_iff (w : ℤ × ℤ) : IsTiling (w +ᵥ R) (w +ᵥ M) ↔ IsTiling R M :=
  isTiling_image (AddAction.toPerm w) (AddAction.toPerm w) fun e f => by
    simp [Finset.vadd_mem_vadd_finset_iff]

/-- The rotation `ρ` maps tilings of `R` to tilings of the rotated region. -/
@[simp] theorem isTiling_rot_iff :
    IsTiling (TriFace.rot '' R) (TriEdge.rot '' M) ↔ IsTiling R M :=
  isTiling_image _ _ fun _ _ => TriEdge.rot_mem_edges_rot

/-! ### Lozenges as placed tiles -/

/-- The protoset of the three lozenges at the origin, `{W(0), B(-e₂)}`, `{W(-e₁), B(0)}` and
`{W(0), B(0)}` (the lozenges of the edges `(0,1)`, `(0,2)`, `(0,3)`), each with trivial
symmetries, under the translations `Multiplicative (ℤ × ℤ)` acting on faces. -/
def lozengeProtoset : DiscreteTiling.Protoset (Multiplicative (ℤ × ℤ)) TriFace (Fin 3) :=
  ⟨fun k => ⟨((⟨0, k⟩ : TriEdge).faces : Set TriFace), ⊥⟩⟩

@[simp] theorem lozengeProtoset_apply (k : Fin 3) :
    lozengeProtoset k = ⟨((⟨0, k⟩ : TriEdge).faces : Set TriFace), ⊥⟩ := (rfl)

namespace TriEdge

/-- An edge `(v, k)` as the placed tile of index `k` at `v` of `lozengeProtoset`. -/
def toPlacedTile (e : TriEdge) : DiscreteTiling.PlacedTile lozengeProtoset :=
  ⟨e.k, (Multiplicative.ofAdd e.v : Multiplicative (ℤ × ℤ))⟩

theorem toPlacedTile_def (e : TriEdge) :
    e.toPlacedTile = ⟨e.k, (Multiplicative.ofAdd e.v : Multiplicative (ℤ × ℤ))⟩ := (rfl)

/-- The placed tile of an edge is its lozenge. -/
@[simp] theorem coe_toPlacedTile (e : TriEdge) :
    (e.toPlacedTile : Set TriFace) = e.faces := by
  rw [toPlacedTile_def, DiscreteTiling.PlacedTile.coe_mk_coe, lozengeProtoset_apply,
    DiscreteTiling.Prototile.coe_mk]
  have he : e = e.v +ᵥ (⟨0, e.k⟩ : TriEdge) := by simp
  conv_rhs => rw [he, faces_vadd, Finset.coe_vadd_finset]
  rfl

/-- An edge is determined by its lozenge. -/
theorem faces_injective : Function.Injective faces := by
  intro e e' h
  have hw : e.whiteFace ∈ e'.faces := h ▸ mem_faces.2 e.mem_whiteFace_edges
  have hb : e.blackFace ∈ e'.faces := h ▸ mem_faces.2 e.mem_blackFace_edges
  rw [faces_def, Finset.mem_insert, Finset.mem_singleton] at hw hb
  refine eq_of_whiteFace_eq_of_blackFace_eq (hw.resolve_right fun h' => ?_)
    (hb.resolve_left fun h' => ?_)
  · simpa using congrArg TriFace.isWhite h'
  · simpa using congrArg TriFace.isWhite h'

theorem toPlacedTile_bijective : Function.Bijective toPlacedTile := by
  refine ⟨fun e e' h => faces_injective (Finset.coe_injective ?_), fun pt => ?_⟩
  · rw [← coe_toPlacedTile, h, coe_toPlacedTile]
  · induction pt using DiscreteTiling.PlacedTile.induction_on with
    | h k g => exact ⟨⟨Multiplicative.toAdd g, k⟩, rfl⟩

/-- **Lozenges are placed tiles.** The bijection from edges onto the placed tiles of
`lozengeProtoset`, sending `(v, k)` to the placed tile of index `k` at `v`. -/
noncomputable def equivPlacedTile : TriEdge ≃ DiscreteTiling.PlacedTile lozengeProtoset :=
  Equiv.ofBijective _ toPlacedTile_bijective

@[simp] theorem equivPlacedTile_apply (e : TriEdge) : equivPlacedTile e = e.toPlacedTile := (rfl)

end TriEdge

/-- A set `M` of edges is a tiling of `R` exactly when the placed tiles of its edges lie in `R`,
are pairwise disjoint and cover `R`. -/
theorem isTiling_iff_placedTile :
    IsTiling R M ↔ (∀ e ∈ M, (e.toPlacedTile : Set TriFace) ⊆ R) ∧
      M.PairwiseDisjoint (fun e => (e.toPlacedTile : Set TriFace)) ∧
      R ⊆ ⋃ e ∈ M, (e.toPlacedTile : Set TriFace) := by
  simp only [TriEdge.coe_toPlacedTile]
  exact isTiling_iff_lozenges

end TauCeti
