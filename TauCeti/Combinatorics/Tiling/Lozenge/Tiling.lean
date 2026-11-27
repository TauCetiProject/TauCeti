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
  `TauCeti.IsTiling.card_filter_isWhite_eq_card_filter_isWhite_eq_false`: a finite tileable region
  has `|R| = 2 |M|` and as many white as black faces.
* `TauCeti.IsFreeTiling.inter_regionEdges`, `TauCeti.IsTiling.isFreeTiling_inter_regionEdges`: the
  restriction of a free tiling of `S ⊇ R`, in particular of a plane tiling, to the edges of `R` is
  a free tiling of `R`.
* `TauCeti.IsTiling.sdiff_union`: replacing a tiling of a subregion by another tiling of it.
* `TauCeti.IsFreeTiling.isTiling_iff`: a free tiling is a tiling exactly when it contains no
  boundary edge.
* `TauCeti.isTiling_vadd_iff`, `TauCeti.isTiling_rot_iff`, `TauCeti.isFreeTiling_vadd_iff`,
  `TauCeti.isFreeTiling_rot_iff`: translations and `ρ` map tilings and free tilings to those of the
  image region.
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

/-! ### Replacing a tiling of a subregion -/

section Replace

variable {A B : Set TriEdge}

/-- If `M` contains at most one edge of each face of `S` and contains a tiling `A` of `S`, then it
contains no edge of a tiling `B` of `S` disjoint from `A`. -/
theorem disjoint_of_isTiling_of_subset {S : Set TriFace} (hA : IsTiling S A) (hB : IsTiling S B)
    (hAB : Disjoint A B) (hM : ∀ f ∈ S, ∀ e ∈ M, ∀ e' ∈ M, e ∈ f.edges → e' ∈ f.edges → e = e')
    (hAM : A ⊆ M) : Disjoint M B := by
  rw [Set.disjoint_right]
  intro b hb hbM
  have hf : b.whiteFace ∈ S := hB.whiteFace_mem hb
  obtain ⟨a, ⟨ha, haf⟩, -⟩ := hA.existsUnique hf
  have := hM _ hf a (hAM ha) b hbM haf b.mem_whiteFace_edges
  exact Set.disjoint_left.1 hAB ha (this ▸ hb)

/-- Replacing a tiling `A` of a subregion `S` by another tiling `B` of `S`, inside a tiling `M` of
`R` containing `A`, gives a tiling of `R`. -/
theorem IsTiling.sdiff_union {S : Set TriFace} (hM : IsTiling R M) (hA : IsTiling S A)
    (hB : IsTiling S B) (hAM : A ⊆ M) : IsTiling R (M \ A ∪ B) := by
  have hSR : S ⊆ R := fun f hf => by
    obtain ⟨a, ⟨ha, haf⟩, -⟩ := hA.existsUnique hf
    exact hM.mem_of_mem_edges (hAM ha) haf
  refine isTiling_def.2 ⟨?_, fun f hf => ?_⟩
  · rintro e (⟨heM, -⟩ | heB) f hef
    · exact hM.mem_of_mem_edges heM hef
    · exact hSR (hB.mem_of_mem_edges heB hef)
  by_cases hfS : f ∈ S
  · obtain ⟨b, ⟨hb, hbf⟩, hbu⟩ := hB.existsUnique hfS
    refine ⟨b, ⟨Or.inr hb, hbf⟩, fun e ⟨he, hef⟩ => ?_⟩
    rcases he with ⟨heM, heA⟩ | heB
    · obtain ⟨a, ⟨ha, haf⟩, -⟩ := hA.existsUnique hfS
      exact absurd (hM.eq_of_mem_edges heM (hAM ha) hef haf ▸ ha) heA
    · exact hbu e ⟨heB, hef⟩
  · have hAf : ∀ e ∈ A, e ∉ f.edges := fun e he hef => hfS (hA.mem_of_mem_edges he hef)
    have hBf : ∀ e ∈ B, e ∉ f.edges := fun e he hef => hfS (hB.mem_of_mem_edges he hef)
    obtain ⟨e, ⟨heM, hef⟩, heu⟩ := hM.existsUnique hf
    refine ⟨e, ⟨Or.inl ⟨heM, fun heA => hAf e heA hef⟩, hef⟩, fun e' ⟨he', he'f⟩ => ?_⟩
    rcases he' with ⟨he'M, -⟩ | he'B
    · exact heu e' ⟨he'M, he'f⟩
    · exact absurd he'f (hBf e' he'B)

end Replace

/-- A plane free tiling is a plane tiling: every edge is an edge of some face. -/
theorem isFreeTiling_univ_iff :
    IsFreeTiling Set.univ M ↔ ∀ f : TriFace, ∃! e, e ∈ M ∧ e ∈ f.edges :=
  ⟨fun h f => h.2 f (Set.mem_univ f), fun h =>
    ⟨fun e _ => mem_regionEdges.2 ⟨_, Set.mem_univ _, e.mem_whiteFace_edges⟩, fun f _ => h f⟩⟩

namespace IsFreeTiling

theorem subset_regionEdges (h : IsFreeTiling R M) : M ⊆ regionEdges R := h.1

theorem existsUnique (h : IsFreeTiling R M) (hf : f ∈ R) : ∃! e, e ∈ M ∧ e ∈ f.edges := h.2 f hf

/-- Two edges of a free tiling lying in a common face of the region are equal. -/
theorem eq_of_mem_edges (h : IsFreeTiling R M) (hf : f ∈ R) {e e' : TriEdge} (he : e ∈ M)
    (he' : e' ∈ M) (hef : e ∈ f.edges) (he'f : e' ∈ f.edges) : e = e' :=
  (h.2 f hf).unique ⟨he, hef⟩ ⟨he', he'f⟩

/-- A free tiling of a finite region is finite. -/
theorem finite {R : Finset TriFace} (h : IsFreeTiling (R : Set TriFace) M) : M.Finite :=
  (finite_regionEdges R).subset h.1

end IsFreeTiling

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
  h.isFreeTiling.finite

/-- In a finite tileable region, each tiling has one lozenge per white face and one per black
face: the faces of colour `c` are in bijection with the edges of the tiling. -/
theorem card_filter_isWhite_eq_ncard (h : IsTiling (R : Set TriFace) M) (c : Bool) :
    (R.filter fun f => f.isWhite = c).card = M.ncard := by
  classical
  have hF : ∀ e : TriEdge, e ∈ (if c then e.whiteFace else e.blackFace).edges := by
    intro e
    cases c <;> simp
  have hR : R.filter (fun f => f.isWhite = c) =
      h.finite.toFinset.image fun e => if c then e.whiteFace else e.blackFace := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image, Set.Finite.mem_toFinset]
    refine ⟨fun ⟨hf, hw⟩ => ?_, ?_⟩
    · obtain ⟨e, ⟨he, hfe⟩, -⟩ := h.2 f hf
      refine ⟨e, he, ?_⟩
      cases c
      exacts [(TriEdge.eq_blackFace_of_mem_edges hfe hw).symm,
        (TriEdge.eq_whiteFace_of_mem_edges hfe hw).symm]
    · rintro ⟨e, he, rfl⟩
      exact ⟨h.mem_of_mem_edges he (hF e), by cases c <;> simp⟩
  rw [hR, Finset.card_image_of_injOn, Set.ncard_eq_toFinset_card M h.finite]
  intro e he e' he' hee
  exact h.eq_of_mem_edges (h.finite.mem_toFinset.1 he) (h.finite.mem_toFinset.1 he') (hF e)
    (by simp only at hee; exact hee ▸ hF e')

/-- A finite tileable region has twice as many faces as its tilings have lozenges. -/
theorem card_eq_two_mul_ncard (h : IsTiling (R : Set TriFace) M) : R.card = 2 * M.ncard := by
  rw [← Finset.card_filter_add_card_filter_not (s := R) (fun f => f.isWhite = true),
    h.card_filter_isWhite_eq_ncard true]
  simp only [Bool.not_eq_true]
  rw [h.card_filter_isWhite_eq_ncard false, two_mul]

/-- A finite tileable region has as many white as black faces. -/
theorem card_filter_isWhite_eq_card_filter_isWhite_eq_false (h : IsTiling (R : Set TriFace) M) :
    (R.filter fun f => f.isWhite = true).card = (R.filter fun f => f.isWhite = false).card := by
  rw [h.card_filter_isWhite_eq_ncard true, h.card_filter_isWhite_eq_ncard false]

end IsTiling

/-! ### Free tilings -/

/-- The restriction of a free tiling of `S` to the edges of a subregion `R` is a free tiling of
`R`. -/
theorem IsFreeTiling.inter_regionEdges {S : Set TriFace} (h : IsFreeTiling S M) (hRS : R ⊆ S) :
    IsFreeTiling R (M ∩ regionEdges R) := by
  refine ⟨Set.inter_subset_right, fun f hf => ?_⟩
  obtain ⟨e, ⟨he, hfe⟩, huniq⟩ := h.2 f (hRS hf)
  exact ⟨e, ⟨⟨he, mem_regionEdges.2 ⟨f, hf, hfe⟩⟩, hfe⟩,
    fun e' he' => huniq e' ⟨he'.1.1, he'.2⟩⟩

/-- The restriction of a plane tiling to the edges of a region is a free tiling of the region. -/
theorem IsTiling.isFreeTiling_inter_regionEdges (h : IsTiling Set.univ M) (R : Set TriFace) :
    IsFreeTiling R (M ∩ regionEdges R) :=
  h.isFreeTiling.inter_regionEdges (Set.subset_univ R)

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

/- Tilings and free tilings are transported along permutations `φ` of the faces and `ψ` of the
edges compatible with incidence. The translation lemmas instantiate these with
`AddAction.toPerm w`, whose image of a set is `w +ᵥ ·` of it by definition. -/

/-- Both tiling conditions, `M ⊆ E R` and the unique edge of `M` in each face of `R`, transported
along `φ` and `ψ`, for an edge set `E R` of the region compatible with them. -/
private theorem image_iff (φ : Equiv.Perm TriFace) (ψ : Equiv.Perm TriEdge)
    (hψ : ∀ e f, ψ e ∈ (φ f).edges ↔ e ∈ f.edges) (E : Set TriFace → Set TriEdge)
    (hE : E (φ '' R) = ψ '' E R) :
    (ψ '' M ⊆ E (φ '' R) ∧ ∀ f ∈ φ '' R, ∃! e, e ∈ ψ '' M ∧ e ∈ f.edges) ↔
      (M ⊆ E R ∧ ∀ f ∈ R, ∃! e, e ∈ M ∧ e ∈ f.edges) := by
  rw [hE, Set.image_subset_image_iff ψ.injective, Set.forall_mem_image]
  refine and_congr_right fun _ => forall₂_congr fun f _ =>
    (ψ.existsUnique_congr fun {e} => ?_).symm
  rw [ψ.injective.mem_set_image, hψ]

/-- Translations map tilings of `R` to tilings of the translated region. -/
@[simp] theorem isTiling_vadd_iff (w : ℤ × ℤ) : IsTiling (w +ᵥ R) (w +ᵥ M) ↔ IsTiling R M := by
  rw [isTiling_iff_subset_interiorEdges, isTiling_iff_subset_interiorEdges]
  exact image_iff (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) interiorEdges (interiorEdges_vadd w R)

/-- The rotation `ρ` maps tilings of `R` to tilings of the rotated region. -/
@[simp] theorem isTiling_rot_iff :
    IsTiling (TriFace.rot '' R) (TriEdge.rot '' M) ↔ IsTiling R M := by
  rw [isTiling_iff_subset_interiorEdges, isTiling_iff_subset_interiorEdges]
  exact image_iff _ _ (fun _ _ => TriEdge.rot_mem_edges_rot) interiorEdges (interiorEdges_rot R)

/-- Translations map free tilings of `R` to free tilings of the translated region. -/
@[simp] theorem isFreeTiling_vadd_iff (w : ℤ × ℤ) :
    IsFreeTiling (w +ᵥ R) (w +ᵥ M) ↔ IsFreeTiling R M :=
  image_iff (AddAction.toPerm w) (AddAction.toPerm w)
    (fun _ _ => TriEdge.vadd_mem_edges_vadd) regionEdges (regionEdges_vadd w R)

/-- The rotation `ρ` maps free tilings of `R` to free tilings of the rotated region. -/
@[simp] theorem isFreeTiling_rot_iff :
    IsFreeTiling (TriFace.rot '' R) (TriEdge.rot '' M) ↔ IsFreeTiling R M :=
  image_iff _ _ (fun _ _ => TriEdge.rot_mem_edges_rot) regionEdges (regionEdges_rot R)

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
  ext f
  simp [toPlacedTile_def, DiscreteTiling.PlacedTile.coe_mk_coe, Set.mem_vadd_set_iff_neg_vadd_mem,
    Finset.mem_neg_vadd_finset_iff]

@[simp] theorem mem_toPlacedTile {e : TriEdge} {f : TriFace} :
    f ∈ e.toPlacedTile ↔ e ∈ f.edges := by
  rw [← DiscreteTiling.PlacedTile.mem_coe, coe_toPlacedTile, Finset.mem_coe, mem_faces]

@[simp] theorem toPlacedTile_vadd (w : ℤ × ℤ) (e : TriEdge) :
    (w +ᵥ e).toPlacedTile = Multiplicative.ofAdd w • e.toPlacedTile := by
  -- Destructuring `e` makes the index `(w +ᵥ e).k` reduce to `k`, on which the coset depends.
  obtain ⟨v, k⟩ := e
  simp [toPlacedTile_def, ofAdd_add]

theorem toPlacedTile_bijective : Function.Bijective toPlacedTile := by
  refine ⟨fun e e' h => faces_injective (Finset.coe_injective ?_), fun pt => ?_⟩
  · rw [← coe_toPlacedTile, h, coe_toPlacedTile]
  · induction pt using DiscreteTiling.PlacedTile.induction_on with
    | h k g => exact ⟨⟨Multiplicative.toAdd g, k⟩, by simp [toPlacedTile_def]⟩

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
