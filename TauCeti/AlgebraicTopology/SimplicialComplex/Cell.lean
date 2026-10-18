/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Cells of an abstract simplicial complex

An `n`-cell of an abstract simplicial complex is a face with `n + 1` vertices.  For a linearly
ordered vertex type, every cell has a canonical increasing enumeration.  This file also defines
the codimension-one cell obtained by deleting an enumerated vertex and proves the semisimplicial
face identity.

## Main definitions

* `AbstractSimplicialComplex.RealizationCell`: the faces with a prescribed dimension.
* `AbstractSimplicialComplex.RealizationCell.vertexEmbedding`: the increasing vertex enumeration.
* `AbstractSimplicialComplex.RealizationCell.face`: deletion of one enumerated vertex.
-/

public section

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The `n`-dimensional cells of `K`: its faces with `n + 1` vertices. -/
abbrev RealizationCell (K : AbstractSimplicialComplex ι) (n : ℕ) :=
  {σ : TauCeti.SetLike.Face K // σ.1.card = n + 1}

namespace RealizationCell

variable [LinearOrder ι]
variable {K : AbstractSimplicialComplex ι} {n : ℕ}

/-- The increasing enumeration of the vertices of a simplicial cell. -/
def vertexEmbedding (c : RealizationCell K n) : Fin (n + 1) ↪ ι :=
  (c.1.1.orderEmbOfFin c.2).toEmbedding

/-- The chosen vertex enumeration is strictly increasing. -/
theorem strictMono_vertexEmbedding (c : RealizationCell K n) : StrictMono c.vertexEmbedding :=
  (c.1.1.orderEmbOfFin c.2).strictMono

/-- Every enumerated vertex belongs to the cell's face. -/
@[simp]
theorem vertexEmbedding_mem (c : RealizationCell K n) (i : Fin (n + 1)) :
    c.vertexEmbedding i ∈ c.1.1 :=
  Finset.orderEmbOfFin_mem c.1.1 c.2 i

/-- The increasing enumeration has the cell's face as its image. -/
@[simp]
theorem image_vertexEmbedding (c : RealizationCell K n) :
    Finset.univ.image c.vertexEmbedding = c.1.1 :=
  Finset.image_orderEmbOfFin_univ c.1.1 c.2

/-- The codimension-one face obtained by deleting the `j`-th vertex in the increasing
enumeration of a simplicial cell. -/
def face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) : RealizationCell K n := by
  let σ := c.1.1.erase (c.vertexEmbedding j)
  have hcard : σ.card = n + 1 := by
    dsimp only [σ]
    rw [Finset.card_erase_of_mem (c.vertexEmbedding_mem j), c.2]
    omega
  refine ⟨⟨σ, K.isRelLowerSet_faces.mem_of_le c.1.2 (Finset.erase_subset _ _) ?_⟩, hcard⟩
  exact Finset.card_pos.mp (hcard.trans_gt (Nat.zero_lt_succ n))

/-- The finite set underlying a deleted-vertex face is obtained by erasing that vertex. -/
@[simp]
theorem face_val (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).1.1 = c.1.1.erase (c.vertexEmbedding j) :=
  (rfl)

/-- The increasing enumeration of a deleted-vertex face skips exactly the deleted position. -/
theorem vertexEmbedding_face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    ⇑(c.face j).vertexEmbedding = c.vertexEmbedding ∘ j.succAbove := by
  have hmono : StrictMono (c.vertexEmbedding ∘ j.succAbove) :=
    c.strictMono_vertexEmbedding.comp (Fin.strictMono_succAbove j)
  symm
  apply (hmono.range_inj_of_wellFoundedLT (c.face j).strictMono_vertexEmbedding).mp
  have himage : Finset.univ.image (c.vertexEmbedding ∘ j.succAbove) =
      Finset.univ.image (c.face j).vertexEmbedding := by
    rw [(c.face j).image_vertexEmbedding, face_val]
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
      Finset.mem_erase]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨fun h ↦ j.succAbove_ne i (c.vertexEmbedding.injective h),
        c.vertexEmbedding_mem (j.succAbove i)⟩
    · rintro ⟨hvj, hv⟩
      rw [← c.image_vertexEmbedding] at hv
      rcases Finset.mem_image.mp hv with ⟨i, -, rfl⟩
      rcases Fin.exists_succAbove_eq (fun h ↦ hvj (congrArg c.vertexEmbedding h)) with ⟨k, hk⟩
      exact ⟨k, congrArg c.vertexEmbedding hk⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    congrArg (fun s : Finset ι ↦ (s : Set ι)) himage

/-- Deleting two vertices is independent of their order, with the indices transported through
the first deletion.  This is the semisimplicial face identity. -/
theorem face_face (c : RealizationCell K (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (c.face i).face j = (c.face (i.succAbove j)).face (j.predAbove i) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [face_val, face_val, face_val, face_val]
  rw [congrFun (vertexEmbedding_face c i) j,
    congrFun (vertexEmbedding_face c (i.succAbove j)) (j.predAbove i)]
  simp only [Function.comp_apply, Fin.succAbove_succAbove_predAbove]
  ext v
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hvi, hvj, hv⟩
    exact ⟨hvj, hvi, hv⟩
  · rintro ⟨hvj, hvi, hv⟩
    exact ⟨hvi, hvj, hv⟩

end RealizationCell

end AbstractSimplicialComplex
