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
face identity.  The codimension-one cells are classified by the vertex deleted from the original
face.  Finally, a cell whose vertices all precede a vertex `v`, and to which `v` can be adjoined,
has a cone with `v` as its last vertex; its faces are the original cell and the cones on the
faces of the original cell.

## Main definitions

* `AbstractSimplicialComplex.RealizationCell`: the faces with a prescribed dimension.
* `AbstractSimplicialComplex.RealizationCell.vertexEmbedding`: the increasing vertex enumeration.
* `AbstractSimplicialComplex.RealizationCell.face`: deletion of one enumerated vertex.
* `AbstractSimplicialComplex.RealizationCell.vertex`: the `0`-cell of a vertex.
* `AbstractSimplicialComplex.RealizationCell.cone`: the cone on a cell with a later vertex.
-/

public section

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The `n`-dimensional cells of `K`: its faces with `n + 1` vertices. -/
abbrev RealizationCell (K : AbstractSimplicialComplex ι) (n : ℕ) :=
  {σ : TauCeti.SetLike.Face K // σ.1.card = n + 1}

namespace RealizationCell

section Vertex

variable (K : AbstractSimplicialComplex ι)

/-- The `0`-cell of `K` whose only vertex is `v`. -/
def vertex (v : ι) : RealizationCell K 0 :=
  ⟨⟨{v}, K.singleton_mem v⟩, Finset.card_singleton v⟩

/-- The vertex set of the `0`-cell of a vertex is that vertex. -/
@[simp]
theorem vertex_val (v : ι) : (vertex K v).1.1 = {v} :=
  (rfl)

end Vertex

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

/-- The only enumerated vertex of the `0`-cell of a vertex is that vertex. -/
@[simp]
theorem vertexEmbedding_vertex (v : ι) (i : Fin 1) : (vertex K v).vertexEmbedding i = v :=
  Finset.mem_singleton.mp ((vertex K v).vertexEmbedding_mem i)

/-- Every `0`-cell is the `0`-cell of its only vertex. -/
theorem eq_vertex (c : RealizationCell K 0) : c = vertex K (c.vertexEmbedding 0) :=
  Subtype.ext (Subtype.ext (Finset.eq_singleton_iff_unique_mem.mpr ⟨c.vertexEmbedding_mem 0,
    fun _ hw ↦ Finset.card_le_one.mp c.2.le _ hw _ (c.vertexEmbedding_mem 0)⟩))

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

/-- The codimension-one faces obtained by deleting vertices are pairwise distinct. -/
theorem face_injective (c : RealizationCell K (n + 1)) : Function.Injective c.face := by
  intro i j hij
  have herase : c.1.1.erase (c.vertexEmbedding i) =
      c.1.1.erase (c.vertexEmbedding j) := by
    simpa only [face_val] using congrArg (fun d => d.1.1) hij
  exact c.vertexEmbedding.injective
    ((Finset.erase_inj c.1.1 (c.vertexEmbedding_mem i)).mp herase)

/-- A finite set lies in a codimension-one face exactly when it is a proper subset of the
original face. -/
theorem exists_subset_face_iff_ssubset (c : RealizationCell K (n + 1)) (s : Finset ι) :
    (∃ j, s ⊆ (c.face j).1.1) ↔ s ⊂ c.1.1 := by
  constructor
  · rintro ⟨j, hs⟩
    exact hs.trans_lt (Finset.erase_ssubset (c.vertexEmbedding_mem j))
  · intro hs
    obtain ⟨a, ha, hsa⟩ := Finset.ssubset_iff_exists_subset_erase.mp hs
    have ha' : a ∈ Finset.univ.image c.vertexEmbedding := by
      simpa only [image_vertexEmbedding] using ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha'
    exact ⟨j, by simpa only [face_val] using hsa⟩

/-- The codimension-one cells of a cell are exactly its subfaces of the appropriate dimension. -/
theorem exists_face_eq_iff_subset (c : RealizationCell K (n + 1)) (d : RealizationCell K n) :
    (∃ j, c.face j = d) ↔ d.1.1 ⊆ c.1.1 := by
  constructor
  · rintro ⟨j, rfl⟩
    exact Finset.erase_subset _ _
  · intro hdc
    have hdc' : d.1.1 ⊂ c.1.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hdc, by
        intro h
        have hcard := congrArg Finset.card h
        simp only [d.2, c.2] at hcard
        omega⟩
    obtain ⟨j, hdj⟩ := (c.exists_subset_face_iff_ssubset d.1.1).mpr hdc'
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    exact (Finset.eq_of_subset_of_card_le hdj (by
      simp only [d.2, (c.face j).2]
      omega)).symm

/-- The increasing enumeration of a deleted-vertex face skips exactly the deleted position. -/
@[simp]
theorem vertexEmbedding_face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    ⇑(c.face j).vertexEmbedding = c.vertexEmbedding ∘ j.succAbove := by
  symm
  apply Finset.orderEmbOfFin_unique (c.face j).2
  · intro i
    rw [face_val, Finset.mem_erase]
    exact ⟨fun h ↦ j.succAbove_ne i (c.vertexEmbedding.injective h),
      c.vertexEmbedding_mem (j.succAbove i)⟩
  · exact c.strictMono_vertexEmbedding.comp (Fin.strictMono_succAbove j)

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
  exact Finset.erase_right_comm

section Cone

/-- The cone on a cell `c` with a vertex `v` larger than all vertices of `c`, when adjoining `v`
to `c` gives a face: the cell with vertex set `c ∪ {v}`. -/
def cone (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) : RealizationCell K (n + 1) :=
  ⟨⟨insert v c.1.1, hK⟩, by
    rw [Finset.card_insert_of_notMem fun hv ↦ (hlt v hv).false, c.2]⟩

/-- The vertex set of a cone is obtained by adjoining the cone vertex. -/
@[simp]
theorem cone_val (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) : (c.cone v hlt hK).1.1 = insert v c.1.1 :=
  (rfl)

/-- The increasing enumeration of a cone enumerates the original cell and then the cone
vertex. -/
theorem vertexEmbedding_cone (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) :
    ⇑(c.cone v hlt hK).vertexEmbedding = Fin.lastCases v c.vertexEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique (c.cone v hlt hK).2
  · intro i
    rw [cone_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact hlt _ (c.vertexEmbedding_mem (Fin.last n))
    | cast i =>
      rw [Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      exact c.strictMono_vertexEmbedding Fin.castSucc_lt_succ

/-- Deleting the cone vertex from a cone recovers the original cell. -/
@[simp]
theorem face_cone_last (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) : (c.cone v hlt hK).face (Fin.last (n + 1)) = c := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [face_val, congrFun (vertexEmbedding_cone c v hlt hK), Fin.lastCases_last, cone_val,
    Finset.erase_insert fun hv ↦ (hlt v hv).false]

/-- The vertex set of a deleted-vertex face of a cell lies in the original cell. -/
theorem face_val_subset (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).1.1 ⊆ c.1.1 := by
  rw [face_val]
  exact Finset.erase_subset _ _

/-- Adjoining `v` to a deleted-vertex face of a cell gives a face of `K` when adjoining it to the
cell does. -/
theorem insert_face_mem (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) {v : ι}
    (hK : insert v c.1.1 ∈ K) : insert v (c.face j).1.1 ∈ K :=
  K.isRelLowerSet_faces.mem_of_le hK (Finset.insert_subset_insert v (c.face_val_subset j))
    (Finset.insert_nonempty _ _)

/-- Deleting a vertex of the original cell from a cone gives the cone on the corresponding
face. -/
@[simp]
theorem face_cone_castSucc (c : RealizationCell K (n + 1)) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) (j : Fin (n + 2)) :
    (c.cone v hlt hK).face j.castSucc =
      (c.face j).cone v (fun w hw ↦ hlt w (c.face_val_subset j hw)) (c.insert_face_mem j hK) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [face_val, congrFun (vertexEmbedding_cone c v hlt hK), Fin.lastCases_castSucc, cone_val,
    cone_val, face_val, Finset.erase_insert_of_ne (hlt _ (c.vertexEmbedding_mem j)).ne']

/-- Deleting the first vertex of the cone on a `0`-cell leaves the cone vertex. -/
@[simp]
theorem face_cone_zero (c : RealizationCell K 0) (v : ι) (hlt : ∀ w ∈ c.1.1, w < v)
    (hK : insert v c.1.1 ∈ K) : (c.cone v hlt hK).face 0 = vertex K v := by
  refine Subtype.ext (Subtype.ext ?_)
  have hc : c.1.1 = {c.vertexEmbedding 0} := congrArg (fun d ↦ d.1.1) c.eq_vertex
  rw [face_val, ← Fin.castSucc_zero, congrFun (vertexEmbedding_cone c v hlt hK),
    Fin.lastCases_castSucc, cone_val, hc]
  simp [Finset.erase_insert_of_ne (hlt _ (c.vertexEmbedding_mem 0)).ne']

end Cone

end RealizationCell

end AbstractSimplicialComplex
