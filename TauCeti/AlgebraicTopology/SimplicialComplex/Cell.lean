/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Sort
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
import TauCeti.Data.Fin.Tuple.Sort

/-!
# Cells of an abstract simplicial complex

An `n`-cell of an abstract simplicial complex is a face with `n + 1` vertices.  For a linearly
ordered vertex type, every cell has a canonical increasing enumeration, and every tuple of
distinct vertices spanning a face permutes the increasing enumeration of that face's cell.  This
file also defines the codimension-one cell obtained by deleting an enumerated vertex and proves
the semisimplicial face identity.  The codimension-one cells are classified by the vertex deleted
from the original face.  Finally, a cell whose vertices all precede a vertex `v`, and to which `v`
can be adjoined, has a cone with `v` as its last vertex; its faces are the original cell and the
cones on the faces of the original cell. Conversely, every cell of positive dimension is the cone
on the face opposite its last vertex.

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
  {σ : TauCeti.SetLike.Face K // σ.val.card = n + 1}

namespace RealizationCell

/-- Cells with the same vertex set are equal. -/
theorem ext {K : AbstractSimplicialComplex ι} {n : ℕ} {c d : RealizationCell K n}
    (h : c.val.val = d.val.val) : c = d :=
  Subtype.ext (Subtype.ext h)

section Vertex

variable (K : AbstractSimplicialComplex ι)

/-- The `0`-cell of `K` whose only vertex is `v`. -/
def vertex (v : ι) : RealizationCell K 0 :=
  ⟨⟨{v}, K.singleton_mem v⟩, Finset.card_singleton v⟩

/-- The vertex set of the `0`-cell of a vertex is that vertex. -/
@[simp]
theorem vertex_val (v : ι) : (vertex K v).val.val = {v} :=
  (rfl)

end Vertex

variable [LinearOrder ι]
variable {K : AbstractSimplicialComplex ι} {n : ℕ}

/-- The increasing enumeration of the vertices of a simplicial cell. -/
def vertexEmbedding (c : RealizationCell K n) : Fin (n + 1) ↪ ι :=
  (c.val.val.orderEmbOfFin c.property).toEmbedding

/-- The chosen vertex enumeration is strictly increasing. -/
theorem strictMono_vertexEmbedding (c : RealizationCell K n) : StrictMono c.vertexEmbedding :=
  (c.val.val.orderEmbOfFin c.property).strictMono

/-- Every enumerated vertex belongs to the cell's face. -/
@[simp]
theorem vertexEmbedding_mem (c : RealizationCell K n) (i : Fin (n + 1)) :
    c.vertexEmbedding i ∈ c.val.val :=
  Finset.orderEmbOfFin_mem c.val.val c.property i

/-- The increasing enumeration has the cell's face as its image. -/
@[simp]
theorem image_vertexEmbedding (c : RealizationCell K n) :
    Finset.univ.image c.vertexEmbedding = c.val.val :=
  Finset.image_orderEmbOfFin_univ c.val.val c.property

/-- The last enumerated vertex of a cell is its largest vertex. -/
theorem vertexEmbedding_last (c : RealizationCell K n) :
    c.vertexEmbedding (Fin.last n) = c.val.val.max' ⟨_, c.vertexEmbedding_mem 0⟩ :=
  Finset.orderEmbOfFin_last c.property n.succ_pos

/-- The only enumerated vertex of the `0`-cell of a vertex is that vertex. -/
@[simp]
theorem vertexEmbedding_vertex (v : ι) (i : Fin 1) : (vertex K v).vertexEmbedding i = v :=
  Finset.mem_singleton.mp ((vertex K v).vertexEmbedding_mem i)

/-- Every `0`-cell is the `0`-cell of its only vertex. -/
theorem eq_vertex (c : RealizationCell K 0) : c = vertex K (c.vertexEmbedding 0) :=
  ext (Finset.eq_singleton_iff_unique_mem.mpr ⟨c.vertexEmbedding_mem 0,
    fun _ hw ↦ Finset.card_le_one.mp c.property.le _ hw _ (c.vertexEmbedding_mem 0)⟩)

/-- A tuple of distinct vertices spanning a face is a permuted increasing enumeration of the
cell it spans. -/
theorem exists_eq_vertexEmbedding_comp {g : Fin (n + 1) → ι} (hg : Function.Injective g)
    (hK : Finset.univ.image g ∈ K) :
    ∃ (c : RealizationCell K n) (σ : Equiv.Perm (Fin (n + 1))), g = c.vertexEmbedding ∘ σ := by
  let c : RealizationCell K n :=
    ⟨⟨Finset.univ.image g, hK⟩, by simp [Finset.card_image_of_injective _ hg]⟩
  have hsort : g ∘ Tuple.sort g = c.vertexEmbedding := Tuple.comp_sort_eq_orderEmbOfFin hg
  refine ⟨c, (Tuple.sort g).symm, ?_⟩
  rw [← hsort]
  ext i
  simp

/-- The codimension-one face obtained by deleting the `j`-th vertex in the increasing
enumeration of a simplicial cell. -/
def face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) : RealizationCell K n := by
  let σ := c.val.val.erase (c.vertexEmbedding j)
  have hcard : σ.card = n + 1 := by
    dsimp only [σ]
    rw [Finset.card_erase_of_mem (c.vertexEmbedding_mem j), c.property]
    omega
  refine ⟨⟨σ, K.isRelLowerSet_faces.mem_of_le c.val.property (Finset.erase_subset _ _) ?_⟩, hcard⟩
  exact Finset.card_pos.mp (hcard.trans_gt (Nat.zero_lt_succ n))

/-- The finite set underlying a deleted-vertex face is obtained by erasing that vertex. -/
@[simp]
theorem face_val (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).val.val = c.val.val.erase (c.vertexEmbedding j) :=
  (rfl)

/-- The codimension-one faces obtained by deleting vertices are pairwise distinct. -/
theorem face_injective (c : RealizationCell K (n + 1)) : Function.Injective c.face := by
  intro i j hij
  have herase : c.val.val.erase (c.vertexEmbedding i) =
      c.val.val.erase (c.vertexEmbedding j) := by
    simpa only [face_val] using congrArg (fun d => d.val.val) hij
  exact c.vertexEmbedding.injective
    ((Finset.erase_inj c.val.val (c.vertexEmbedding_mem i)).mp herase)

/-- A finite set lies in a codimension-one face exactly when it is a proper subset of the
original face. -/
theorem exists_subset_face_iff_ssubset (c : RealizationCell K (n + 1)) (s : Finset ι) :
    (∃ j, s ⊆ (c.face j).val.val) ↔ s ⊂ c.val.val := by
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
    (∃ j, c.face j = d) ↔ d.val.val ⊆ c.val.val := by
  constructor
  · rintro ⟨j, rfl⟩
    exact Finset.erase_subset _ _
  · intro hdc
    have hdc' : d.val.val ⊂ c.val.val := Finset.ssubset_iff_subset_ne.mpr ⟨hdc, by
        intro h
        have hcard := congrArg Finset.card h
        simp only [d.property, c.property] at hcard
        omega⟩
    obtain ⟨j, hdj⟩ := (c.exists_subset_face_iff_ssubset d.val.val).mpr hdc'
    refine ⟨j, ext ?_⟩
    exact (Finset.eq_of_subset_of_card_le hdj (by
      simp only [d.property, (c.face j).property]
      omega)).symm

/-- The increasing enumeration of a deleted-vertex face skips exactly the deleted position. -/
@[simp]
theorem vertexEmbedding_face (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    ⇑(c.face j).vertexEmbedding = c.vertexEmbedding ∘ j.succAbove := by
  symm
  apply Finset.orderEmbOfFin_unique (c.face j).property
  · intro i
    rw [face_val, Finset.mem_erase]
    exact ⟨fun h ↦ j.succAbove_ne i (c.vertexEmbedding.injective h),
      c.vertexEmbedding_mem (j.succAbove i)⟩
  · exact c.strictMono_vertexEmbedding.comp (Fin.strictMono_succAbove j)

/-- Deleting two vertices is independent of their order, with the indices transported through
the first deletion.  This is the semisimplicial face identity. -/
theorem face_face (c : RealizationCell K (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (c.face i).face j = (c.face (i.succAbove j)).face (j.predAbove i) := by
  apply ext
  rw [face_val, face_val, face_val, face_val]
  rw [congrFun (vertexEmbedding_face c i) j,
    congrFun (vertexEmbedding_face c (i.succAbove j)) (j.predAbove i)]
  simp only [Function.comp_apply, Fin.succAbove_succAbove_predAbove]
  exact Finset.erase_right_comm

section Cone

/-- The cone on a cell `c` with a vertex `v` larger than all vertices of `c`, when adjoining `v`
to `c` gives a face: the cell with vertex set `c ∪ {v}`. -/
def cone (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) : RealizationCell K (n + 1) :=
  ⟨⟨insert v c.val.val, hK⟩, by
    rw [Finset.card_insert_of_notMem fun hv ↦ (hlt v hv).false, c.property]⟩

/-- The vertex set of a cone is obtained by adjoining the cone vertex. -/
@[simp]
theorem cone_val (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) : (c.cone v hlt hK).val.val = insert v c.val.val :=
  (rfl)

/-- The increasing enumeration of a cone enumerates the original cell and then the cone
vertex. -/
theorem vertexEmbedding_cone (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) :
    ⇑(c.cone v hlt hK).vertexEmbedding = Fin.lastCases v c.vertexEmbedding := by
  symm
  apply Finset.orderEmbOfFin_unique (c.cone v hlt hK).property
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
theorem face_cone_last (c : RealizationCell K n) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) : (c.cone v hlt hK).face (Fin.last (n + 1)) = c := by
  refine ext ?_
  rw [face_val, congrFun (vertexEmbedding_cone c v hlt hK), Fin.lastCases_last, cone_val,
    Finset.erase_insert fun hv ↦ (hlt v hv).false]

/-- The vertex set of a deleted-vertex face of a cell lies in the original cell. -/
theorem face_val_subset (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).val.val ⊆ c.val.val := by
  rw [face_val]
  exact Finset.erase_subset _ _

/-- The vertex set of a deleted-vertex face of a cell is a proper subset of the original cell. -/
theorem face_val_ssubset (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    (c.face j).val.val ⊂ c.val.val := by
  rw [face_val]
  exact Finset.erase_ssubset (c.vertexEmbedding_mem j)

/-- Adjoining `v` to a deleted-vertex face of a cell gives a face of `K` when adjoining it to the
cell does. -/
theorem insert_face_mem (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) {v : ι}
    (hK : insert v c.val.val ∈ K) : insert v (c.face j).val.val ∈ K :=
  K.isRelLowerSet_faces.mem_of_le hK (Finset.insert_subset_insert v (c.face_val_subset j))
    (Finset.insert_nonempty _ _)

/-- Deleting a vertex of the original cell from a cone gives the cone on the corresponding
face. -/
@[simp]
theorem face_cone_castSucc (c : RealizationCell K (n + 1)) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) (j : Fin (n + 2)) :
    (c.cone v hlt hK).face j.castSucc =
      (c.face j).cone v (fun w hw ↦ hlt w (c.face_val_subset j hw)) (c.insert_face_mem j hK) := by
  refine ext ?_
  rw [face_val, congrFun (vertexEmbedding_cone c v hlt hK), Fin.lastCases_castSucc, cone_val,
    cone_val, face_val, Finset.erase_insert_of_ne (hlt _ (c.vertexEmbedding_mem j)).ne']

/-- Deleting the first vertex of the cone on a `0`-cell leaves the cone vertex. -/
@[simp]
theorem face_cone_zero (c : RealizationCell K 0) (v : ι) (hlt : ∀ w ∈ c.val.val, w < v)
    (hK : insert v c.val.val ∈ K) : (c.cone v hlt hK).face 0 = vertex K v := by
  refine ext ?_
  have hc : c.val.val = {c.vertexEmbedding 0} := congrArg (fun d ↦ d.val.val) c.eq_vertex
  rw [face_val, ← Fin.castSucc_zero, congrFun (vertexEmbedding_cone c v hlt hK),
    Fin.lastCases_castSucc, cone_val, hc]
  simp [Finset.erase_insert_of_ne (hlt _ (c.vertexEmbedding_mem 0)).ne']

/-- A vertex of a cell that no vertex of the cell exceeds is its last vertex. -/
theorem vertexEmbedding_last_eq {c : RealizationCell K n} {v : ι} (hv : v ∈ c.val.val)
    (hle : ∀ w ∈ c.val.val, w ≤ v) : c.vertexEmbedding (Fin.last n) = v :=
  c.vertexEmbedding_last.trans ((Finset.max'_eq_iff _ _ _).mpr ⟨hv, hle⟩)

/-- Every vertex of the face opposite the last vertex of a cell precedes that last vertex. -/
theorem lt_of_mem_face_last (c : RealizationCell K (n + 1)) {w : ι}
    (hw : w ∈ (c.face (Fin.last (n + 1))).val.val) : w < c.vertexEmbedding (Fin.last (n + 1)) := by
  rw [face_val] at hw
  rw [vertexEmbedding_last] at hw ⊢
  exact Finset.lt_max'_of_mem_erase_max' _ _ hw

/-- Adjoining the last vertex of a cell to the face opposite it recovers the cell. -/
theorem insert_face_last (c : RealizationCell K (n + 1)) :
    insert (c.vertexEmbedding (Fin.last (n + 1))) (c.face (Fin.last (n + 1))).val.val =
      c.val.val := by
  rw [face_val, Finset.insert_erase (c.vertexEmbedding_mem _)]

/-- **A cell is the cone on the face opposite its last vertex**, with that vertex as cone
vertex. -/
theorem cone_face_last (c : RealizationCell K (n + 1)) :
    (c.face (Fin.last (n + 1))).cone (c.vertexEmbedding (Fin.last (n + 1)))
      (fun _ hw ↦ c.lt_of_mem_face_last hw) (by rw [insert_face_last]; exact c.val.property) =
      c :=
  ext (by rw [cone_val, insert_face_last])

/-- Every face of a cell other than the one opposite its last vertex contains that vertex. -/
theorem vertexEmbedding_last_mem_face_castSucc (c : RealizationCell K (n + 1)) (j : Fin (n + 1)) :
    c.vertexEmbedding (Fin.last (n + 1)) ∈ (c.face j.castSucc).val.val := by
  rw [face_val, Finset.mem_erase]
  exact ⟨c.vertexEmbedding.injective.ne (Fin.castSucc_lt_last j).ne', c.vertexEmbedding_mem _⟩

end Cone

end RealizationCell

end AbstractSimplicialComplex
