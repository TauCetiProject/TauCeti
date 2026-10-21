/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Order.Sigma
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedMap
public import TauCeti.Topology.CWComplex.Classical.FreeAction
public import TauCeti.Topology.CWComplex.Classical.OrbitSpace

/-!
# The CW structures on Milnor's countable join and classifying space

The realization of a simplicial complex is a CW complex whose `n`-cells are its faces with
`n + 1` vertices, once a linear order on the vertices fixes the characteristic maps. The vertices
`⟨i, h⟩` of a face of the countable join `universalGSpace G` have pairwise distinct indices `i`,
so any order on the vertices that compares different indices as `ℕ` does orders every face by
index. We fix one such order, `universalGSpaceVertexOrder G`, lexicographic for an arbitrary
well-order on `G`. The characteristic maps of the resulting CW structure on `universalGSpace G`
only compare vertices of a common face, so they enumerate each simplex by increasing index,
whatever the order on `G`.

Translation by `g : G` relabels the vertices of a face, `⟨i, h⟩ ↦ ⟨i, g * h⟩`, without changing
their indices. So it preserves the order on each face, and carries the characteristic map of each
cell exactly onto the characteristic map of the translated cell, not merely up to orientation.
This is an action of `G` on the `n`-cells, and it is free: if `g ≠ 1`, translation by `g` changes
the label of every vertex. Hence `G` permutes the open cells, closed cells and cell frontiers of
`universalGSpace G`, carrying an open cell onto itself only for `g = 1`. This is also the input
for describing the cellular chains of `universalGSpace G` as free modules over the group ring.

The CW structure descends along the quotient covering map `classifyingSpaceProj G`
(`IsQuotientCoveringMap.cwComplexQuotient`), so the classifying space `classifyingSpace G` is a
Hausdorff CW complex whose `n`-cells are the `G`-orbits of the `n`-simplices of the countable join.
Since translation carries characteristic maps exactly onto characteristic maps and does not move
points of the classifying space, the characteristic map of an orbit is the characteristic map of
any of its simplices followed by the orbit map; it does not depend on the chosen representative.

## Main definitions

* `TauCeti.universalGSpaceVertexOrder`: a linear order on the vertices of the countable join
  extending the order of the indices.
* `TauCeti.instCWComplexUniversalGSpace`: the CW structure on `universalGSpace G` whose cells are
  the simplices of the countable join, each enumerated by increasing index.
* `TauCeti.instMulActionRealizationCellUniversalGSpace`: the action of `G` on the simplices of
  the countable join.
* `TauCeti.instMulActionCellUniversalGSpace`: the corresponding action on the cells of the CW
  structure.
* `TauCeti.instCWComplexClassifyingSpace`: the CW structure on `classifyingSpace G`.
* `TauCeti.classifyingSpaceCellEquiv`: its `n`-cells are the `G`-orbits of `n`-simplices of the
  countable join.

## Main results

* `TauCeti.universalGSpaceVertexOrder_lt_iff`: on a face, the vertex order is the order of the
  indices.
* `TauCeti.face_smul_universalGSpace`: translation commutes with taking faces of simplices.
* `TauCeti.smul_characteristicMap_universalGSpace` and `TauCeti.smul_map_universalGSpace`:
  translation carries characteristic maps to characteristic maps.
* `TauCeti.smul_openCell_universalGSpace`, `TauCeti.smul_closedCell_universalGSpace` and
  `TauCeti.smul_cellFrontier_universalGSpace`: translation permutes the open cells, closed cells
  and cell frontiers.
* `TauCeti.instIsCancelSMulCellUniversalGSpace` and
  `TauCeti.eq_one_of_smul_openCell_universalGSpace_eq`: the action on cells is free.
* `TauCeti.instT2SpaceClassifyingSpace`: the classifying space is Hausdorff.
* `TauCeti.map_classifyingSpaceCellEquiv_symm_mk`: the characteristic map of the orbit of a
  simplex is its characteristic map followed by the orbit map.
* `TauCeti.openCell_classifyingSpaceCellEquiv_symm_mk`,
  `TauCeti.closedCell_classifyingSpaceCellEquiv_symm_mk` and
  `TauCeti.cellFrontier_classifyingSpaceCellEquiv_symm_mk`: the open cells, closed cells and cell
  frontiers of the classifying space are the images of those of the countable join.

## References

* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0.
-/

public section

noncomputable section

open AbstractSimplicialComplex Metric Set Topology
open scoped Pointwise

namespace TauCeti

universe u

section VertexOrder

variable (G : Type u)

/-- A linear order on the vertices `⟨i, h⟩` of the countable join of copies of `G`: vertices
with different indices are compared by their indices, and vertices with the same index by an
arbitrary well-order of `G`. Only the first clause matters for the faces of the join, whose
vertices have pairwise distinct indices. -/
@[instance_reducible]
def universalGSpaceVertexOrder : LinearOrder (Σ _ : ℕ, G) :=
  letI : LinearOrder G := IsWellOrder.linearOrder WellOrderingRel
  inferInstanceAs (LinearOrder (Lex (Σ _ : ℕ, G)))

attribute [local instance] universalGSpaceVertexOrder

variable {G}

/-- Vertices with smaller index come first. -/
theorem universalGSpaceVertexOrder_lt_of_fst_lt {v w : Σ _ : ℕ, G} (h : v.1 < w.1) : v < w :=
  -- The order is by definition the lexicographic order `Sigma.Lex`.
  Sigma.Lex.left _ _ h

/-- On a face of the countable join, the vertex order is the order of the indices. -/
theorem universalGSpaceVertexOrder_lt_iff {σ : Finset (Σ _ : ℕ, G)}
    (hσ : σ ∈ indexedJoin fun _ : ℕ => G) {v w : Σ _ : ℕ, G} (hv : v ∈ σ) (hw : w ∈ σ) :
    v < w ↔ v.1 < w.1 := by
  refine ⟨fun hvw => ?_, universalGSpaceVertexOrder_lt_of_fst_lt⟩
  rcases lt_trichotomy v.1 w.1 with h | h | h
  · exact h
  · exact absurd (eq_of_mem_indexedJoin hσ hv hw h) hvw.ne
  · exact absurd (universalGSpaceVertexOrder_lt_of_fst_lt h) hvw.asymm

/-- The increasing enumeration of the vertices of a cell of the countable join enumerates them
by increasing index. -/
theorem strictMono_fst_vertexEmbedding_universalGSpace {n : ℕ}
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    StrictMono fun k => (c.vertexEmbedding k).1 := fun _ _ hkl =>
  (universalGSpaceVertexOrder_lt_iff c.1.2 (c.vertexEmbedding_mem _)
    (c.vertexEmbedding_mem _)).mp (c.strictMono_vertexEmbedding hkl)

/-- The CW structure on Milnor's countable join: its `n`-cells are the simplices of the join
with `n + 1` vertices, and the characteristic map of a simplex enumerates its vertices by
increasing index. -/
instance instCWComplexUniversalGSpace : CWComplex (univ : Set (universalGSpace G)) :=
  realizationCWComplex _

end VertexOrder

attribute [local instance] universalGSpaceVertexOrder

variable {G : Type u} [Group G] {n : ℕ}

section RealizationCell

/-- The translate of a face of the countable join by `g` is a face. -/
theorem map_toPerm_mem_indexedJoin (g : G) {σ : Finset (Σ _ : ℕ, G)}
    (hσ : σ ∈ indexedJoin fun _ : ℕ => G) :
    σ.map (MulAction.toPerm g).toEmbedding ∈ indexedJoin fun _ : ℕ => G := by
  rw [mem_indexedJoin_iff] at hσ ⊢
  refine ⟨hσ.1.map, ?_⟩
  rintro _ hv' _ hw' hvw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hv')
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hw')
  exact congrArg (g • ·) (hσ.2 hv hw hvw)

/-- A group acts on the simplices of Milnor's countable join of copies of itself by translating
the labels of their vertices. -/
instance instSMulRealizationCellUniversalGSpace :
    SMul G ((indexedJoin fun _ : ℕ => G).RealizationCell n) where
  smul g c :=
    ⟨⟨c.1.1.map (MulAction.toPerm g).toEmbedding, map_toPerm_mem_indexedJoin g c.1.2⟩,
      (Finset.card_map _).trans c.2⟩

/-- The face of a translated simplex is the translated face. -/
theorem smul_realizationCell_face (g : G) (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    ((g • c).1.1 : Finset (Σ _ : ℕ, G)) = c.1.1.map (MulAction.toPerm g).toEmbedding :=
  (rfl)

/-- A vertex lies in the face of a translated simplex exactly when its translate back lies in the
face of the original simplex. -/
@[simp]
theorem mem_smul_realizationCell_face_iff (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (v : Σ _ : ℕ, G) :
    v ∈ (g • c).1.1 ↔ g⁻¹ • v ∈ c.1.1 := by
  rw [smul_realizationCell_face, Finset.mem_map_equiv, MulAction.toPerm_symm_apply]

/-- The translation of simplices is an action of the group. -/
instance instMulActionRealizationCellUniversalGSpace :
    MulAction G ((indexedJoin fun _ : ℕ => G).RealizationCell n) where
  one_smul c := Subtype.ext <| Subtype.ext <| by
    ext v
    simp
  mul_smul g h c := Subtype.ext <| Subtype.ext <| by
    ext v
    simp [mul_smul]

/-- The action of a group on the simplices of the countable join is free: a simplex fixed by `g`
has a vertex `v`, and `g • v` is a vertex of the same simplex over the same index as `v`, so
`g • v = v` and `g = 1`. -/
instance instIsCancelSMulRealizationCellUniversalGSpace :
    IsCancelSMul G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g c hgc => by
    obtain ⟨v, hv⟩ := (mem_indexedJoin_iff.mp c.1.2).1
    have hgv : g • v ∈ c.1.1 := by
      rw [← hgc, mem_smul_realizationCell_face_iff, inv_smul_smul]
      exact hv
    have := eq_of_mem_indexedJoin c.1.2 hgv hv rfl
    exact mul_eq_right.mp (eq_of_heq (Sigma.ext_iff.mp this).2)

/-- The simplicial automorphism of the countable join relabelling the vertices by `g`, typed
with the decidable equality of the vertex order. -/
private def smulSimplicialMap (g : G) :
    PreAbstractSimplicialComplex.SimplicialMap
      (indexedJoin fun _ : ℕ => G).toPreAbstractSimplicialComplex
      (indexedJoin fun _ : ℕ => G).toPreAbstractSimplicialComplex where
  toFun v := g • v
  map_face' σ hσ := by
    have := map_toPerm_mem_indexedJoin g hσ
    rwa [Finset.map_eq_image] at this

/-- Translation preserves the vertex order on each simplex of the countable join. -/
private theorem smulSimplicialMap_strictMonoOn (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    StrictMonoOn (smulSimplicialMap g) (↑c.1.1 : Set (Σ _ : ℕ, G)) := by
  intro v hv w hw hvw
  exact universalGSpaceVertexOrder_lt_of_fst_lt
    ((universalGSpaceVertexOrder_lt_iff c.1.2 hv hw).mp hvw)

/-- Translation of a cell agrees with its image under the translating simplicial map. -/
private theorem smul_realizationCell_eq_map (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    g • c = c.map (smulSimplicialMap g) (smulSimplicialMap_strictMonoOn g c).injOn := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply,
    smul_realizationCell_face, Finset.map_eq_image]
  -- Both faces are images under the same relabelling of vertices.
  rfl

/-- Translation of the countable join is the realization of the simplicial map relabelling the
vertices. -/
private theorem smul_eq_realizationMap (g : G) (x : universalGSpace G) :
    g • x = (smulSimplicialMap g).realizationMap x :=
  Subtype.ext <| by
    rw [universalGSpace_smul_val,
      PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val]
    -- Both sides push the coordinates forward along the same relabelling of vertices.
    rfl

/-- **Translation carries characteristic maps to characteristic maps.** For a simplex `c` of the
countable join, translating its characteristic map by `g` gives the characteristic map of
`g • c`, on the whole domain. -/
theorem smul_characteristicMap_universalGSpace (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (x : Fin n → ℝ) :
    g • c.characteristicMap x = (g • c).characteristicMap x := by
  rw [smul_eq_realizationMap,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_characteristicMap _ c
      (smulSimplicialMap_strictMonoOn g c), ← smul_realizationCell_eq_map]

/-- Translation preserves the index-ordered enumeration of each simplex of the countable join. -/
@[simp]
theorem vertexEmbedding_smul_universalGSpace (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (j : Fin (n + 1)) :
    (g • c).vertexEmbedding j = g • c.vertexEmbedding j := by
  rw [smul_realizationCell_eq_map]
  exact congrFun
    (c.vertexEmbedding_map (smulSimplicialMap g) (smulSimplicialMap_strictMonoOn g c)) j

/-- Translation commutes with deleting a vertex: the `j`-th face of a translated simplex of the
countable join is the translate of its `j`-th face. -/
@[simp]
theorem face_smul_universalGSpace (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell (n + 1)) (j : Fin (n + 2)) :
    (g • c).face j = g • c.face j := by
  refine Subtype.ext (Subtype.ext ?_)
  simp [RealizationCell.face_val, smul_realizationCell_face, Finset.map_erase]

end RealizationCell

section CWComplex

open Topology.RelCWComplex

/-- The action of a group on the cells of the CW structure on the countable join, through the
identification of the cells with the simplices of the join. -/
instance instMulActionCellUniversalGSpace :
    MulAction G (cell (univ : Set (universalGSpace G)) n) :=
  (realizationCellEquiv _ n).mulAction G

/-- The identification of the cells of the countable join with its simplices is equivariant. -/
@[simp]
theorem realizationCellEquiv_smul (g : G) (i : cell (univ : Set (universalGSpace G)) n) :
    realizationCellEquiv _ n (g • i) = g • realizationCellEquiv _ n i := by
  rw [Equiv.smul_def, Equiv.apply_symm_apply]

/-- The inverse identification of the simplices of the countable join with its cells is
equivariant. -/
@[simp]
theorem realizationCellEquiv_symm_smul (g : G)
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    (realizationCellEquiv _ n).symm (g • c) = g • (realizationCellEquiv _ n).symm c := by
  rw [Equiv.symm_apply_eq, realizationCellEquiv_smul, Equiv.apply_symm_apply]

/-- **Translation carries characteristic maps to characteristic maps**: translating the
characteristic map of a cell of the countable join by `g` gives the characteristic map of the
translated cell. -/
theorem smul_map_universalGSpace (g : G) (i : cell (univ : Set (universalGSpace G)) n)
    (x : Fin n → ℝ) : g • map n i x = map n (g • i) x := by
  obtain ⟨c, rfl⟩ := (realizationCellEquiv _ n).symm.surjective i
  rw [← realizationCellEquiv_symm_smul, map_realizationCellEquiv_symm,
    map_realizationCellEquiv_symm]
  exact smul_characteristicMap_universalGSpace g c x

/-- Translation carries each open cell of the countable join onto the open cell of the
translated cell. -/
theorem smul_openCell_universalGSpace (g : G) (i : cell (univ : Set (universalGSpace G)) n) :
    g • openCell n i = openCell n (g • i) := by
  simp only [openCell, ← Set.image_smul, Set.image_image, smul_map_universalGSpace]

/-- Translation carries each closed cell of the countable join onto the closed cell of the
translated cell. -/
theorem smul_closedCell_universalGSpace (g : G) (i : cell (univ : Set (universalGSpace G)) n) :
    g • closedCell n i = closedCell n (g • i) := by
  simp only [closedCell, ← Set.image_smul, Set.image_image, smul_map_universalGSpace]

/-- Translation carries each cell frontier of the countable join onto the cell frontier of the
translated cell. -/
theorem smul_cellFrontier_universalGSpace (g : G) (i : cell (univ : Set (universalGSpace G)) n) :
    g • cellFrontier n i = cellFrontier n (g • i) := by
  simp only [cellFrontier, ← Set.image_smul, Set.image_image, smul_map_universalGSpace]

/-- The action of a group on the cells of the countable join is free. -/
instance instIsCancelSMulCellUniversalGSpace :
    IsCancelSMul G (cell (univ : Set (universalGSpace G)) n) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun g i h =>
    IsCancelSMul.eq_one_of_smul (x := realizationCellEquiv _ n i) (by
      rw [← realizationCellEquiv_smul, h])

/-- **The action on the cells of the countable join is free**: translation by `g` carries an
open cell onto itself only when `g = 1`. -/
theorem eq_one_of_smul_openCell_universalGSpace_eq {g : G}
    {i : cell (univ : Set (universalGSpace G)) n} (h : g • openCell n i = openCell n i) :
    g = 1 :=
  IsCancelSMul.eq_one_of_smul (openCell_congr n ((smul_openCell_universalGSpace g i).symm.trans h))

end CWComplex

section ClassifyingSpace

open Topology.RelCWComplex

/-- Translation carries each open cell of the countable join onto an open cell, in the form
asked by the orbit-space construction `IsQuotientCoveringMap.cwComplexQuotient`. -/
private theorem exists_smul_openCell_eq (g : G) (n : ℕ)
    (i : cell (univ : Set (universalGSpace G)) n) :
    ∃ j : cell (univ : Set (universalGSpace G)) n, g • openCell n i = openCell n j :=
  ⟨g • i, smul_openCell_universalGSpace g i⟩

/-- **Milnor's classifying space is a CW complex.** Its `n`-cells are the `G`-orbits of the
`n`-simplices of the countable join (`TauCeti.classifyingSpaceCellEquiv`), and the characteristic
map of an orbit is the characteristic map of any of its simplices followed by the orbit map
(`TauCeti.map_classifyingSpaceCellEquiv_symm_mk`). -/
instance instCWComplexClassifyingSpace : CWComplex (univ : Set (classifyingSpace G)) :=
  (isQuotientCoveringMap_classifyingSpaceProj G).cwComplexQuotient
    (fun g _ i => ⟨g • i, smul_openCell_universalGSpace g i⟩)
    fun _ _ _ => eq_one_of_smul_openCell_universalGSpace_eq

/-- Milnor's classifying space is Hausdorff, as the orbit space of a free cellular action on a
Hausdorff CW complex. -/
instance instT2SpaceClassifyingSpace : T2Space (classifyingSpace G) :=
  (isQuotientCoveringMap_classifyingSpaceProj G).t2Space_of_cwComplex
    (fun g _ i => ⟨g • i, smul_openCell_universalGSpace g i⟩)
    fun _ _ _ => eq_one_of_smul_openCell_universalGSpace_eq

/-- The action on the cells of the countable join by which the orbit-space construction indexes
the cells of the classifying space is the translation of simplices. -/
private theorem cellMulAction_smul_eq (g : G) (i : cell (univ : Set (universalGSpace G)) n) :
    (letI := cellMulAction (G := G) exists_smul_openCell_eq n; g • i) = g • i :=
  openCell_congr n <|
    (smul_openCell (G := G) exists_smul_openCell_eq g i).symm.trans
      (smul_openCell_universalGSpace g i)

variable (G) in
/-- **The cells of the classifying space are the orbits of simplices.** The `n`-cells of
`classifyingSpace G` correspond to the `G`-orbits of the simplices of the countable join with
`n + 1` vertices. -/
def classifyingSpaceCellEquiv (n : ℕ) :
    cell (univ : Set (classifyingSpace G)) n ≃
      MulAction.orbitRel.Quotient G ((indexedJoin fun _ : ℕ => G).RealizationCell n) :=
  letI := cellMulAction (G := G) exists_smul_openCell_eq n
  ((isQuotientCoveringMap_classifyingSpaceProj G).cellQuotientEquiv
      exists_smul_openCell_eq (fun _ _ _ => eq_one_of_smul_openCell_universalGSpace_eq) n).trans <|
    MulAction.orbitRelQuotientCongr (MulEquiv.refl G) (realizationCellEquiv _ n) fun g i => by
      rw [cellMulAction_smul_eq, realizationCellEquiv_smul]
      rfl

/-- **The characteristic maps of the classifying space.** The characteristic map of the orbit of
a simplex `c` of the countable join is the characteristic map of `c` followed by the orbit map,
whichever simplex of the orbit is chosen. -/
@[simp]
theorem map_classifyingSpaceCellEquiv_symm_mk
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) (x : Fin n → ℝ) :
    map n ((classifyingSpaceCellEquiv G n).symm (Quotient.mk'' c)) x =
      classifyingSpaceProj G (c.characteristicMap x) := by
  let := cellMulAction (G := G) exists_smul_openCell_eq n
  set i := (realizationCellEquiv _ n).symm c
  have hp := isQuotientCoveringMap_classifyingSpaceProj G
  have hc : (classifyingSpaceCellEquiv G n).symm (Quotient.mk'' c) =
      (hp.cellQuotientEquiv exists_smul_openCell_eq
        (fun _ _ _ => eq_one_of_smul_openCell_universalGSpace_eq) n).symm (Quotient.mk'' i) := by
    rw [Equiv.symm_apply_eq, classifyingSpaceCellEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [MulAction.orbitRelQuotientCongr_mk, (realizationCellEquiv _ n).apply_symm_apply]
  -- The orbit-space construction uses a chosen representative, a translate of `i`.
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact'
    (Quotient.out_eq' (Quotient.mk'' i : MulAction.orbitRel.Quotient G _)))
  rw [hc, hp.map_cellQuotientEquiv_symm, ← hg, cellMulAction_smul_eq,
    ← smul_map_universalGSpace, classifyingSpaceProj_smul, map_realizationCellEquiv_symm]

/-- The open cell of the orbit of a simplex of the countable join is the image of the points
whose support is that simplex. -/
@[simp]
theorem openCell_classifyingSpaceCellEquiv_symm_mk
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    openCell n ((classifyingSpaceCellEquiv G n).symm (Quotient.mk'' c)) =
      classifyingSpaceProj G '' {x : universalGSpace G | x.1.support = c.1.1} := by
  rw [← c.image_characteristicMap_ball, image_image]
  exact image_congr fun x _ => map_classifyingSpaceCellEquiv_symm_mk c x

/-- The closed cell of the orbit of a simplex of the countable join is the image of the closed
simplex. -/
@[simp]
theorem closedCell_classifyingSpaceCellEquiv_symm_mk
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    closedCell n ((classifyingSpaceCellEquiv G n).symm (Quotient.mk'' c)) =
      classifyingSpaceProj G '' {x : universalGSpace G | x.1.support ⊆ c.1.1} := by
  rw [← c.image_characteristicMap_closedBall, image_image]
  exact image_congr fun x _ => map_classifyingSpaceCellEquiv_symm_mk c x

/-- The cell frontier of the orbit of a simplex of the countable join is the image of the points
supported on its proper faces. -/
@[simp]
theorem cellFrontier_classifyingSpaceCellEquiv_symm_mk
    (c : (indexedJoin fun _ : ℕ => G).RealizationCell n) :
    cellFrontier n ((classifyingSpaceCellEquiv G n).symm (Quotient.mk'' c)) =
      classifyingSpaceProj G '' {x : universalGSpace G | x.1.support ⊂ c.1.1} := by
  rw [← c.image_characteristicMap_sphere, image_image]
  exact image_congr fun x _ => map_classifyingSpaceCellEquiv_symm_mk c x

end ClassifyingSpace

end TauCeti
