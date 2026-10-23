/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cell
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.CharacteristicMap

/-!
# The CW structure on a simplicial realization

The weak geometric realization of an abstract simplicial complex is a classical CW complex.
Its `n`-cells are the nonempty faces with `n + 1` vertices, and the characteristic map of a
cell is the ball parametrization of its closed simplex.  The boundary sphere lands in the
proper subfaces, while the open ball consists of the points whose barycentric support is the
whole face.

A linear order on the vertex type chooses one enumeration of each face.  This avoids duplicate
cells and fixes the orientations of the characteristic maps.  The resulting open and closed
cells themselves depend only on the underlying faces.  The equivalence `realizationCellEquiv`
identifies the cells of `realizationCWComplex K` with `RealizationCell K`, through which its open
cells, closed cells, and cell frontiers are described by barycentric supports.  In positive
dimensions, each frontier is the union of its codimension-one closed cells.  The CW
filtration stage `skeletonLT n` consists of points with at most `n` nonzero barycentric
coordinates.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (simplicial complexes as CW complexes).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Metric Set Topology

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι]

namespace RealizationCell

variable {K : AbstractSimplicialComplex ι} {n : ℕ}

/-- The characteristic map of a simplicial cell, using its increasing vertex enumeration. -/
def characteristicMap (c : RealizationCell K n) : PartialEquiv (Fin n → ℝ) (Realization K) :=
  simplexCharacteristicMap K c.vertexEmbedding (c.image_vertexEmbedding.symm ▸ c.1.2)

/-- A cell's characteristic map uses its increasing vertex enumeration. -/
theorem characteristicMap_def (c : RealizationCell K n) :
    c.characteristicMap =
      simplexCharacteristicMap K c.vertexEmbedding (c.image_vertexEmbedding.symm ▸ c.1.2) :=
  (rfl)

/-- The source of a simplicial cell's characteristic map is the open unit ball. -/
@[simp]
theorem characteristicMap_source (c : RealizationCell K n) :
    c.characteristicMap.source = ball 0 1 :=
  simplexCharacteristicMap_source K c.vertexEmbedding _

/-- The open cell consists of the points whose barycentric support is its face. -/
@[simp]
theorem characteristicMap_target (c : RealizationCell K n) :
    c.characteristicMap.target = {x : Realization K | x.1.support = c.1.1} := by
  rw [characteristicMap, simplexCharacteristicMap_target, image_vertexEmbedding]

/-- A cell's characteristic map is injective on the closed ball. -/
theorem injOn_characteristicMap_closedBall (c : RealizationCell K n) :
    InjOn c.characteristicMap (closedBall 0 1) :=
  injOn_simplexCharacteristicMap_closedBall K c.vertexEmbedding _

/-- The open ball maps onto the points whose support is the cell's face. -/
@[simp]
theorem image_characteristicMap_ball (c : RealizationCell K n) :
    c.characteristicMap '' ball 0 1 = {x : Realization K | x.1.support = c.1.1} := by
  rw [← c.characteristicMap_source, PartialEquiv.image_source_eq_target,
    characteristicMap_target]

/-- The closed ball maps onto the closed simplex spanned by the cell's face. -/
@[simp]
theorem image_characteristicMap_closedBall (c : RealizationCell K n) :
    c.characteristicMap '' closedBall 0 1 =
      {x : Realization K | x.1.support ⊆ c.1.1} := by
  rw [characteristicMap, image_simplexCharacteristicMap_closedBall, image_vertexEmbedding]

/-- The boundary sphere maps onto the proper subfaces of the cell's face. -/
@[simp]
theorem image_characteristicMap_sphere (c : RealizationCell K n) :
    c.characteristicMap '' sphere 0 1 =
      {x : Realization K | x.1.support ⊂ c.1.1} := by
  rw [characteristicMap, image_simplexCharacteristicMap_sphere, image_vertexEmbedding]

end RealizationCell

omit [LinearOrder ι] in
private theorem finite_lowerCells {K : AbstractSimplicialComplex ι} {n : ℕ}
    (c : RealizationCell K n) (m : ℕ) :
    {d : RealizationCell K m | d.1.1 ⊆ c.1.1}.Finite := by
  have himage : ((fun d : RealizationCell K m => d.1.1) ''
      {d | d.1.1 ⊆ c.1.1}).Finite :=
    c.1.1.powerset.finite_toSet.subset (by
      rintro _ ⟨d, hd, rfl⟩
      exact Finset.mem_powerset.mpr hd)
  exact Set.Finite.of_finite_image himage fun d _ e _ hde =>
    Subtype.ext (Subtype.ext hde)

private noncomputable def lowerCells {K : AbstractSimplicialComplex ι} {n : ℕ}
    (c : RealizationCell K n) (m : ℕ) : Finset (RealizationCell K m) :=
  (finite_lowerCells c m).toFinset

omit [LinearOrder ι] in
@[simp]
private theorem mem_lowerCells {K : AbstractSimplicialComplex ι} {n m : ℕ}
    (c : RealizationCell K n) (d : RealizationCell K m) :
    d ∈ lowerCells c m ↔ d.1.1 ⊆ c.1.1 :=
  Set.Finite.mem_toFinset _

private theorem pairwiseDisjoint_characteristicMap (K : AbstractSimplicialComplex ι) :
    (Set.univ : Set (Σ n, RealizationCell K n)).PairwiseDisjoint
      (fun c => c.2.characteristicMap '' ball 0 1) := by
  rintro ⟨n, c⟩ - ⟨m, d⟩ - hne
  rw [Function.onFun_apply, RealizationCell.image_characteristicMap_ball,
    RealizationCell.image_characteristicMap_ball, Set.disjoint_left]
  intro x hxc hxd
  have hfaces : c.1.1 = d.1.1 := hxc.symm.trans hxd
  have hcard : n + 1 = m + 1 := by
    calc
      n + 1 = c.1.1.card := c.2.symm
      _ = d.1.1.card := congrArg Finset.card hfaces
      _ = m + 1 := d.2
  have hnm : n = m := by omega
  subst m
  have hcd : c = d := Subtype.ext (Subtype.ext hfaces)
  subst d
  exact hne rfl

private theorem mapsTo_characteristicMap (K : AbstractSimplicialComplex ι) (n : ℕ)
    (c : RealizationCell K n) :
    MapsTo c.characteristicMap (sphere 0 1)
      (⋃ (m < n) (d ∈ lowerCells c m), d.characteristicMap '' closedBall 0 1) := by
  intro x hx
  let y := c.characteristicMap x
  have hy : y.1.support ⊂ c.1.1 := by
    have : y ∈ c.characteristicMap '' sphere 0 1 := ⟨x, hx, rfl⟩
    simpa only [RealizationCell.image_characteristicMap_sphere, Set.mem_ofPred_eq] using this
  have hface : y.1.support ∈ K := support_mem K y
  have hnonempty : y.1.support.Nonempty := K.isRelLowerSet_faces.prop_of_mem hface
  let m := y.1.support.card - 1
  have hmcard : y.1.support.card = m + 1 := by
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hnonempty)).symm
  let d : RealizationCell K m := ⟨⟨y.1.support, hface⟩, hmcard⟩
  have hmn : m < n := by
    have hcard := Finset.card_lt_card hy
    dsimp only [m]
    rw [c.2] at hcard
    omega
  refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn, mem_iUnion.mpr ⟨d, ?_⟩⟩⟩
  refine mem_iUnion.mpr ⟨(mem_lowerCells c d).mpr hy.subset, ?_⟩
  rw [RealizationCell.image_characteristicMap_closedBall]
  exact Finset.Subset.rfl

/-- The classical CW structure on a weak simplicial realization.  Its `n`-cells are the faces
with `n + 1` vertices, enumerated increasingly, and its characteristic maps are the canonical
closed-simplex parametrizations by sup-norm balls. -/
@[instance_reducible]
def realizationCWComplex (K : AbstractSimplicialComplex ι) :
    CWComplex (Set.univ : Set (Realization K)) where
  cell := RealizationCell K
  map _ c := c.characteristicMap
  source_eq _ c := c.characteristicMap_source
  continuousOn _ c := continuousOn_simplexCharacteristicMap K c.vertexEmbedding _
  continuousOn_symm _ c := continuousOn_simplexCharacteristicMap_symm K c.vertexEmbedding _
  pairwiseDisjoint' := pairwiseDisjoint_characteristicMap K
  mapsTo' n c := ⟨lowerCells c, mapsTo_characteristicMap K n c⟩
  closed' A _ hA := by
    rw [isClosed_iff_faceInclusion]
    intro σ
    have hσne : σ.1.Nonempty := K.isRelLowerSet_faces.prop_of_mem σ.2
    let n := σ.1.card - 1
    have hcard : σ.1.card = n + 1 :=
      (Nat.sub_add_cancel (Finset.card_pos.mpr hσne)).symm
    let c : RealizationCell K n := ⟨σ, hcard⟩
    have hc := hA n c
    have heq : faceInclusion K σ ⁻¹' A =
        faceInclusion K σ ⁻¹' (A ∩ c.characteristicMap '' closedBall 0 1) := by
      ext x
      simp only [mem_preimage, mem_inter_iff]
      constructor
      · intro hx
        refine ⟨hx, ?_⟩
        rw [RealizationCell.image_characteristicMap_closedBall, Set.mem_ofPred_eq,
          faceInclusion_val]
        exact StandardSimplex.support_subset x
      · exact And.left
    rw [heq]
    exact hc.preimage (continuous_faceInclusion K σ)
  union' := by
    apply eq_univ_of_forall
    intro x
    have hface : x.1.support ∈ K := support_mem K x
    have hnonempty : x.1.support.Nonempty := K.isRelLowerSet_faces.prop_of_mem hface
    let n := x.1.support.card - 1
    have hcard : x.1.support.card = n + 1 :=
      (Nat.sub_add_cancel (Finset.card_pos.mpr hnonempty)).symm
    let c : RealizationCell K n := ⟨⟨x.1.support, hface⟩, hcard⟩
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨c, ?_⟩⟩
    rw [RealizationCell.image_characteristicMap_closedBall]
    exact Finset.Subset.rfl

/-- The `n`-cells of `realizationCWComplex K` are the faces of `K` with `n + 1` vertices. -/
def realizationCellEquiv (K : AbstractSimplicialComplex ι) (n : ℕ) :
    (letI := realizationCWComplex K; RelCWComplex.cell (univ : Set (Realization K)) n) ≃
      RealizationCell K n :=
  Equiv.refl _

/-- The characteristic maps of `realizationCWComplex K` are those of its simplicial cells. -/
theorem map_realizationCellEquiv_symm (K : AbstractSimplicialComplex ι) {n : ℕ}
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    RelCWComplex.map n ((realizationCellEquiv K n).symm c) = c.characteristicMap :=
  (rfl)

/-- The open cells of `realizationCWComplex K` are the points whose support is the cell's face. -/
@[simp]
theorem openCell_realizationCellEquiv_symm (K : AbstractSimplicialComplex ι) {n : ℕ}
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    RelCWComplex.openCell n ((realizationCellEquiv K n).symm c) =
      {x : Realization K | x.1.support = c.1.1} :=
  c.image_characteristicMap_ball

/-- The closed cells of `realizationCWComplex K` are the closed simplices of the cell's face. -/
@[simp]
theorem closedCell_realizationCellEquiv_symm (K : AbstractSimplicialComplex ι) {n : ℕ}
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    RelCWComplex.closedCell n ((realizationCellEquiv K n).symm c) =
      {x : Realization K | x.1.support ⊆ c.1.1} :=
  c.image_characteristicMap_closedBall

/-- The cell frontiers of `realizationCWComplex K` are the proper subfaces of the cell's face. -/
@[simp]
theorem cellFrontier_realizationCellEquiv_symm (K : AbstractSimplicialComplex ι) {n : ℕ}
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    RelCWComplex.cellFrontier n ((realizationCellEquiv K n).symm c) =
      {x : Realization K | x.1.support ⊂ c.1.1} :=
  c.image_characteristicMap_sphere

/-- The frontier of a positive-dimensional realization cell is the union of the closed cells
obtained by deleting one vertex. -/
theorem cellFrontier_realizationCellEquiv_symm_eq_iUnion_face
    (K : AbstractSimplicialComplex ι) (c : RealizationCell K (n + 1)) :
    letI := realizationCWComplex K
    RelCWComplex.cellFrontier (n + 1) ((realizationCellEquiv K (n + 1)).symm c) =
      ⋃ j : Fin (n + 2),
        RelCWComplex.closedCell n ((realizationCellEquiv K n).symm (c.face j)) := by
  let := realizationCWComplex K
  ext x
  simp only [cellFrontier_realizationCellEquiv_symm,
    closedCell_realizationCellEquiv_symm, Set.mem_ofPred_eq, Set.mem_iUnion]
  exact (c.exists_subset_face_iff_ssubset x.1.support).symm

/-- Stage `n` of the CW filtration consists exactly of points with at most `n` nonzero
barycentric coordinates. Stage zero is empty and stage infinity is the whole realization. -/
@[simp]
theorem skeletonLT_realizationCWComplex (K : AbstractSimplicialComplex ι) (n : ℕ∞) :
    letI := realizationCWComplex K
    (RelCWComplex.skeletonLT (univ : Set (Realization K)) n : Set (Realization K)) =
      {x | (x.1.support.card : ℕ∞) ≤ n} := by
  let := realizationCWComplex K
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n =>
    ext x
    simp only [SetLike.mem_coe, mem_ofPred_eq, ENat.natCast_le_natCast]
    rw [CWComplex.mem_skeletonLT_iff]
    constructor
    · rintro ⟨m, hmn, c, hxc⟩
      let d := realizationCellEquiv K m c
      have hx : x.1.support = d.1.1 := by
        rw [← (realizationCellEquiv K m).symm_apply_apply c,
          openCell_realizationCellEquiv_symm] at hxc
        exact hxc
      have hm : m < n := by exact_mod_cast hmn
      rw [hx, d.2]
      omega
    · intro hx
      have hpos : 0 < x.1.support.card :=
        Finset.card_pos.mpr (K.isRelLowerSet_faces.prop_of_mem (support_mem K x))
      let m := x.1.support.card - 1
      let d : RealizationCell K m :=
        ⟨⟨x.1.support, support_mem K x⟩, by dsimp [m]; omega⟩
      refine ⟨m, ?_, (realizationCellEquiv K m).symm d, ?_⟩
      · have hm : m < n := by dsimp [m]; omega
        exact_mod_cast hm
      · rw [openCell_realizationCellEquiv_symm]
        rfl

end AbstractSimplicialComplex
