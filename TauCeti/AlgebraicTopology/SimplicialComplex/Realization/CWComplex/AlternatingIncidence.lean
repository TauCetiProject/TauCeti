/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EdgeIncidence
public import TauCeti.AlgebraicTopology.Cellular.Permutation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Incidence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.OrderedMap

/-!
# The cellular boundary of a simplicial realization alternates

For the CW structure on the weak realization of an abstract simplicial complex with ordered
vertices, the cellular boundary of a cell `c` is supported on its deleted-vertex faces
`c.face j` (`TauCeti.cellularDifferential_realization_cellularChainBasis`). This file shows that
the incidence coefficients alternate in sign along the vertex order:

`[c : c.face j] = (-1) ^ j * [c : c.face 0]`

(`TauCeti.cellularIncidence_realization_face_eq_neg_one_pow_mul`), and that `[c : c.face 0]` is a
unit depending only on the dimension of `c` (`TauCeti.cellularIncidence_realization_face_eq` and
`TauCeti.isUnit_cellularIncidence_realization_face`). Thus the cellular boundary of a simplicial
cell is the ordered simplicial boundary `∑ⱼ (-1) ^ j [c.face j]` up to one unit in each dimension.
This unit `εₙ` is computed once on the standard `(n + 1)`-simplex
(`TauCeti.realizationFaceIncidence`) and transported to every cell of every complex along the
increasing vertex map onto that cell.

## Main definitions

* `TauCeti.realizationFaceIncidence`: the incidence coefficient `εₙ` of the `0`-th face of the
  standard `(n + 1)`-simplex.

## Main results

* `TauCeti.cellularIncidence_realization_map_face`: incidence numbers are natural under
  simplicial maps increasing on the cell.
* `TauCeti.cellularIncidence_realization_face_eq`: the incidence of the `j`-th face of a cell does
  not depend on the cell.
* `TauCeti.isUnit_cellularIncidence_realization_face`: the incidence of every deleted-vertex face
  is a unit, including in dimension one.
* `TauCeti.cellularIncidence_realization_face_succ` and
  `TauCeti.cellularIncidence_realization_face_eq_neg_one_pow_mul`: **the incidence numbers
  alternate in sign**.
* `TauCeti.cellularIncidence_realization_face_eq_neg_one_pow_mul_realizationFaceIncidence`:
  the incidence numbers of a simplicial realization are `(-1) ^ j * εₙ`, independently of the
  complex and the cell.
* `TauCeti.isUnit_realizationFaceIncidence`: `εₙ` is a unit.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (simplicial boundary) and Section 2.2
  (cellular boundary, and the equivalence of simplicial and cellular homology).
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

open _root_.AbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι] {K : _root_.AbstractSimplicialComplex ι}
  (R : Type u) [Ring R] {n : ℕ}

section Naturality

variable {κ : Type u} [LinearOrder κ] {L : _root_.AbstractSimplicialComplex κ}

/-- A simplicial map increasing on a cell sends its cellular basis vector to the cellular basis
vector of the image cell. -/
theorem cellularChainGroupMap_realization_cellularChainBasis {m : ℕ}
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (c : RealizationCell K m) (hf : StrictMonoOn f (↑c.1.1 : Set ι)) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
        f.isCellular_realizationMap (ModuleCat.of R R) m
        (cellularChainBasis (univ : Set (Realization K)) R m
          ((realizationCellEquiv K m).symm c)) =
      cellularChainBasis (univ : Set (Realization L)) R m
        ((realizationCellEquiv L m).symm (c.map f hf.injOn)) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  refine cellularChainGroupMap_cellularChainBasis _ _ _ R fun x _ _ ↦ ?_
  simp only [map_realizationCellEquiv_symm]
  exact f.realizationMap_characteristicMap c hf x

/-- **Incidence numbers are natural under increasing simplicial maps.** If a simplicial map is
strictly increasing on a cell `c`, then the incidence coefficient of the `j`-th face of the image
cell in its cellular boundary is that of the `j`-th face of `c` in the cellular boundary of `c`. -/
theorem cellularIncidence_realization_map_face
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (c : RealizationCell K (n + 1)) (hf : StrictMonoOn f (↑c.1.1 : Set ι)) (j : Fin (n + 2)) :
    letI := realizationCWComplex L
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization L)) R n
        ((realizationCellEquiv L n).symm ((c.map f hf.injOn).face j))
        ((realizationCellEquiv L (n + 1)).symm (c.map f hf.injOn)) =
      cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j)) ((realizationCellEquiv K (n + 1)).symm c) := by
  let := realizationCWComplex K
  let := realizationCWComplex L
  -- Apply the chain-map identity `F ∘ d = d ∘ F` to the basis vector of `c`, and compare the
  -- coefficients of the `j`-th face of the image cell.
  have hcomm := congrArg (fun φ ↦ φ (cellularChainBasis (univ : Set (Realization K)) R (n + 1)
      ((realizationCellEquiv K (n + 1)).symm c)))
    (cellularChainGroupMap_comp_cellularDifferential (univ : Set (Realization K))
      (univ : Set (Realization L)) f.isCellular_realizationMap (ModuleCat.of R R) n)
  simp only [ModuleCat.comp_apply] at hcomm
  rw [cellularChainGroupMap_realization_cellularChainBasis R f c hf,
    cellularDifferential_realization_cellularChainBasis,
    cellularDifferential_realization_cellularChainBasis, map_sum] at hcomm
  simp only [map_smul] at hcomm
  have hfaces (k : Fin (n + 2)) :
      cellularChainGroupMap (univ : Set (Realization K)) (univ : Set (Realization L))
          f.isCellular_realizationMap (ModuleCat.of R R) n
          (cellularChainBasis (univ : Set (Realization K)) R n
            ((realizationCellEquiv K n).symm (c.face k))) =
        cellularChainBasis (univ : Set (Realization L)) R n
          ((realizationCellEquiv L n).symm ((c.map f hf.injOn).face k)) := by
    rw [cellularChainGroupMap_realization_cellularChainBasis R f (c.face k)
      (hf.mono (by simp)), RealizationCell.face_map c f hf k]
  simp only [hfaces] at hcomm
  have h := congrArg (fun x ↦ (cellularChainBasis (univ : Set (Realization L)) R n).repr x
    ((realizationCellEquiv L n).symm ((c.map f hf.injOn).face j))) hcomm
  have hg : Function.Injective fun k ↦
      (realizationCellEquiv L n).symm ((c.map f hf.injOn).face k) :=
    (realizationCellEquiv L n).symm.injective.comp (c.map f hf.injOn).face_injective
  classical
  simpa only [map_sum, map_smul, Module.Basis.repr_self, Finset.sum_apply',
    Finsupp.smul_apply, Finsupp.single_apply, hg.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end Naturality

/-- Any two cells of the same dimension have equal incidence coefficients with their
respective `j`-th deleted-vertex faces. -/
theorem cellularIncidence_realization_face_eq (c c' : RealizationCell K (n + 1))
    (j : Fin (n + 2)) :
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c'.face j)) ((realizationCellEquiv K (n + 1)).symm c') =
      cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j)) ((realizationCellEquiv K (n + 1)).symm c) := by
  -- Compare the two cells in the full simplicial complex, using an increasing vertex map.
  let ι' := PreAbstractSimplicialComplex.SimplicialMap.inclusion
    (le_top : K.toPreAbstractSimplicialComplex ≤ (⊤ : _root_.AbstractSimplicialComplex ι).1)
  have hι'v (v : ι) : ι' v = v :=
    PreAbstractSimplicialComplex.SimplicialMap.inclusion_apply _ v
  have hι' (d : RealizationCell K (n + 1)) : StrictMonoOn ι' (↑d.1.1 : Set ι) :=
    fun a _ b _ h ↦ by simpa only [hι'v] using h
  -- The vertex map sending the vertices of `c` in order to those of `c'`.
  let g : PreAbstractSimplicialComplex.SimplicialMap (⊤ : _root_.AbstractSimplicialComplex ι).1
      (⊤ : _root_.AbstractSimplicialComplex ι).1 :=
    ⟨Function.extend c.vertexEmbedding c'.vertexEmbedding id, fun σ hσ ↦
      Finset.image_nonempty.2 hσ⟩
  have hgc (k : Fin (n + 2)) : g (c.vertexEmbedding k) = c'.vertexEmbedding k :=
    c.vertexEmbedding.injective.extend_apply _ _ k
  have hg : StrictMonoOn g
      (((c.map (L := ⊤) ι' (hι' c).injOn).1.1 : Finset ι) : Set ι) := by
    intro a ha b hb hab
    simp only [RealizationCell.map_face,
      TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply, Finset.coe_image,
      hι'v, Set.image_id', Finset.mem_coe] at ha hb
    rw [← RealizationCell.image_vertexEmbedding, Finset.mem_image] at ha hb
    obtain ⟨k, -, rfl⟩ := ha
    obtain ⟨l, -, rfl⟩ := hb
    rw [hgc, hgc]
    exact c'.strictMono_vertexEmbedding (c.strictMono_vertexEmbedding.lt_iff_lt.1 hab)
  have hcc' : (c.map (L := ⊤) ι' (hι' c).injOn).map (L := ⊤) g hg.injOn =
      c'.map (L := ⊤) ι' (hι' c').injOn := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [RealizationCell.map_face,
      TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply, Finset.image_image]
    rw [← c.image_vertexEmbedding, ← c'.image_vertexEmbedding, Finset.image_image,
      Finset.image_image]
    exact congrArg (Finset.image · Finset.univ) (funext fun k ↦ by simp [hι'v, hgc])
  rw [← cellularIncidence_realization_map_face (L := ⊤) R ι' c' (hι' c') j,
    ← cellularIncidence_realization_map_face (L := ⊤) R ι' c (hι' c) j,
    ← cellularIncidence_realization_map_face (L := ⊤) R g _ hg j, hcc']

/-- Every codimension-one deleted-vertex face has a unit incidence coefficient,
including the endpoint faces of a `1`-cell. -/
theorem isUnit_cellularIncidence_realization_face (c : RealizationCell K (n + 1))
    (j : Fin (n + 2)) :
    letI := realizationCWComplex K
    IsUnit (cellularIncidence (univ : Set (Realization K)) R n
      ((realizationCellEquiv K n).symm (c.face j)) ((realizationCellEquiv K (n + 1)).symm c)) := by
  -- In positive face dimension use the subset criterion; for endpoints use attaching injectivity.
  let := realizationCWComplex K
  cases n with
  | zero =>
    refine isUnit_cellularIncidence_zero_of_injective _ R (cellAttachingMap_realization_injective c)
      ?_
    rw [openCell_realizationCellEquiv_symm, cellFrontier_realizationCellEquiv_symm]
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [hx]
    exact Finset.ssubset_iff_subset_ne.2 ⟨c.face_val_subset j, fun h ↦ by
      have hcard := congrArg Finset.card h
      rw [(c.face j).2, c.2] at hcard
      omega⟩
  | succ n =>
    exact isUnit_cellularIncidence_realization_of_subset (R := R) c (c.face j)
      (c.face_val_subset j)

open scoped Classical in
/-- Each endpoint of the attaching map of a simplicial `1`-cell is exactly one of its two
vertices. -/
private theorem ite_add_ite_realization_face_one (c : RealizationCell K 1)
    (q : TopCat.diskBoundary.{u} 1) :
    letI := realizationCWComplex K
    ((if ((cellAttachingMap ((realizationCellEquiv K 1).symm c) q :
        skeletonObj (univ : Set (Realization K)) 1) : Realization K) ∈
          openCell 0 ((realizationCellEquiv K 0).symm (c.face 0)) then 1 else 0) +
      if ((cellAttachingMap ((realizationCellEquiv K 1).symm c) q :
        skeletonObj (univ : Set (Realization K)) 1) : Realization K) ∈
          openCell 0 ((realizationCellEquiv K 0).symm (c.face 1)) then 1 else 0 : R) = 1 := by
  let := realizationCWComplex K
  set y : Realization K :=
    ((cellAttachingMap ((realizationCellEquiv K 1).symm c) q :
      skeletonObj (univ : Set (Realization K)) 1) : Realization K)
  have hy : y ∈ cellFrontier 1 ((realizationCellEquiv K 1).symm c) := by
    rw [← range_cellAttachingMap]
    exact ⟨q, rfl⟩
  rw [cellFrontier_realizationCellEquiv_symm, Set.mem_ofPred_eq] at hy
  simp only [openCell_realizationCellEquiv_symm, Set.mem_ofPred_eq]
  -- The support of `y` is a nonempty proper subset of the two vertices of `c`.
  obtain ⟨k, hk⟩ := (c.exists_subset_face_iff_ssubset y.1.support).2 hy
  have hyk : y.1.support = (c.face k).1.1 :=
    Finset.eq_of_subset_of_card_le hk (by
      rw [(c.face k).2]
      exact Finset.card_pos.2 (K.isRelLowerSet_faces.prop_of_mem (support_mem K y)))
  have hne (a b : Fin 2) (hab : a ≠ b) :
      c.1.1.erase (c.vertexEmbedding a) ≠ c.1.1.erase (c.vertexEmbedding b) := fun h ↦
    hab (c.vertexEmbedding.injective
      ((Finset.erase_inj _ (c.vertexEmbedding_mem a)).1 h))
  fin_cases k
  · simp [hyk, hne 0 1 (by decide)]
  · simp [hyk, hne 1 0 (by decide)]

/-- In dimension one, the two incidence numbers of a simplicial cell are opposite. -/
private theorem cellularIncidence_realization_face_one (c : RealizationCell K 1) :
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization K)) R 0
        ((realizationCellEquiv K 0).symm (c.face 1)) ((realizationCellEquiv K 1).symm c) =
      -cellularIncidence (univ : Set (Realization K)) R 0
        ((realizationCellEquiv K 0).symm (c.face 0)) ((realizationCellEquiv K 1).symm c) := by
  let := realizationCWComplex K
  classical
  rw [cellularIncidence_zero, cellularIncidence_zero]
  have hm := ite_add_ite_realization_face_one R c sphereMinus
  have hp := ite_add_ite_realization_face_one R c spherePlus
  rw [← eq_sub_iff_add_eq'] at hm hp
  rw [hm, hp]
  abel

/-- Deleting two consecutive vertices `j` and `j + 1` of a cell gives a face contained in no
deleted-vertex face of the cell other than the faces `j` and `j + 1`. -/
private theorem not_subset_face_face_castSucc (c : RealizationCell K (n + 2)) (j : Fin (n + 2))
    (i : Fin (n + 3)) (hi : i ≠ j.castSucc ∧ i ≠ j.succ) :
    ¬ ((c.face j.castSucc).face j).1.1 ⊆ (c.face i).1.1 := by
  intro h
  have hmem : c.vertexEmbedding i ∈ ((c.face j.castSucc).face j).1.1 := by
    rw [RealizationCell.face_val, RealizationCell.face_val,
      congrFun (RealizationCell.vertexEmbedding_face c j.castSucc) j, Function.comp_apply,
      Fin.succAbove_castSucc_self, Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h' ↦ hi.2 (c.vertexEmbedding.injective h'),
      fun h' ↦ hi.1 (c.vertexEmbedding.injective h'), c.vertexEmbedding_mem i⟩
  have := h hmem
  rw [RealizationCell.face_val, Finset.mem_erase] at this
  exact this.1 rfl

/-- **The incidence numbers of a simplicial cell alternate**: deleting the vertex `j + 1` instead
of the vertex `j` negates the incidence coefficient. -/
theorem cellularIncidence_realization_face_succ (c : RealizationCell K (n + 1))
    (j : Fin (n + 1)) :
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j.succ))
        ((realizationCellEquiv K (n + 1)).symm c) =
      -cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j.castSucc))
        ((realizationCellEquiv K (n + 1)).symm c) := by
  let := realizationCWComplex K
  -- In dimension one this is the endpoint formula `TauCeti.cellularIncidence_zero`. In higher
  -- dimensions, the face `k` of `c` with the consecutive vertices `j` and `j + 1` deleted lies in
  -- exactly two deleted-vertex faces of `c`, namely `c.face j` and `c.face (j + 1)`, and is the
  -- `j`-th face of both. By homogeneity its two incidences agree and are units, so the coefficient
  -- of `k` in `d² c = 0` gives the sign flip.
  cases n with
  | zero =>
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    exact cellularIncidence_realization_face_one R c
  | succ n =>
    classical
    -- The coefficient of `k = (c.face j).face j` in `d² c = 0`.
    set k := (c.face j.castSucc).face j with hk
    have hk' : k = (c.face j.succ).face j := by
      rw [hk, RealizationCell.face_face, Fin.succAbove_castSucc_self, Fin.predAbove_castSucc_self]
    have hsum := sum_cellularIncidence_mul (univ : Set (Realization K)) R n
      ((realizationCellEquiv K n).symm k) ((realizationCellEquiv K (n + 2)).symm c)
    rw [Finset.sum_subset (support_cellularBoundaryColumn_realization_subset_faces c)
        fun d _ hd ↦ by
        rw [← cellularBoundaryColumn_apply, Finsupp.notMem_support_iff.1 hd, zero_mul],
      Finset.sum_image fun i _ i' _ h ↦
        c.face_injective ((realizationCellEquiv K (n + 1)).symm.injective h),
      Fintype.sum_eq_add j.castSucc j.succ Fin.castSucc_lt_succ.ne fun i hi ↦ by
        rw [cellularIncidence_realization_eq_zero_of_not_subset (R := R) _ _
          (not_subset_face_face_castSucc c j i hi), mul_zero]] at hsum
    -- Both incidences of `k` are the incidence of the `j`-th face of a cell of dimension `n + 1`,
    -- which is a unit.
    have hk₂ : cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm k)
          ((realizationCellEquiv K (n + 1)).symm (c.face j.succ)) =
        cellularIncidence (univ : Set (Realization K)) R n
          ((realizationCellEquiv K n).symm k)
            ((realizationCellEquiv K (n + 1)).symm (c.face j.castSucc)) := by
      rw [hk', cellularIncidence_realization_face_eq R (c.face j.castSucc) (c.face j.succ) j, ← hk']
    rw [hk₂, ← add_mul] at hsum
    have hunit := isUnit_cellularIncidence_realization_face R (c.face j.castSucc) j
    rw [← hk] at hunit
    exact eq_neg_of_add_eq_zero_right ((hunit.mul_left_eq_zero).1 hsum)

/-- **The cellular boundary of a simplicial realization alternates in sign**: the incidence
coefficient of the `j`-th face of a cell is `(-1) ^ j` times that of its `0`-th face. -/
theorem cellularIncidence_realization_face_eq_neg_one_pow_mul (c : RealizationCell K (n + 1))
    (j : Fin (n + 2)) :
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j)) ((realizationCellEquiv K (n + 1)).symm c) =
      (-1) ^ (j : ℕ) * cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face 0)) ((realizationCellEquiv K (n + 1)).symm c) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [cellularIncidence_realization_face_succ, ih, Fin.val_succ, Fin.val_castSucc, pow_succ,
      mul_neg_one, neg_mul]

section Model

/-- The cell spanned by all vertices of the full complex on `n + 1` vertices. -/
private def modelCell (n : ℕ) :
    RealizationCell (⊤ : _root_.AbstractSimplicialComplex (ULift.{u} (Fin (n + 1)))) n :=
  ⟨⟨Finset.univ, Finset.univ_nonempty⟩, by simp⟩

/-- The vertex map from the full complex on `n + 1` vertices onto the vertices of an `n`-cell,
in increasing order. -/
private def modelMap (c : RealizationCell K n) :
    PreAbstractSimplicialComplex.SimplicialMap
      (⊤ : _root_.AbstractSimplicialComplex
        (ULift.{u} (Fin (n + 1)))).toPreAbstractSimplicialComplex
      K.toPreAbstractSimplicialComplex where
  toFun k := c.vertexEmbedding k.down
  map_face' _ hσ := K.isRelLowerSet_faces.mem_of_le c.1.2
    (Finset.image_subset_iff.2 fun _ _ ↦ c.vertexEmbedding_mem _) (Finset.image_nonempty.2 hσ)

/-- The vertex map onto a cell is increasing on the model cell. -/
private theorem strictMonoOn_modelMap (c : RealizationCell K n) :
    StrictMonoOn (modelMap c) (↑(modelCell.{u} n).1.1 : Set (ULift.{u} (Fin (n + 1)))) :=
  fun _ _ _ _ h ↦ c.strictMono_vertexEmbedding h

/-- The increasing vertex map onto a cell carries the model cell onto that cell. -/
private theorem modelCell_map (c : RealizationCell K n) :
    (modelCell.{u} n).map (modelMap c) (strictMonoOn_modelMap c).injOn = c := by
  apply Subtype.ext
  apply Subtype.ext
  rw [RealizationCell.map_face,
    TauCeti.PreAbstractSimplicialComplex.SimplicialMap.coe_faceOrderHom_apply]
  conv_rhs => rw [← c.image_vertexEmbedding]
  ext v
  simp [modelCell, modelMap, -RealizationCell.image_vertexEmbedding]

end Model

section Incidence

variable (n)

/-- The incidence coefficient `εₙ` of the `0`-th deleted-vertex face of the standard
`(n + 1)`-simplex in its cellular boundary, the standard simplex being the full complex on the
vertex set `ULift (Fin (n + 2))`. By
`TauCeti.cellularIncidence_realization_face_eq_neg_one_pow_mul_realizationFaceIncidence`,
the `j`-th face of any `(n + 1)`-cell of any simplicial realization has incidence coefficient
`(-1) ^ j * εₙ`. -/
def realizationFaceIncidence : R :=
  letI := realizationCWComplex (⊤ : _root_.AbstractSimplicialComplex (ULift.{u} (Fin (n + 2))))
  cellularIncidence
    (univ : Set (Realization (⊤ : _root_.AbstractSimplicialComplex (ULift.{u} (Fin (n + 2))))))
    R n ((realizationCellEquiv _ n).symm ((modelCell (n + 1)).face 0))
    ((realizationCellEquiv _ (n + 1)).symm (modelCell (n + 1)))

/-- `εₙ` is a unit of the coefficient ring. -/
theorem isUnit_realizationFaceIncidence : IsUnit (realizationFaceIncidence R n) :=
  isUnit_cellularIncidence_realization_face R _ 0

variable {R n}

/-- **The incidence numbers of a simplicial realization.** The incidence coefficient of the
`j`-th deleted-vertex face of an `(n + 1)`-cell in its cellular boundary is `(-1) ^ j * εₙ`,
where the unit `εₙ` depends only on `n` and the coefficient ring. -/
theorem cellularIncidence_realization_face_eq_neg_one_pow_mul_realizationFaceIncidence
    (c : RealizationCell K (n + 1)) (j : Fin (n + 2)) :
    letI := realizationCWComplex K
    cellularIncidence (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm (c.face j)) ((realizationCellEquiv K (n + 1)).symm c) =
      (-1) ^ (j : ℕ) * realizationFaceIncidence R n := by
  have h := cellularIncidence_realization_map_face R (modelMap c) (modelCell (n + 1))
    (strictMonoOn_modelMap c) 0
  rw [modelCell_map] at h
  rw [cellularIncidence_realization_face_eq_neg_one_pow_mul, h, realizationFaceIncidence]

end Incidence

end TauCeti
