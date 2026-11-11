/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Normal
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex
public import TauCeti.Topology.CWComplex.Classical.SubcomplexTower.Basic
import TauCeti.Topology.CWComplex.Classical.OpenCells

/-!
# CW structure and normality on colimits of CW subcomplex towers

Given a sequential tower `T : TauCeti.CWSubcomplexTower W newCell` of closed CW subcomplex
embeddings, this file constructs a classical `CWComplex` structure both on any colimit cocone
`hc : IsColimit c` of `T.diagram : ℕ ⥤ TopCat` (`TauCeti.CWSubcomplexTower.cwComplexOfIsColimit`)
and on the canonical colimit `T.Union := colimit T.diagram`
(`TauCeti.CWSubcomplexTower.cwComplexUnion`):

* **Cell indexing and characteristic maps.** Its `n`-cells are definitionally
  `Σ k : ℕ, newCell k n`, including `newCell 0 n` for `W 0`, and the characteristic map of `⟨k, j⟩`
  is the composition of the birth-stage characteristic map in `W k` with the colimit inclusion.
* **Normality and Hausdorff separation.** Each stage `W k` is normal
  (`TauCeti.instNormalSpaceOfCWComplexUniv`) and singletons in the colimit are closed by the stage
  final topology (`TauCeti.CWSubcomplexTower.t1Space_of_isColimit`), so sequential-colimit normality
  along closed embeddings (`TauCeti.TopCat.normalSpace_of_isColimit`) yields `NormalSpace` and
  `T2Space` on the union independently of paracompactness.
* **Closure-finiteness and stage subcomplexes.** Every cell's closure equals its closed cell, lies
  in the image of its birth stage `W k`, and meets only finitely many open cells (all born at
  stages `≤ k`). Each stage `W k` embeds onto a `CWComplex.Subcomplex` (`stageSubcomplex`,
  `unionStageSubcomplex`) whose `n`-cells are those born at stages `≤ k`.
* **Final topology vs. cellwise weak topology and categorical comparison.** The stage final topology
  coincides with the cellwise weak topology coinduced by closed-ball characteristic maps
  (`iSup_coinduced_stage_eq_iSup_coinduced_closedCell`), and reindexing cells `(k, n, j)` by
  dimension `n` yields a categorical `TopCat.CWComplex` (`toTopCatCWComplexOfIsColimit`,
  `toTopCatCWComplex`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.1, A.2, and A.3.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti.CWSubcomplexTower

/-! ### Classical `CWComplex` structure and properties on any colimit cocone -/

section IsColimit

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- A cell's closure in its birth stage `W k` meets only finitely many open cells of `W k`. -/
theorem finite_inter_openCell_birthStage (k n : ℕ) (j : newCell k n) :
    {a : Σ m : ℕ, cell (univ : Set (W k)) m |
      (closedCell (C := (univ : Set (W k))) n (T.birthCell k n j) ∩
        openCell (C := (univ : Set (W k))) a.1 a.2).Nonempty}.Finite :=
  finite_setOf_nonempty_inter_openCell_of_isCompact isCompact_closedCell

variable {c : Cocone T.diagram}

/-- On the closed unit ball, the cocone map from stage `k` sends the characteristic map of
`T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩` to the characteristic map of `⟨m, j⟩` from its birth stage
`m`. -/
theorem ι_stageCellEquiv_map_eq {m k : ℕ} (hmk : m ≤ k) (n : ℕ) (j : newCell m n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    c.ι.app k (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩) x) =
      c.ι.app m (map (C := (univ : Set (W m))) n (T.birthCell m n j) x) := by
  rw [← T.diagram_map_birthCell hmk n j hx, ← ConcreteCategory.comp_apply, c.w]

private def cellMap (c : Cocone T.diagram) (n : ℕ) (p : Σ k : ℕ, newCell k n) (x : Fin n → ℝ) :
    c.pt :=
  c.ι.app p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x)

private lemma isEmbedding_cellMap (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    IsEmbedding ((ball (0 : Fin n → ℝ) 1).domRestrict (T.cellMap c n p)) := by
  have heq : (ball (0 : Fin n → ℝ) 1).domRestrict (T.cellMap c n p) =
      (c.ι.app p.1 ∘ Subtype.val) ∘
        openCellHomeomorph (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
    ext x
    simp [cellMap, Function.comp_apply]
  rw [heq]
  exact ((T.isClosedEmbedding_ι hc p.1).isEmbedding.comp IsEmbedding.subtypeVal).comp
    (openCellHomeomorph (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2)).isEmbedding

/-- Characteristic `PartialEquiv` of the `n`-cell `p` on `c.pt`, sending `x` to
`c.ι.app p.1 (map n (T.birthCell p.1 n p.2) x)` with source `ball 0 1`. -/
protected def cellPartialEquiv (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    PartialEquiv (Fin n → ℝ) c.pt :=
  Set.InjOn.toPartialEquiv (T.cellMap c n p) (ball 0 1) fun x hx y hy h ↦
    congrArg Subtype.val
      ((T.isEmbedding_cellMap hc n p).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

protected lemma cellPartialEquiv_source (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    (T.cellPartialEquiv hc n p).source = ball 0 1 := by
  rfl

protected lemma coe_cellPartialEquiv (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    (T.cellPartialEquiv hc n p : (Fin n → ℝ) → c.pt) =
      fun x ↦ c.ι.app p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) := by
  rfl

protected lemma continuousOn_cellPartialEquiv_symm (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    ContinuousOn (T.cellPartialEquiv hc n p).symm (T.cellPartialEquiv hc n p).target := by
  let e := T.cellPartialEquiv hc n p
  let g : e.target → ball (0 : Fin n → ℝ) 1 := fun y ↦ ⟨e.symm y, e.map_target y.property⟩
  have hg : Continuous g := (T.isEmbedding_cellMap hc n p).continuous_iff.2 (by
    convert continuous_subtype_val using 1
    funext y
    exact e.right_inv y.property)
  exact continuousOn_iff_continuous_domRestrict.2 (continuous_subtype_val.comp hg)

/-- For any subset `s ⊆ closedBall 0 1` and stage `k ≥ p.1`, the image of `s` under
`T.cellPartialEquiv hc n p` equals the `c.ι.app k`-image of the `s`-image under the corresponding
stage-`k` characteristic map. -/
protected lemma cellPartialEquiv_image_eq_of_le (hc : IsColimit c) {n : ℕ}
    {p : Σ m : ℕ, newCell m n} {k : ℕ} (hpk : p.1 ≤ k) {s : Set (Fin n → ℝ)}
    (hs : s ⊆ closedBall 0 1) :
    T.cellPartialEquiv hc n p '' s =
      c.ι.app k '' (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) '' s) := by
  rw [T.coe_cellPartialEquiv, ← image_comp]
  exact image_congr fun _ hx ↦ (T.ι_stageCellEquiv_map_eq (c := c) hpk n p.2 (hs hx)).symm

/-- **Classical `CWComplex` structure on any colimit `c.pt` of a `CWSubcomplexTower`.**
The body is exposed so that `cell (univ : Set c.pt) n` is `Σ k : ℕ, newCell k n` by definition,
while the characteristic `PartialEquiv` internals remain encapsulated in `T.cellPartialEquiv`. -/
@[expose, instance_reducible]
def cwComplexOfIsColimit (hc : IsColimit c) : CWComplex (univ : Set c.pt) where
  cell n := Σ k : ℕ, newCell k n
  map n p := T.cellPartialEquiv hc n p
  source_eq n p := T.cellPartialEquiv_source hc n p
  continuousOn n p := by
    rw [T.coe_cellPartialEquiv]
    exact (c.ι.app p.1).hom.continuous.comp_continuousOn
      (continuousOn (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2))
  continuousOn_symm n p := T.continuousOn_cellPartialEquiv_symm hc n p
  pairwiseDisjoint' := by
    rintro ⟨n₁, p₁⟩ - ⟨n₂, p₂⟩ - hne
    let K := max p₁.1 p₂.1
    have hk₁ : p₁.1 ≤ K := le_max_left _ _
    have hk₂ : p₂.1 ≤ K := le_max_right _ _
    dsimp only [Function.onFun]
    rw [T.cellPartialEquiv_image_eq_of_le hc hk₁ ball_subset_closedBall,
      T.cellPartialEquiv_image_eq_of_le hc hk₂ ball_subset_closedBall]
    refine (disjoint_image_iff (T.isClosedEmbedding_ι hc K).injective).2
      (disjoint_openCell_of_ne fun h ↦ hne ?_)
    obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk n₁)
      (congrArg Subtype.val ((T.stageCellEquiv K n₁).injective (eq_of_heq hi)))
  mapsTo' n p := by
    obtain ⟨I, hI⟩ := CWComplex.mapsTo (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2)
    let emb (m : ℕ) : cell (univ : Set (W p.1)) m ↪ Σ k : ℕ, newCell k m :=
      ⟨fun i ↦ ((T.stageCellEquiv p.1 m).symm i).1,
        Subtype.val_injective.comp (T.stageCellEquiv p.1 m).symm.injective⟩
    refine ⟨fun m ↦ (I m).map (emb m), fun x hx ↦ ?_⟩
    have hx' := hI hx
    simp only [mem_iUnion, exists_prop] at hx' ⊢
    obtain ⟨m, hmn, i, hiI, y, hyB, hyx⟩ := hx'
    refine ⟨m, hmn, emb m i, Finset.mem_map_of_mem (emb m) hiI, y, hyB, ?_⟩
    let q := (T.stageCellEquiv p.1 m).symm i
    have hiq : T.stageCellEquiv p.1 m q = i := (T.stageCellEquiv p.1 m).apply_symm_apply i
    rw [T.coe_cellPartialEquiv, T.coe_cellPartialEquiv]
    exact (T.ι_stageCellEquiv_map_eq (c := c) q.2 m q.1.2 hyB).symm.trans (by rw [hiq, hyx])
  closed' A _ hA := by
    refine (TopCat.isClosed_iff_of_isColimit _ hc A).2 fun k ↦ ?_
    refine (CWComplex.closed (univ : Set (W k)) (c.ι.app k ⁻¹' A) (subset_univ _)).2 fun n i ↦ ?_
    let q := (T.stageCellEquiv k n).symm i
    have hiq : T.stageCellEquiv k n q = i := (T.stageCellEquiv k n).apply_symm_apply i
    have hcell : c.ι.app k '' closedCell (C := (univ : Set (W k))) n i =
        T.cellPartialEquiv hc n q.1 '' closedBall 0 1 := by
      rw [T.cellPartialEquiv_image_eq_of_le hc q.2 Subset.rfl, hiq]
      rfl
    have heq : (c.ι.app k ⁻¹' A) ∩ closedCell (C := (univ : Set (W k))) n i =
        (c.ι.app k ⁻¹' (A ∩ T.cellPartialEquiv hc n q.1 '' closedBall 0 1)) ∩
          closedCell (C := (univ : Set (W k))) n i := by
      rw [← hcell]
      ext y
      exact ⟨fun ⟨hyA, hyC⟩ ↦ ⟨⟨hyA, mem_image_of_mem _ hyC⟩, hyC⟩,
        fun ⟨⟨hyA, _⟩, hyC⟩ ↦ ⟨hyA, hyC⟩⟩
    rw [heq]
    exact ((hA n q.1).preimage (c.ι.app k).hom.continuous).inter isClosed_closedCell
  union' := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨k, y, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) z
    have hy : y ∈ ⋃ (n : ℕ) (i : cell (univ : Set (W k)) n),
        closedCell (C := (univ : Set (W k))) n i := by
      rw [CWComplex.union]
      exact mem_univ y
    obtain ⟨n, i, x, hx, rfl⟩ := mem_iUnion₂.1 hy
    let q := (T.stageCellEquiv k n).symm i
    have hiq : T.stageCellEquiv k n q = i := (T.stageCellEquiv k n).apply_symm_apply i
    refine mem_iUnion₂.2 ⟨n, q.1, x, hx, ?_⟩
    rw [T.coe_cellPartialEquiv]
    exact (T.ι_stageCellEquiv_map_eq (c := c) q.2 n q.1.2 hx).symm.trans (by rw [hiq]; rfl)

/-- Equivalence identifying the `n`-cells of `T.cwComplexOfIsColimit hc` with
`Σ k : ℕ, newCell k n` without unfolding the CW structure. -/
def cwComplexOfIsColimitCellEquiv (hc : IsColimit c) (n : ℕ) :
    (T.cwComplexOfIsColimit hc).cell n ≃ Σ k : ℕ, newCell k n :=
  Equiv.refl _

lemma cwComplexOfIsColimit_cell (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    cell (univ : Set c.pt) n = (Σ k : ℕ, newCell k n) :=
  (rfl)

lemma cwComplexOfIsColimit_map (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n p = T.cellPartialEquiv hc n p :=
  (rfl)

lemma cwComplexOfIsColimit_map_apply (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n)
    (x : Fin n → ℝ) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n p x =
      c.ι.app p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) :=
  congrFun (T.coe_cellPartialEquiv hc n p) x

/-- On the closed unit ball, the characteristic map of `p = ⟨m, j⟩` in `c.pt` agrees with the
characteristic map of `T.stageCellEquiv k n ⟨p, hpk⟩` in any later stage `W k` (`m ≤ k`). -/
lemma map_eq_ι_stageCellEquiv (hc : IsColimit c) (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n p x =
      c.ι.app k (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) x) :=
  (T.cwComplexOfIsColimit_map_apply hc n p x).trans
    (T.ι_stageCellEquiv_map_eq (c := c) hpk n p.2 hx).symm

lemma openCell_eq_image_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    openCell (C := (univ : Set c.pt)) n p =
      c.ι.app p.1 '' openCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [openCell, T.cwComplexOfIsColimit_map hc, T.coe_cellPartialEquiv, ← image_image]
  rfl

lemma openCell_eq_image_ι_of_le (hc : IsColimit c) (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    openCell (C := (univ : Set c.pt)) n p =
      c.ι.app k '' openCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [openCell, T.cwComplexOfIsColimit_map hc]
  exact T.cellPartialEquiv_image_eq_of_le hc hpk ball_subset_closedBall

lemma closedCell_eq_image_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n p =
      c.ι.app p.1 '' closedCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [closedCell, T.cwComplexOfIsColimit_map hc, T.coe_cellPartialEquiv, ← image_image]
  rfl

lemma closedCell_eq_image_ι_of_le (hc : IsColimit c) (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n p =
      c.ι.app k '' closedCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [closedCell, T.cwComplexOfIsColimit_map hc]
  exact T.cellPartialEquiv_image_eq_of_le hc hpk Subset.rfl

lemma cellFrontier_eq_image_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    cellFrontier (C := (univ : Set c.pt)) n p =
      c.ι.app p.1 '' cellFrontier (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [cellFrontier, T.cwComplexOfIsColimit_map hc, T.coe_cellPartialEquiv, ← image_image]
  rfl

/-- Each closed-ball characteristic map into `c.pt` is a closed map, factoring through the
Hausdorff birth stage `W k` followed by the closed embedding `c.ι.app k`. -/
lemma isClosedMap_closedBall_map (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    IsClosedMap (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set c.pt)) n p x) := by
  let _ := T.cwComplexOfIsColimit hc
  have _ : CompactSpace (closedBall (0 : Fin n → ℝ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have hf_cont : Continuous
      (fun x : closedBall (0 : Fin n → ℝ) 1 ↦
        map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) :=
    continuous_map_closedBall (C := (univ : Set (W p.1))) (T.birthCell p.1 n p.2)
  simp_rw [T.cwComplexOfIsColimit_map_apply hc]
  exact (T.isClosedEmbedding_ι hc p.1).isClosedMap.comp hf_cont.isClosedMap

/-- **The colimit of a `CWSubcomplexTower` is a normal space:** each stage `W k` is normal
(`TauCeti.instNormalSpaceOfCWComplexUniv`) and the stage inclusions are closed embeddings. -/
theorem normalSpace_of_isColimit (hc : IsColimit c) : NormalSpace c.pt :=
  TauCeti.TopCat.normalSpace_of_isColimit (fun n ↦ T.isClosedEmbedding_diagram_map n.le_succ) hc

/-- **The colimit of a `CWSubcomplexTower` is Hausdorff**, combining normality with closed
singletons from the stage final topology. -/
theorem t2Space_of_isColimit (hc : IsColimit c) : T2Space c.pt := by
  let _ := T.normalSpace_of_isColimit hc
  let _ := T.t1Space_of_isColimit hc
  infer_instance

/-- In `c.pt`, the closure of every open cell equals its closed cell. -/
theorem closure_openCell_eq_closedCell (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    closure (openCell (C := (univ : Set c.pt)) n p) = closedCell (C := (univ : Set c.pt)) n p := by
  let _ := T.cwComplexOfIsColimit hc
  let _ := T.t2Space_of_isColimit hc
  exact RelCWComplex.closure_openCell_eq_closedCell

/-- Every cell's closure in `c.pt` is the image of its birth-stage closed cell in `W k`, and in
particular lies inside its birth stage `range (c.ι.app k)`. -/
theorem closure_openCell_subset_range_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    closure (openCell (C := (univ : Set c.pt)) n p) ⊆ range (c.ι.app p.1) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [T.closure_openCell_eq_closedCell hc, T.closedCell_eq_image_ι hc]
  exact image_subset_range _ _

/-- **Stage-refined closure-finiteness:** the cell frontier of `p = ⟨k, j⟩` in `c.pt` is covered by
finitely many closed cells of strictly smaller dimension, all born at stages `≤ k`. -/
theorem cellFrontier_subset_finite_closedCell_le_stage (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    ∃ I : ∀ m, Finset {q : Σ l : ℕ, newCell l m // q.1 ≤ p.1},
      cellFrontier (C := (univ : Set c.pt)) n p ⊆
        ⋃ (m < n) (q ∈ I m), closedCell (C := (univ : Set c.pt)) m q.1 := by
  let _ := T.cwComplexOfIsColimit hc
  obtain ⟨J, hJ⟩ :=
    CWComplex.cellFrontier_subset_finite_closedCell (C := (univ : Set (W p.1))) n
      (T.birthCell p.1 n p.2)
  refine ⟨fun m ↦ (J m).map (T.stageCellEquiv p.1 m).symm.toEmbedding, ?_⟩
  rw [T.cellFrontier_eq_image_ι hc]
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hJ hy
  simp only [mem_iUnion, exists_prop] at hy' ⊢
  obtain ⟨m, hmn, i, hiJ, hyi⟩ := hy'
  let q := (T.stageCellEquiv p.1 m).symm i
  have hiq : T.stageCellEquiv p.1 m q = i := (T.stageCellEquiv p.1 m).apply_symm_apply i
  refine ⟨m, hmn, q, Finset.mem_map_of_mem _ hiJ, ?_⟩
  rw [T.closedCell_eq_image_ι_of_le hc m q.1 q.2, hiq]
  exact mem_image_of_mem _ hyi

/-- Every open cell of `c.pt` meeting `closure (openCell n p)` was born at a stage `≤ p.1` (hence
already lies in `W p.1`). -/
theorem stage_le_of_nonempty_closure_openCell_inter (hc : IsColimit c) {n m : ℕ}
    {p : Σ k : ℕ, newCell k n} {q : Σ l : ℕ, newCell l m}
    (h : letI := T.cwComplexOfIsColimit hc
      (closure (openCell (C := (univ : Set c.pt)) n p) ∩
        openCell (C := (univ : Set c.pt)) m q).Nonempty) :
    q.1 ≤ p.1 := by
  let _ := T.cwComplexOfIsColimit hc
  rcases q with ⟨lq, jq⟩
  by_contra hnot
  have hlt : p.1 < lq := Nat.gt_of_not_le hnot
  obtain ⟨z, hzCl, hzO⟩ := h
  have hzR : z ∈ range (c.ι.app p.1) := T.closure_openCell_subset_range_ι hc n p hzCl
  obtain ⟨y₀, rfl⟩ := hzR
  -- Push `y₀` to stage `p.1 + d` and then one step to `lq = (p.1 + d) + 1`, where `jq` is new.
  obtain ⟨d, rfl⟩ : ∃ d, lq = p.1 + d + 1 := ⟨lq - (p.1 + 1), by omega⟩
  rw [T.openCell_eq_image_ι hc, T.birthCell_succ] at hzO
  obtain ⟨y₁, hy₁, hy⟩ := hzO
  have hmap_eq : T.diagram.map (homOfLE hlt.le) y₀ = y₁ := by
    apply (T.isClosedEmbedding_ι hc (p.1 + d + 1)).injective
    rw [← ConcreteCategory.comp_apply, c.w]
    exact hy.symm
  have hp_le : p.1 ≤ p.1 + d := Nat.le_add_right p.1 d
  have hy₁_range : y₁ ∈ (T.subcomplex (p.1 + d) : Set (W (p.1 + d + 1))) := by
    rw [T.coe_subcomplex]
    refine ⟨T.diagram.map (homOfLE hp_le) y₀, ?_⟩
    rw [← TopCat.hom_ofHom (T.step (p.1 + d)), ← T.diagram_map_succ,
      ← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
    exact hmap_eq
  exact ((T.subcomplex (p.1 + d)).disjoint_openCell_subcomplex_of_notMem
    (T.newCellEquiv (p.1 + d) m jq).2).le_bot ⟨hy₁, hy₁_range⟩

/-- A cell's closure in `c.pt` meets only finitely many open cells of `c.pt`. -/
theorem finite_inter_openCell_of_closure_openCell (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    {a : Σ m : ℕ, Σ l : ℕ, newCell l m |
      (closure (openCell (C := (univ : Set c.pt)) n p) ∩
        openCell (C := (univ : Set c.pt)) a.1 a.2).Nonempty}.Finite := by
  let _ := T.cwComplexOfIsColimit hc
  let _ := T.t2Space_of_isColimit hc
  rw [T.closure_openCell_eq_closedCell hc]
  exact finite_setOf_nonempty_inter_openCell_of_isCompact (C := (univ : Set c.pt))
    isCompact_closedCell

/-- **The CW subcomplex of `c.pt` corresponding to stage `W k`**, with carrier `range (c.ι.app k)`
and `n`-cells `{p : Σ m, newCell m n | p.1 ≤ k}` (`coe_stageSubcomplex`, `stageSubcomplex_I`). -/
def stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    CWComplex.Subcomplex (univ : Set c.pt) :=
  letI := T.cwComplexOfIsColimit hc
  { carrier := range (c.ι.app k)
    I n := {p : Σ m : ℕ, newCell m n | p.1 ≤ k}
    closed' := (T.isClosedEmbedding_ι hc k).isClosed_range
    union' := by
      rw [empty_union]
      ext z
      simp only [mem_iUnion, mem_range]
      refine ⟨?_, ?_⟩
      · rintro ⟨n, ⟨p, hpk⟩, hz⟩
        rw [T.openCell_eq_image_ι_of_le hc n p hpk] at hz
        obtain ⟨y, _, rfl⟩ := hz
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        have hy : y ∈ ⋃ (n : ℕ) (i : cell (univ : Set (W k)) n),
            openCell (C := (univ : Set (W k))) n i := by
          rw [CWComplex.iUnion_openCell_eq_complex]
          exact mem_univ y
        obtain ⟨n, i, hyi⟩ := mem_iUnion₂.1 hy
        let q := (T.stageCellEquiv k n).symm i
        have hiq : T.stageCellEquiv k n q = i := (T.stageCellEquiv k n).apply_symm_apply i
        refine ⟨n, q, ?_⟩
        rw [T.openCell_eq_image_ι_of_le hc n q.1 q.2, hiq]
        exact mem_image_of_mem _ hyi }

@[simp]
lemma coe_stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k : Set c.pt) = range (c.ι.app k) :=
  (rfl)

@[simp]
lemma stageSubcomplex_I (hc : IsColimit c) (k n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k).I n = {p : Σ m : ℕ, newCell m n | p.1 ≤ k} :=
  (rfl)

lemma stageSubcomplex_mono (hc : IsColimit c) {i j : ℕ} (hij : i ≤ j) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc i : Set c.pt) ⊆ T.stageSubcomplex hc j := by
  rw [T.coe_stageSubcomplex hc, T.coe_stageSubcomplex hc]
  rintro _ ⟨x, rfl⟩
  exact ⟨T.diagram.map (homOfLE hij) x, by rw [← ConcreteCategory.comp_apply, c.w]⟩

/-- Pulling `T.stageSubcomplex hc k` back along `c.ι.app (k + 1)` recovers the specified CW
subcomplex `T.subcomplex k` in `W (k + 1)`. -/
theorem preimage_ι_succ_stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    c.ι.app (k + 1) ⁻¹' (T.stageSubcomplex hc k : Set c.pt) =
      (T.subcomplex k : Set (W (k + 1))) := by
  rw [T.coe_stageSubcomplex hc, T.coe_subcomplex]
  ext y
  simp only [mem_preimage, mem_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (T.isClosedEmbedding_ι hc (k + 1)).injective ?_⟩
    have hw : c.ι.app (k + 1) (T.step k x) = c.ι.app k x := by
      rw [← TopCat.hom_ofHom (T.step k), ← T.diagram_map_succ, ← ConcreteCategory.comp_apply, c.w]
    exact hw.trans hx
  · rintro ⟨x, rfl⟩
    exact ⟨x, by
      rw [← TopCat.hom_ofHom (T.step k), ← T.diagram_map_succ, ← ConcreteCategory.comp_apply, c.w]⟩

/-- Each stage `W k` is homeomorphic via `c.ι.app k` to its subcomplex `T.stageSubcomplex hc k` in
`c.pt`. -/
def homeomorphStageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    W k ≃ₜ T.stageSubcomplex hc k :=
  letI := T.cwComplexOfIsColimit hc
  ((T.isClosedEmbedding_ι hc k).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (T.coe_stageSubcomplex hc k).symm)

lemma coe_homeomorphStageSubcomplex_apply (hc : IsColimit c) (k : ℕ) (x : W k) :
    letI := T.cwComplexOfIsColimit hc
    (T.homeomorphStageSubcomplex hc k x : c.pt) = c.ι.app k x :=
  (rfl)

/-- Closedness of a subset of `c.pt` in the stage final topology is equivalent to closedness of its
intersection with every closed cell. -/
theorem isClosed_iff_forall_closedCell (hc : IsColimit c) (A : Set c.pt) :
    letI := T.cwComplexOfIsColimit hc
    IsClosed A ↔
      ∀ (n : ℕ) (p : Σ k : ℕ, newCell k n),
        IsClosed (A ∩ closedCell (C := (univ : Set c.pt)) n p) := by
  let _ := T.cwComplexOfIsColimit hc
  let _ := T.t2Space_of_isColimit hc
  exact CWComplex.closed (univ : Set c.pt) A (subset_univ A)

/-- Equivalence between the stage-final-topology closedness criterion and the cellwise
weak-topology closedness criterion on `c.pt`. -/
theorem forall_isClosed_preimage_iff_forall_isClosed_inter_closedCell (hc : IsColimit c)
    (A : Set c.pt) :
    letI := T.cwComplexOfIsColimit hc
    (∀ k : ℕ, IsClosed (c.ι.app k ⁻¹' A)) ↔
      ∀ (n : ℕ) (p : Σ k : ℕ, newCell k n),
        IsClosed (A ∩ closedCell (C := (univ : Set c.pt)) n p) :=
  (TopCat.isClosed_iff_of_isColimit _ hc A).symm.trans (T.isClosed_iff_forall_closedCell hc A)

/-- The topology on `c.pt` equals the cellwise weak topology coinduced by all closed-ball
characteristic maps. -/
theorem topologicalSpace_eq_iSup_coinduced_closedCell (hc : IsColimit c) :
    letI := T.cwComplexOfIsColimit hc
    c.pt.str =
      ⨆ (n : ℕ) (p : Σ k : ℕ, newCell k n),
        TopologicalSpace.coinduced
          (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set c.pt)) n p x)
          inferInstance := by
  let _ := T.cwComplexOfIsColimit hc
  refine TopologicalSpace.ext_iff.2 fun U ↦ ?_
  simp only [isOpen_iSup_iff, isOpen_coinduced, ← isClosed_compl_iff, ← preimage_compl]
  rw [T.isClosed_iff_forall_closedCell hc Uᶜ]
  refine forall₂_congr fun n p ↦ ?_
  let φ : closedBall (0 : Fin n → ℝ) 1 → c.pt := fun x ↦ map (C := (univ : Set c.pt)) n p x
  have hφ_cont : Continuous φ := continuous_map_closedBall (C := (univ : Set c.pt)) p
  have hφ_closed : IsClosedMap φ := T.isClosedMap_closedBall_map hc n p
  have hrange : range φ = closedCell (C := (univ : Set c.pt)) n p := by
    ext z
    simp [φ, closedCell]
  -- Fold `φ` inside `IsClosed (_ ⁻¹' Uᶜ)` on the right-hand side, where `φ` is a local `let`.
  change _ ↔ IsClosed (φ ⁻¹' Uᶜ)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hpre : φ ⁻¹' Uᶜ = φ ⁻¹' (Uᶜ ∩ closedCell (C := (univ : Set c.pt)) n p) := by
      rw [← hrange]
      ext x
      exact ⟨fun hx ↦ ⟨hx, mem_range_self x⟩, fun hx ↦ hx.1⟩
    rw [hpre]
    exact h.preimage hφ_cont
  · have himg : φ '' (φ ⁻¹' Uᶜ) = Uᶜ ∩ closedCell (C := (univ : Set c.pt)) n p := by
      rw [image_preimage_eq_inter_range, hrange]
    rw [← himg]
    exact hφ_closed _ h

/-- **Equality of the stage final topology and the cellwise weak topology on `c.pt`.** -/
theorem iSup_coinduced_stage_eq_iSup_coinduced_closedCell (hc : IsColimit c) :
    letI := T.cwComplexOfIsColimit hc
    (⨆ k : ℕ, (T.diagram.obj k).str.coinduced (c.ι.app k)) =
      ⨆ (n : ℕ) (p : Σ k : ℕ, newCell k n),
        TopologicalSpace.coinduced
          (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set c.pt)) n p x)
          inferInstance :=
  (TopCat.coinduced_of_isColimit c hc).symm.trans
    (T.topologicalSpace_eq_iSup_coinduced_closedCell hc)

/-- **Categorical `TopCat.CWComplex` structure on `c.pt`**, obtained after reindexing the tower's
cells `(k, n, j)` by dimension `n` first. The body is exposed so that the `n`-th space and cell
types agree by definition with those of `TopCat.toTopCatCWComplex`. -/
@[expose] def toTopCatCWComplexOfIsColimit (hc : IsColimit c) : TopCat.CWComplex c.pt :=
  @TopCat.toTopCatCWComplex c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

lemma toTopCatCWComplexOfIsColimit_obj (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    letI := T.t2Space_of_isColimit hc
    (T.toTopCatCWComplexOfIsColimit hc).F.obj n = skeletonObj (univ : Set c.pt) n :=
  (rfl)

/-- Dimension-indexed identification of the cells of `T.toTopCatCWComplexOfIsColimit hc` with
`Σ (n : ℕ) (k : ℕ), newCell k n`. -/
def toTopCatCWComplexOfIsColimitCellsEquiv (hc : IsColimit c) :
    (T.toTopCatCWComplexOfIsColimit hc).Cells ≃ Σ (n : ℕ) (k : ℕ), newCell k n :=
  @TopCat.toTopCatCWComplexCellsEquiv c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

/-- Reindexing equivalence between the cells of `T.toTopCatCWComplexOfIsColimit hc` (grouped by
dimension `n`) and the stage-ordered cells `Σ (k : ℕ) (n : ℕ), newCell k n` of the tower. -/
def toTopCatCWComplexOfIsColimitStageReindexEquiv (hc : IsColimit c) :
    (T.toTopCatCWComplexOfIsColimit hc).Cells ≃ Σ (k : ℕ) (n : ℕ), newCell k n :=
  (T.toTopCatCWComplexOfIsColimitCellsEquiv hc).trans
    { toFun := fun ⟨n, k, j⟩ ↦ ⟨k, n, j⟩
      invFun := fun ⟨k, n, j⟩ ↦ ⟨n, k, j⟩
      left_inv := fun ⟨_, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, _⟩ ↦ rfl }

@[simp]
lemma toTopCatCWComplexOfIsColimit_cells_ι_apply (hc : IsColimit c)
    (γ : (T.toTopCatCWComplexOfIsColimit hc).Cells) (z : TopCat.disk.{u} γ.j) :
    γ.ι z =
      c.ι.app γ.k.1
        (map (C := (univ : Set (W γ.k.1))) γ.j (T.birthCell γ.k.1 γ.j γ.k.2)
          (diskHomeomorphClosedBall γ.j z)) :=
  @TopCat.toTopCatCWComplex_cells_ι_apply c.pt (T.t2Space_of_isColimit hc)
    (T.cwComplexOfIsColimit hc) γ z

end IsColimit

/-! ### Canonical colimit carrier `T.Union` and `cwComplexUnion` -/

section Union

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- The canonical raw final-topology union `colimit T.diagram` in `TopCat.{u}`. -/
abbrev Union : TopCat.{u} :=
  colimit T.diagram

/-- The canonical closed embedding `W k ⟶ T.Union` of stage `k` into the union. -/
abbrev incl (k : ℕ) : TopCat.of (W k) ⟶ T.Union :=
  colimit.ι T.diagram k

@[simp]
lemma incl_step_apply (k : ℕ) (x : W k) :
    T.incl (k + 1) (T.step k x) = T.incl k x := by
  rw [← TopCat.hom_ofHom (T.step k), ← T.diagram_map_succ, ← ConcreteCategory.comp_apply,
    colimit.w]

theorem isClosedEmbedding_incl (k : ℕ) : IsClosedEmbedding (T.incl k) :=
  T.isClosedEmbedding_ι (colimit.isColimit T.diagram) k

/-- **Classical `CWComplex` structure on the raw final-topology union `T.Union` of a sequential
tower of CW subcomplexes.** The body is exposed so that `cell (univ : Set T.Union) n` is
`Σ k : ℕ, newCell k n` by definition. -/
@[expose, instance_reducible]
def cwComplexUnion : CWComplex (univ : Set T.Union) :=
  T.cwComplexOfIsColimit (colimit.isColimit T.diagram)

instance instCWComplexUnion : CWComplex (univ : Set T.Union) :=
  T.cwComplexUnion

instance instT1SpaceUnion : T1Space T.Union :=
  T.t1Space_of_isColimit (colimit.isColimit T.diagram)

instance instNormalSpaceUnion : NormalSpace T.Union :=
  T.normalSpace_of_isColimit (colimit.isColimit T.diagram)

instance instT2SpaceUnion : T2Space T.Union :=
  T.t2Space_of_isColimit (colimit.isColimit T.diagram)

/-- Equivalence identifying the `n`-cells of `T.Union` with `Σ k : ℕ, newCell k n` without
unfolding the CW structure. -/
def unionCellEquiv (n : ℕ) :
    cell (univ : Set T.Union) n ≃ Σ k : ℕ, newCell k n :=
  Equiv.refl _

@[simp]
lemma union_cell (n : ℕ) :
    cell (univ : Set T.Union) n = (Σ k : ℕ, newCell k n) :=
  (rfl)

@[simp]
lemma union_map_apply (n : ℕ) (p : Σ k : ℕ, newCell k n) (x : Fin n → ℝ) :
    map (C := (univ : Set T.Union)) n p x =
      T.incl p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) :=
  T.cwComplexOfIsColimit_map_apply (colimit.isColimit T.diagram) n p x

lemma union_openCell_eq (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    openCell (C := (univ : Set T.Union)) n p =
      T.incl p.1 '' openCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.openCell_eq_image_ι (colimit.isColimit T.diagram) n p

lemma union_closedCell_eq (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    closedCell (C := (univ : Set T.Union)) n p =
      T.incl p.1 '' closedCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.closedCell_eq_image_ι (colimit.isColimit T.diagram) n p

lemma union_cellFrontier_eq (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    cellFrontier (C := (univ : Set T.Union)) n p =
      T.incl p.1 '' cellFrontier (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.cellFrontier_eq_image_ι (colimit.isColimit T.diagram) n p

lemma union_closure_openCell_subset_range_incl (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    closure (openCell (C := (univ : Set T.Union)) n p) ⊆ range (T.incl p.1) :=
  T.closure_openCell_subset_range_ι (colimit.isColimit T.diagram) n p

/-- The specified `CWComplex.Subcomplex` of `T.Union` onto which stage `W k` embeds, characterized
by `coe_unionStageSubcomplex` and `unionStageSubcomplex_I`. -/
def unionStageSubcomplex (k : ℕ) : CWComplex.Subcomplex (univ : Set T.Union) :=
  T.stageSubcomplex (colimit.isColimit T.diagram) k

@[simp]
lemma coe_unionStageSubcomplex (k : ℕ) :
    (T.unionStageSubcomplex k : Set T.Union) = range (T.incl k) :=
  T.coe_stageSubcomplex (colimit.isColimit T.diagram) k

@[simp]
lemma unionStageSubcomplex_I (k n : ℕ) :
    (T.unionStageSubcomplex k).I n = {p : Σ m : ℕ, newCell m n | p.1 ≤ k} :=
  T.stageSubcomplex_I (colimit.isColimit T.diagram) k n

/-- Homeomorphism of `W k` onto its CW subcomplex `T.unionStageSubcomplex k` in `T.Union`. -/
def homeomorphUnionStageSubcomplex (k : ℕ) :
    W k ≃ₜ T.unionStageSubcomplex k :=
  T.homeomorphStageSubcomplex (colimit.isColimit T.diagram) k

@[simp]
lemma coe_homeomorphUnionStageSubcomplex_apply (k : ℕ) (x : W k) :
    (T.homeomorphUnionStageSubcomplex k x : T.Union) = T.incl k x :=
  T.coe_homeomorphStageSubcomplex_apply (colimit.isColimit T.diagram) k x

/-- Categorical `TopCat.CWComplex` structure on `T.Union` after reindexing cells by dimension. -/
@[expose] def toTopCatCWComplex : TopCat.CWComplex T.Union :=
  T.toTopCatCWComplexOfIsColimit (colimit.isColimit T.diagram)

end Union

end TauCeti.CWSubcomplexTower
