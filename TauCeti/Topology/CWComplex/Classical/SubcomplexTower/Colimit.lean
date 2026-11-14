/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Normal
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex
public import TauCeti.Topology.CWComplex.Classical.SubcomplexTower.Basic
import TauCeti.Topology.CWComplex.Classical.Image

/-!
# CW structure and normality on colimits of CW subcomplex towers

Given `T : TauCeti.CWSubcomplexTower W newCell`, this file constructs a classical `CWComplex`
structure on any colimit cocone `hc : IsColimit c` of `T.diagram : ℕ ⥤ TopCat`
(`TauCeti.CWSubcomplexTower.cwComplexOfIsColimit`) and on `T.Union := colimit T.diagram`
(`TauCeti.CWSubcomplexTower.instCWComplexUnion`):

* **Cells and characteristic maps.** Its `n`-cells correspond to `Σ k : ℕ, newCell k n`
  (`cwComplexOfIsColimitCellEquiv`, `unionCellEquiv`), with characteristic maps pushed forward from
  birth stages along `c.ι.app k` (`Topology.IsClosedEmbedding.relCWComplex`).
* **Normality and Hausdorff separation.** Stagewise normality (`instNormalSpaceOfCWComplexUniv`) and
  closed singletons (`t1Space_of_isColimit`) yield `NormalSpace` and `T2Space` on the colimit via
  `TauCeti.TopCat.normalSpace_of_isColimit`, independently of paracompactness.
* **Closure-finiteness, stage subcomplexes, weak topology, and categorical comparison.** Every
  cell's closure equals its closed cell, lies in `range (c.ι.app k)`, and meets finitely many open
  cells (all at stages `≤ k`); each stage embeds onto a `CWComplex.Subcomplex` (`stageSubcomplex`,
  `unionStageSubcomplex`); the stage final and closed-ball weak topologies coincide
  (`iSup_coinduced_ι_eq_iSup_coinduced_map_closedBall`); reindexing by dimension yields
  `TopCat.CWComplex` (`toTopCatCWComplexOfIsColimit`, `TopCat.toTopCatCWComplex`); and
  `(const X).Union ≃ₜ X` (`constUnionHomeomorph`).

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
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell) {c : Cocone T.diagram}

/-- On the closed unit ball, `c.ι.app k` sends the characteristic map of
`T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩` to the characteristic map of `⟨m, j⟩` from its birth stage. -/
theorem ι_map_stageCellEquiv {m k : ℕ} (hmk : m ≤ k) (n : ℕ) (j : newCell m n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    c.ι.app k (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩) x) =
      c.ι.app m (map (C := (univ : Set (W m))) n (T.birthCell m n j) x) := by
  rw [← T.diagram_map_birthCell hmk n j hx, ← ConcreteCategory.comp_apply, c.w]

@[instance_reducible]
private def birthImageRelCWComplex (hc : IsColimit c) (k : ℕ) :
    RelCWComplex (range (c.ι.app k)) (∅ : Set c.pt) :=
  (T.isClosedEmbedding_ι hc k).relCWComplex image_univ (image_empty _)

private abbrev birthImageCell (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    @cell c.pt _ _ _ (T.birthImageRelCWComplex hc p.1) n :=
  ((T.isClosedEmbedding_ι hc p.1).relCWComplexCellEquiv image_univ (image_empty _) n).symm
    (T.birthCell p.1 n p.2)

private def cellPartialEquiv (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    PartialEquiv (Fin n → ℝ) c.pt :=
  @RelCWComplex.map c.pt _ _ _ (T.birthImageRelCWComplex hc p.1) n (T.birthImageCell hc n p)

private lemma coe_cellPartialEquiv (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    (T.cellPartialEquiv hc n p : (Fin n → ℝ) → c.pt) =
      fun x ↦ c.ι.app p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) := by
  dsimp only [cellPartialEquiv, birthImageRelCWComplex, birthImageCell]
  rw [(T.isClosedEmbedding_ι hc p.1).coe_map_relCWComplex image_univ (image_empty _) n,
    Equiv.apply_symm_apply]; rfl

private lemma cellPartialEquiv_image_eq_of_le (hc : IsColimit c) {n : ℕ}
    {p : Σ m : ℕ, newCell m n} {k : ℕ} (hpk : p.1 ≤ k) {s : Set (Fin n → ℝ)}
    (hs : s ⊆ closedBall 0 1) :
    T.cellPartialEquiv hc n p '' s =
      c.ι.app k '' (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) '' s) := by
  rw [T.coe_cellPartialEquiv, ← image_comp]
  exact image_congr fun _ hx ↦ (T.ι_map_stageCellEquiv (c := c) hpk n p.2 (hs hx)).symm

private lemma ι_map_eq_cellPartialEquiv (hc : IsColimit c) {k n : ℕ}
    (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    c.ι.app k (map (C := (univ : Set (W k))) n i x) =
      T.cellPartialEquiv hc n ((T.stageCellEquiv k n).symm i).1 x := by
  let q := (T.stageCellEquiv k n).symm i; rw [T.coe_cellPartialEquiv]
  exact (congrArg (fun j ↦ c.ι.app k (map n j x))
    ((T.stageCellEquiv k n).apply_symm_apply i)).symm.trans
    (T.ι_map_stageCellEquiv (c := c) q.2 n q.1.2 hx)

private lemma image_ι_image_map_eq_cellPartialEquiv (hc : IsColimit c) {k n : ℕ}
    (i : cell (univ : Set (W k)) n) {s : Set (Fin n → ℝ)} (hs : s ⊆ closedBall 0 1) :
    c.ι.app k '' (map (C := (univ : Set (W k))) n i '' s) =
      T.cellPartialEquiv hc n ((T.stageCellEquiv k n).symm i).1 '' s := by
  let q := (T.stageCellEquiv k n).symm i
  rw [T.cellPartialEquiv_image_eq_of_le hc q.2 hs, (T.stageCellEquiv k n).apply_symm_apply i]

/-- **Classical `CWComplex` structure on any colimit `c.pt` of a `CWSubcomplexTower`.**
Its `n`-cells correspond to `Σ k : ℕ, newCell k n` (`cwComplexOfIsColimitCellEquiv`), with
characteristic maps factoring through their birth stages
(`map_cwComplexOfIsColimitCellEquiv_symm_apply`). -/
@[instance_reducible]
def cwComplexOfIsColimit (hc : IsColimit c) : CWComplex (univ : Set c.pt) where
  cell n := Σ k : ℕ, newCell k n
  map n p := T.cellPartialEquiv hc n p
  source_eq n p :=
    @RelCWComplex.source_eq c.pt _ _ _ (T.birthImageRelCWComplex hc p.1) n (T.birthImageCell hc n p)
  continuousOn n p :=
    @RelCWComplex.continuousOn c.pt _ _ _ (T.birthImageRelCWComplex hc p.1) n
      (T.birthImageCell hc n p)
  continuousOn_symm n p :=
    @RelCWComplex.continuousOn_symm c.pt _ _ _ (T.birthImageRelCWComplex hc p.1) n
      (T.birthImageCell hc n p)
  pairwiseDisjoint' := by
    rintro ⟨n₁, p₁⟩ - ⟨n₂, p₂⟩ - hne; dsimp only [Function.onFun]
    rw [T.cellPartialEquiv_image_eq_of_le hc (le_max_left p₁.1 p₂.1) ball_subset_closedBall,
      T.cellPartialEquiv_image_eq_of_le hc (le_max_right p₁.1 p₂.1) ball_subset_closedBall]
    refine (disjoint_image_iff (T.isClosedEmbedding_ι hc (max p₁.1 p₂.1)).injective).2
      (disjoint_openCell_of_ne fun h ↦ hne ?_)
    obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk n₁)
      (congrArg Subtype.val ((T.stageCellEquiv _ n₁).injective (eq_of_heq hi)))
  mapsTo' n p := by
    obtain ⟨I, hI⟩ := CWComplex.mapsTo (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2)
    let emb (m : ℕ) : cell (univ : Set (W p.1)) m ↪ Σ k : ℕ, newCell k m :=
      ⟨fun i ↦ ((T.stageCellEquiv p.1 m).symm i).1,
        Subtype.val_injective.comp (T.stageCellEquiv p.1 m).symm.injective⟩
    refine ⟨fun m ↦ (I m).map (emb m), fun x hx ↦ ?_⟩
    obtain ⟨m, hmn, i, hiI, y, hyB, hyx⟩ := by simpa only [mem_iUnion, exists_prop] using hI hx
    exact mem_iUnion₂.2 ⟨m, hmn, mem_iUnion₂.2 ⟨emb m i, Finset.mem_map_of_mem _ hiI, y, hyB,
      (T.ι_map_eq_cellPartialEquiv hc i hyB).symm.trans (by rw [hyx, T.coe_cellPartialEquiv])⟩⟩
  closed' A _ hA := (TopCat.isClosed_iff_of_isColimit _ hc A).2 fun k ↦
    (CWComplex.closed (univ : Set (W k)) (c.ι.app k ⁻¹' A) (subset_univ _)).2 fun n i ↦ by
      rw [← (T.isClosedEmbedding_ι hc k).injective.preimage_image (closedCell n i),
        ← preimage_inter, closedCell, T.image_ι_image_map_eq_cellPartialEquiv hc i Subset.rfl]
      exact (hA n ((T.stageCellEquiv k n).symm i).1).preimage (c.ι.app k).hom.continuous
  union' := eq_univ_of_forall fun z ↦ by
    obtain ⟨k, y, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) z
    obtain ⟨n, i, x, hx, rfl⟩ :=
      mem_iUnion₂.1 ((CWComplex.union (C := (univ : Set (W k)))).symm ▸ mem_univ y)
    exact mem_iUnion₂.2
      ⟨n, ((T.stageCellEquiv k n).symm i).1, x, hx, (T.ι_map_eq_cellPartialEquiv hc i hx).symm⟩

/-- Equivalence identifying the `n`-cells of `T.cwComplexOfIsColimit hc` with
`Σ k : ℕ, newCell k n` without unfolding the CW structure. -/
def cwComplexOfIsColimitCellEquiv (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc; cell (univ : Set c.pt) n ≃ Σ k : ℕ, newCell k n :=
  Equiv.refl _

private lemma map_cwComplexOfIsColimitCellEquiv_symm (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      T.cellPartialEquiv hc n p := (rfl)

@[simp] lemma map_cwComplexOfIsColimitCellEquiv_symm_apply (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) (x : Fin n → ℝ) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) x =
      c.ι.app p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) :=
  congrFun (T.coe_cellPartialEquiv hc n p) x

/-- On the closed unit ball, the characteristic map of `p = ⟨m, j⟩` in `c.pt` agrees with the
characteristic map of `T.stageCellEquiv k n ⟨p, hpk⟩` in any later stage `W k` (`m ≤ k`). -/
lemma map_cwComplexOfIsColimitCellEquiv_symm_apply_of_le (hc : IsColimit c) (n : ℕ)
    (p : Σ m : ℕ, newCell m n) {k : ℕ} (hpk : p.1 ≤ k) {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := T.cwComplexOfIsColimit hc
    map (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) x =
      c.ι.app k (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) x) :=
  (T.map_cwComplexOfIsColimitCellEquiv_symm_apply hc n p x).trans
    (T.ι_map_stageCellEquiv (c := c) hpk n p.2 hx).symm

@[simp] lemma openCell_cwComplexOfIsColimitCellEquiv_symm (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    openCell (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      c.ι.app p.1 '' openCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [openCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc, T.coe_cellPartialEquiv, ← image_image]
  rfl

lemma openCell_cwComplexOfIsColimitCellEquiv_symm_of_le (hc : IsColimit c) (n : ℕ)
    (p : Σ m : ℕ, newCell m n) {k : ℕ} (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    openCell (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      c.ι.app k '' openCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc; rw [openCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc]
  exact T.cellPartialEquiv_image_eq_of_le hc hpk ball_subset_closedBall

@[simp] lemma closedCell_cwComplexOfIsColimitCellEquiv_symm (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      c.ι.app p.1 '' closedCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [closedCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc, T.coe_cellPartialEquiv,
    ← image_image]; rfl

lemma closedCell_cwComplexOfIsColimitCellEquiv_symm_of_le (hc : IsColimit c) (n : ℕ)
    (p : Σ m : ℕ, newCell m n) {k : ℕ} (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      c.ι.app k '' closedCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc; rw [closedCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc]
  exact T.cellPartialEquiv_image_eq_of_le hc hpk Subset.rfl

@[simp] lemma cellFrontier_cwComplexOfIsColimitCellEquiv_symm (hc : IsColimit c) (n : ℕ)
    (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    cellFrontier (C := (univ : Set c.pt)) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p) =
      c.ι.app p.1 '' cellFrontier (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [cellFrontier, T.map_cwComplexOfIsColimitCellEquiv_symm hc, T.coe_cellPartialEquiv,
    ← image_image]; rfl

/-- On the closed unit ball, `c.ι.app k` sends each stage characteristic map to the characteristic
map of its corresponding colimit cell. -/
theorem ι_map_eq_map (hc : IsColimit c) (k n : ℕ) (i : cell (univ : Set (W k)) n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := T.cwComplexOfIsColimit hc
    c.ι.app k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set c.pt)) n
        ((T.cwComplexOfIsColimitCellEquiv hc n).symm ((T.stageCellEquiv k n).symm i).1) x := by
  let _ := T.cwComplexOfIsColimit hc; rw [T.map_cwComplexOfIsColimitCellEquiv_symm hc]
  exact T.ι_map_eq_cellPartialEquiv hc i hx

/-- `c.ι.app k` maps each open cell of `W k` onto the open cell of its colimit cell in `c.pt`. -/
theorem image_ι_openCell (hc : IsColimit c) (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    letI := T.cwComplexOfIsColimit hc
    c.ι.app k '' openCell (C := (univ : Set (W k))) n i =
      openCell (C := (univ : Set c.pt)) n
        ((T.cwComplexOfIsColimitCellEquiv hc n).symm ((T.stageCellEquiv k n).symm i).1) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [openCell, openCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc]
  exact T.image_ι_image_map_eq_cellPartialEquiv hc i ball_subset_closedBall

/-- `c.ι.app k` maps each closed cell of `W k` onto the closed cell of its colimit cell in
`c.pt`. -/
theorem image_ι_closedCell (hc : IsColimit c) (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    letI := T.cwComplexOfIsColimit hc
    c.ι.app k '' closedCell (C := (univ : Set (W k))) n i =
      closedCell (C := (univ : Set c.pt)) n
        ((T.cwComplexOfIsColimitCellEquiv hc n).symm ((T.stageCellEquiv k n).symm i).1) := by
  let _ := T.cwComplexOfIsColimit hc
  rw [closedCell, closedCell, T.map_cwComplexOfIsColimitCellEquiv_symm hc]
  exact T.image_ι_image_map_eq_cellPartialEquiv hc i Subset.rfl

/-- Any colimit of a `CWSubcomplexTower` is a normal space. -/
theorem normalSpace_of_isColimit (hc : IsColimit c) : NormalSpace c.pt :=
  TauCeti.TopCat.normalSpace_of_isColimit (fun n ↦ T.isClosedEmbedding_diagram_map n.le_succ) hc

/-- Any colimit of a `CWSubcomplexTower` is Hausdorff. -/
theorem t2Space_of_isColimit (hc : IsColimit c) : T2Space c.pt :=
  have := T.normalSpace_of_isColimit hc; have := T.t1Space_of_isColimit hc; inferInstance

/-- In `c.pt`, the closure of every open cell equals its closed cell. -/
theorem closure_openCell_eq_closedCell (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    ∀ i : cell (univ : Set c.pt) n,
      closure (openCell (C := (univ : Set c.pt)) n i) = closedCell (C := (univ : Set c.pt)) n i :=
  letI := T.cwComplexOfIsColimit hc; letI := T.t2Space_of_isColimit hc
  fun _ ↦ RelCWComplex.closure_openCell_eq_closedCell

/-- The closure of each open cell `i` in `c.pt` lies in
`range (c.ι.app (T.cwComplexOfIsColimitCellEquiv hc n i).1)`. -/
theorem closure_openCell_subset_range_ι (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    ∀ i : cell (univ : Set c.pt) n,
      closure (openCell (C := (univ : Set c.pt)) n i) ⊆
        range (c.ι.app (T.cwComplexOfIsColimitCellEquiv hc n i).1) := by
  let _ := T.cwComplexOfIsColimit hc; intro i
  obtain ⟨p, rfl⟩ := (T.cwComplexOfIsColimitCellEquiv hc n).symm.surjective i
  rw [Equiv.apply_symm_apply, T.closure_openCell_eq_closedCell hc,
    T.closedCell_cwComplexOfIsColimitCellEquiv_symm hc]
  exact image_subset_range _ _

/-- **Stage-refined closure-finiteness:** the cell frontier of an `n`-cell `i` in `c.pt` is covered
by finitely many closed cells of strictly smaller dimension, all born at stages at most the birth
stage of `i`. -/
theorem cellFrontier_subset_finite_closedCell_le_stage (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    ∀ i : cell (univ : Set c.pt) n,
      ∃ I : ∀ m, Finset {j : cell (univ : Set c.pt) m //
          (T.cwComplexOfIsColimitCellEquiv hc m j).1 ≤
            (T.cwComplexOfIsColimitCellEquiv hc n i).1},
        cellFrontier (C := (univ : Set c.pt)) n i ⊆
          ⋃ (m < n) (j ∈ I m), closedCell (C := (univ : Set c.pt)) m j.1 := by
  let _ := T.cwComplexOfIsColimit hc; intro i
  obtain ⟨p, rfl⟩ := (T.cwComplexOfIsColimitCellEquiv hc n).symm.surjective i
  obtain ⟨J, hJ⟩ := CWComplex.cellFrontier_subset_finite_closedCell (C := (univ : Set (W p.1))) n
    (T.birthCell p.1 n p.2)
  let emb (m : ℕ) : cell (univ : Set (W p.1)) m ↪
      {j : cell (univ : Set c.pt) m // (T.cwComplexOfIsColimitCellEquiv hc m j).1 ≤
        (T.cwComplexOfIsColimitCellEquiv hc n ((T.cwComplexOfIsColimitCellEquiv hc n).symm p)).1} :=
    ⟨fun a ↦ ⟨(T.cwComplexOfIsColimitCellEquiv hc m).symm ((T.stageCellEquiv p.1 m).symm a).1,
        by simp [((T.stageCellEquiv p.1 m).symm a).2]⟩,
      fun a₁ a₂ h ↦ (T.stageCellEquiv p.1 m).symm.injective <| Subtype.ext <|
        (T.cwComplexOfIsColimitCellEquiv hc m).symm.injective (congrArg Subtype.val h)⟩
  refine ⟨fun m ↦ (J m).map (emb m), ?_⟩
  rw [T.cellFrontier_cwComplexOfIsColimitCellEquiv_symm hc]; rintro _ ⟨y, hy, rfl⟩
  obtain ⟨m, hmn, a, haJ, hya⟩ := by simpa only [mem_iUnion, exists_prop] using hJ hy
  refine mem_iUnion₂.2 ⟨m, hmn, mem_iUnion₂.2 ⟨emb m a, Finset.mem_map_of_mem _ haJ, ?_⟩⟩
  have hemb : (emb m a).1 =
      (T.cwComplexOfIsColimitCellEquiv hc m).symm ((T.stageCellEquiv p.1 m).symm a).1 := rfl
  rw [hemb, ← T.image_ι_closedCell hc]; exact mem_image_of_mem _ hya

/-- A cell's closure in `c.pt` meets only finitely many open cells of `c.pt`. -/
theorem finite_setOf_nonempty_closure_openCell_inter_openCell (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    ∀ i : cell (univ : Set c.pt) n,
      {a : Σ m : ℕ, cell (univ : Set c.pt) m |
        (closure (openCell (C := (univ : Set c.pt)) n i) ∩
          openCell (C := (univ : Set c.pt)) a.1 a.2).Nonempty}.Finite := by
  let _ := T.cwComplexOfIsColimit hc; let _ := T.t2Space_of_isColimit hc; intro i
  rw [T.closure_openCell_eq_closedCell hc]
  exact finite_setOf_nonempty_inter_openCell_of_isCompact isCompact_closedCell

/-- **The CW subcomplex of `c.pt` corresponding to stage `W k`**, with carrier `range (c.ι.app k)`
and `n`-cells `{i | (T.cwComplexOfIsColimitCellEquiv hc n i).1 ≤ k}`. -/
def stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc; CWComplex.Subcomplex (univ : Set c.pt) :=
  letI := T.cwComplexOfIsColimit hc
  { carrier := range (c.ι.app k)
    I n := {i : cell (univ : Set c.pt) n | (T.cwComplexOfIsColimitCellEquiv hc n i).1 ≤ k}
    closed' := (T.isClosedEmbedding_ι hc k).isClosed_range
    union' := by
      rw [empty_union]; ext z; simp only [mem_iUnion, mem_range]; refine ⟨?_, ?_⟩
      · rintro ⟨n, ⟨i, hpk⟩, hz⟩
        obtain ⟨p, rfl⟩ := (T.cwComplexOfIsColimitCellEquiv hc n).symm.surjective i
        rw [T.openCell_cwComplexOfIsColimitCellEquiv_symm_of_le hc n p (by simpa using hpk)] at hz
        obtain ⟨y, _, rfl⟩ := hz; exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨n, i, hyi⟩ := mem_iUnion₂.1
          ((CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (W k)))) ▸ mem_univ y)
        refine ⟨n, ⟨(T.cwComplexOfIsColimitCellEquiv hc n).symm ((T.stageCellEquiv k n).symm i).1,
          by simp [((T.stageCellEquiv k n).symm i).2]⟩, ?_⟩
        rw [← T.image_ι_openCell hc]; exact mem_image_of_mem _ hyi }

@[simp] lemma coe_stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k : Set c.pt) = range (c.ι.app k) := (rfl)

@[simp] lemma mem_stageSubcomplex_iff (hc : IsColimit c) {k : ℕ} {x : c.pt} :
    letI := T.cwComplexOfIsColimit hc
    x ∈ T.stageSubcomplex hc k ↔ x ∈ range (c.ι.app k) := Iff.rfl

@[simp] lemma stageSubcomplex_I (hc : IsColimit c) (k n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k).I n =
      {i : cell (univ : Set c.pt) n | (T.cwComplexOfIsColimitCellEquiv hc n i).1 ≤ k} := (rfl)

lemma stageSubcomplex_mono (hc : IsColimit c) :
    letI := T.cwComplexOfIsColimit hc; Monotone (T.stageSubcomplex hc) := by
  let _ := T.cwComplexOfIsColimit hc; rintro i j hij _ ⟨x, rfl⟩
  exact ⟨T.diagram.map (homOfLE hij) x, by rw [← ConcreteCategory.comp_apply, c.w]⟩

/-- Every open cell of `c.pt` meeting `closure (openCell n i)` was born at a stage at most the birth
stage of `i`. -/
theorem stage_le_of_nonempty_closure_openCell_inter (hc : IsColimit c) {n m : ℕ} :
    letI := T.cwComplexOfIsColimit hc
    ∀ {i : cell (univ : Set c.pt) n} {j : cell (univ : Set c.pt) m},
      (closure (openCell (C := (univ : Set c.pt)) n i) ∩
        openCell (C := (univ : Set c.pt)) m j).Nonempty →
      (T.cwComplexOfIsColimitCellEquiv hc m j).1 ≤
        (T.cwComplexOfIsColimitCellEquiv hc n i).1 := by
  let _ := T.cwComplexOfIsColimit hc; intro i j ⟨z, hzCl, hzO⟩; by_contra hnot
  exact ((T.stageSubcomplex hc (T.cwComplexOfIsColimitCellEquiv hc n i).1
    ).disjoint_openCell_subcomplex_of_notMem hnot).le_bot
    ⟨hzO, T.closure_openCell_subset_range_ι hc n i hzCl⟩

/-- Pulling `T.stageSubcomplex hc k` back along `c.ι.app (k + 1)` recovers `T.subcomplex k`. -/
theorem preimage_ι_succ_stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    c.ι.app (k + 1) ⁻¹' (T.stageSubcomplex hc k : Set c.pt) =
      (T.subcomplex k : Set (W (k + 1))) := by
  have hw (x : W k) : c.ι.app (k + 1) (T.step k x) = c.ι.app k x := by
    rw [← TopCat.hom_ofHom (T.step k), ← T.diagram_map_succ, ← ConcreteCategory.comp_apply, c.w]
  ext (y : W (k + 1))
  simp only [T.coe_stageSubcomplex hc, T.coe_subcomplex, diagram_obj, TopCat.coe_of, mem_preimage,
    mem_range, ← hw, (T.isClosedEmbedding_ι hc (k + 1)).injective.eq_iff]

/-- Each stage `W k` is homeomorphic via `c.ι.app k` to `T.stageSubcomplex hc k`. -/
def homeomorphStageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc; W k ≃ₜ T.stageSubcomplex hc k :=
  letI := T.cwComplexOfIsColimit hc
  ((T.isClosedEmbedding_ι hc k).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (T.coe_stageSubcomplex hc k).symm)

@[simp] lemma coe_homeomorphStageSubcomplex_apply (hc : IsColimit c) (k : ℕ) (x : W k) :
    letI := T.cwComplexOfIsColimit hc
    (T.homeomorphStageSubcomplex hc k x : c.pt) = c.ι.app k x := (rfl)

/-- Closedness in `c.pt` is equivalent to closedness of intersections with all closed cells. -/
theorem isClosed_iff_forall_isClosed_inter_closedCell (hc : IsColimit c) (A : Set c.pt) :
    letI := T.cwComplexOfIsColimit hc
    IsClosed A ↔ ∀ (n : ℕ) (i : cell (univ : Set c.pt) n),
      IsClosed (A ∩ closedCell (C := (univ : Set c.pt)) n i) :=
  letI := T.cwComplexOfIsColimit hc; letI := T.t2Space_of_isColimit hc
  CWComplex.closed (univ : Set c.pt) A (subset_univ A)

/-- Equivalence between the stage-final-topology and cellwise weak-topology closedness criteria. -/
theorem forall_isClosed_preimage_iff_forall_isClosed_inter_closedCell (hc : IsColimit c)
    (A : Set c.pt) :
    letI := T.cwComplexOfIsColimit hc
    (∀ k : ℕ, IsClosed (c.ι.app k ⁻¹' A)) ↔ ∀ (n : ℕ) (i : cell (univ : Set c.pt) n),
      IsClosed (A ∩ closedCell (C := (univ : Set c.pt)) n i) :=
  (TopCat.isClosed_iff_of_isColimit _ hc A).symm.trans
    (T.isClosed_iff_forall_isClosed_inter_closedCell hc A)

/-- The topology on `c.pt` equals the topology coinduced by all closed-ball characteristic maps. -/
theorem topologicalSpace_eq_iSup_coinduced_map_closedBall (hc : IsColimit c) :
    letI := T.cwComplexOfIsColimit hc
    c.pt.str = ⨆ (n : ℕ) (i : cell (univ : Set c.pt) n),
      TopologicalSpace.coinduced
        (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set c.pt)) n i x) inferInstance :=
  @TauCeti.topologicalSpace_eq_iSup_coinduced_map_closedBall c.pt c.pt.str
    (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

/-- **Equality of the stage final topology and the cellwise weak topology on `c.pt`.** -/
theorem iSup_coinduced_ι_eq_iSup_coinduced_map_closedBall (hc : IsColimit c) :
    letI := T.cwComplexOfIsColimit hc
    (⨆ k : ℕ, (T.diagram.obj k).str.coinduced (c.ι.app k)) =
      ⨆ (n : ℕ) (i : cell (univ : Set c.pt) n),
        TopologicalSpace.coinduced
          (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set c.pt)) n i x)
          inferInstance :=
  (TopCat.coinduced_of_isColimit c hc).symm.trans
    (T.topologicalSpace_eq_iSup_coinduced_map_closedBall hc)

/-- **Categorical `TopCat.CWComplex` structure on `c.pt`**, obtained by reindexing cells `(k, n, j)`
by dimension `n` first (`toTopCatCWComplexOfIsColimitStageReindexEquiv`). -/
abbrev toTopCatCWComplexOfIsColimit (hc : IsColimit c) : TopCat.CWComplex c.pt :=
  @TopCat.toTopCatCWComplex c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

/-- The `n`-cells attached at step `n` of `T.toTopCatCWComplexOfIsColimit hc`. -/
def toTopCatCWComplexOfIsColimitAttachCellsEquiv (hc : IsColimit c) (n : ℕ) (hn : ¬ IsMax n) :
    ((T.toTopCatCWComplexOfIsColimit hc).attachCells n hn).ι ≃ Σ k : ℕ, newCell k n :=
  (@TopCat.toTopCatCWComplexAttachCellsEquiv c.pt (T.t2Space_of_isColimit hc)
    (T.cwComplexOfIsColimit hc) n hn).trans (T.cwComplexOfIsColimitCellEquiv hc n)

lemma toTopCatCWComplexOfIsColimitAttachCellsEquiv_eq (hc : IsColimit c) (n : ℕ) (hn : ¬ IsMax n) :
    T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc n hn =
      (@TopCat.toTopCatCWComplexAttachCellsEquiv c.pt (T.t2Space_of_isColimit hc)
        (T.cwComplexOfIsColimit hc) n hn).trans (T.cwComplexOfIsColimitCellEquiv hc n) := (rfl)

/-- Dimension-indexed identification of `(T.toTopCatCWComplexOfIsColimit hc).Cells`. -/
def toTopCatCWComplexOfIsColimitCellsEquiv (hc : IsColimit c) :
    (T.toTopCatCWComplexOfIsColimit hc).Cells ≃ Σ (n : ℕ) (k : ℕ), newCell k n :=
  (@TopCat.toTopCatCWComplexCellsEquiv c.pt (T.t2Space_of_isColimit hc)
    (T.cwComplexOfIsColimit hc)).trans (Equiv.sigmaCongrRight (T.cwComplexOfIsColimitCellEquiv hc))

@[simp] lemma toTopCatCWComplexOfIsColimitCellsEquiv_apply (hc : IsColimit c)
    (γ : (T.toTopCatCWComplexOfIsColimit hc).Cells) :
    T.toTopCatCWComplexOfIsColimitCellsEquiv hc γ =
      ⟨γ.j, T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k⟩ :=
  congrArg (Equiv.sigmaCongrRight (T.cwComplexOfIsColimitCellEquiv hc))
    (@TopCat.toTopCatCWComplexCellsEquiv_apply c.pt (T.t2Space_of_isColimit hc)
      (T.cwComplexOfIsColimit hc) γ)

@[simp] lemma toTopCatCWComplexOfIsColimitCellsEquiv_symm_apply (hc : IsColimit c) (n k : ℕ)
    (j : newCell k n) :
    (T.toTopCatCWComplexOfIsColimitCellsEquiv hc).symm ⟨n, k, j⟩ =
      ⟨n, not_isMax n,
        (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc n (not_isMax n)).symm ⟨k, j⟩⟩ :=
  @TopCat.toTopCatCWComplexCellsEquiv_symm_apply c.pt (T.t2Space_of_isColimit hc)
    (T.cwComplexOfIsColimit hc) n ((T.cwComplexOfIsColimitCellEquiv hc n).symm ⟨k, j⟩)

/-- Reindexing equivalence between `(T.toTopCatCWComplexOfIsColimit hc).Cells` and stage-ordered
cells `Σ (k : ℕ) (n : ℕ), newCell k n`. -/
def toTopCatCWComplexOfIsColimitStageReindexEquiv (hc : IsColimit c) :
    (T.toTopCatCWComplexOfIsColimit hc).Cells ≃ Σ (k : ℕ) (n : ℕ), newCell k n :=
  (T.toTopCatCWComplexOfIsColimitCellsEquiv hc).trans
    ⟨fun ⟨n, k, j⟩ ↦ ⟨k, n, j⟩, fun ⟨k, n, j⟩ ↦ ⟨n, k, j⟩,
      fun ⟨_, _, _⟩ ↦ rfl, fun ⟨_, _, _⟩ ↦ rfl⟩

@[simp] lemma toTopCatCWComplexOfIsColimitStageReindexEquiv_apply (hc : IsColimit c)
    (γ : (T.toTopCatCWComplexOfIsColimit hc).Cells) :
    T.toTopCatCWComplexOfIsColimitStageReindexEquiv hc γ =
      ⟨(T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k).1, γ.j,
        (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k).2⟩ := by
  simp [toTopCatCWComplexOfIsColimitStageReindexEquiv]

@[simp] lemma toTopCatCWComplexOfIsColimitStageReindexEquiv_symm_apply (hc : IsColimit c) (k n : ℕ)
    (j : newCell k n) :
    (T.toTopCatCWComplexOfIsColimitStageReindexEquiv hc).symm ⟨k, n, j⟩ =
      ⟨n, not_isMax n,
        (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc n (not_isMax n)).symm ⟨k, j⟩⟩ := by
  simp [toTopCatCWComplexOfIsColimitStageReindexEquiv]

lemma toTopCatCWComplexOfIsColimit_cells_ι_apply (hc : IsColimit c)
    (γ : (T.toTopCatCWComplexOfIsColimit hc).Cells) (z : TopCat.disk.{u} γ.j) :
    γ.ι z =
      c.ι.app (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k).1
        (map (C := (univ : Set (W (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc
            γ.j γ.hj γ.k).1))) γ.j
          (T.birthCell (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k).1 γ.j
            (T.toTopCatCWComplexOfIsColimitAttachCellsEquiv hc γ.j γ.hj γ.k).2)
          (diskHomeomorphClosedBall γ.j z)) := by
  refine (@TopCat.toTopCatCWComplex_cells_ι_apply c.pt (T.t2Space_of_isColimit hc)
    (T.cwComplexOfIsColimit hc) γ z).trans ?_
  rw [← (T.cwComplexOfIsColimitCellEquiv hc γ.j).symm_apply_apply
    (@TopCat.toTopCatCWComplexAttachCellsEquiv c.pt (T.t2Space_of_isColimit hc)
      (T.cwComplexOfIsColimit hc) γ.j γ.hj γ.k)]
  exact T.map_cwComplexOfIsColimitCellEquiv_symm_apply hc γ.j _ _

end IsColimit

/-! ### Canonical colimit carrier `T.Union` and `instCWComplexUnion` -/

section Union

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- The canonical raw final-topology union `colimit T.diagram` in `TopCat.{u}`. -/
abbrev Union : TopCat.{u} := colimit T.diagram

/-- The canonical closed embedding `W k ⟶ T.Union` of stage `k` into the union. -/
abbrev incl (k : ℕ) : TopCat.of (W k) ⟶ T.Union := colimit.ι T.diagram k

@[simp] lemma incl_step_apply (k : ℕ) (x : W k) : T.incl (k + 1) (T.step k x) = T.incl k x := by
  rw [← TopCat.hom_ofHom (T.step k), ← T.diagram_map_succ, ← ConcreteCategory.comp_apply, colimit.w]

theorem isClosedEmbedding_incl (k : ℕ) : IsClosedEmbedding (T.incl k) :=
  T.isClosedEmbedding_ι (colimit.isColimit T.diagram) k

/-- **Classical `CWComplex` structure on `T.Union`.** Its `n`-cells correspond to
`Σ k : ℕ, newCell k n` (`unionCellEquiv`), with characteristic maps given by
`map_unionCellEquiv_symm_apply`. -/
instance instCWComplexUnion : CWComplex (univ : Set T.Union) :=
  T.cwComplexOfIsColimit (colimit.isColimit T.diagram)

lemma instCWComplexUnion_eq :
    T.instCWComplexUnion = T.cwComplexOfIsColimit (colimit.isColimit T.diagram) := (rfl)

instance instT1SpaceUnion : T1Space T.Union := T.t1Space_of_isColimit (colimit.isColimit T.diagram)

instance instNormalSpaceUnion : NormalSpace T.Union :=
  T.normalSpace_of_isColimit (colimit.isColimit T.diagram)

instance instT2SpaceUnion : T2Space T.Union := T.t2Space_of_isColimit (colimit.isColimit T.diagram)

/-- Equivalence identifying the `n`-cells of `T.Union` with `Σ k : ℕ, newCell k n`. -/
def unionCellEquiv (n : ℕ) : cell (univ : Set T.Union) n ≃ Σ k : ℕ, newCell k n :=
  T.cwComplexOfIsColimitCellEquiv (colimit.isColimit T.diagram) n

@[simp] lemma map_unionCellEquiv_symm_apply (n : ℕ) (p : Σ k : ℕ, newCell k n) (x : Fin n → ℝ) :
    map (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) x =
      T.incl p.1 (map (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x) :=
  T.map_cwComplexOfIsColimitCellEquiv_symm_apply (colimit.isColimit T.diagram) n p x

/-- On the closed unit ball, the characteristic map of `p = ⟨m, j⟩` in `T.Union` agrees with that of
`T.stageCellEquiv k n ⟨p, hpk⟩` in any later stage `W k` (`m ≤ k`). -/
lemma map_unionCellEquiv_symm_apply_of_le (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ} (hpk : p.1 ≤ k)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    map (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) x =
      T.incl k (map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) x) :=
  T.map_cwComplexOfIsColimitCellEquiv_symm_apply_of_le (colimit.isColimit T.diagram) n p hpk hx

@[simp] lemma openCell_unionCellEquiv_symm (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    openCell (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) =
      T.incl p.1 '' openCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.openCell_cwComplexOfIsColimitCellEquiv_symm (colimit.isColimit T.diagram) n p

lemma openCell_unionCellEquiv_symm_of_le (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    openCell (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) =
      T.incl k '' openCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) :=
  T.openCell_cwComplexOfIsColimitCellEquiv_symm_of_le (colimit.isColimit T.diagram) n p hpk

@[simp] lemma closedCell_unionCellEquiv_symm (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    closedCell (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) =
      T.incl p.1 '' closedCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.closedCell_cwComplexOfIsColimitCellEquiv_symm (colimit.isColimit T.diagram) n p

lemma closedCell_unionCellEquiv_symm_of_le (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    closedCell (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) =
      T.incl k '' closedCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) :=
  T.closedCell_cwComplexOfIsColimitCellEquiv_symm_of_le (colimit.isColimit T.diagram) n p hpk

@[simp] lemma cellFrontier_unionCellEquiv_symm (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    cellFrontier (C := (univ : Set T.Union)) n ((T.unionCellEquiv n).symm p) =
      T.incl p.1 '' cellFrontier (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) :=
  T.cellFrontier_cwComplexOfIsColimitCellEquiv_symm (colimit.isColimit T.diagram) n p

theorem incl_map_eq_map (k n : ℕ) (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    T.incl k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set T.Union)) n
        ((T.unionCellEquiv n).symm ((T.stageCellEquiv k n).symm i).1) x :=
  T.ι_map_eq_map (colimit.isColimit T.diagram) k n i hx

theorem image_incl_openCell (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    T.incl k '' openCell (C := (univ : Set (W k))) n i =
      openCell (C := (univ : Set T.Union)) n
        ((T.unionCellEquiv n).symm ((T.stageCellEquiv k n).symm i).1) :=
  T.image_ι_openCell (colimit.isColimit T.diagram) k n i

theorem image_incl_closedCell (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    T.incl k '' closedCell (C := (univ : Set (W k))) n i =
      closedCell (C := (univ : Set T.Union)) n
        ((T.unionCellEquiv n).symm ((T.stageCellEquiv k n).symm i).1) :=
  T.image_ι_closedCell (colimit.isColimit T.diagram) k n i

lemma closure_openCell_subset_range_incl (n : ℕ) (i : cell (univ : Set T.Union) n) :
    closure (openCell (C := (univ : Set T.Union)) n i) ⊆
      range (T.incl (T.unionCellEquiv n i).1) :=
  T.closure_openCell_subset_range_ι (colimit.isColimit T.diagram) n i

/-- Stage-refined closure-finiteness on `T.Union`. -/
theorem cellFrontier_subset_finite_closedCell_unionCellEquiv_fst_le (n : ℕ)
    (i : cell (univ : Set T.Union) n) :
    ∃ I : ∀ m, Finset {j : cell (univ : Set T.Union) m //
        (T.unionCellEquiv m j).1 ≤ (T.unionCellEquiv n i).1},
      cellFrontier (C := (univ : Set T.Union)) n i ⊆
        ⋃ (m < n) (j ∈ I m), closedCell (C := (univ : Set T.Union)) m j.1 :=
  T.cellFrontier_subset_finite_closedCell_le_stage (colimit.isColimit T.diagram) n i

/-- Every open cell of `T.Union` meeting `closure (openCell n i)` was born at a stage at most the
birth stage of `i`. -/
theorem unionCellEquiv_fst_le_of_nonempty_closure_openCell_inter {n m : ℕ}
    {i : cell (univ : Set T.Union) n} {j : cell (univ : Set T.Union) m}
    (h : (closure (openCell (C := (univ : Set T.Union)) n i) ∩
      openCell (C := (univ : Set T.Union)) m j).Nonempty) :
    (T.unionCellEquiv m j).1 ≤ (T.unionCellEquiv n i).1 :=
  T.stage_le_of_nonempty_closure_openCell_inter (colimit.isColimit T.diagram) h

/-- The specified `CWComplex.Subcomplex` of `T.Union` onto which stage `W k` embeds. -/
def unionStageSubcomplex (k : ℕ) : CWComplex.Subcomplex (univ : Set T.Union) :=
  T.stageSubcomplex (colimit.isColimit T.diagram) k

@[simp] lemma coe_unionStageSubcomplex (k : ℕ) :
    (T.unionStageSubcomplex k : Set T.Union) = range (T.incl k) :=
  T.coe_stageSubcomplex (colimit.isColimit T.diagram) k

@[simp] lemma mem_unionStageSubcomplex_iff {k : ℕ} {x : T.Union} :
    x ∈ T.unionStageSubcomplex k ↔ x ∈ range (T.incl k) := Iff.rfl

@[simp] lemma unionStageSubcomplex_I (k n : ℕ) :
    (T.unionStageSubcomplex k).I n =
      {i : cell (univ : Set T.Union) n | (T.unionCellEquiv n i).1 ≤ k} :=
  T.stageSubcomplex_I (colimit.isColimit T.diagram) k n

lemma unionStageSubcomplex_mono : Monotone T.unionStageSubcomplex :=
  T.stageSubcomplex_mono (colimit.isColimit T.diagram)

/-- Pulling `T.unionStageSubcomplex k` back along `T.incl (k + 1)` recovers `T.subcomplex k`. -/
theorem preimage_incl_succ_unionStageSubcomplex (k : ℕ) :
    T.incl (k + 1) ⁻¹' (T.unionStageSubcomplex k : Set T.Union) =
      (T.subcomplex k : Set (W (k + 1))) :=
  T.preimage_ι_succ_stageSubcomplex (colimit.isColimit T.diagram) k

/-- Homeomorphism of `W k` onto its CW subcomplex `T.unionStageSubcomplex k` in `T.Union`. -/
def homeomorphUnionStageSubcomplex (k : ℕ) : W k ≃ₜ T.unionStageSubcomplex k :=
  T.homeomorphStageSubcomplex (colimit.isColimit T.diagram) k

@[simp] lemma coe_homeomorphUnionStageSubcomplex_apply (k : ℕ) (x : W k) :
    (T.homeomorphUnionStageSubcomplex k x : T.Union) = T.incl k x :=
  T.coe_homeomorphStageSubcomplex_apply (colimit.isColimit T.diagram) k x

/-- Equality of the stage final topology and the cellwise weak topology on `T.Union`. -/
theorem iSup_coinduced_incl_eq_iSup_coinduced_map_closedBall :
    (⨆ k : ℕ, (T.diagram.obj k).str.coinduced (T.incl k)) =
      ⨆ (n : ℕ) (i : cell (univ : Set T.Union) n),
        TopologicalSpace.coinduced
          (fun x : closedBall (0 : Fin n → ℝ) 1 ↦ map (C := (univ : Set T.Union)) n i x)
          inferInstance :=
  T.iSup_coinduced_ι_eq_iSup_coinduced_map_closedBall (colimit.isColimit T.diagram)

/-- The `n`-cells attached at step `n` of `T.Union.toTopCatCWComplex`. -/
def toTopCatCWComplexAttachCellsEquiv (n : ℕ) (hn : ¬ IsMax n) :
    (T.Union.toTopCatCWComplex.attachCells n hn).ι ≃ Σ k : ℕ, newCell k n :=
  T.toTopCatCWComplexOfIsColimitAttachCellsEquiv (colimit.isColimit T.diagram) n hn

lemma toTopCatCWComplexAttachCellsEquiv_eq (n : ℕ) (hn : ¬ IsMax n) :
    T.toTopCatCWComplexAttachCellsEquiv n hn =
      (T.Union.toTopCatCWComplexAttachCellsEquiv n hn).trans (T.unionCellEquiv n) := (rfl)

/-- Dimension-indexed identification of `T.Union.toTopCatCWComplex.Cells`. -/
def toTopCatCWComplexCellsEquiv :
    T.Union.toTopCatCWComplex.Cells ≃ Σ (n : ℕ) (k : ℕ), newCell k n :=
  T.toTopCatCWComplexOfIsColimitCellsEquiv (colimit.isColimit T.diagram)

@[simp] lemma toTopCatCWComplexCellsEquiv_apply (γ : T.Union.toTopCatCWComplex.Cells) :
    T.toTopCatCWComplexCellsEquiv γ = ⟨γ.j, T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k⟩ :=
  T.toTopCatCWComplexOfIsColimitCellsEquiv_apply (colimit.isColimit T.diagram) γ

@[simp] lemma toTopCatCWComplexCellsEquiv_symm_apply (n k : ℕ) (j : newCell k n) :
    T.toTopCatCWComplexCellsEquiv.symm ⟨n, k, j⟩ =
      ⟨n, not_isMax n, (T.toTopCatCWComplexAttachCellsEquiv n (not_isMax n)).symm ⟨k, j⟩⟩ :=
  T.toTopCatCWComplexOfIsColimitCellsEquiv_symm_apply (colimit.isColimit T.diagram) n k j

/-- Reindexing equivalence between `T.Union.toTopCatCWComplex.Cells` and stage-ordered cells. -/
def toTopCatCWComplexStageReindexEquiv :
    T.Union.toTopCatCWComplex.Cells ≃ Σ (k : ℕ) (n : ℕ), newCell k n :=
  T.toTopCatCWComplexOfIsColimitStageReindexEquiv (colimit.isColimit T.diagram)

@[simp] lemma toTopCatCWComplexStageReindexEquiv_apply (γ : T.Union.toTopCatCWComplex.Cells) :
    T.toTopCatCWComplexStageReindexEquiv γ =
      ⟨(T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).1, γ.j,
        (T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).2⟩ :=
  T.toTopCatCWComplexOfIsColimitStageReindexEquiv_apply (colimit.isColimit T.diagram) γ

@[simp] lemma toTopCatCWComplexStageReindexEquiv_symm_apply (k n : ℕ) (j : newCell k n) :
    T.toTopCatCWComplexStageReindexEquiv.symm ⟨k, n, j⟩ =
      ⟨n, not_isMax n, (T.toTopCatCWComplexAttachCellsEquiv n (not_isMax n)).symm ⟨k, j⟩⟩ :=
  T.toTopCatCWComplexOfIsColimitStageReindexEquiv_symm_apply (colimit.isColimit T.diagram) k n j

lemma toTopCatCWComplex_cells_ι_apply (γ : T.Union.toTopCatCWComplex.Cells)
    (z : TopCat.disk.{u} γ.j) :
    γ.ι z =
      T.incl (T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).1
        (map (C := (univ : Set (W (T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).1))) γ.j
          (T.birthCell (T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).1 γ.j
            (T.toTopCatCWComplexAttachCellsEquiv γ.j γ.hj γ.k).2)
          (diskHomeomorphClosedBall γ.j z)) :=
  T.toTopCatCWComplexOfIsColimit_cells_ι_apply (colimit.isColimit T.diagram) γ z

/-- The union of the constant tower `CWSubcomplexTower.const X` is homeomorphic to `X`. -/
def constUnionHomeomorph (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] :
    (const X).Union ≃ₜ X :=
  let T := const X
  let cX : Cocone T.diagram :=
    ⟨TopCat.of X, NatTrans.ofSequence (fun _ ↦ 𝟙 (TopCat.of X)) fun k ↦ by
      rw [T.diagram_map_succ, const_step]; rfl⟩
  let hcX : IsColimit cX :=
    { desc s := s.ι.app 0
      fac s k := (Category.id_comp (s.ι.app 0)).trans <| by
        induction k with
        | zero => rfl
        | succ k ih =>
          have hw := s.w (homOfLE (Nat.le_add_right k 1))
          rw [T.diagram_map_succ, const_step, TopCat.ofHom_id] at hw
          exact ih.trans (hw.symm.trans (Category.id_comp (s.ι.app (k + 1))))
      uniq s m hm := (Category.id_comp m).symm.trans (hm 0) }
  TopCat.homeoOfIso (colimit.isoColimitCocone ⟨cX, hcX⟩)

@[simp] lemma constUnionHomeomorph_incl_apply (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (k : ℕ) (x : X) :
    constUnionHomeomorph X ((const X).incl k x) = x := by
  dsimp only [constUnionHomeomorph, TopCat.homeoOfIso_apply]
  exact (ConcreteCategory.comp_apply ((const X).incl k) _ x).symm.trans
    (ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom (F := (const X).diagram) _ k) x)

@[simp] lemma constUnionHomeomorph_symm_apply (X : Type u) [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] (x : X) :
    (constUnionHomeomorph X).symm x = (const X).incl 0 x :=
  (constUnionHomeomorph X).toEquiv.symm_apply_eq.2 (constUnionHomeomorph_incl_apply X 0 x).symm

end Union

end TauCeti.CWSubcomplexTower
