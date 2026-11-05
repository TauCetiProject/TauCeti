/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.CWComplex.Classical.CompactSupport
public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.Normal
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
import TauCeti.Topology.CWComplex.Classical.OpenCells

/-!
# CW structure on the union of a sequential tower of CW subcomplexes

Let `W₀ → W₁ → W₂ → ⋯` be a sequence of Hausdorff classical CW complexes
(`CWComplex (univ : Set _)`) in which each `step k : W k → W (k + 1)` is a closed embedding onto a
specified CW subcomplex `subcomplex k` of `W (k + 1)`, equipped with compatible cell labels and
characteristic maps on the closed unit ball. Crucially, the new cells added from `W k` to
`W (k + 1)` may have **arbitrary dimensions in any stage order**: stage `k + 1` is allowed to
attach lower-dimensional cells after stage `k` has already attached higher-dimensional ones.

This file packages such data as `TauCeti.CWSubcomplexTower W newCell` and constructs a native
classical `CWComplex` structure on the raw final-topology union — both for an arbitrary colimit
cocone `hc : IsColimit c` of `T.diagram : ℕ ⥤ TopCat`
(`TauCeti.CWSubcomplexTower.cwComplexOfIsColimit`) and on the canonical colimit carrier
`T.Union := colimit T.diagram` (`TauCeti.cwSubcomplexTowerUnion`):

* **Cell indexing and characteristic maps.** Its `n`-cells are definitionally
  `Σ k : ℕ, newCell k n`, including `newCell 0 n` for `W 0`, and the characteristic map of `⟨k, j⟩`
  is the composition of the birth-stage characteristic map in `W k` with the colimit inclusion
  `c.ι.app k`.
* **Stage subcomplexes.** Each `c.ι.app k : W k → c.pt` is a closed embedding onto a specified
  `CWComplex.Subcomplex` (`TauCeti.CWSubcomplexTower.stageSubcomplex`) whose `n`-cells are those
  born at stages `≤ k`.
* **Closure-finiteness and birth-stage support.** Every cell's closure equals its closed cell, lies
  in the image of its birth stage `W k`, and meets only finitely many open cells (all born at
  stages `≤ k`, hence already in `W k`).
* **Final topology vs. cellwise weak topology.** Closedness in the colimit final topology coincides
  with closedness in every closed cell, and the supremum of stage-coinduced topologies equals the
  supremum of closed-ball-coinduced topologies
  (`TauCeti.CWSubcomplexTower.iSup_coinduced_stage_eq_iSup_coinduced_closedCell`).
* **Normality and Hausdorff separation.** Each stage `W k` is normal
  (`TauCeti.instNormalSpaceOfCWComplexUniv`) and singletons in the colimit are closed by the stage
  final topology (`TauCeti.TopCat.t1Space_of_isColimit`), so sequential-colimit normality along
  closed embeddings (`TauCeti.TopCat.normalSpace_of_isColimit`) yields `NormalSpace` and `T2Space`
  on the union independently of paracompactness.
* **Categorical comparison and cellular naturality.** Reindexing the cells `(k, n, j)` by dimension
  `n` yields a categorical `TopCat.CWComplex` (`TauCeti.CWSubcomplexTower.toTopCatCWComplex`), and
  stagewise cellular morphisms of towers (`TauCeti.CWSubcomplexTower.Hom`) induce cellular maps on
  the union commuting with skeletal restrictions.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.1, A.2, and A.3.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

/-! ### Sequential towers of CW subcomplex inclusions -/

/-- A sequential tower `W 0 → W 1 → W 2 → ⋯` of Hausdorff classical CW complexes on `Set.univ`
along closed embeddings onto specified CW subcomplexes, with compatible cell labels and
characteristic maps on the closed unit ball. Here `newCell k n` indexes the `n`-cells born at stage
`k` (including `k = 0` for all `n`-cells of `W 0`); new cells at stage `k + 1` may have arbitrary
dimensions regardless of the dimensions already present in `W k`. -/
structure CWSubcomplexTower (W : ℕ → Type u)
    [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
    (newCell : ℕ → ℕ → Type u) where
  /-- The stage inclusion `W k → W (k + 1)`. -/
  step (k : ℕ) : C(W k, W (k + 1))
  /-- Each stage inclusion is a closed embedding. -/
  isClosedEmbedding_step (k : ℕ) : IsClosedEmbedding (step k)
  /-- The specified CW subcomplex of `W (k + 1)` onto which `W k` embeds. -/
  subcomplex (k : ℕ) : CWComplex.Subcomplex (univ : Set (W (k + 1)))
  /-- The carrier of `subcomplex k` is the image of `step k`. -/
  coe_subcomplex (k : ℕ) : (subcomplex k : Set (W (k + 1))) = range (step k)
  /-- Indexing of the `n`-cells of `W 0` by `newCell 0 n`. -/
  cellZeroEquiv (n : ℕ) : newCell 0 n ≃ cell (univ : Set (W 0)) n
  /-- Identification of the `n`-cells of `W k` with the `n`-cells of `subcomplex k` in
  `W (k + 1)`. -/
  oldCellEquiv (k n : ℕ) : cell (univ : Set (W k)) n ≃ ↥((subcomplex k).I n)
  /-- Identification of `newCell (k + 1) n` with the `n`-cells of `W (k + 1)` outside
  `subcomplex k`. -/
  newCellEquiv (k n : ℕ) : newCell (k + 1) n ≃ ↥((subcomplex k).I n)ᶜ
  /-- On the closed unit ball, `step k` carries each characteristic map of `W k` onto the
  corresponding characteristic map of `subcomplex k` in `W (k + 1)`. -/
  map_oldCell (k n : ℕ) (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    step k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set (W (k + 1)))) n (oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n) x

namespace CWSubcomplexTower

section ExtAndConstructors

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u}

/-- Two `CWSubcomplexTower`s with the same stage maps have equal stage subcomplexes. -/
theorem subcomplex_eq_of_step_eq {T₁ T₂ : CWSubcomplexTower W newCell}
    (hstep : T₁.step = T₂.step) (k : ℕ) : T₁.subcomplex k = T₂.subcomplex k :=
  SetLike.coe_injective ((T₁.coe_subcomplex k).trans (by rw [hstep, ← T₂.coe_subcomplex k]))

/-- Two `CWSubcomplexTower`s are equal if they have the same stage maps, initial cell labels, and
new-cell labels; the subcomplexes and old-cell equivalences are uniquely determined by open-cell
disjointness at `0 ∈ ball 0 1`. -/
@[ext]
theorem ext {T₁ T₂ : CWSubcomplexTower W newCell}
    (hstep : ∀ k, T₁.step k = T₂.step k)
    (hzero : ∀ n, T₁.cellZeroEquiv n = T₂.cellZeroEquiv n)
    (hnew : ∀ k n (j : newCell (k + 1) n),
      (T₁.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n) =
        (T₂.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n)) :
    T₁ = T₂ := by
  have hstep' : T₁.step = T₂.step := funext hstep
  have hsub : T₁.subcomplex = T₂.subcomplex := funext (subcomplex_eq_of_step_eq hstep')
  cases T₁ with
  | mk step₁ emb₁ sub₁ coe₁ zero₁ old₁ new₁ map₁ =>
    cases T₂ with
    | mk step₂ emb₂ sub₂ coe₂ zero₂ old₂ new₂ map₂ =>
      dsimp at hstep' hsub hzero hnew
      subst hstep' hsub
      congr
      · exact funext hzero
      · funext k n
        ext i
        have hz : (0 : Fin n → ℝ) ∈ closedBall 0 1 := mem_closedBall_self zero_le_one
        have h0 : map (C := (univ : Set (W (k + 1)))) n (old₁ k n i : cell _ n) 0 =
            map (C := (univ : Set (W (k + 1)))) n (old₂ k n i : cell _ n) 0 :=
          (map₁ k n i hz).symm.trans (map₂ k n i hz)
        have hmem₁ := map_zero_mem_openCell (C := (univ : Set (W (k + 1)))) n (old₁ k n i)
        have hmem₂ : map (C := (univ : Set (W (k + 1)))) n (old₁ k n i : cell _ n) 0 ∈
            openCell (C := (univ : Set (W (k + 1)))) n (old₂ k n i : cell _ n) := by
          rw [h0]
          exact map_zero_mem_openCell (C := (univ : Set (W (k + 1)))) n (old₂ k n i)
        by_contra hne
        have hne' : (⟨n, (old₁ k n i : cell _ n)⟩ : Σ m, cell (univ : Set (W (k + 1))) m) ≠
            ⟨n, (old₂ k n i : cell _ n)⟩ :=
          fun h ↦ hne (eq_of_heq (Sigma.mk.inj h).2)
        exact (disjoint_openCell_of_ne hne').le_bot ⟨hmem₁, hmem₂⟩
      · funext k n
        ext j
        exact hnew k n j

/-- Canonical new-cell indexing determined directly by a sequence of CW subcomplexes `E k` of
`W (k + 1)`: stage `0` uses `cell (univ : Set (W 0)) n`, and stage `k + 1` uses `↥((E k).I n)ᶜ`. -/
def StageNewCell (W : ℕ → Type u)
    [∀ k, TopologicalSpace (W k)] [∀ k, CWComplex (univ : Set (W k))]
    (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1)))) : ℕ → ℕ → Type u
  | 0, n => cell (univ : Set (W 0)) n
  | k + 1, n => ↥((E k).I n)ᶜ

/-- Construct a `CWSubcomplexTower` directly from stage subcomplexes `E k` and old-cell
equivalences, using `StageNewCell W E` as the new-cell indexing. -/
def ofSubcomplex
    (step : ∀ k, C(W k, W (k + 1)))
    (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
    (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1))))
    (coe_E : ∀ k, (E k : Set (W (k + 1))) = range (step k))
    (oldCellEquiv : ∀ k n, cell (univ : Set (W k)) n ≃ ↥((E k).I n))
    (map_oldCell : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      step k (map (C := (univ : Set (W k))) n i x) =
        map (C := (univ : Set (W (k + 1)))) n (oldCellEquiv k n i : cell _ n) x) :
    CWSubcomplexTower W (StageNewCell W E) where
  step := step
  isClosedEmbedding_step := isClosedEmbedding_step
  subcomplex := E
  coe_subcomplex := coe_E
  cellZeroEquiv _ := Equiv.refl _
  oldCellEquiv := oldCellEquiv
  newCellEquiv _ _ := Equiv.refl _
  map_oldCell := map_oldCell

/-- Construct a `CWSubcomplexTower` from sum decompositions
`cellSumEquiv k n : cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n`
compatible with `step k` on old cells; the stage subcomplexes `subcomplex k` with carrier
`range (step k)` are synthesized automatically. -/
def ofCellSum
    (step : ∀ k, C(W k, W (k + 1)))
    (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
    (cellZeroEquiv : ∀ n, newCell 0 n ≃ cell (univ : Set (W 0)) n)
    (cellSumEquiv : ∀ k n,
      cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n)
    (map_inl : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      step k (map (C := (univ : Set (W k))) n i x) =
        map (C := (univ : Set (W (k + 1)))) n (cellSumEquiv k n (Sum.inl i)) x) :
    CWSubcomplexTower W newCell :=
  let I (k n : ℕ) : Set (cell (univ : Set (W (k + 1))) n) :=
    range fun i ↦ cellSumEquiv k n (Sum.inl i)
  have hunion (k : ℕ) :
      (∅ : Set (W (k + 1))) ∪ ⋃ (n : ℕ) (j : I k n),
        openCell (C := (univ : Set (W (k + 1)))) n j.1 = range (step k) := by
    rw [empty_union]
    ext y
    simp only [mem_iUnion, mem_range]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, ⟨_, ⟨i, rfl⟩⟩, z, hz, rfl⟩
      exact ⟨map (C := (univ : Set (W k))) n i z, map_inl k n i (ball_subset_closedBall hz)⟩
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ (n : ℕ) (i : cell (univ : Set (W k)) n),
          openCell (C := (univ : Set (W k))) n i := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        exact mem_univ x
      obtain ⟨n, i, z, hz, rfl⟩ := by simpa only [mem_iUnion, mem_image] using hx
      exact ⟨n, ⟨_, i, rfl⟩, z, hz, (map_inl k n i (ball_subset_closedBall hz)).symm⟩
  let sub (k : ℕ) : CWComplex.Subcomplex (univ : Set (W (k + 1))) :=
    { carrier := range (step k)
      I := I k
      closed' := (isClosedEmbedding_step k).isClosed_range
      union' := hunion k }
  have hinl_inj (k n : ℕ) : Function.Injective (fun i ↦ cellSumEquiv k n (Sum.inl i)) :=
    (cellSumEquiv k n).injective.comp Sum.inl_injective
  have hinr_notMem (k n : ℕ) (j : newCell (k + 1) n) :
      cellSumEquiv k n (Sum.inr j) ∉ I k n := by
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr ((cellSumEquiv k n).injective hi)
  { step := step
    isClosedEmbedding_step := isClosedEmbedding_step
    subcomplex := sub
    coe_subcomplex _ := rfl
    cellZeroEquiv := cellZeroEquiv
    oldCellEquiv k n := Equiv.ofInjective (fun i ↦ cellSumEquiv k n (Sum.inl i)) (hinl_inj k n)
    newCellEquiv k n :=
      { toFun := fun j ↦ ⟨cellSumEquiv k n (Sum.inr j), hinr_notMem k n j⟩
        invFun := fun c ↦ match h : (cellSumEquiv k n).symm c.1 with
          | Sum.inr j => j
          | Sum.inl i => False.elim <| c.2 ⟨i, by
              have := congrArg (cellSumEquiv k n) h
              simpa using this.symm⟩
        left_inv := fun j ↦ by
          dsimp
          split
          · rename_i j' h
            have h' := (cellSumEquiv k n).symm_apply_apply (Sum.inr j)
            exact Sum.inr.inj (h'.symm.trans h).symm
          · rename_i i h
            have h' := (cellSumEquiv k n).symm_apply_apply (Sum.inr j)
            exact False.elim (Sum.inl_ne_inr (h'.symm.trans h).symm)
        right_inv := fun ⟨c, hc⟩ ↦ by
          apply Subtype.ext
          dsimp
          split
          · rename_i j h
            have := congrArg (cellSumEquiv k n) h
            simpa using this.symm
          · rename_i i h
            exact False.elim (hc ⟨i, by
              have := congrArg (cellSumEquiv k n) h
              simpa using this.symm⟩) }
    map_oldCell := map_inl }

end ExtAndConstructors

/-! ### Stagewise cell equivalences and sequential diagram -/

section StageMachinery

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u}

/-- The `n`-cell in its birth stage `W k` corresponding to `j : newCell k n`. -/
def birthCell (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), newCell k n → cell (univ : Set (W k)) n
  | 0, n, j => T.cellZeroEquiv n j
  | k + 1, n, j => (T.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n)

@[simp]
lemma birthCell_zero (T : CWSubcomplexTower W newCell) (n : ℕ) (j : newCell 0 n) :
    T.birthCell 0 n j = T.cellZeroEquiv n j :=
  (rfl)

@[simp]
lemma birthCell_succ (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell (k + 1) n) :
    T.birthCell (k + 1) n j = (T.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n) :=
  (rfl)

lemma birthCell_injective (T : CWSubcomplexTower W newCell) (k n : ℕ) :
    Function.Injective (T.birthCell k n) := by
  cases k with
  | zero => exact (T.cellZeroEquiv n).injective
  | succ k => exact Subtype.val_injective.comp (T.newCellEquiv k n).injective

/-- Decomposition of the `n`-cells of `W (k + 1)` into old cells from `W k` and new cells from
`newCell (k + 1) n`. -/
def stepCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ) :
    cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n :=
  open Classical in
  (Equiv.sumCongr (T.oldCellEquiv k n) (T.newCellEquiv k n)).trans
    (Equiv.Set.sumCompl ((T.subcomplex k).I n))

@[simp]
lemma stepCellEquiv_inl (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (i : cell (univ : Set (W k)) n) :
    T.stepCellEquiv k n (Sum.inl i) = (T.oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n) := by
  simp [stepCellEquiv]

@[simp]
lemma stepCellEquiv_inr (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell (k + 1) n) :
    T.stepCellEquiv k n (Sum.inr j) = T.birthCell (k + 1) n j := by
  simp [stepCellEquiv]

private def stageIndexZeroEquiv (n : ℕ) :
    {p : Σ m : ℕ, newCell m n // p.1 ≤ 0} ≃ newCell 0 n where
  toFun p := Nat.eq_zero_of_le_zero p.2 ▸ p.1.2
  invFun j := ⟨⟨0, j⟩, le_rfl⟩
  left_inv := fun ⟨⟨m, j⟩, hm⟩ ↦ by
    obtain rfl := Nat.eq_zero_of_le_zero hm
    rfl
  right_inv _ := rfl

private def stageIndexSuccEquiv (k n : ℕ) :
    {p : Σ m : ℕ, newCell m n // p.1 ≤ k + 1} ≃
      {p : Σ m : ℕ, newCell m n // p.1 ≤ k} ⊕ newCell (k + 1) n where
  toFun p :=
    if hp : p.1.1 ≤ k then
      Sum.inl ⟨p.1, hp⟩
    else
      Sum.inr (Nat.le_antisymm p.2 (Nat.gt_of_not_le hp) ▸ p.1.2)
  invFun
    | Sum.inl p => ⟨p.1, Nat.le_succ_of_le p.2⟩
    | Sum.inr j => ⟨⟨k + 1, j⟩, le_rfl⟩
  left_inv := fun ⟨⟨m, j⟩, hm⟩ ↦ by
    by_cases hmk : m ≤ k
    · simp [hmk]
    · have hmeq : m = k + 1 := Nat.le_antisymm hm (Nat.gt_of_not_le hmk)
      subst hmeq
      simp
  right_inv
    | Sum.inl ⟨p, hp⟩ => by simp [hp]
    | Sum.inr j => by simp

/-- Equivalence between all `n`-cells born at stages `≤ k` and the `n`-cells of `W k`. -/
def stageCellEquiv (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), {p : Σ m : ℕ, newCell m n // p.1 ≤ k} ≃ cell (univ : Set (W k)) n
  | 0, n => (stageIndexZeroEquiv n).trans (T.cellZeroEquiv n)
  | k + 1, n =>
      (stageIndexSuccEquiv k n).trans
        (((stageCellEquiv T k n).sumCongr (Equiv.refl _)).trans (T.stepCellEquiv k n))

@[simp]
lemma stageCellEquiv_birth (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell k n) :
    T.stageCellEquiv k n ⟨⟨k, j⟩, le_rfl⟩ = T.birthCell k n j := by
  cases k with
  | zero => rfl
  | succ k => simp [stageCellEquiv, stageIndexSuccEquiv]

lemma stageCellEquiv_succ_of_le (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (p : Σ m : ℕ, newCell m n) (hp : p.1 ≤ k) :
    T.stageCellEquiv (k + 1) n ⟨p, Nat.le_succ_of_le hp⟩ =
      (T.oldCellEquiv k n (T.stageCellEquiv k n ⟨p, hp⟩) : cell (univ : Set (W (k + 1))) n) := by
  simp [stageCellEquiv, stageIndexSuccEquiv, hp]

@[simp]
lemma stageCellEquiv_symm_birthCell (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell k n) :
    (T.stageCellEquiv k n).symm (T.birthCell k n j) = ⟨⟨k, j⟩, le_rfl⟩ :=
  (T.stageCellEquiv k n).symm_apply_eq.2 (T.stageCellEquiv_birth k n j).symm

/-- The sequential diagram `ℕ ⥤ TopCat.{u}` of stages `W 0 → W 1 → W 2 → ⋯`. -/
abbrev diagram (T : CWSubcomplexTower W newCell) : ℕ ⥤ TopCat.{u} where
  obj k := TopCat.of (W k)
  map f := Functor.OfSequence.map (fun k ↦ TopCat.ofHom (T.step k)) _ _ (leOfHom f)
  map_id k := Functor.OfSequence.map_id (fun k ↦ TopCat.ofHom (T.step k)) k
  map_comp f g :=
    Functor.OfSequence.map_comp (fun k ↦ TopCat.ofHom (T.step k)) _ _ _ (leOfHom f) (leOfHom g)

lemma diagram_obj (T : CWSubcomplexTower W newCell) (k : ℕ) :
    T.diagram.obj k = TopCat.of (W k) :=
  (rfl)

lemma diagram_map_succ (T : CWSubcomplexTower W newCell) (k : ℕ) :
    T.diagram.map (homOfLE (Nat.le_add_right k 1)) = TopCat.ofHom (T.step k) :=
  Functor.OfSequence.map_le_succ _ k

/-- Transition maps in `T.diagram` carry the characteristic map of a cell at its birth stage `m`
onto its characteristic map in any later stage `k ≥ m` on the closed unit ball. -/
theorem diagram_map_birthCell (T : CWSubcomplexTower W newCell) {m k : ℕ} (hmk : m ≤ k) (n : ℕ)
    (j : newCell m n) {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    T.diagram.map (homOfLE hmk) (map (C := (univ : Set (W m))) n (T.birthCell m n j) x) =
      map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩) x := by
  induction hmk with
  | refl =>
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), CategoryTheory.Functor.map_id, T.stageCellEquiv_birth]
    rfl
  | @step k hmk ih =>
    have hcomp : homOfLE (Nat.le_succ_of_le hmk) =
        homOfLE hmk ≫ homOfLE (Nat.le_add_right k 1) := rfl
    rw [hcomp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply,
      T.diagram_map_succ, ih]
    exact (T.map_oldCell k n _ hx).trans
      (congrArg (fun i ↦ map n i x) (T.stageCellEquiv_succ_of_le k n ⟨m, j⟩ hmk).symm)

/-- Every transition map `W i → W j` (`i ≤ j`) of the tower is a closed embedding. -/
theorem isClosedEmbedding_diagram_map (T : CWSubcomplexTower W newCell) {i j : ℕ} (hij : i ≤ j) :
    IsClosedEmbedding (T.diagram.map (homOfLE hij)) := by
  induction hij with
  | refl =>
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), CategoryTheory.Functor.map_id]
    exact IsClosedEmbedding.id
  | @step k hik ih =>
    have hcomp : homOfLE (Nat.le_succ_of_le hik) =
        homOfLE hik ≫ homOfLE (Nat.le_add_right k 1) := rfl
    rw [hcomp, CategoryTheory.Functor.map_comp, TopCat.coe_comp, T.diagram_map_succ]
    exact (T.isClosedEmbedding_step k).comp ih

/-- For any colimit cocone `c` of `T.diagram`, every stage map `c.ι.app k : W k → c.pt` is a
closed embedding. -/
theorem isClosedEmbedding_ι (T : CWSubcomplexTower W newCell) {c : Cocone T.diagram}
    (hc : IsColimit c) (k : ℕ) : IsClosedEmbedding (c.ι.app k) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit
    (fun _ _ hij ↦ T.isClosedEmbedding_diagram_map hij) hc k

/-- Singletons in any colimit `c.pt` of `T.diagram` are closed by the stage final topology. -/
theorem t1Space_of_isColimit (T : CWSubcomplexTower W newCell) {c : Cocone T.diagram}
    (hc : IsColimit c) : T1Space c.pt :=
  TauCeti.TopCat.t1Space_of_isColimit
    (fun _ _ hij ↦ (T.isClosedEmbedding_diagram_map hij).injective) hc

end StageMachinery

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
    funext x
    change T.cellMap c n p x =
      c.ι.app p.1 (openCellHomeomorph (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) x)
    rw [openCellHomeomorph_apply]
    rfl
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
    rintro ⟨n₁, k₁, j₁⟩ - ⟨n₂, k₂, j₂⟩ - hne
    let K := max k₁ k₂
    have hk₁ : k₁ ≤ K := le_max_left k₁ k₂
    have hk₂ : k₂ ≤ K := le_max_right k₁ k₂
    let i₁ := T.stageCellEquiv K n₁ ⟨⟨k₁, j₁⟩, hk₁⟩
    let i₂ := T.stageCellEquiv K n₂ ⟨⟨k₂, j₂⟩, hk₂⟩
    have himg₁ : T.cellPartialEquiv hc n₁ ⟨k₁, j₁⟩ '' ball 0 1 =
        c.ι.app K '' openCell (C := (univ : Set (W K))) n₁ i₁ := by
      rw [T.coe_cellPartialEquiv]
      ext z
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩,
          T.ι_stageCellEquiv_map_eq (c := c) hk₁ n₁ j₁ (ball_subset_closedBall hx)⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx,
          (T.ι_stageCellEquiv_map_eq (c := c) hk₁ n₁ j₁ (ball_subset_closedBall hx)).symm⟩
    have himg₂ : T.cellPartialEquiv hc n₂ ⟨k₂, j₂⟩ '' ball 0 1 =
        c.ι.app K '' openCell (C := (univ : Set (W K))) n₂ i₂ := by
      rw [T.coe_cellPartialEquiv]
      ext z
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩,
          T.ι_stageCellEquiv_map_eq (c := c) hk₂ n₂ j₂ (ball_subset_closedBall hx)⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx,
          (T.ι_stageCellEquiv_map_eq (c := c) hk₂ n₂ j₂ (ball_subset_closedBall hx)).symm⟩
    dsimp only [Function.onFun]
    rw [himg₁, himg₂]
    have hneK : (⟨n₁, i₁⟩ : Σ m, cell (univ : Set (W K)) m) ≠ ⟨n₂, i₂⟩ := by
      intro h
      obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
      have hsub := (T.stageCellEquiv K n₁).injective (eq_of_heq hi)
      exact hne (congrArg (Sigma.mk n₁) (congrArg Subtype.val hsub))
    exact (disjoint_image_iff (T.isClosedEmbedding_ι hc K).injective).2
      (disjoint_openCell_of_ne hneK)
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
    have heq : (c.ι.app k ⁻¹' A) ∩ closedCell (C := (univ : Set (W k))) n i =
        (c.ι.app k ⁻¹' (A ∩ T.cellPartialEquiv hc n q.1 '' closedBall 0 1)) ∩
          closedCell (C := (univ : Set (W k))) n i := by
      rw [T.coe_cellPartialEquiv]
      ext y
      refine ⟨fun ⟨hyA, hyC⟩ ↦ ⟨⟨hyA, ?_⟩, hyC⟩, fun ⟨⟨hyA, _⟩, hyC⟩ ↦ ⟨hyA, hyC⟩⟩
      obtain ⟨x, hx, rfl⟩ := hyC
      exact ⟨x, hx, (T.ι_stageCellEquiv_map_eq (c := c) q.2 n q.1.2 hx).symm.trans (by rw [hiq])⟩
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
  change T.cellPartialEquiv hc n p '' ball 0 1 = _
  rw [T.coe_cellPartialEquiv]
  exact image_comp (c.ι.app p.1) (map n (T.birthCell p.1 n p.2)) (ball 0 1)

lemma openCell_eq_image_ι_of_le (hc : IsColimit c) (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    openCell (C := (univ : Set c.pt)) n p =
      c.ι.app k '' openCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩,
      (T.map_eq_ι_stageCellEquiv hc n p hpk (ball_subset_closedBall hx)).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, T.map_eq_ι_stageCellEquiv hc n p hpk (ball_subset_closedBall hx)⟩

lemma closedCell_eq_image_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n p =
      c.ι.app p.1 '' closedCell (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  change T.cellPartialEquiv hc n p '' closedBall 0 1 = _
  rw [T.coe_cellPartialEquiv]
  exact image_comp (c.ι.app p.1) (map n (T.birthCell p.1 n p.2)) (closedBall 0 1)

lemma closedCell_eq_image_ι_of_le (hc : IsColimit c) (n : ℕ) (p : Σ m : ℕ, newCell m n) {k : ℕ}
    (hpk : p.1 ≤ k) :
    letI := T.cwComplexOfIsColimit hc
    closedCell (C := (univ : Set c.pt)) n p =
      c.ι.app k '' closedCell (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨p, hpk⟩) := by
  let _ := T.cwComplexOfIsColimit hc
  ext z
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (T.map_eq_ι_stageCellEquiv hc n p hpk hx).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, T.map_eq_ι_stageCellEquiv hc n p hpk hx⟩

lemma cellFrontier_eq_image_ι (hc : IsColimit c) (n : ℕ) (p : Σ k : ℕ, newCell k n) :
    letI := T.cwComplexOfIsColimit hc
    cellFrontier (C := (univ : Set c.pt)) n p =
      c.ι.app p.1 '' cellFrontier (C := (univ : Set (W p.1))) n (T.birthCell p.1 n p.2) := by
  let _ := T.cwComplexOfIsColimit hc
  change T.cellPartialEquiv hc n p '' sphere 0 1 = _
  rw [T.coe_cellPartialEquiv]
  exact image_comp (c.ι.app p.1) (map n (T.birthCell p.1 n p.2)) (sphere 0 1)

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
  rw [T.openCell_eq_image_ι hc] at hzO
  obtain ⟨y₁, hy₁, hy⟩ := hzO
  have hmap_eq : T.diagram.map (homOfLE hlt.le) y₀ = y₁ := by
    apply (T.isClosedEmbedding_ι hc lq).injective
    rw [← ConcreteCategory.comp_apply, c.w]
    exact hy.symm
  -- Push `y₀` to stage `p.1 + d` and then one step to `lq = (p.1 + d) + 1`, where `jq` is new.
  obtain ⟨d, rfl⟩ : ∃ d, lq = p.1 + d + 1 := ⟨lq - (p.1 + 1), by omega⟩
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

/-- **The CW subcomplex of `c.pt` corresponding to stage `W k`.** The body is exposed so that its
carrier is `range (c.ι.app k)` and its `n`-cells are `{p : Σ m, newCell m n | p.1 ≤ k}` by
definition. -/
@[expose] def stageSubcomplex (hc : IsColimit c) (k : ℕ) :
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

lemma coe_stageSubcomplex (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k : Set c.pt) = range (c.ι.app k) :=
  (rfl)

lemma stageSubcomplex_I (hc : IsColimit c) (k n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc k).I n = {p : Σ m : ℕ, newCell m n | p.1 ≤ k} :=
  (rfl)

lemma stageSubcomplex_mono (hc : IsColimit c) {i j : ℕ} (hij : i ≤ j) :
    letI := T.cwComplexOfIsColimit hc
    (T.stageSubcomplex hc i : Set c.pt) ⊆ T.stageSubcomplex hc j := by
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
  (T.isClosedEmbedding_ι hc k).isEmbedding.toHomeomorph

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
  -- Fold `φ` inside `IsClosed (_ ⁻¹' Uᶜ)` on the right-hand side.
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
types agree by definition with those of `TauCeti.toTopCatCWComplex`. -/
@[expose] def toTopCatCWComplexOfIsColimit (hc : IsColimit c) : TopCat.CWComplex c.pt :=
  @TauCeti.toTopCatCWComplex c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

lemma toTopCatCWComplexOfIsColimit_obj (hc : IsColimit c) (n : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    letI := T.t2Space_of_isColimit hc
    (T.toTopCatCWComplexOfIsColimit hc).F.obj n = skeletonObj (univ : Set c.pt) n :=
  (rfl)

/-- Dimension-indexed identification of the cells of `T.toTopCatCWComplexOfIsColimit hc` with
`Σ (n : ℕ) (k : ℕ), newCell k n`. -/
def toTopCatCWComplexOfIsColimitCellsEquiv (hc : IsColimit c) :
    (T.toTopCatCWComplexOfIsColimit hc).Cells ≃ Σ (n : ℕ) (k : ℕ), newCell k n :=
  @toTopCatCWComplexCellsEquiv c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc)

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
  @toTopCatCWComplex_cells_ι_apply c.pt (T.t2Space_of_isColimit hc) (T.cwComplexOfIsColimit hc) γ z

end IsColimit

/-! ### Canonical colimit carrier `T.Union` and `cwSubcomplexTowerUnion` -/

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

end Union

end CWSubcomplexTower

/-- **Classical `CWComplex` structure on the raw final-topology union of a sequential tower of CW
subcomplexes.** The body is exposed so that `cell (univ : Set T.Union) n` is `Σ k : ℕ, newCell k n`
by definition. -/
@[expose, instance_reducible]
def cwSubcomplexTowerUnion {W : ℕ → Type u}
    [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
    {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell) :
    CWComplex (univ : Set T.Union) :=
  T.cwComplexOfIsColimit (colimit.isColimit T.diagram)

namespace CWSubcomplexTower

section UnionInstances

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

instance instCWComplexUnion : CWComplex (univ : Set T.Union) :=
  cwSubcomplexTowerUnion T

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

/-- The specified `CWComplex.Subcomplex` of `T.Union` onto which stage `W k` embeds. The body is
exposed so that its carrier and cell-index sets reduce by definition. -/
@[expose] def unionStageSubcomplex (k : ℕ) : CWComplex.Subcomplex (univ : Set T.Union) :=
  T.stageSubcomplex (colimit.isColimit T.diagram) k

@[simp]
lemma coe_unionStageSubcomplex (k : ℕ) :
    (T.unionStageSubcomplex k : Set T.Union) = range (T.incl k) :=
  (rfl)

@[simp]
lemma unionStageSubcomplex_I (k n : ℕ) :
    (T.unionStageSubcomplex k).I n = {p : Σ m : ℕ, newCell m n | p.1 ≤ k} :=
  (rfl)

/-- Homeomorphism of `W k` onto its CW subcomplex `T.unionStageSubcomplex k` in `T.Union`. -/
def homeomorphUnionStageSubcomplex (k : ℕ) :
    W k ≃ₜ T.unionStageSubcomplex k :=
  T.homeomorphStageSubcomplex (colimit.isColimit T.diagram) k

@[simp]
lemma coe_homeomorphUnionStageSubcomplex_apply (k : ℕ) (x : W k) :
    (T.homeomorphUnionStageSubcomplex k x : T.Union) = T.incl k x :=
  (rfl)

/-- Categorical `TopCat.CWComplex` structure on `T.Union` after reindexing cells by dimension. -/
@[expose] def toTopCatCWComplex : TopCat.CWComplex T.Union :=
  T.toTopCatCWComplexOfIsColimit (colimit.isColimit T.diagram)

end UnionInstances

/-! ### Cellularity of stage maps and cellular naturality -/

section CellularNaturality

section SingleTower

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- Each stage inclusion `T.step k : W k → W (k + 1)` is cellular. -/
theorem isCellular_step (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set (W (k + 1)))
      (TopCat.ofHom ((T.step k).restrictPreimage univ)) := by
  refine isCellular_of_map_eq _ _ (fun _ h ↦ False.elim h) fun n i ↦ ?_
  refine ⟨(T.oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n), fun x hx _ ↦ ?_⟩
  exact T.map_oldCell k n i hx

/-- For any colimit cocone `c` of `T.diagram`, each stage inclusion `c.ι.app k : W k → c.pt` is
cellular. -/
theorem isCellular_ι {c : Cocone T.diagram} (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    letI := T.t2Space_of_isColimit hc
    IsCellular (univ : Set (W k)) (univ : Set c.pt)
      (TopCat.ofHom ((c.ι.app k).hom.restrictPreimage univ)) := by
  let _ := T.cwComplexOfIsColimit hc
  let _ := T.t2Space_of_isColimit hc
  refine isCellular_of_map_eq _ _ (fun _ h ↦ False.elim h) fun n i ↦ ?_
  let q := (T.stageCellEquiv k n).symm i
  have hiq : T.stageCellEquiv k n q = i := (T.stageCellEquiv k n).apply_symm_apply i
  refine ⟨q.1, fun x hx _ ↦ ?_⟩
  exact (congrArg (fun j ↦ c.ι.app k (map (C := (univ : Set (W k))) n j x)) hiq).symm.trans
    (T.map_eq_ι_stageCellEquiv hc n q.1 q.2 hx).symm

/-- Each stage inclusion `T.incl k : W k → T.Union` is cellular. -/
theorem isCellular_incl (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set T.Union)
      (TopCat.ofHom ((T.incl k).hom.restrictPreimage univ)) :=
  T.isCellular_ι (colimit.isColimit T.diagram) k

end SingleTower

/-- A cellular morphism between two `CWSubcomplexTower`s: a family of continuous stage maps
commuting with the stage inclusions such that each stage map is cellular. -/
structure Hom {W₁ W₂ : ℕ → Type u}
    [∀ k, TopologicalSpace (W₁ k)] [∀ k, T2Space (W₁ k)] [∀ k, CWComplex (univ : Set (W₁ k))]
    [∀ k, TopologicalSpace (W₂ k)] [∀ k, T2Space (W₂ k)] [∀ k, CWComplex (univ : Set (W₂ k))]
    {newCell₁ newCell₂ : ℕ → ℕ → Type u}
    (T₁ : CWSubcomplexTower W₁ newCell₁) (T₂ : CWSubcomplexTower W₂ newCell₂) where
  /-- The stage map `W₁ k → W₂ k`. -/
  app (k : ℕ) : C(W₁ k, W₂ k)
  /-- Commutativity with stage inclusions. -/
  comm (k : ℕ) : (app (k + 1)).comp (T₁.step k) = (T₂.step k).comp (app k)
  /-- Each stage map is cellular. -/
  isCellular_app (k : ℕ) :
    IsCellular (univ : Set (W₁ k)) (univ : Set (W₂ k))
      (TopCat.ofHom ((app k).restrictPreimage univ))

namespace Hom

section Basic

variable {W₁ W₂ W₃ : ℕ → Type u}
  [∀ k, TopologicalSpace (W₁ k)] [∀ k, T2Space (W₁ k)] [∀ k, CWComplex (univ : Set (W₁ k))]
  [∀ k, TopologicalSpace (W₂ k)] [∀ k, T2Space (W₂ k)] [∀ k, CWComplex (univ : Set (W₂ k))]
  [∀ k, TopologicalSpace (W₃ k)] [∀ k, T2Space (W₃ k)] [∀ k, CWComplex (univ : Set (W₃ k))]
  {newCell₁ newCell₂ newCell₃ : ℕ → ℕ → Type u}
  {T₁ : CWSubcomplexTower W₁ newCell₁} {T₂ : CWSubcomplexTower W₂ newCell₂}
  {T₃ : CWSubcomplexTower W₃ newCell₃}

@[ext]
theorem ext {φ ψ : T₁.Hom T₂} (h : ∀ k, φ.app k = ψ.app k) : φ = ψ := by
  cases φ
  cases ψ
  congr
  exact funext h

/-- The identity cellular morphism on a `CWSubcomplexTower`. -/
def id (T₁ : CWSubcomplexTower W₁ newCell₁) : T₁.Hom T₁ where
  app k := ContinuousMap.id (W₁ k)
  comm _ := rfl
  isCellular_app _ _ _ hx := hx

@[simp]
lemma id_app (T₁ : CWSubcomplexTower W₁ newCell₁) (k : ℕ) :
    (Hom.id T₁).app k = ContinuousMap.id (W₁ k) :=
  (rfl)

/-- Composition of cellular morphisms of `CWSubcomplexTower`s. -/
def comp (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) : T₁.Hom T₃ where
  app k := (ψ.app k).comp (φ.app k)
  comm k := by
    ext x
    have h₁ := ContinuousMap.congr_fun (φ.comm k) x
    have h₂ := ContinuousMap.congr_fun (ψ.comm k) (φ.app k x)
    exact (congrArg (ψ.app (k + 1)) h₁).trans h₂
  isCellular_app k n _ hx := ψ.isCellular_app k n (φ.isCellular_app k n hx)

@[simp]
lemma comp_app (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) (k : ℕ) :
    (φ.comp ψ).app k = (ψ.app k).comp (φ.app k) :=
  (rfl)

/-- The natural transformation `T₁.diagram ⟶ T₂.diagram` induced by `φ : T₁.Hom T₂`. -/
def natTrans (φ : T₁.Hom T₂) : T₁.diagram ⟶ T₂.diagram :=
  NatTrans.ofSequence (fun k ↦ TopCat.ofHom (φ.app k)) fun k ↦ by
    rw [T₁.diagram_map_succ, T₂.diagram_map_succ]
    ext x
    exact ContinuousMap.congr_fun (φ.comm k) x

@[simp]
lemma natTrans_app (φ : T₁.Hom T₂) (k : ℕ) :
    φ.natTrans.app k = TopCat.ofHom (φ.app k) :=
  (rfl)

/-- The induced continuous map `c₁.pt ⟶ c₂.pt` between any colimit cocones of `T₁` and `T₂`. -/
def mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) : c₁.pt ⟶ c₂.pt :=
  hc₁.desc ⟨c₂.pt, φ.natTrans ≫ c₂.ι⟩

@[simp, reassoc]
lemma ι_comp_mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (k : ℕ) :
    c₁.ι.app k ≫ φ.mapOfIsColimit hc₁ = TopCat.ofHom (φ.app k) ≫ c₂.ι.app k :=
  hc₁.fac ⟨c₂.pt, φ.natTrans ≫ c₂.ι⟩ k

lemma mapOfIsColimit_ι_apply (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (k : ℕ) (x : W₁ k) :
    φ.mapOfIsColimit hc₁ (c₁.ι.app k x) = c₂.ι.app k (φ.app k x) := by
  rw [← ConcreteCategory.comp_apply, φ.ι_comp_mapOfIsColimit hc₁ k, ConcreteCategory.comp_apply]
  rfl

/-- **Cellular naturality:** the map induced on colimits by a cellular tower morphism is
cellular. -/
theorem isCellular_mapOfIsColimit (φ : T₁.Hom T₂)
    {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    letI := T₁.cwComplexOfIsColimit hc₁
    letI := T₁.t2Space_of_isColimit hc₁
    letI := T₂.cwComplexOfIsColimit hc₂
    letI := T₂.t2Space_of_isColimit hc₂
    IsCellular (univ : Set c₁.pt) (univ : Set c₂.pt)
      (TopCat.ofHom ((φ.mapOfIsColimit (c₂ := c₂) hc₁).hom.restrictPreimage univ)) := by
  let _ := T₁.cwComplexOfIsColimit hc₁
  let _ := T₁.t2Space_of_isColimit hc₁
  let _ := T₂.cwComplexOfIsColimit hc₂
  let _ := T₂.t2Space_of_isColimit hc₂
  rintro n ⟨z, -⟩ (hz : z ∈ skeletonLT (univ : Set c₁.pt) (n : ℕ∞))
  rw [RelCWComplex.mem_skeletonLT_iff] at hz
  rcases hz with hzEmpty | ⟨m, hmn, p, hzp⟩
  · exact False.elim hzEmpty
  · rw [T₁.openCell_eq_image_ι hc₁] at hzp
    obtain ⟨y, hy, rfl⟩ := hzp
    have hy_skel : y ∈ skeletonLT (univ : Set (W₁ p.1)) (n : ℕ∞) :=
      RelCWComplex.mem_skeletonLT_iff.2 (Or.inr ⟨m, hmn, T₁.birthCell p.1 m p.2, hy⟩)
    have hφy_skel : φ.app p.1 y ∈ skeletonLT (univ : Set (W₂ p.1)) (n : ℕ∞) :=
      φ.isCellular_app p.1 n (x := ⟨y, mem_univ y⟩) hy_skel
    have hι_skel := T₂.isCellular_ι hc₂ p.1 n (x := ⟨φ.app p.1 y, mem_univ _⟩) hφy_skel
    -- Unfold `restrictPreimage univ` to evaluate `mapOfIsColimit` on `c₁.ι.app p.1 y`.
    change φ.mapOfIsColimit (c₂ := c₂) hc₁ (c₁.ι.app p.1 y) ∈ skeletonLT (univ : Set c₂.pt) (n : ℕ∞)
    rw [φ.mapOfIsColimit_ι_apply hc₁]
    exact hι_skel

/-- The induced continuous map `T₁.Union ⟶ T₂.Union` between canonical tower unions. -/
def unionMap (φ : T₁.Hom T₂) : T₁.Union ⟶ T₂.Union :=
  φ.mapOfIsColimit (colimit.isColimit T₁.diagram)

@[simp, reassoc]
lemma incl_comp_unionMap (φ : T₁.Hom T₂) (k : ℕ) :
    T₁.incl k ≫ φ.unionMap = TopCat.ofHom (φ.app k) ≫ T₂.incl k :=
  φ.ι_comp_mapOfIsColimit (colimit.isColimit T₁.diagram) k

@[simp]
lemma unionMap_incl_apply (φ : T₁.Hom T₂) (k : ℕ) (x : W₁ k) :
    φ.unionMap (T₁.incl k x) = T₂.incl k (φ.app k x) :=
  φ.mapOfIsColimit_ι_apply (colimit.isColimit T₁.diagram) k x

@[simp]
lemma unionMap_id : (Hom.id T₁).unionMap = 𝟙 T₁.Union :=
  colimit.hom_ext fun k ↦ by
    rw [incl_comp_unionMap]
    ext x
    rfl

@[simp, reassoc]
lemma unionMap_comp (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) :
    (φ.comp ψ).unionMap = φ.unionMap ≫ ψ.unionMap :=
  colimit.hom_ext fun k ↦ by
    rw [incl_comp_unionMap, incl_comp_unionMap_assoc, comp_app]
    ext x
    simp

/-- The induced map `T₁.Union ⟶ T₂.Union` of a cellular tower morphism is cellular. -/
theorem isCellular_unionMap (φ : T₁.Hom T₂) :
    IsCellular (univ : Set T₁.Union) (univ : Set T₂.Union)
      (TopCat.ofHom (φ.unionMap.hom.restrictPreimage univ)) :=
  φ.isCellular_mapOfIsColimit (colimit.isColimit T₁.diagram) (colimit.isColimit T₂.diagram)

/-- On every dimension skeleton, the induced map `φ.unionMap` restricts to a map commuting with
stage skeletal restrictions. -/
@[reassoc]
theorem skeletonMap_incl_comp (φ : T₁.Hom T₂) (k n : ℕ) :
    skeletonMap _ _ (T₁.isCellular_incl k) n ≫ skeletonMap _ _ φ.isCellular_unionMap n =
      skeletonMap _ _ (φ.isCellular_app k) n ≫ skeletonMap _ _ (T₂.isCellular_incl k) n := by
  have hcongr :
      ∀ {f₁ f₂ : TopCat.of (univ : Set (W₁ k)) ⟶ TopCat.of (univ : Set T₂.Union)}
        (_ : f₁ = f₂) (hf₁ : IsCellular _ _ f₁) (hf₂ : IsCellular _ _ f₂),
        skeletonMap _ _ hf₁ n = skeletonMap _ _ hf₂ n := by
    rintro _ _ rfl _ _
    rfl
  rw [← skeletonMap_comp, ← skeletonMap_comp]
  exact hcongr (by ext x; exact φ.unionMap_incl_apply k x.1) _ _

end Basic

end Hom

end CellularNaturality

/-! ### Stabilizing and two-stage towers -/

section Examples

/-- The constant `CWSubcomplexTower` on a Hausdorff classical CW complex `X`, where stage `0` has
all cells of `X` and stages `k + 1` attach no new cells (`PEmpty`). -/
def const (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] :
    CWSubcomplexTower (fun _ ↦ X) (fun k n ↦ match k with
      | 0 => cell (univ : Set X) n
      | _ + 1 => PEmpty) :=
  ofCellSum
    (fun _ ↦ ContinuousMap.id X)
    (fun _ ↦ IsClosedEmbedding.id)
    (fun _ ↦ Equiv.refl _)
    (fun _ _ ↦ Equiv.sumEmpty _ _)
    (fun _ _ _ {_} _ ↦ rfl)

/-- The union of the constant tower `CWSubcomplexTower.const X` is homeomorphic to `X`. -/
def constUnionHomeomorph (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] :
    (const X).Union ≃ₜ X :=
  let T := const X
  let cX : Cocone T.diagram :=
    { pt := TopCat.of X
      ι := NatTrans.ofSequence (fun _ ↦ 𝟙 (TopCat.of X)) fun k ↦ by
        rw [T.diagram_map_succ]
        rfl }
  let hcX : IsColimit cX :=
    { desc := fun s ↦ s.ι.app 0
      fac := fun s k ↦ by
        simp only [cX, NatTrans.ofSequence_app, Category.id_comp]
        induction k with
        | zero => rfl
        | succ k ih =>
          have hw := s.w (homOfLE (Nat.le_add_right k 1))
          rw [T.diagram_map_succ] at hw
          have hid : TopCat.ofHom (T.step k) = 𝟙 (TopCat.of X) := by ext x; rfl
          rw [hid, Category.id_comp] at hw
          exact ih.trans hw.symm
      uniq := fun s m hm ↦ by
        simpa only [cX, NatTrans.ofSequence_app, Category.id_comp] using hm 0 }
  TopCat.homeoOfIso (colimit.isoColimitCocone ⟨cX, hcX⟩)

/-- A two-stage-then-stabilizing `CWSubcomplexTower` built from a single closed CW subcomplex
embedding `f : C(W₀, W₁)`: stage `0` has the cells of `W₀`, stage `1` attaches the complementary
cells `new₁` of `W₁` (which may have **strictly smaller** dimensions than cells of `W₀`), and all
higher stages `k + 2` stabilize at `W₁` with no further cells. -/
def pair {W₀ W₁ : Type u}
    [TopologicalSpace W₀] [T2Space W₀] [CWComplex (univ : Set W₀)]
    [TopologicalSpace W₁] [T2Space W₁] [CWComplex (univ : Set W₁)]
    {new₁ : ℕ → Type u}
    (f : C(W₀, W₁)) (hf : IsClosedEmbedding f)
    (cellSum : ∀ n, cell (univ : Set W₀) n ⊕ new₁ n ≃ cell (univ : Set W₁) n)
    (hmap : ∀ n (i : cell (univ : Set W₀) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      f (map (C := (univ : Set W₀)) n i x) =
        map (C := (univ : Set W₁)) n (cellSum n (Sum.inl i)) x) :
    let W : ℕ → Type u := fun
      | 0 => W₀
      | _ + 1 => W₁
    letI : ∀ k, TopologicalSpace (W k) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    letI : ∀ k, T2Space (W k) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    letI : ∀ k, CWComplex (univ : Set (W k)) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    CWSubcomplexTower W (fun k n ↦ match k with
      | 0 => cell (univ : Set W₀) n
      | 1 => new₁ n
      | _ + 2 => PEmpty) :=
  let W : ℕ → Type u := fun
    | 0 => W₀
    | _ + 1 => W₁
  letI : ∀ k, TopologicalSpace (W k) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  letI : ∀ k, T2Space (W k) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  letI : ∀ k, CWComplex (univ : Set (W k)) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  ofCellSum (W := W)
    (fun
      | 0 => f
      | _ + 1 => ContinuousMap.id W₁)
    (fun
      | 0 => hf
      | _ + 1 => IsClosedEmbedding.id)
    (fun _ ↦ Equiv.refl _)
    (fun
      | 0, n => cellSum n
      | _ + 1, _ => Equiv.sumEmpty _ _)
    (fun k n i {_} hx ↦ by
      cases k with
      | zero => exact hmap n i hx
      | succ _ => exact rfl)

end Examples

end CWSubcomplexTower

end TauCeti
