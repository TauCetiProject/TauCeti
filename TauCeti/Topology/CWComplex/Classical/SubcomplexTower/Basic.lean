/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.Logic.Equiv.Sigma
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# Sequential towers of CW subcomplex inclusions

While `TauCeti.Topology.CWComplex.Classical.Tower` and
`TauCeti.Topology.CWComplex.Classical.TowerUnion` equip the union `⋃ k, W k` of a tower of CW
subspaces inside an already-given ambient space `X` with a classical CW structure, sequential
exhaustions (such as sublevel models of proper below-bounded Morse functions) present an abstract
sequence `W₀ → W₁ → W₂ → ⋯` of Hausdorff classical CW spaces (`CWComplex (univ : Set (W k))`) in
which each `step k : W k → W (k + 1)` is a closed embedding onto a specified CW subcomplex
`subcomplex k` of `W (k + 1)`, equipped with compatible cell labels and characteristic maps on the
closed unit ball. Crucially, the new cells added from `W k` to `W (k + 1)` may have **arbitrary
dimensions in any stage order**: stage `k + 1` is allowed to attach lower-dimensional cells after
stage `k` has already attached higher-dimensional ones.

This file defines `TauCeti.CWSubcomplexTower W newCell`, gives constructors from subcomplex families
(`ofSubcomplex`) and sum decompositions of cell index sets (`ofCellSum`), builds cumulative
stagewise cell equivalences (`birthCell`, `stepCellEquiv`, `stageCellEquiv`), and constructs the
sequential diagram `T.diagram : ℕ ⥤ TopCat` whose transition and colimit maps are closed embeddings
(`isClosedEmbedding_diagram_map`, `isClosedEmbedding_ι`, `t1Space_of_isColimit`).

The classical CW structure, normality, Hausdorff separation, stage subcomplexes, and categorical
comparison on colimits of `T.diagram` are developed in
`TauCeti.Topology.CWComplex.Classical.SubcomplexTower.Colimit`, and cellular morphisms of towers in
`TauCeti.Topology.CWComplex.Classical.SubcomplexTower.Hom`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.1, A.2, and A.3.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press, 1990.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

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
    newCellEquiv k n := Equiv.ofBijective
      (fun j ↦ ⟨cellSumEquiv k n (Sum.inr j), hinr_notMem k n j⟩)
      ⟨fun _ _ h ↦ Sum.inr.inj ((cellSumEquiv k n).injective (congrArg Subtype.val h)),
        fun ⟨c, hc⟩ ↦ by
          rcases h : (cellSumEquiv k n).symm c with i | j
          · exact False.elim (hc ⟨i, ((cellSumEquiv k n).symm_apply_eq.1 h).symm⟩)
          · exact ⟨j, Subtype.ext ((cellSumEquiv k n).symm_apply_eq.1 h).symm⟩⟩
    map_oldCell := map_inl }

@[simp]
lemma ofSubcomplex_step
    (step : ∀ k, C(W k, W (k + 1)))
    (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
    (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1))))
    (coe_E : ∀ k, (E k : Set (W (k + 1))) = range (step k))
    (oldCellEquiv : ∀ k n, cell (univ : Set (W k)) n ≃ ↥((E k).I n))
    (map_oldCell : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      step k (map (C := (univ : Set (W k))) n i x) =
        map (C := (univ : Set (W (k + 1)))) n (oldCellEquiv k n i : cell _ n) x)
    (k : ℕ) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv map_oldCell).step k =
      step k := by
  rfl

@[simp]
lemma ofCellSum_step
    (step : ∀ k, C(W k, W (k + 1)))
    (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
    (cellZeroEquiv : ∀ n, newCell 0 n ≃ cell (univ : Set (W 0)) n)
    (cellSumEquiv : ∀ k n,
      cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n)
    (map_inl : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      step k (map (C := (univ : Set (W k))) n i x) =
        map (C := (univ : Set (W (k + 1)))) n (cellSumEquiv k n (Sum.inl i)) x)
    (k : ℕ) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).step k =
      step k := by
  rfl

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

/-- Equivalence between all `n`-cells born at stages `≤ k` and the `n`-cells of `W k`. -/
def stageCellEquiv (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), {p : Σ m : ℕ, newCell m n // p.1 ≤ k} ≃ cell (univ : Set (W k)) n
  | 0, n => (Equiv.sigmaFstLeZeroEquiv (newCell · n)).trans (T.cellZeroEquiv n)
  | k + 1, n =>
      (Equiv.sigmaFstLeSuccEquiv (newCell · n) k).trans
        (((stageCellEquiv T k n).sumCongr (Equiv.refl _)).trans (T.stepCellEquiv k n))

@[simp]
lemma stageCellEquiv_birth (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell k n) :
    T.stageCellEquiv k n ⟨⟨k, j⟩, le_rfl⟩ = T.birthCell k n j := by
  cases k with
  | zero => simp [stageCellEquiv]
  | succ k => simp [stageCellEquiv]

lemma stageCellEquiv_succ_of_le (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (p : Σ m : ℕ, newCell m n) (hp : p.1 ≤ k) :
    T.stageCellEquiv (k + 1) n ⟨p, Nat.le_succ_of_le hp⟩ =
      (T.oldCellEquiv k n (T.stageCellEquiv k n ⟨p, hp⟩) : cell (univ : Set (W (k + 1))) n) := by
  simp [stageCellEquiv, hp]

@[simp]
lemma stageCellEquiv_symm_birthCell (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell k n) :
    (T.stageCellEquiv k n).symm (T.birthCell k n j) = ⟨⟨k, j⟩, le_rfl⟩ :=
  (T.stageCellEquiv k n).symm_apply_eq.2 (T.stageCellEquiv_birth k n j).symm

/-- The sequential diagram `ℕ ⥤ TopCat.{u}` of stages `W 0 → W 1 → W 2 → ⋯`. -/
abbrev diagram (T : CWSubcomplexTower W newCell) : ℕ ⥤ TopCat.{u} where
  obj k := TopCat.of (W k)
  map φ := Functor.OfSequence.map (fun k ↦ TopCat.ofHom (T.step k)) _ _ (leOfHom φ)
  map_id i := Functor.OfSequence.map_id _ i
  map_comp _ _ := Functor.OfSequence.map_comp _ _ _ _ _ _

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

end CWSubcomplexTower

end TauCeti
