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
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Sequential towers of CW subcomplex inclusions

While `TauCeti.cwSubcomplexTowerUnion` equips the union `⋃ k, W k` of a tower of CW subspaces inside
an already-given ambient space `X` with a classical CW structure, sequential exhaustions (such as
sublevel models of proper below-bounded Morse functions) present an abstract sequence
`W₀ → W₁ → W₂ → ⋯` of Hausdorff classical CW spaces (`CWComplex (univ : Set (W k))`) in which each
`step k : W k → W (k + 1)` is a closed embedding onto a specified CW subcomplex `subcomplex k` of
`W (k + 1)`, equipped with compatible cell labels and characteristic maps on the closed unit ball.
Crucially, the new cells added from `W k` to `W (k + 1)` may have **arbitrary dimensions in any
stage order**: stage `k + 1` may attach lower-dimensional cells after stage `k` has attached
higher-dimensional ones.

This file defines `TauCeti.CWSubcomplexTower W newCell`, builds cumulative stagewise cell
equivalences (`birthCell`, `stepCellEquiv`, `stageCellEquiv`) and the sequential diagram
`T.diagram : ℕ ⥤ TopCat` (`isClosedEmbedding_diagram_map`, `isClosedEmbedding_ι`,
`t1Space_of_isColimit`), and gives constructors from subcomplex families (`ofSubcomplex`), cell-sum
decompositions (`ofCellSum`), constant CW complexes (`const`), and stabilizing two-stage subcomplex
embeddings (`pair`). Colimits and morphisms are developed in
`TauCeti.Topology.CWComplex.Classical.Tower.Subcomplex.Colimit` and
`TauCeti.Topology.CWComplex.Classical.Tower.Subcomplex.Hom`.

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

/-- A sequential tower `W 0 → W 1 → W 2 → ⋯` of Hausdorff classical CW complexes on `Set.univ`
along closed embeddings onto specified CW subcomplexes, with compatible cell labels and
characteristic maps on the closed unit ball. Here `newCell k n` indexes the `n`-cells born at stage
`k` (including `k = 0` for all `n`-cells of `W 0`); new cells at stage `k + 1` may have arbitrary
dimensions regardless of dimensions already present in `W k`. -/
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
  step_map_eq_map (k n : ℕ) (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    step k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set (W (k + 1)))) n (oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n) x

attribute [simp] CWSubcomplexTower.coe_subcomplex

namespace CWSubcomplexTower

section StageNewCell

variable {W : ℕ → Type u} [∀ k, TopologicalSpace (W k)] [∀ k, CWComplex (univ : Set (W k))]

/-- A cell of `W k` is new at stage `k` relative to `E` if `k = 0` or `i ∉ (E k').I n`. -/
def IsStageNewCell (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1)))) :
    ∀ (k : ℕ) {n : ℕ}, cell (univ : Set (W k)) n → Prop
  | 0, _, _ => True
  | k + 1, n, i => i ∈ ((E k).I n)ᶜ

@[simp] lemma isStageNewCell_zero (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1)))) {n : ℕ}
    (i : cell (univ : Set (W 0)) n) : IsStageNewCell E 0 i := trivial

@[simp] lemma isStageNewCell_succ_iff (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1))))
    {k n : ℕ} (i : cell (univ : Set (W (k + 1))) n) :
    IsStageNewCell E (k + 1) i ↔ i ∉ (E k).I n := Iff.rfl

/-- Canonical new-cell indexing determined by CW subcomplexes `E k` of `W (k + 1)`. -/
abbrev StageNewCell (W : ℕ → Type u) [∀ k, TopologicalSpace (W k)]
    [∀ k, CWComplex (univ : Set (W k))]
    (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1)))) (k n : ℕ) : Type u :=
  {i : cell (univ : Set (W k)) n // IsStageNewCell E k i}

end StageNewCell

section StageMachinery

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u}

@[simp] lemma mem_subcomplex_iff (T : CWSubcomplexTower W newCell) {k : ℕ} {x : W (k + 1)} :
    x ∈ T.subcomplex k ↔ x ∈ range (T.step k) := by
  rw [← SetLike.mem_coe, T.coe_subcomplex]

/-- Two `CWSubcomplexTower`s sharing the `k`-th stage map have equal `k`-th stage subcomplexes. -/
theorem subcomplex_eq_of_step_eq {newCell₁ newCell₂ : ℕ → ℕ → Type u}
    {T₁ : CWSubcomplexTower W newCell₁} {T₂ : CWSubcomplexTower W newCell₂} {k : ℕ}
    (hstep : T₁.step k = T₂.step k) : T₁.subcomplex k = T₂.subcomplex k :=
  SetLike.coe_injective ((T₁.coe_subcomplex k).trans (by rw [hstep, ← T₂.coe_subcomplex k]))

/-- Two `CWSubcomplexTower`s are equal if they have the same stage maps, initial cell labels, and
new-cell labels; the stage subcomplexes and old-cell equivalences are uniquely determined. -/
@[ext] theorem ext {T₁ T₂ : CWSubcomplexTower W newCell}
    (hstep : ∀ k, T₁.step k = T₂.step k)
    (hzero : ∀ n, T₁.cellZeroEquiv n = T₂.cellZeroEquiv n)
    (hnew : ∀ k n (j : newCell (k + 1) n),
      (T₁.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n) =
        (T₂.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n)) :
    T₁ = T₂ := by
  have hstep' : T₁.step = T₂.step := funext hstep
  have hsub : T₁.subcomplex = T₂.subcomplex := funext fun k ↦ subcomplex_eq_of_step_eq (hstep k)
  cases T₁ with
  | mk _ _ _ _ zero₁ old₁ new₁ map₁ =>
    cases T₂ with
    | mk _ _ _ _ zero₂ old₂ new₂ map₂ =>
      dsimp at hstep' hsub hzero hnew; subst hstep' hsub
      congr
      · exact funext hzero
      · exact funext₂ fun k n ↦ Equiv.ext fun i ↦ Subtype.ext <| openCell_congr n
          (image_congr fun x hx ↦ (map₁ k n i (ball_subset_closedBall hx)).symm.trans
            (map₂ k n i (ball_subset_closedBall hx)))
      · exact funext₂ fun k n ↦ Equiv.ext fun j ↦ Subtype.ext (hnew k n j)

/-- The `n`-cell in its birth stage `W k` corresponding to `j : newCell k n`. -/
def birthCell (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), newCell k n → cell (univ : Set (W k)) n
  | 0, n, j => T.cellZeroEquiv n j
  | k + 1, n, j => (T.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n)

@[simp] lemma birthCell_zero (T : CWSubcomplexTower W newCell) (n : ℕ) (j : newCell 0 n) :
    T.birthCell 0 n j = T.cellZeroEquiv n j := (rfl)

@[simp] lemma birthCell_succ (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell (k + 1) n) :
    T.birthCell (k + 1) n j = (T.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n) := (rfl)

lemma birthCell_injective (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), Function.Injective (T.birthCell k n)
  | 0, n => (T.cellZeroEquiv n).injective
  | k + 1, n => Subtype.val_injective.comp (T.newCellEquiv k n).injective

/-- Decomposition of the `n`-cells of `W (k + 1)` into old cells from `W k` and new cells from
`newCell (k + 1) n`. -/
def stepCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ) :
    cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n :=
  open Classical in
  (Equiv.sumCongr (T.oldCellEquiv k n) (T.newCellEquiv k n)).trans
    (Equiv.Set.sumCompl ((T.subcomplex k).I n))

@[simp] lemma stepCellEquiv_inl (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (i : cell (univ : Set (W k)) n) : T.stepCellEquiv k n (Sum.inl i) =
      (T.oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n) := by simp [stepCellEquiv]

@[simp] lemma stepCellEquiv_inr (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell (k + 1) n) : T.stepCellEquiv k n (Sum.inr j) =
      (T.newCellEquiv k n j : cell (univ : Set (W (k + 1))) n) := by simp [stepCellEquiv]

@[simp] lemma stepCellEquiv_symm_oldCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (i : cell (univ : Set (W k)) n) :
    (T.stepCellEquiv k n).symm (T.oldCellEquiv k n i) = Sum.inl i :=
  (T.stepCellEquiv k n).symm_apply_eq.2 (T.stepCellEquiv_inl k n i).symm

@[simp] lemma stepCellEquiv_symm_newCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell (k + 1) n) :
    (T.stepCellEquiv k n).symm (T.newCellEquiv k n j) = Sum.inr j :=
  (T.stepCellEquiv k n).symm_apply_eq.2 (T.stepCellEquiv_inr k n j).symm

/-- Equivalence between all `n`-cells born at stages `≤ k` and the `n`-cells of `W k`. -/
def stageCellEquiv (T : CWSubcomplexTower W newCell) :
    ∀ (k n : ℕ), {p : Σ m : ℕ, newCell m n // p.1 ≤ k} ≃ cell (univ : Set (W k)) n
  | 0, n => (Equiv.sigmaFstLeZeroEquiv (newCell · n)).trans (T.cellZeroEquiv n)
  | k + 1, n =>
      (Equiv.sigmaFstLeSuccEquiv (newCell · n) k).trans
        (((stageCellEquiv T k n).sumCongr (Equiv.refl _)).trans (T.stepCellEquiv k n))

@[simp] lemma stageCellEquiv_birth (T : CWSubcomplexTower W newCell) (k n : ℕ) (j : newCell k n) :
    T.stageCellEquiv k n ⟨⟨k, j⟩, le_rfl⟩ = T.birthCell k n j := by
  cases k <;> simp [stageCellEquiv]

@[simp] lemma stageCellEquiv_succ_of_le (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (p : Σ m : ℕ, newCell m n) (hp : p.1 ≤ k) :
    T.stageCellEquiv (k + 1) n ⟨p, Nat.le_succ_of_le hp⟩ =
      (T.oldCellEquiv k n (T.stageCellEquiv k n ⟨p, hp⟩) : cell (univ : Set (W (k + 1))) n) := by
  simp [stageCellEquiv, hp]

@[simp] lemma stageCellEquiv_symm_birthCell (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell k n) :
    (T.stageCellEquiv k n).symm (T.birthCell k n j) = ⟨⟨k, j⟩, le_rfl⟩ :=
  (T.stageCellEquiv k n).symm_apply_eq.2 (T.stageCellEquiv_birth k n j).symm

@[simp] lemma stageCellEquiv_zero_symm_cellZeroEquiv (T : CWSubcomplexTower W newCell) (n : ℕ)
    (j : newCell 0 n) :
    (T.stageCellEquiv 0 n).symm (T.cellZeroEquiv n j) = ⟨⟨0, j⟩, le_rfl⟩ :=
  T.stageCellEquiv_symm_birthCell 0 n j

@[simp] lemma stageCellEquiv_succ_symm_newCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (j : newCell (k + 1) n) :
    (T.stageCellEquiv (k + 1) n).symm (T.newCellEquiv k n j) = ⟨⟨k + 1, j⟩, le_rfl⟩ :=
  T.stageCellEquiv_symm_birthCell (k + 1) n j

@[simp] lemma stageCellEquiv_succ_symm_oldCellEquiv (T : CWSubcomplexTower W newCell) (k n : ℕ)
    (i : cell (univ : Set (W k)) n) :
    (T.stageCellEquiv (k + 1) n).symm (T.oldCellEquiv k n i) =
      ⟨((T.stageCellEquiv k n).symm i).1, Nat.le_succ_of_le ((T.stageCellEquiv k n).symm i).2⟩ := by
  simp [stageCellEquiv]

/-- The sequential diagram `ℕ ⥤ TopCat.{u}` of stages `W 0 → W 1 → W 2 → ⋯`. -/
@[expose, simps obj, instance_reducible]
def diagram (T : CWSubcomplexTower W newCell) : ℕ ⥤ TopCat.{u} where
  obj k := TopCat.of (W k)
  map φ := Functor.OfSequence.map (fun k ↦ TopCat.ofHom (T.step k)) _ _ (leOfHom φ)
  map_id i := Functor.OfSequence.map_id _ i
  map_comp _ _ := Functor.OfSequence.map_comp _ _ _ _ _ _

lemma diagram_eq_ofSequence (T : CWSubcomplexTower W newCell) :
    T.diagram = Functor.ofSequence (fun k ↦ TopCat.ofHom (T.step k)) := (rfl)

@[simp] lemma diagram_map_succ (T : CWSubcomplexTower W newCell) (k : ℕ) :
    T.diagram.map (homOfLE (Nat.le_add_right k 1)) = TopCat.ofHom (T.step k) :=
  Functor.OfSequence.map_le_succ _ k

@[reassoc (attr := simp)] lemma step_comp_ι_app (T : CWSubcomplexTower W newCell)
    (c : Cocone T.diagram) (k : ℕ) : TopCat.ofHom (T.step k) ≫ c.ι.app (k + 1) = c.ι.app k := by
  rw [← T.diagram_map_succ, c.w]

@[simp] lemma ι_app_step_apply (T : CWSubcomplexTower W newCell) (c : Cocone T.diagram)
    (k : ℕ) (x : W k) :
    dsimp% c.ι.app (k + 1) (T.step k x) = c.ι.app k x := by
  rw [← TopCat.hom_ofHom (T.step k), ← ConcreteCategory.comp_apply, T.step_comp_ι_app]

/-- Transition maps in `T.diagram` carry the characteristic map of a cell at its birth stage `m`
onto its characteristic map in any later stage `k ≥ m` on the closed unit ball. -/
theorem diagram_map_map_birthCell (T : CWSubcomplexTower W newCell) {m k : ℕ} (hmk : m ≤ k) (n : ℕ)
    (j : newCell m n) {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    T.diagram.map (homOfLE hmk) (map (C := (univ : Set (W m))) n (T.birthCell m n j) x) =
      map (C := (univ : Set (W k))) n (T.stageCellEquiv k n ⟨⟨m, j⟩, hmk⟩) x := by
  induction hmk with
  | refl =>
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), CategoryTheory.Functor.map_id, T.stageCellEquiv_birth]
    rfl
  | @step k hmk ih =>
    rw [← homOfLE_comp hmk (Nat.le_add_right k 1), CategoryTheory.Functor.map_comp,
      ConcreteCategory.comp_apply, T.diagram_map_succ, ih]
    exact (T.step_map_eq_map k n _ hx).trans
      (congrArg (fun i ↦ map n i x) (T.stageCellEquiv_succ_of_le k n ⟨m, j⟩ hmk).symm)

/-- Every transition map `W i → W j` (`i ≤ j`) of the tower is a closed embedding. -/
theorem isClosedEmbedding_diagram_map (T : CWSubcomplexTower W newCell) {i j : ℕ} (hij : i ≤ j) :
    IsClosedEmbedding (T.diagram.map (homOfLE hij)) :=
  TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous T.diagram
    (fun k _ ↦ by
      simp only [diagram_obj, Nat.succ_eq_succ, Nat.succ_eq_add_one, homOfLE_leOfHom,
        diagram_map_succ, ConcreteCategory.hom_ofHom]
      exact T.isClosedEmbedding_step k) hij

/-- For any colimit cocone `c` of `T.diagram`, every stage map `c.ι.app k` is a closed embedding. -/
theorem isClosedEmbedding_ι (T : CWSubcomplexTower W newCell) {c : Cocone T.diagram}
    (hc : IsColimit c) (k : ℕ) : IsClosedEmbedding (c.ι.app k) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit
    (fun _ _ hij ↦ T.isClosedEmbedding_diagram_map hij) hc k

/-- Any colimit `c.pt` of `T.diagram` is a `T₁` space. -/
theorem t1Space_of_isColimit (T : CWSubcomplexTower W newCell) {c : Cocone T.diagram}
    (hc : IsColimit c) : T1Space c.pt :=
  TauCeti.TopCat.t1Space_of_isColimit
    (fun _ _ hij ↦ (T.isClosedEmbedding_diagram_map hij).injective) hc

end StageMachinery

/-! ### Constructors from subcomplexes and cell-sum decompositions -/

section Constructors

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u}

section OfSubcomplex

variable (step : ∀ k, C(W k, W (k + 1))) (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
  (E : ∀ k, CWComplex.Subcomplex (univ : Set (W (k + 1))))
  (coe_E : ∀ k, (E k : Set (W (k + 1))) = range (step k))
  (oldCellEquiv : ∀ k n, cell (univ : Set (W k)) n ≃ ↥((E k).I n))
  (hmap : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ}, x ∈ closedBall 0 1 →
    step k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set (W (k + 1)))) n (oldCellEquiv k n i : cell _ n) x)

/-- Construct a `CWSubcomplexTower` directly from stage subcomplexes `E k` and old-cell
equivalences, using `StageNewCell W E` as the new-cell indexing. -/
def ofSubcomplex : CWSubcomplexTower W (StageNewCell W E) where
  step := step
  isClosedEmbedding_step := isClosedEmbedding_step
  subcomplex := E
  coe_subcomplex := coe_E
  cellZeroEquiv _ := Equiv.subtypeUnivEquiv (isStageNewCell_zero E)
  oldCellEquiv := oldCellEquiv
  newCellEquiv _ _ := Equiv.refl _
  step_map_eq_map := hmap

@[simp] lemma ofSubcomplex_step (k : ℕ) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).step k = step k := (rfl)

@[simp] lemma ofSubcomplex_subcomplex (k : ℕ) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).subcomplex k = E k := (rfl)

lemma ofSubcomplex_cellZeroEquiv (n : ℕ) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).cellZeroEquiv n =
      Equiv.subtypeUnivEquiv (isStageNewCell_zero E) := (rfl)

@[simp] lemma ofSubcomplex_cellZeroEquiv_apply (n : ℕ) (j : StageNewCell W E 0 n) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).cellZeroEquiv n j = j.1 :=
  (rfl)

@[simp] lemma coe_ofSubcomplex_oldCellEquiv_apply (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    ((ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).oldCellEquiv
      k n i : cell (univ : Set (W (k + 1))) n) = (oldCellEquiv k n i : cell _ n) := (rfl)

@[simp] lemma coe_ofSubcomplex_newCellEquiv_apply (k n : ℕ) (j : StageNewCell W E (k + 1) n) :
    ((ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).newCellEquiv
      k n j : cell (univ : Set (W (k + 1))) n) = j.1 := (rfl)

@[simp] lemma ofSubcomplex_birthCell (k n : ℕ) (j : StageNewCell W E k n) :
    (ofSubcomplex step isClosedEmbedding_step E coe_E oldCellEquiv hmap).birthCell k n j = j.1 := by
  cases k <;> simp

end OfSubcomplex

section OfCellSum

variable (step : ∀ k, C(W k, W (k + 1))) (isClosedEmbedding_step : ∀ k, IsClosedEmbedding (step k))
  (cellZeroEquiv : ∀ n, newCell 0 n ≃ cell (univ : Set (W 0)) n)
  (cellSumEquiv : ∀ k n,
    cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n)
  (map_inl : ∀ k n (i : cell (univ : Set (W k)) n) {x : Fin n → ℝ}, x ∈ closedBall 0 1 →
    step k (map (C := (univ : Set (W k))) n i x) =
      map (C := (univ : Set (W (k + 1)))) n (cellSumEquiv k n (Sum.inl i)) x)

/-- Construct a `CWSubcomplexTower` from sum decompositions
`cellSumEquiv k n : cell (univ : Set (W k)) n ⊕ newCell (k + 1) n ≃ cell (univ : Set (W (k + 1))) n`
compatible with `step k` on old cells; the stage subcomplexes are synthesized automatically. -/
def ofCellSum : CWSubcomplexTower W newCell :=
  let I (k n : ℕ) : Set (cell (univ : Set (W (k + 1))) n) :=
    range fun i ↦ cellSumEquiv k n (Sum.inl i)
  have hinr_notMem (k n : ℕ) (j : newCell (k + 1) n) : cellSumEquiv k n (Sum.inr j) ∉ I k n := by
    rintro ⟨i, hi⟩; exact Sum.inl_ne_inr ((cellSumEquiv k n).injective hi)
  { step := step
    isClosedEmbedding_step := isClosedEmbedding_step
    subcomplex k := {
      carrier := range (step k), I := I k, closed' := (isClosedEmbedding_step k).isClosed_range
      union' := by
        rw [empty_union]; ext y; simp only [mem_iUnion, mem_range]; constructor
        · rintro ⟨n, ⟨_, ⟨i, rfl⟩⟩, z, hz, rfl⟩
          exact ⟨map n i z, map_inl k n i (ball_subset_closedBall hz)⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨n, i, z, hz, rfl⟩ := mem_iUnion₂.1
            (CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (W k))).symm ▸ mem_univ x)
          exact ⟨n, ⟨_, i, rfl⟩, z, hz, (map_inl k n i (ball_subset_closedBall hz)).symm⟩ }
    coe_subcomplex _ := rfl
    cellZeroEquiv := cellZeroEquiv
    oldCellEquiv k n := Equiv.ofInjective (fun i ↦ cellSumEquiv k n (Sum.inl i))
      ((cellSumEquiv k n).injective.comp Sum.inl_injective)
    newCellEquiv k n := Equiv.ofBijective
      (fun j ↦ ⟨cellSumEquiv k n (Sum.inr j), hinr_notMem k n j⟩)
      ⟨fun _ _ h ↦ Sum.inr.inj ((cellSumEquiv k n).injective (congrArg Subtype.val h)),
        fun ⟨c, hc⟩ ↦ by
          rcases h : (cellSumEquiv k n).symm c with i | j
          · exact False.elim (hc ⟨i, ((cellSumEquiv k n).symm_apply_eq.1 h).symm⟩)
          · exact ⟨j, Subtype.ext ((cellSumEquiv k n).symm_apply_eq.1 h).symm⟩⟩
    step_map_eq_map := map_inl }

@[simp] lemma ofCellSum_step (k : ℕ) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).step k = step k :=
  (rfl)

@[simp] lemma ofCellSum_subcomplex_I (k n : ℕ) :
    ((ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).subcomplex k).I n =
      range (fun i ↦ cellSumEquiv k n (Sum.inl i)) := (rfl)

@[simp] lemma ofCellSum_cellZeroEquiv (n : ℕ) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).cellZeroEquiv n =
      cellZeroEquiv n := (rfl)

@[simp] lemma coe_ofCellSum_oldCellEquiv_apply (k n : ℕ) (i : cell (univ : Set (W k)) n) :
    ((ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).oldCellEquiv
      k n i : cell (univ : Set (W (k + 1))) n) = cellSumEquiv k n (Sum.inl i) := (rfl)

@[simp] lemma coe_ofCellSum_newCellEquiv_apply (k n : ℕ) (j : newCell (k + 1) n) :
    ((ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).newCellEquiv
      k n j : cell (univ : Set (W (k + 1))) n) = cellSumEquiv k n (Sum.inr j) := (rfl)

lemma ofCellSum_birthCell_zero (n : ℕ) (j : newCell 0 n) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).birthCell 0 n j =
      cellZeroEquiv n j := (rfl)

lemma ofCellSum_birthCell_succ (k n : ℕ) (j : newCell (k + 1) n) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).birthCell
      (k + 1) n j = cellSumEquiv k n (Sum.inr j) := (rfl)

@[simp] lemma ofCellSum_stepCellEquiv (k n : ℕ) :
    (ofCellSum step isClosedEmbedding_step cellZeroEquiv cellSumEquiv map_inl).stepCellEquiv k n =
      cellSumEquiv k n := by ext (_ | _) <;> simp

end OfCellSum

end Constructors

/-! ### Constant and stabilizing two-stage examples -/

section Examples

section Const

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- New-cell indexing of `CWSubcomplexTower.const X`: stage `0` has all cells of `X` and stages
`k + 1` attach no new cells (`PEmpty`). -/
abbrev ConstNewCell : ℕ → ℕ → Type u
  | 0, n => cell (univ : Set X) n
  | _ + 1, _ => PEmpty

/-- The constant `CWSubcomplexTower` on a Hausdorff classical CW complex `X`. -/
def const : CWSubcomplexTower (fun _ ↦ X) (ConstNewCell X) :=
  ofCellSum (fun _ ↦ ContinuousMap.id X) (fun _ ↦ .id) (fun _ ↦ Equiv.refl _)
    (fun _ _ ↦ Equiv.sumEmpty _ _) (fun _ _ _ {_} _ ↦ rfl)

@[simp] lemma const_step (k : ℕ) :
    (const X).step k = ContinuousMap.id X := ofCellSum_step _ _ _ _ _ k

@[simp] lemma const_subcomplex_I (k n : ℕ) : ((const X).subcomplex k).I n = univ := by
  rw [const]; generalize_proofs; rw [ofCellSum_subcomplex_I]; ext; simp

@[simp] lemma const_cellZeroEquiv (n : ℕ) : (const X).cellZeroEquiv n = Equiv.refl _ :=
  ofCellSum_cellZeroEquiv _ _ _ _ _ n

@[simp] lemma coe_const_oldCellEquiv_apply (k n : ℕ) (i : cell (univ : Set X) n) :
    ((const X).oldCellEquiv k n i : cell (univ : Set X) n) = i := by
  rw [const]; generalize_proofs; rw [coe_ofCellSum_oldCellEquiv_apply]; rfl

@[simp] lemma const_stepCellEquiv (k n : ℕ) : (const X).stepCellEquiv k n = Equiv.sumEmpty _ _ :=
  ofCellSum_stepCellEquiv _ _ _ _ _ k n

lemma const_birthCell_zero (n : ℕ) (i : cell (univ : Set X) n) : (const X).birthCell 0 n i = i := by
  simp

end Const

/-- Stage spaces `W₀, W₁, W₁, ⋯` of a two-stage stabilizing tower. -/
@[expose, instance_reducible]
def PairStage (W₀ W₁ : Type u) (k : ℕ) : Type u := Nat.casesOn k W₀ (fun _ ↦ W₁)

instance instTopologicalSpacePairStage {W₀ W₁ : Type u} [TopologicalSpace W₀]
    [TopologicalSpace W₁] (k : ℕ) : TopologicalSpace (PairStage W₀ W₁ k) :=
  Nat.casesOn k inferInstance (fun _ ↦ inferInstance)

instance instT2SpacePairStage {W₀ W₁ : Type u} [TopologicalSpace W₀] [T2Space W₀]
    [TopologicalSpace W₁] [T2Space W₁] (k : ℕ) : T2Space (PairStage W₀ W₁ k) :=
  Nat.casesOn k inferInstance (fun _ ↦ inferInstance)

instance instCWComplexPairStage {W₀ W₁ : Type u} [TopologicalSpace W₀]
    [CWComplex (univ : Set W₀)] [TopologicalSpace W₁] [CWComplex (univ : Set W₁)] (k : ℕ) :
    CWComplex (univ : Set (PairStage W₀ W₁ k)) :=
  Nat.casesOn k inferInstance (fun _ ↦ inferInstance)

/-- New-cell indexing of `CWSubcomplexTower.pair`: stage `0` has `cell (univ : Set W₀) n`, stage
`1` attaches `new₁ n`, and higher stages `k + 2` attach `PEmpty`. -/
abbrev PairNewCell (W₀ : Type u) [TopologicalSpace W₀] [CWComplex (univ : Set W₀)]
    (new₁ : ℕ → Type u) (k n : ℕ) : Type u :=
  Nat.casesOn k (cell (univ : Set W₀) n) (fun k' ↦ Nat.casesOn k' (new₁ n) (fun _ ↦ PEmpty))

section Pair

variable {W₀ W₁ : Type u}
  [TopologicalSpace W₀] [T2Space W₀] [CWComplex (univ : Set W₀)]
  [TopologicalSpace W₁] [T2Space W₁] [CWComplex (univ : Set W₁)]
  {new₁ : ℕ → Type u}
  (f : C(W₀, W₁)) (hf : IsClosedEmbedding f)
  (cellSum : ∀ n, cell (univ : Set W₀) n ⊕ new₁ n ≃ cell (univ : Set W₁) n)
  (hmap : ∀ n (i : cell (univ : Set W₀) n) {x : Fin n → ℝ}, x ∈ closedBall 0 1 →
    f (map (C := (univ : Set W₀)) n i x) =
      map (C := (univ : Set W₁)) n (cellSum n (Sum.inl i)) x)

/-- A two-stage-then-stabilizing `CWSubcomplexTower` built from a single closed CW subcomplex
embedding `f : C(W₀, W₁)`: stage `1` attaches `new₁` (which may have strictly smaller dimensions
than cells of `W₀`) and stages `k + 2` stabilize at `W₁`. -/
def pair : CWSubcomplexTower (PairStage W₀ W₁) (PairNewCell W₀ new₁) :=
  ofCellSum (W := PairStage W₀ W₁)
    (fun | 0 => f | _ + 1 => ContinuousMap.id W₁) (fun | 0 => hf | _ + 1 => .id)
    (fun _ ↦ Equiv.refl _) (fun | 0, n => cellSum n | _ + 1, _ => Equiv.sumEmpty _ _)
    (fun k n i {_} hx ↦ by cases k with | zero => exact hmap n i hx | succ _ => rfl)

@[simp] lemma pair_step_zero : (pair f hf cellSum hmap).step 0 = f := ofCellSum_step _ _ _ _ _ 0

@[simp] lemma pair_step_succ (k : ℕ) : (pair f hf cellSum hmap).step (k + 1) = .id W₁ :=
  ofCellSum_step _ _ _ _ _ (k + 1)

@[simp] lemma pair_subcomplex_zero_I (n : ℕ) :
    ((pair f hf cellSum hmap).subcomplex 0).I n = range (fun i ↦ cellSum n (Sum.inl i)) :=
  ofCellSum_subcomplex_I _ _ _ _ _ 0 n

@[simp] lemma pair_subcomplex_succ_I (k n : ℕ) :
    ((pair f hf cellSum hmap).subcomplex (k + 1)).I n = univ := by
  rw [pair]; generalize_proofs; rw [ofCellSum_subcomplex_I]; ext; simp

@[simp] lemma pair_cellZeroEquiv (n : ℕ) : (pair f hf cellSum hmap).cellZeroEquiv n = .refl _ :=
  ofCellSum_cellZeroEquiv _ _ _ _ _ n

@[simp] lemma coe_pair_oldCellEquiv_zero_apply (n : ℕ) (i : cell (univ : Set W₀) n) :
    ((pair f hf cellSum hmap).oldCellEquiv 0 n i : cell (univ : Set W₁) n) =
      cellSum n (Sum.inl i) := by
  rw [pair]; generalize_proofs; rw [coe_ofCellSum_oldCellEquiv_apply]

@[simp] lemma coe_pair_oldCellEquiv_succ_apply (k n : ℕ) (i : cell (univ : Set W₁) n) :
    ((pair f hf cellSum hmap).oldCellEquiv (k + 1) n i : cell (univ : Set W₁) n) = i := by
  rw [pair]; generalize_proofs; rw [coe_ofCellSum_oldCellEquiv_apply]; rfl

@[simp] lemma coe_pair_newCellEquiv_zero_apply (n : ℕ) (j : new₁ n) :
    dsimp% ((pair f hf cellSum hmap).newCellEquiv 0 n j : cell (univ : Set W₁) n) =
      cellSum n (Sum.inr j) := by
  rw [pair]; generalize_proofs; rw [coe_ofCellSum_newCellEquiv_apply]

@[simp] lemma pair_stepCellEquiv_zero (n : ℕ) :
    (pair f hf cellSum hmap).stepCellEquiv 0 n = cellSum n :=
  ofCellSum_stepCellEquiv _ _ _ _ _ 0 n

@[simp] lemma pair_stepCellEquiv_succ (k n : ℕ) :
    (pair f hf cellSum hmap).stepCellEquiv (k + 1) n = Equiv.sumEmpty _ _ :=
  ofCellSum_stepCellEquiv _ _ _ _ _ (k + 1) n

lemma pair_birthCell_zero (n : ℕ) (i : cell (univ : Set W₀) n) :
    (pair f hf cellSum hmap).birthCell 0 n i = i := by simp

lemma pair_birthCell_one (n : ℕ) (j : new₁ n) :
    (pair f hf cellSum hmap).birthCell 1 n j = cellSum n (Sum.inr j) :=
  coe_pair_newCellEquiv_zero_apply f hf cellSum hmap n j

end Pair

end Examples

end CWSubcomplexTower

end TauCeti
