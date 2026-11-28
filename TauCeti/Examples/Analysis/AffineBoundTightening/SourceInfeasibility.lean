/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.SourceInfeasibility
public import TauCeti.Analysis.AffineBoundTightening.Examples
public import TauCeti.Examples.Analysis.AffineBoundTightening.Source
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# One-way source infeasibility controls

The unit row with variable singleton one and cap zero has an infeasible scalar LP.
An empty extra set can instead give an empty original set with a feasible scalar LP.
Finally both directions of each native four-row equality give eight actual inequalities:
their scalar program is feasible and every public iterate is nonempty, but their original
bounded affine set is empty. Extra and integer restrictions remain unchanged throughout.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening.SourceInfeasibilityExamples

noncomputable section

/-- The row `x ≤ 0` with `x = 1` has an infeasible scalar LP and an empty bounded source set,
independently of additional or designated-integer restrictions. -/
theorem unit_row_infeasible (extra : Set (Fin 1 → ℝ)) (integers : Finset (Fin 1)) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    let q := sourceInitial A ![0] ![1] ![1]
    (¬ ∃ p, IsFeasible A q p) ∧ sourceSet A ![0] extra integers ∩ Icc ![1] ![1] = ∅ := by
  intro A q
  have hnone : ¬ ∃ p, IsFeasible A q p := by
    rintro ⟨p, hp⟩
    have hx : 1 ≤ p.endpoints.1 (.inl 0) := by
      simpa [q] using hp.within.fst_le (.inl 0)
    have hb : p.endpoints.1 (.inr 0) ≤ 0 := by
      simpa [q] using (hp.fst_le_snd (.inr 0)).trans (hp.within.le_snd (.inr 0))
    have hz : p.zL 0 0 = p.endpoints.1 (.inl 0) := by
      rw [hp.zL_eq 0 0, zLo_of_nonneg (A := A) (by norm_num [A])]
      norm_num [A]
    have hs := hp.sum_zL_le 0
    simp only [Fin.sum_univ_one, hz] at hs
    linarith
  exact ⟨hnone, source_infeasible A ![0] ![1] ![1] extra integers hnone⟩

/-- Empty extra restrictions can make the source empty while the zero graph still supplies
an actual feasible scalar singleton, with any designated integer coordinates. -/
theorem empty_extra_feasible_lp (integers : Finset (Fin 1)) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q := sourceInitial A ![0] ![0] ![0]
    IsFeasible A q (graphAssignment A ![0]) ∧
      sourceSet A ![0] ∅ integers ∩ Icc ![0] ![0] = ∅ := by
  intro A q
  constructor
  · apply isFeasible_graphAssignment
    apply mem_Icc_sourceInitial_graph_iff.mpr
    refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
    intro i
    norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_one]
  · rw [SourceExamples.empty_extra]
    simp

/-- Native four-row lower variable endpoints, namely `(-1,-1,-1)`. -/
def equalityLower : Fin 3 → ℝ := fun j => Examples.fourRowBox.1 (.inl j)

/-- Native four-row upper variable endpoints, namely `(1,1,1)`. -/
def equalityUpper : Fin 3 → ℝ := fun j => Examples.fourRowBox.2 (.inl j)

/-- Both actual inequality directions of each of the native four equalities. The first four
rows are the native matrix; the last four are their negatives. -/
def equalityRows : Matrix (Fin 8) (Fin 3) ℝ :=
  fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => Fin 3 → ℝ)
    (fun i => Examples.fourRowMatrix i) (fun i j => -Examples.fourRowMatrix i j) k

/-- Caps for both inequality directions: the native upper row endpoints, then the negatives
of the lower endpoints, giving `(0,0,0,1,0,0,0,-1)`. -/
def equalityCaps : Fin 8 → ℝ :=
  fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.2 (.inr i)) (fun i => -Examples.fourRowBox.1 (.inr i)) k

/-- Copy the native fixed box to the positive rows and reflect its intervals on the negative
rows. Its variable box is unchanged. -/
def equalityBox : Raw 3 8 :=
  (Sum.elim equalityLower (fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.1 (.inr i)) (fun i => -Examples.fourRowBox.2 (.inr i)) k),
   Sum.elim equalityUpper (fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.2 (.inr i)) (fun i => -Examples.fourRowBox.1 (.inr i)) k))

/-- Actual source initialization of the eight inequalities on the native variable box. -/
def equalityInitial : Raw 3 8 :=
  sourceInitial equalityRows equalityCaps equalityLower equalityUpper

private theorem positive_products (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) (j : Fin 3) :
    zLo equalityRows q (i.castAdd 4) j = zLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    zHi equalityRows q (i.castAdd 4) j = zHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  by_cases ha : 0 ≤ Examples.fourRowMatrix i j
  · have he : 0 ≤ equalityRows (i.castAdd 4) j := by simpa [equalityRows] using ha
    constructor
    · rw [zLo_of_nonneg he, zLo_of_nonneg ha, hl]
      simp only [equalityRows, Fin.addCases_left, equalityLower]
    · rw [zHi_of_nonneg he, zHi_of_nonneg ha, hu]
      simp only [equalityRows, Fin.addCases_left, equalityUpper]
  · have hn := le_of_not_ge ha
    have he : equalityRows (i.castAdd 4) j ≤ 0 := by simpa [equalityRows] using hn
    constructor
    · rw [zLo_of_nonpos he, zLo_of_nonpos hn, hu]
      simp only [equalityRows, Fin.addCases_left, equalityUpper]
    · rw [zHi_of_nonpos he, zHi_of_nonpos hn, hl]
      simp only [equalityRows, Fin.addCases_left, equalityLower]

private theorem negative_products (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) (j : Fin 3) :
    zLo equalityRows q (Fin.natAdd 4 i) j = -zHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    zHi equalityRows q (Fin.natAdd 4 i) j =
      -zLo Examples.fourRowMatrix Examples.fourRowBox i j := by
  have hcoef : equalityRows (Fin.natAdd 4 i) j = -Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_right]
  by_cases ha : 0 ≤ Examples.fourRowMatrix i j
  · have he : equalityRows (Fin.natAdd 4 i) j ≤ 0 := by
      rw [hcoef]
      exact neg_nonpos.mpr ha
    constructor
    · rw [zLo_of_nonpos he, zHi_of_nonneg ha, hu]
      simp only [equalityRows, Fin.addCases_right, equalityUpper, neg_mul]
    · rw [zHi_of_nonpos he, zLo_of_nonneg ha, hl]
      simp only [equalityRows, Fin.addCases_right, equalityLower, neg_mul]
  · have hn := le_of_not_ge ha
    have he : 0 ≤ equalityRows (Fin.natAdd 4 i) j := by
      rw [hcoef]
      exact neg_nonneg.mpr hn
    constructor
    · rw [zLo_of_nonneg he, zHi_of_nonpos hn, hl]
      simp only [equalityRows, Fin.addCases_right, equalityLower, neg_mul]
    · rw [zHi_of_nonneg he, zLo_of_nonpos hn, hu]
      simp only [equalityRows, Fin.addCases_right, equalityUpper, neg_mul]

private theorem row_images (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) :
    imageLo equalityRows q (i.castAdd 4) = imageLo Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageHi equalityRows q (i.castAdd 4) = imageHi Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageLo equalityRows q (Fin.natAdd 4 i) =
      -imageHi Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageHi equalityRows q (Fin.natAdd 4 i) =
      -imageLo Examples.fourRowMatrix Examples.fourRowBox i := by
  have hpL j := (positive_products q hl hu i j).1
  have hpU j := (positive_products q hl hu i j).2
  have hnL j := (negative_products q hl hu i j).1
  have hnU j := (negative_products q hl hu i j).2
  simp only [imageLo_def, imageHi_def, hpL, hpU, hnL, hnU, Finset.sum_neg_distrib, and_self]

private theorem row_rests (i : Fin 4) (j : Fin 3) :
    restLo equalityRows equalityBox (i.castAdd 4) j =
      restLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restHi equalityRows equalityBox (i.castAdd 4) j =
      restHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restLo equalityRows equalityBox (Fin.natAdd 4 i) j =
      -restHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restHi equalityRows equalityBox (Fin.natAdd 4 i) j =
      -restLo Examples.fourRowMatrix Examples.fourRowBox i j := by
  have hpL k := (positive_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).1
  have hpU k := (positive_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).2
  have hnL k := (negative_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).1
  have hnU k := (negative_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).2
  simp only [restLo_def, restHi_def, hpL, hpU, hnL, hnU, Finset.sum_neg_distrib, and_self]

private theorem positive_inverses (i : Fin 4) (j : Fin 3) :
    inverseLo equalityRows equalityBox (i.castAdd 4) j =
      inverseLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    inverseHi equalityRows equalityBox (i.castAdd 4) j =
      inverseHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  obtain ⟨hl, hu, _, _⟩ := row_rests i j
  have hcoef : equalityRows (i.castAdd 4) j = Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_left]
  have hrL : equalityBox.1 (.inr (i.castAdd 4)) = Examples.fourRowBox.1 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_left]
  have hrU : equalityBox.2 (.inr (i.castAdd 4)) = Examples.fourRowBox.2 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_left]
  have hvL : equalityBox.1 (.inl j) = Examples.fourRowBox.1 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityLower]
  have hvU : equalityBox.2 (.inl j) = Examples.fourRowBox.2 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityUpper]
  rcases lt_trichotomy (Examples.fourRowMatrix i j) 0 with ha | ha | ha
  · have he : equalityRows (i.castAdd 4) j < 0 := by rw [hcoef]; exact ha
    constructor
    · rw [inverseLo_of_neg he, inverseLo_of_neg ha, hl, hrU, hcoef]
    · rw [inverseHi_of_neg he, inverseHi_of_neg ha, hu, hrL, hcoef]
  · have he : equalityRows (i.castAdd 4) j = 0 := hcoef.trans ha
    constructor
    · exact (inverseLo_of_zero he).trans (hvL.trans (inverseLo_of_zero ha).symm)
    · exact (inverseHi_of_zero he).trans (hvU.trans (inverseHi_of_zero ha).symm)
  · have he : 0 < equalityRows (i.castAdd 4) j := by rw [hcoef]; exact ha
    constructor
    · rw [inverseLo_of_pos he, inverseLo_of_pos ha, hu, hrL, hcoef]
    · rw [inverseHi_of_pos he, inverseHi_of_pos ha, hl, hrU, hcoef]

private theorem negative_inverses (i : Fin 4) (j : Fin 3) :
    inverseLo equalityRows equalityBox (Fin.natAdd 4 i) j =
      inverseLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    inverseHi equalityRows equalityBox (Fin.natAdd 4 i) j =
      inverseHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  obtain ⟨_, _, hl, hu⟩ := row_rests i j
  have hcoef : equalityRows (Fin.natAdd 4 i) j = -Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_right]
  have hrL : equalityBox.1 (.inr (Fin.natAdd 4 i)) = -Examples.fourRowBox.2 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_right]
  have hrU : equalityBox.2 (.inr (Fin.natAdd 4 i)) = -Examples.fourRowBox.1 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_right]
  have hvL : equalityBox.1 (.inl j) = Examples.fourRowBox.1 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityLower]
  have hvU : equalityBox.2 (.inl j) = Examples.fourRowBox.2 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityUpper]
  have hdiv (u v a : ℝ) : (-u - -v) / -a = (u - v) / a := by
    rw [div_neg, neg_sub_neg]
    ring
  rcases lt_trichotomy (Examples.fourRowMatrix i j) 0 with ha | ha | ha
  · have he : 0 < equalityRows (Fin.natAdd 4 i) j := by
      rw [hcoef]
      exact neg_pos.mpr ha
    constructor
    · rw [inverseLo_of_pos he, inverseLo_of_neg ha, hu, hrL, hcoef, hdiv]
    · rw [inverseHi_of_pos he, inverseHi_of_neg ha, hl, hrU, hcoef, hdiv]
  · have he : equalityRows (Fin.natAdd 4 i) j = 0 := hcoef.trans (neg_eq_zero.mpr ha)
    constructor
    · exact (inverseLo_of_zero he).trans (hvL.trans (inverseLo_of_zero ha).symm)
    · exact (inverseHi_of_zero he).trans (hvU.trans (inverseHi_of_zero ha).symm)
  · have he : equalityRows (Fin.natAdd 4 i) j < 0 := by
      rw [hcoef]
      exact neg_neg_of_pos ha
    constructor
    · rw [inverseLo_of_neg he, inverseLo_of_pos ha, hl, hrU, hcoef, hdiv]
    · rw [inverseHi_of_neg he, inverseHi_of_pos ha, hu, hrL, hcoef, hdiv]

private theorem equality_box_ordered : equalityBox.1 ≤ equalityBox.2 := by
  have ho := Examples.fourRow_feasible_without_graph_point.1
  intro c
  cases c with
  | inl j => exact ho (.inl j)
  | inr i =>
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · simpa only [equalityBox, Sum.elim_inr, Fin.addCases_left] using ho (.inr k)
    · simpa only [equalityBox, Sum.elim_inr, Fin.addCases_right] using
        neg_le_neg (ho (.inr k))

private theorem equality_box_within_initial : Within equalityBox equalityInitial := by
  have hrow := (isFixedPt_step_iff.mp Examples.fourRow_feasible_without_graph_point.2.1).2.1
  have himg := row_images
    (Sum.elim equalityLower (fun _ => 0), Sum.elim equalityUpper (fun _ => 0))
    (fun _ => rfl) (fun _ => rfl)
  apply within_iff.mpr
  constructor
  · intro c
    cases c with
    | inl j => simp [equalityBox, equalityInitial]
    | inr i =>
      refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
      · simp only [equalityInitial, sourceInitial_fst_inr, equalityBox, Sum.elim_inr,
          Fin.addCases_left]
        exact (min_le_left _ _).trans ((himg k).1.trans_le (hrow k).1)
      · simp only [equalityInitial, sourceInitial_fst_inr, equalityBox, Sum.elim_inr,
          Fin.addCases_right]
        exact (min_le_left _ _).trans ((himg k).2.2.1.trans_le (neg_le_neg (hrow k).2))
  · intro c
    cases c with
    | inl j => simp [equalityBox, equalityInitial]
    | inr i =>
      refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i <;>
        simp [equalityBox, equalityInitial, equalityCaps]

private theorem equality_box_fixed :
    Function.IsFixedPt (step equalityRows equalityInitial) equalityBox := by
  obtain ⟨_, hrow, hinv⟩ :=
    isFixedPt_step_iff.mp Examples.fourRow_feasible_without_graph_point.2.1
  have himg := row_images equalityBox (fun _ => rfl) (fun _ => rfl)
  refine isFixedPt_step_iff.mpr ⟨equality_box_within_initial, ?_, ?_⟩
  · intro i
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · rw [(himg k).1, (himg k).2.1]
      simpa only [equalityBox, Sum.elim_inr, Fin.addCases_left] using hrow k
    · rw [(himg k).2.2.1, (himg k).2.2.2]
      simpa only [equalityBox, Sum.elim_inr, Fin.addCases_right] using
        And.intro (neg_le_neg (hrow k).2) (neg_le_neg (hrow k).1)
  · intro i j
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · rw [(positive_inverses k j).1, (positive_inverses k j).2]
      simpa only [equalityBox, Sum.elim_inl, equalityLower, equalityUpper] using hinv k j
    · rw [(negative_inverses k j).1, (negative_inverses k j).2]
      simpa only [equalityBox, Sum.elim_inl, equalityLower, equalityUpper] using hinv k j

private theorem equality_source_empty (extra : Set (Fin 3 → ℝ))
    (integers : Finset (Fin 3)) :
    sourceSet equalityRows equalityCaps extra integers ∩ Icc equalityLower equalityUpper = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hs, hx⟩
  have hr := (mem_sourceSet.mp hs).1
  have hg : graph Examples.fourRowMatrix x ∈ Icc Examples.fourRowBox.1 Examples.fourRowBox.2 := by
    apply mem_Icc_graph_iff.mpr
    refine ⟨fun j => ⟨hx.1 j, hx.2 j⟩, fun i => ?_⟩
    have hup := hr (i.castAdd 4)
    have hlo := hr (Fin.natAdd 4 i)
    simp only [Matrix.mulVec_apply_eq_sum, equalityRows, equalityCaps, Fin.addCases_left,
      Fin.addCases_right, neg_mul, Finset.sum_neg_distrib] at hup hlo
    exact ⟨neg_le_neg_iff.mp hlo, hup⟩
  exact Examples.fourRow_feasible_without_graph_point.2.2.2 x hg

/-- Both directions of the four inconsistent native equalities give eight inequalities with
an actual scalar-feasible canonical box and nonempty public iterates, yet no original feasible
point in the initial box, for arbitrary unchanged extra and integer restrictions. -/
theorem eight_rows_nonempty_but_source_empty (extra : Set (Fin 3 → ℝ))
    (integers : Finset (Fin 3)) :
    IsFeasible equalityRows equalityInitial (canonical equalityRows equalityBox) ∧
    (∀ k, (publicRun equalityRows equalityInitial k : Set (Coord 3 8 → ℝ)).Nonempty) ∧
    sourceSet equalityRows equalityCaps extra integers ∩ Icc equalityLower equalityUpper = ∅ :=
  ⟨isFeasible_canonical_iff.mpr ⟨equality_box_ordered, equality_box_fixed⟩,
    coe_publicRun_nonempty_of_isFixedPt_step equality_box_ordered equality_box_fixed,
    equality_source_empty extra integers⟩

end

end TauCeti.AffineBoundTightening.SourceInfeasibilityExamples
