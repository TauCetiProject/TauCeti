/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lifting.SupportRows
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Examples of free-height elimination over finite support rows

Small real examples for `TauCeti.ConvexLifting.sharedRows` and
`TauCeti.ConvexLifting.independentRows`.

* Singleton supports recover the single sum row, and constant rows `{1, 3}` and `{2}` have
  maximum-sum `5`, so the shared projection is `x ∈ D ∧ 5 ≤ b`.
* With no components the shared projection is `x ∈ D ∧ 0 ≤ b`; with no anchors the independent
  projection is `D`, and with no components it is `x ∈ D ∧ ∀ a, 0 ≤ b a`.
* On `D = [0, 1]` with one component of empty support and budget `-3`, every `x ∈ D` lifts with
  height `-3`, and the objective `x` attains its minimum at `(0, -3)`.
* With one constant row `1` and budget one, free heights project onto `D` using the height `1`,
  but restricting the height to `0` empties the system: the height domain cannot be dropped.
* For the tangent rows `2 a x_j - 1` of `x_j ^ 2` at the anchors `a = ±1` on the box `[-1, 1]²`
  with budget `1/2`, independent heights cut out `|x₀ + x₁| ≤ 5/4` and shared heights cut out
  `|x₀| + |x₁| ≤ 5/4`. The point `(1, -1/2)` separates the two: shared heights enforce the mixed
  choices of anchors, independent heights only the diagonal ones.
-/

public section

open Set TauCeti.ConvexLifting

namespace TauCeti.Examples.SupportRows

/-- Singleton supports: with one row `c j` per component, shared heights exist exactly when the
single sum row `∑ j, row j (c j) x ≤ b` holds. -/
theorem exists_mem_sharedRows_singleton_iff {X ι κ : Type*} [Fintype κ] {D : Set X}
    {row : κ → ι → X → ℝ} {c : κ → ι} {b : ℝ} (x : X) :
    (∃ y, (x, y) ∈ sharedRows D row (fun j => {c j}) b) ↔ x ∈ D ∧ ∑ j, row j (c j) x ≤ b := by
  rw [exists_mem_sharedRows_iff_sum_sup'_le (fun j => Finset.singleton_nonempty (c j))]
  simp

/-- Constant rows `{1, 3}` and `{2}` have maximum-sum `5`, so shared heights exist exactly when
`x ∈ D` and `5 ≤ b`. -/
theorem exists_mem_sharedRows_one_three_two_iff {X : Type*} {D : Set X} {b : ℝ} (x : X) :
    (∃ y, (x, y) ∈ sharedRows D (fun _ (i : ℕ) _ => (i : ℝ)) ![{1, 3}, {2}] b) ↔
      x ∈ D ∧ 5 ≤ b := by
  rw [exists_mem_sharedRows_iff_sum_sup'_le (by simp [Fin.forall_fin_two])]
  norm_num [Fin.sum_univ_two]

/-- Every mixed choice of one row from `{1, 3}` and one from `{2}` has sum `3` or `5`. -/
theorem sum_choice_one_three_two {c : Fin 2 → ℕ}
    (hc : ∀ j, c j ∈ (![{1, 3}, {2}] j : Finset ℕ)) :
    ∑ j, (c j : ℝ) = 3 ∨ ∑ j, (c j : ℝ) = 5 := by
  have h0 := hc 0
  have h1 := hc 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_insert,
    Finset.mem_singleton] at h0 h1
  rcases h0 with h0 | h0 <;> norm_num [Fin.sum_univ_two, h0, h1]

/-- With no components, shared heights exist exactly when `x ∈ D` and `0 ≤ b`. -/
theorem exists_mem_sharedRows_fin_zero_iff {X ι : Type*} {D : Set X} {row : Fin 0 → ι → X → ℝ}
    {H : Fin 0 → Finset ι} {b : ℝ} (x : X) :
    (∃ y, (x, y) ∈ sharedRows D row H b) ↔ x ∈ D ∧ 0 ≤ b := by
  rw [exists_mem_sharedRows_iff_sum_sup'_le (fun j => Fin.elim0 j)]
  simp

/-- One component with empty support on `[0, 1]` and budget `-3`: every `x ∈ [0, 1]` lifts with
height `-3`. -/
theorem mk_mem_sharedRows_empty_support {row : Fin 1 → ℕ → ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc 0 1) :
    (x, fun _ => -3) ∈ sharedRows (Icc 0 1) row (fun _ => ∅) (-3) := by
  simpa using hx

/-- One component with empty support on `[0, 1]` and budget `-3`: the projection is `[0, 1]`. -/
theorem fst_image_sharedRows_empty_support {row : Fin 1 → ℕ → ℝ → ℝ} :
    Prod.fst '' sharedRows (Icc 0 1) row (fun _ => ∅) (-3) = Icc 0 1 := by
  ext x
  simpa only [mem_image, Prod.exists, exists_and_right, exists_eq_right] using
    exists_mem_sharedRows_iff_of_eq_empty (j₀ := 0) rfl x

/-- One component with empty support on `[0, 1]` and budget `-3`: the objective `x` attains its
minimum zero at the feasible pair `(0, -3)`. -/
theorem isMinOn_fst_sharedRows_empty_support {row : Fin 1 → ℕ → ℝ → ℝ} :
    ((0 : ℝ), fun _ => (-3 : ℝ)) ∈ sharedRows (Icc 0 1) row (fun _ => ∅) (-3) ∧
      IsMinOn Prod.fst (sharedRows (Icc 0 1) row (fun _ => ∅) (-3)) (0, fun _ => -3) :=
  ⟨mk_mem_sharedRows_empty_support (by simp),
    isMinOn_iff.2 fun _ hz => (mem_sharedRows_iff.1 hz).1.1⟩

/-- One constant row `1` with budget one: free heights project onto the whole domain. -/
theorem fst_image_sharedRows_const_one {X : Type*} {D : Set X} :
    Prod.fst '' sharedRows D (fun (_ : Fin 1) (_ : Unit) _ => (1 : ℝ)) (fun _ => {()}) 1 = D := by
  rw [fst_image_sharedRows (fun _ => Finset.singleton_nonempty ())]
  ext x
  simp

/-- One constant row `1` with budget one: restricting the height to `0` makes the row `1 ≤ y`
impossible, so the restricted system is empty although its free-height projection is `D`. -/
theorem sharedRows_const_one_inter_height_zero_eq_empty {X : Type*} {D : Set X} :
    sharedRows D (fun (_ : Fin 1) (_ : Unit) _ => (1 : ℝ)) (fun _ => {()}) 1 ∩ {z | z.2 = 0} =
      ∅ := by
  ext ⟨x, y⟩
  simp only [mem_inter_iff, mem_sharedRows_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨-, hrow, -⟩ rfl
  exact absurd (hrow 0 () (Finset.mem_singleton_self ())) (by simp)

/-- With no anchors, independent heights exist exactly on `D`. -/
theorem exists_mem_independentRows_iff_of_isEmpty {X κ α : Type*} [Fintype κ] [IsEmpty α]
    {D : Set X} {row : α → κ → X → ℝ} {b : α → ℝ} (x : X) :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D := by
  simp

/-- With no components, independent heights exist exactly when `x ∈ D` and every anchor's budget
is nonnegative. -/
theorem exists_mem_independentRows_fin_zero_iff {X α : Type*} {D : Set X}
    {row : α → Fin 0 → X → ℝ} {b : α → ℝ} (x : X) :
    (∃ y, (x, y) ∈ independentRows D row b) ↔ x ∈ D ∧ ∀ a, 0 ≤ b a := by
  simp

/-- The tangent row `2 a x_j - 1` of `x_j ^ 2` at the anchor coordinate `a = ±1`, indexed by the
anchors `0 ↦ (1, 1)` and `1 ↦ (-1, -1)`. -/
def squareTangentRow (a j : Fin 2) (x : Fin 2 → ℝ) : ℝ :=
  2 * ![1, -1] a * x j - 1

/-- The larger of the two tangent rows of `x_j ^ 2` is `2 |x_j| - 1`. -/
theorem sup'_squareTangentRow (j : Fin 2) (x : Fin 2 → ℝ) :
    (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty (fun a => squareTangentRow a j x) =
      2 * |x j| - 1 := by
  refine le_antisymm (Finset.sup'_le _ _ ?_) ?_
  · simp only [Finset.mem_univ, forall_const, Fin.forall_fin_two, squareTangentRow,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> linarith [le_abs_self (x j), neg_abs_le (x j)]
  · rcases abs_cases (x j) with ⟨h, -⟩ | ⟨h, -⟩
    · refine le_of_eq_of_le ?_
        (Finset.le_sup' (fun a => squareTangentRow a j x) (Finset.mem_univ 0))
      simp [squareTangentRow, h]
    · refine le_of_eq_of_le ?_
        (Finset.le_sup' (fun a => squareTangentRow a j x) (Finset.mem_univ 1))
      simp only [squareTangentRow, h, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring

/-- Shared heights over both anchors on `[-1, 1]²` with budget `1/2` cut out
`|x₀| + |x₁| ≤ 5/4`. -/
theorem exists_mem_sharedRows_squareTangentRow_iff (x : Fin 2 → ℝ) :
    (∃ y, (x, y) ∈ sharedRows (Icc (-1) 1) (fun j a => squareTangentRow a j) (fun _ => Finset.univ)
      (1 / 2)) ↔ x ∈ Icc (-1) 1 ∧ |x 0| + |x 1| ≤ 5 / 4 := by
  rw [exists_mem_sharedRows_iff_sum_sup'_le (fun _ => Finset.univ_nonempty)]
  simp only [sup'_squareTangentRow, Fin.sum_univ_two]
  exact and_congr_right fun _ => ⟨fun h => by linarith, fun h => by linarith⟩

/-- Independent heights at the two anchors on `[-1, 1]²` with budget `1/2` cut out
`|x₀ + x₁| ≤ 5/4`. -/
theorem exists_mem_independentRows_squareTangentRow_iff (x : Fin 2 → ℝ) :
    (∃ y, (x, y) ∈ independentRows (Icc (-1) 1) squareTangentRow fun _ => 1 / 2) ↔
      x ∈ Icc (-1) 1 ∧ |x 0 + x 1| ≤ 5 / 4 := by
  rw [exists_mem_independentRows_iff]
  simp only [Fin.forall_fin_two, Fin.sum_univ_two, squareTangentRow, Matrix.cons_val_zero,
    Matrix.cons_val_one, abs_le]
  exact and_congr_right fun _ =>
    ⟨fun h => ⟨by linarith [h.2], by linarith [h.1]⟩, fun h => ⟨by linarith, by linarith⟩⟩

/-- The point `(1, -1/2)` admits independent heights but no shared heights: shared heights enforce
the mixed choice of anchors `(1, 1)` in the first component and `(-1, -1)` in the second. -/
theorem squareTangentRow_separation :
    (∃ y, ((![1, -1 / 2] : Fin 2 → ℝ), y) ∈
        independentRows (Icc (-1) 1) squareTangentRow fun _ => 1 / 2) ∧
      ¬∃ y, ((![1, -1 / 2] : Fin 2 → ℝ), y) ∈
        sharedRows (Icc (-1) 1) (fun j a => squareTangentRow a j) (fun _ => Finset.univ)
          (1 / 2) := by
  have hD : (![1, -1 / 2] : Fin 2 → ℝ) ∈ Icc (-1) 1 := by
    simp only [mem_Icc, Pi.le_def, Fin.forall_fin_two]
    norm_num
  rw [exists_mem_independentRows_squareTangentRow_iff,
    exists_mem_sharedRows_squareTangentRow_iff]
  refine ⟨⟨hD, ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · norm_num [abs_of_pos]
  · norm_num [abs_of_neg] at h

end TauCeti.Examples.SupportRows
