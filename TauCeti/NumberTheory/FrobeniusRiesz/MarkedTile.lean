/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bernoulli.UniqueSuccess
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.Data.Fin.Parity

/-!
# Marked tiles of Bernoulli-selected tops

A tile has alternating empty and occupied cells, starting and ending with an empty cell.
Each occupied cell must have exactly one top, in an even one-based position. The probability
of this pattern has a uniform lower bound even when the selection probabilities differ.

This is the marked-tile event in Levent Alpöge's `Formalism.G0.TileConditionFailureProbBound`
(<https://github.com/leanprover-community/riemann-hypothesis>), allowing a nonconstant
Bernoulli profile, as needed for sampling with prescribed coset weights.
-/

public section

open Finset MeasureTheory ProbabilityTheory Set

namespace TauCeti.FrobeniusRiesz

/-- The configurations marking a tile with `2 * k + 1` cells of width `u`. Indices are
zero-based: an odd index denotes an even one-based cell or position. -/
def markedTile (k u : ℕ) : Set (Fin (2 * k + 1) → Fin u → Bool) :=
  {x | (∀ j, Even j.val → ∀ i, x j i = false) ∧
    (∀ j, Odd j.val → ∃ i, Odd i.val ∧ ∀ i', x j i' = true ↔ i' = i)}

/-- Read the marked-tile condition as emptiness in the odd one-based cells and a unique top
at an even one-based position in each even one-based cell. -/
@[simp] theorem mem_markedTile {k u : ℕ} {x : Fin (2 * k + 1) → Fin u → Bool} :
    x ∈ markedTile k u ↔ (∀ j, Even j.val → ∀ i, x j i = false) ∧
      (∀ j, Odd j.val → ∃ i, Odd i.val ∧ ∀ i', x j i' = true ↔ i' = i) := (Iff.rfl)

/-- Under the independent cell laws, the probability of a marked tile is bounded below by
one empty-cell factor for each of the `k + 1` empty cells and one unique-success factor for
each of the `k` occupied cells. -/
theorem le_measureReal_markedTile {k u : ℕ}
    (p : Fin (2 * k + 1) → Fin u → unitInterval) (δ q : unitInterval)
    (hp : ∀ j i, (p j i : ℝ) ≤ δ)
    (hq : ∀ j, Odd j.val → ∀ i, Odd i.val → (q : ℝ) ≤ p j i) :
    (1 - (δ : ℝ)) ^ (u * (k + 1)) *
        ((u / 2 : ℕ) * (q : ℝ) * (1 - (δ : ℝ)) ^ (u - 1)) ^ k ≤
      (Measure.pi fun j ↦ Measure.pi fun i ↦ bernoulliMeasure true false (p j i)).real
        (markedTile k u) := by
  let E (j : Fin (2 * k + 1)) : Set (Fin u → Bool) :=
    if Odd j.val then {x | ∃ i, Odd i.val ∧ ∀ i', x i' = true ↔ i' = i} else {fun _ ↦ false}
  have ht : markedTile k u = Set.univ.pi E := by
    ext x
    simp only [mem_markedTile, Set.mem_univ_pi]
    constructor
    · rintro ⟨he, ho⟩ j
      by_cases h : Odd j.val
      · simpa [E, h] using ho j h
      · simp [E, h, funext_iff, he j (Nat.not_odd_iff_even.mp h)]
    · intro h
      refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
      · have hn := Nat.not_odd_iff_even.mpr hj
        simpa [E, hn, funext_iff] using h j
      · simpa [E, hj] using h j
  rw [ht, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [← measureReal_def]
  let b : ℝ := 1 - (δ : ℝ)
  let v : ℝ := ((u / 2 : ℕ) : ℝ) * (q : ℝ) * b ^ (u - 1)
  have hb : 0 ≤ b := unitInterval.one_sub_nonneg δ
  have hv : 0 ≤ v := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (unitInterval.nonneg q))
    (pow_nonneg hb _)
  calc
    _ = ∏ j : Fin (2 * k + 1), if Odd j.val then v else b ^ u := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Fin.card_filter_odd,
        Nat.mul_add_div (by decide : 0 < 2)]
      have hc := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (2 * k + 1)))) (p := fun j ↦ Odd j.val)
      simp only [Fin.card_filter_odd, Finset.card_univ, Fintype.card_fin] at hc
      have hn : (Finset.univ.filter fun j : Fin (2 * k + 1) ↦ ¬Odd j.val).card = k + 1 := by omega
      rw [hn, ← pow_mul, mul_comm]
      simp [b, v]
    _ ≤ _ := by
      refine Finset.prod_le_prod₀ (fun j _ ↦ by split_ifs <;> positivity) fun j _ ↦ ?_
      by_cases hj : Odd j.val
      · simpa only [hj, ite_true, E, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.card_filter_odd, Fintype.card_fin, v, b] using
          le_measureReal_pi_bernoulliMeasure_existsUnique_mem (p j)
            (Finset.univ.filter fun i : Fin u ↦ Odd i.val) δ
            (fun i hi ↦ hq j hj i (Finset.mem_filter.mp hi).2) (hp j)
      · simp only [E, hj, ite_false, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
        simp only [← measureReal_def]
        calc
          b ^ u = ∏ _ : Fin u, b := by simp
          _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ hb) fun i _ ↦ by
            simpa [b] using sub_le_sub_left (hp j i) 1

/-- The marked-tile lower bound also holds in a larger independent Bernoulli sample. The
embedding lists the distinct positions of all the cells of a complete tile. -/
theorem le_measureReal_preimage_markedTile {ι : Type*} [Fintype ι] {k u : ℕ}
    (e : Fin (2 * k + 1) × Fin u ↪ ι) (p : ι → unitInterval) (δ q : unitInterval)
    (hp : ∀ j i, (p (e (j, i)) : ℝ) ≤ δ)
    (hq : ∀ j, Odd j.val → ∀ i, Odd i.val → (q : ℝ) ≤ p (e (j, i))) :
    (1 - (δ : ℝ)) ^ (u * (k + 1)) *
        ((u / 2 : ℕ) * (q : ℝ) * (1 - (δ : ℝ)) ^ (u - 1)) ^ k ≤
      (Measure.pi fun a ↦ bernoulliMeasure true false (p a)).real
        ((fun x j i ↦ x (e (j, i))) ⁻¹' markedTile k u) := by
  let μ (j : Fin (2 * k + 1)) (i : Fin u) := bernoulliMeasure true false (p (e (j, i)))
  have he : MeasurePreserving (fun (x : ι → Bool) j i ↦ x (e (j, i)))
      (Measure.pi fun a ↦ bernoulliMeasure true false (p a))
      (Measure.pi fun j ↦ Measure.pi (μ j)) :=
    (TauCeti.measurePreserving_curry μ).comp
      (TauCeti.measurePreserving_pi_comp_embedding (fun a ↦ bernoulliMeasure true false (p a)) e)
  have hs : MeasurableSet (markedTile k u) := .of_discrete
  rw [he.measureReal_preimage hs.nullMeasurableSet]
  exact le_measureReal_markedTile (fun j i ↦ p (e (j, i))) δ q hp hq

end TauCeti.FrobeniusRiesz
