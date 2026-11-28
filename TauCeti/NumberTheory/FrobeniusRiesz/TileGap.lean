/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Data.Fin.Embedding
import TauCeti.Probability.ConditionalProbability
import TauCeti.Probability.Distributions.Bernoulli.Basic
import TauCeti.Probability.Independence.BlockFailure

/-!
# Gaps between marked tiles on a sampled orbit

Partition the cyclically ordered positions into complete tiles of equal width, skipping the
incomplete suffix when cycling through the tiles. If each tile is marked with probability at
least `q`, a run of `M + 1` unmarked tiles has conditional probability at most `(1 - q)^M`
given that a specified position is selected. A union bound costs one factor of the number of
complete tiles. The bound can be used with any marking rule depending only on its tile.

The marked-tile gap is the term from Levent Alpöge's `Formalism.G0.TileConditionFailureProbBound`.
Here, using the starting tile as well as the next `M` tiles leaves at least `M` complete tiles
that do not read the conditioned coordinate.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

/-- Tile `t` starts at position `t * w`. The first `n / w` tiles of width `w` fit in `n`
positions; the incomplete suffix is not in the image of this embedding. -/
def completeTileEmbedding (n w : ℕ) : Fin (n / w) × Fin w ↪ Fin n :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (Nat.div_mul_le_self n w))

/-- The position of an entry in a complete tile is its start plus its offset. -/
@[simp]
theorem val_completeTileEmbedding {n w : ℕ} (t : Fin (n / w)) (j : Fin w) :
    (completeTileEmbedding n w (t, j)).val = t.val * w + j.val := by
  calc
    _ = j.val + w * t.val := rfl
    _ = _ := by ac_rfl

/-- The event that some cyclic run of `M + 1` complete tiles has no mark.
Addition on `Fin (n / w)` wraps at the last complete tile, not at the incomplete suffix. -/
def cyclicUnmarkedRun {n w M : ℕ} (hM : M + 1 ≤ n / w) (A : Set (Fin w → Bool)) :
    Set (Fin n → Bool) :=
  {x | ∃ t : Fin (n / w), ∀ i : Fin (M + 1),
    (fun j ↦ x (completeTileEmbedding n w (t + Fin.castLE hM i, j))) ∉ A}

/-- A sample belongs to the gap event exactly when all tiles in some run are unmarked. -/
@[simp]
theorem mem_cyclicUnmarkedRun {n w M : ℕ} (hM : M + 1 ≤ n / w)
    {A : Set (Fin w → Bool)} {x : Fin n → Bool} :
    x ∈ cyclicUnmarkedRun hM A ↔ ∃ t : Fin (n / w), ∀ i : Fin (M + 1),
      (fun j ↦ x (completeTileEmbedding n w (t + Fin.castLE hM i, j))) ∉ A := (Iff.rfl)

/-- The joint probability that `a` is selected and some cyclic run of `M + 1` complete tiles
has no mark is at most the selection probability times `(n / w) * (1 - q)^M`. -/
theorem measureReal_selected_inter_cyclicUnmarkedRun_le {n w M : ℕ}
    (hM : M + 1 ≤ n / w) (p : Fin n → unitInterval) (a : Fin n)
    (A : Set (Fin w → Bool)) (q : unitInterval)
    (hmark : ∀ t : Fin (n / w), (q : ℝ) ≤
      (Measure.pi fun i ↦ bernoulliMeasure true false (p i)).real
        ((fun x j ↦ x (completeTileEmbedding n w (t, j))) ⁻¹' A)) :
    (Measure.pi fun i ↦ bernoulliMeasure true false (p i)).real
      ({x | x a = true} ∩ cyclicUnmarkedRun hM A) ≤
        (p a : ℝ) * ((n / w : ℕ) * (1 - (q : ℝ)) ^ M) := by
  let μ (i : Fin n) := bernoulliMeasure true false (p i)
  let E : Set (Fin n → Bool) := {x | x a = true}
  let e (t : Fin (n / w)) : Fin (M + 1) × Fin w ↪ Fin n :=
    (Function.Embedding.prodMap
      ⟨fun i ↦ t + Fin.castLE hM i, fun _ _ h ↦ Fin.castLE_injective _ (add_left_cancel h)⟩
      (.refl _)).trans (completeTileEmbedding n w)
  have he (t : Fin (n / w)) (i : Fin (M + 1)) (j : Fin w) :
      e t (i, j) = completeTileEmbedding n w (t + Fin.castLE hM i, j) := rfl
  let F (t : Fin (n / w)) : Set (Fin n → Bool) :=
    ⋂ i : Fin (M + 1), (fun x j ↦ x (e t (i, j))) ⁻¹' Aᶜ
  have hcover : E ∩ cyclicUnmarkedRun hM A = ⋃ t, E ∩ F t := by
    ext x
    simp [F, he]
  have hE : E = (fun x : Fin n → Bool ↦ x a) ⁻¹' {true} := by
    ext x
    simp [E]
  have hbound (t : Fin (n / w)) : (Measure.pi μ).real (E ∩ F t) ≤
      (p a : ℝ) * (1 - (q : ℝ)) ^ M := by
    have ha : (Measure.pi μ).real E = p a :=
      Probability.measureReal_pi_bernoulliMeasure_eval_eq_true p a
    have h := Probability.measureReal_inter_iInter_compl_preimage_blocks_le μ (e t) a
      (B := {true}) (by simp) (fun _ ↦ A) (fun _ ↦ .of_discrete) q
      (fun i ↦ hmark (t + Fin.castLE hM i))
    rw [← ha]
    simpa only [hE, F, Fintype.card_fin, Nat.add_sub_cancel] using h
  calc
    _ = (Measure.pi μ).real (⋃ t, E ∩ F t) := by rw [← hcover]
    _ ≤ ∑ t, (Measure.pi μ).real (E ∩ F t) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _t : Fin (n / w), (p a : ℝ) * (1 - (q : ℝ)) ^ M :=
      Finset.sum_le_sum fun t _ ↦ hbound t
    _ = _ := by simp [mul_left_comm]

/-- Conditional on selecting `a`, the probability of a cyclic run of `M + 1` unmarked
complete tiles is bounded by the number of complete tiles times `(1 - q)^M`.
For a null selection event the conditional measure is zero. -/
theorem cond_real_cyclicUnmarkedRun_le {n w M : ℕ} (hM : M + 1 ≤ n / w)
    (p : Fin n → unitInterval) (a : Fin n) (A : Set (Fin w → Bool)) (q : unitInterval)
    (hmark : ∀ t : Fin (n / w), (q : ℝ) ≤
      (Measure.pi fun i ↦ bernoulliMeasure true false (p i)).real
        ((fun x j ↦ x (completeTileEmbedding n w (t, j))) ⁻¹' A)) :
    (ProbabilityTheory.cond (Measure.pi fun i ↦ bernoulliMeasure true false (p i))
      {x | x a = true}).real (cyclicUnmarkedRun hM A) ≤
        (n / w : ℕ) * (1 - (q : ℝ)) ^ M := by
  rw [cond_real_apply (measurableSet_eq_fun (measurable_pi_apply a) measurable_const),
    Probability.measureReal_pi_bernoulliMeasure_eval_eq_true]
  rcases (unitInterval.nonneg (p a)).eq_or_lt with h | hp
  · rw [← h, div_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr q.property.2) _)
  · exact (div_le_iff₀ hp).mpr
      ((measureReal_selected_inter_cyclicUnmarkedRun_le hM p a A q hmark).trans_eq (mul_comm ..))

end TauCeti
