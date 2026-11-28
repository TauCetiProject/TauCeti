/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card

/-!
# Sampling from logarithmic windows

If every short logarithmic window contains a natural number satisfying a predicate,
we can choose a prescribed number of distinct such witnesses in a longer interval.
This applies, for instance, to primes in a fixed residue class.
-/

public section

open Set

namespace TauCeti

/-- If every window of positive width `W` contained in `[L, R]` contains the logarithm
of a natural number satisfying `P`, then `[L, R]` contains the logarithms of `n` distinct
natural numbers satisfying `P`, provided `L + 2 * n * W ≤ R`. -/
theorem exists_finset_card_eq_and_log_mem_Icc {P : ℕ → Prop} {n : ℕ} {L R W : ℝ}
    (hW : 0 < W) (hsize : L + 2 * n * W ≤ R)
    (hwin : ∀ U : ℝ, L ≤ U → U + W ≤ R → ∃ p : ℕ, P p ∧ Real.log p ∈ Icc U (U + W)) :
    ∃ S : Finset ℕ, S.card = n ∧ ∀ p ∈ S, P p ∧ Real.log p ∈ Icc L R := by
  let u (i : Fin n) : ℝ := L + 2 * (i.val : ℝ) * W
  have hlo (i : Fin n) : L ≤ u i := by
    dsimp [u]
    exact le_add_of_nonneg_right (by positivity)
  have hhi (i : Fin n) : u i + W ≤ R := by
    have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    dsimp [u]
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) hW.le]
  choose p hp hlog using fun i ↦ hwin (u i) (hlo i) (hhi i)
  have hmono : StrictMono fun i ↦ Real.log (p i) := by
    intro i j hij
    have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    have hsep : u i + W < u j := by
      dsimp [u]
      nlinarith [mul_nonneg (sub_nonneg.mpr hij') hW.le]
    exact (hlog i).2.trans_lt (hsep.trans_le (hlog j).1)
  have hinj : Function.Injective p := fun _ _ h ↦
    hmono.injective (congrArg (fun k : ℕ ↦ Real.log k) h)
  refine ⟨Finset.univ.image p, by simp [Finset.card_image_of_injective _ hinj], ?_⟩
  intro p' hp'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp'
  exact ⟨hp i, (hlo i).trans (hlog i).1, (hlog i).2.trans (hhi i)⟩

end TauCeti
