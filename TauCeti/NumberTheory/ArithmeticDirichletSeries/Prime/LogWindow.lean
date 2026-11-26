/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card

/-!
# Sampling primes from logarithmic windows

A one-prime existence theorem on short logarithmic windows also gives a finite set of
prescribed cardinality on a longer interval. The left endpoints of the sampled windows
are spaced by twice their width, so a prime cannot be chosen twice.
-/

public section

open Set

namespace TauCeti

/-- If each window of width `W` contained in `[L, R]` contains the logarithm of a prime
congruent to `a` modulo `q`, then `[L, R]` contains the logarithms of `n` distinct such
primes, provided `2 * n * W ≤ R - L`. -/
theorem exists_finset_primes_modEq_log_mem_Icc {n q a : ℕ} {L R W : ℝ}
    (hW : 0 < W) (hsize : L + 2 * n * W ≤ R)
    (hwin : ∀ U : ℝ, L ≤ U → U + W ≤ R →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ Real.log p ∈ Icc U (U + W)) :
    ∃ S : Finset ℕ, S.card = n ∧
      ∀ p ∈ S, p.Prime ∧ p ≡ a [MOD q] ∧ Real.log p ∈ Icc L R := by
  let u (i : Fin n) : ℝ := L + 2 * (i.val : ℝ) * W
  have hlo (i : Fin n) : L ≤ u i := by
    dsimp [u]
    exact le_add_of_nonneg_right (by positivity)
  have hhi (i : Fin n) : u i + W ≤ R := by
    have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    dsimp [u]
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) hW.le]
  choose p hp hmod hlog using fun i ↦ hwin (u i) (hlo i) (hhi i)
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
  exact ⟨hp i, hmod i, (hlo i).trans (hlog i).1, (hlog i).2.trans (hhi i)⟩

end TauCeti
