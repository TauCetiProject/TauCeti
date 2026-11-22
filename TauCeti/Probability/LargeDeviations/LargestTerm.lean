/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Order.Filter.ENNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Order.LiminfLimsup
import TauCeti.Probability.LargeDeviations.Basic

/-!
# The principle of the largest term

At a speed `ε i` tending to `0`, the exponential rate of a sum of two nonnegative quantities is
the larger of the two rates:
`limsup ε log (a + b) = max (limsup ε log a) (limsup ε log b)`.
For finitely many summands the rate of the sum is the largest of the rates, once the speed is
eventually positive; this is also what makes the rate of an empty sum `⊥`. The liminf companion
bounds `liminf ε log (a + b)` by the liminf rate of `a` and the limsup rate of `b`. It lets an
exponentially negligible error be absorbed in a lower bound. At a speed that is only eventually
bounded, a sum of two sequences of rate `⊥` still has rate `⊥`.

These estimates split events into a main part and an error part in the proofs of large deviation
principles, as in the passage from weak to full principles and in exponential equivalence.

## Main results

* `TauCeti.Probability.limsup_coe_mul_log_add`: the principle of the largest term for two
  summands.
* `TauCeti.Probability.liminf_coe_mul_log_add_le`: its liminf companion.
* `TauCeti.Probability.limsup_coe_mul_log_add_eq_bot`: at an eventually bounded speed, a sum of
  two sequences of rate `⊥` has rate `⊥`.
* `TauCeti.Probability.limsup_coe_mul_log_sum`: the principle for a finite sum.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Lemma 1.2.15.
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} {l : Filter ι} {ε : ι → ℝ≥0}

/-- The limsup rate `limsup ε log u` is the logarithm of `limsup u ^ ε`. -/
private theorem limsup_coe_mul_log (u : ι → ℝ≥0∞) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l =
      ENNReal.log (limsup (fun i => u i ^ (ε i : ℝ)) l) := by
  simp_rw [← ENNReal.log_rpow]
  exact (ENNReal.logOrderIso.limsup_apply).symm

/-- The liminf rate `liminf ε log u` is the logarithm of `liminf u ^ ε`. -/
private theorem liminf_coe_mul_log (u : ι → ℝ≥0∞) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l =
      ENNReal.log (liminf (fun i => u i ^ (ε i : ℝ)) l) := by
  simp_rw [← ENNReal.log_rpow]
  exact (ENNReal.logOrderIso.liminf_apply).symm

/-- The limsup rate is monotone in the sequence. -/
private theorem limsup_coe_mul_log_mono {u v : ι → ℝ≥0∞} (h : ∀ i, u i ≤ v i) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l ≤
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l :=
  limsup_le_limsup (.of_forall fun i => monotone_coe_mul_log (ε i) (h i))

private theorem tendsto_two_rpow (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => (2 : ℝ≥0∞) ^ (ε i : ℝ)) l (𝓝 1) := by
  have h : Tendsto (fun i => (2 : ℝ) ^ (ε i : ℝ)) l (𝓝 1) := by
    have := ((Real.continuous_const_rpow (a := 2) (by norm_num)).tendsto 0).comp
      (NNReal.tendsto_coe.2 hε)
    simpa [Function.comp_def] using this
  have h2 := ENNReal.tendsto_ofReal h
  rw [ENNReal.ofReal_one] at h2
  refine h2.congr fun i => ?_
  rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- At a speed tending to `0`, doubling a sequence does not raise its limsup rate. -/
private theorem limsup_coe_mul_log_add_self_le (hε : Tendsto ε l (𝓝 0)) (w : ι → ℝ≥0∞) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (w i + w i)) l ≤
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (w i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have h1 := (tendsto_two_rpow hε).limsup_eq
  rw [limsup_coe_mul_log, limsup_coe_mul_log, ENNReal.log_le_log_iff]
  simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe]
  calc limsup (fun i => 2 ^ (ε i : ℝ) * w i ^ (ε i : ℝ)) l
      ≤ limsup (fun i => (2 : ℝ≥0∞) ^ (ε i : ℝ)) l * limsup (fun i => w i ^ (ε i : ℝ)) l :=
        ENNReal.limsup_mul_le' (by simp [h1]) (by simp [h1])
    _ = limsup (fun i => w i ^ (ε i : ℝ)) l := by rw [h1, one_mul]

/-- At a speed tending to `0`, doubling a sequence does not raise its liminf rate. -/
private theorem liminf_coe_mul_log_add_self_le (hε : Tendsto ε l (𝓝 0)) (w : ι → ℝ≥0∞) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (w i + w i)) l ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (w i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have h1 := (tendsto_two_rpow hε).limsup_eq
  rw [liminf_coe_mul_log, liminf_coe_mul_log, ENNReal.log_le_log_iff]
  simp only [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe]
  calc liminf (fun i => 2 ^ (ε i : ℝ) * w i ^ (ε i : ℝ)) l
      ≤ limsup (fun i => (2 : ℝ≥0∞) ^ (ε i : ℝ)) l * liminf (fun i => w i ^ (ε i : ℝ)) l :=
        ENNReal.liminf_mul_le (by simp [h1]) (by simp [h1])
    _ = liminf (fun i => w i ^ (ε i : ℝ)) l := by rw [h1, one_mul]

/-- **The principle of the largest term.** At a speed tending to `0`, the limsup rate of a sum of
two nonnegative sequences is the larger of their limsup rates. -/
theorem limsup_coe_mul_log_add (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l =
      max (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  refine le_antisymm ?_ (max_le (limsup_coe_mul_log_mono fun i => le_self_add)
    (limsup_coe_mul_log_mono fun i => le_add_self))
  -- Bound the sum by twice the larger term; the rate of a maximum is the maximum of the rates.
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log (max (u i) (v i) + max (u i) (v i))) l :=
        limsup_coe_mul_log_mono fun i => add_le_add (le_max_left _ _) (le_max_right _ _)
    _ ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (max (u i) (v i))) l :=
        limsup_coe_mul_log_add_self_le hε _
    _ = _ := (limsup_congr (.of_forall fun i => (monotone_coe_mul_log (ε i)).map_max)).trans
        limsup_max

/-- At a speed tending to `0`, the liminf rate of a sum of two nonnegative sequences is at most
the larger of the liminf rate of the first and the limsup rate of the second. If the second rate
is below the first, the second summand does not change the liminf rate. -/
theorem liminf_coe_mul_log_add_le (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l ≤
      max (liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  calc liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l
      ≤ liminf (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log (max (u i) (v i) + max (u i) (v i))) l :=
        liminf_le_liminf (.of_forall fun i => monotone_coe_mul_log (ε i)
          (add_le_add (le_max_left _ _) (le_max_right _ _)))
    _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (max (u i) (v i))) l :=
        liminf_coe_mul_log_add_self_le hε _
    _ = liminf (fun i => max (((ε i : ℝ) : EReal) * ENNReal.log (u i))
          (((ε i : ℝ) : EReal) * ENNReal.log (v i))) l :=
        liminf_congr (.of_forall fun i => (monotone_coe_mul_log (ε i)).map_max)
    _ ≤ _ := liminf_max_le_max_liminf_limsup _ _

/-- At an eventually bounded speed, the sum of two nonnegative sequences of limsup rate `⊥` has
limsup rate `⊥`. Unlike `limsup_coe_mul_log_add`, this needs no vanishing speed. -/
theorem limsup_coe_mul_log_add_eq_bot {u v : ι → ℝ≥0∞} (hε : IsBoundedUnder (· ≤ ·) l ε)
    (hu : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l = ⊥)
    (hv : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l = ⊥) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l = ⊥ := by
  have hmax : limsup (fun i => max (u i) (v i) ^ (ε i : ℝ)) l = 0 := by
    rw [← ENNReal.log_eq_bot_iff, ← limsup_coe_mul_log,
      limsup_congr (.of_forall fun i => (monotone_coe_mul_log (ε i)).map_max), limsup_max, hu, hv,
      max_self]
  obtain ⟨B, hB⟩ := hε
  refine le_bot_iff.1 ((limsup_coe_mul_log_mono fun i =>
    add_le_add (le_max_left (u i) (v i)) (le_max_right (u i) (v i))).trans ?_)
  rw [limsup_coe_mul_log, le_bot_iff, ENNReal.log_eq_bot_iff, ← nonpos_iff_eq_zero]
  -- Bound the sum by twice the larger term, and the factor `2 ^ ε` by `2 ^ B`.
  calc limsup (fun i => (max (u i) (v i) + max (u i) (v i)) ^ (ε i : ℝ)) l
      ≤ limsup (fun i => 2 ^ (B : ℝ) * max (u i) (v i) ^ (ε i : ℝ)) l := by
        refine limsup_le_limsup ?_
        filter_upwards [hB] with i hi
        rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ (ε i).coe_nonneg]
        gcongr
        · norm_num
        · exact_mod_cast hi
    _ = 0 := by
      rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.rpow_ne_top_of_nonneg B.coe_nonneg
        ENNReal.ofNat_ne_top), hmax, mul_zero]

/-- **The principle of the largest term** for a finite sum. At an eventually positive speed
tending to `0`, the limsup rate of a finite sum of nonnegative sequences is the largest of their
limsup rates. The empty sum has rate `⊥`. -/
theorem limsup_coe_mul_log_sum {κ : Type*} (u : κ → ι → ℝ≥0∞) (s : Finset κ)
    (hε : Tendsto ε l (𝓝 0)) (hpos : ∀ᶠ i in l, 0 < ε i) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (∑ j ∈ s, u j i)) l =
      ⨆ j ∈ s, limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u j i)) l := by
  classical
  refine le_antisymm ?_ (iSup₂_le fun j hj => limsup_coe_mul_log_mono fun i =>
    Finset.single_le_sum (f := fun j => u j i) (fun _ _ => bot_le) hj)
  induction s using Finset.induction_on with
  | empty =>
    refine (limsup_congr ?_).trans_le (limsup_const_bot.trans_le bot_le)
    filter_upwards [hpos] with i hi
    simpa using EReal.mul_bot_of_pos (by exact_mod_cast hi)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj, Finset.iSup_insert]
    exact (limsup_coe_mul_log_add _ _ hε).le.trans (sup_le_sup le_rfl ih)

end TauCeti.Probability
