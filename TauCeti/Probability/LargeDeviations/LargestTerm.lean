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

/-!
# The principle of the largest term

At a speed `ε i` tending to `0`, the exponential rate of a sum of two nonnegative quantities is
the larger of the two rates:
`limsup ε log (a + b) = max (limsup ε log a) (limsup ε log b)`.
For finitely many summands the rate of the sum is the largest of the rates, once the speed is
eventually positive; this is also what makes the rate of an empty sum `⊥`. The liminf companion
bounds `liminf ε log (a + b)` by the liminf rate of `a` and the limsup rate of `b`. It lets an
exponentially negligible error be absorbed in a lower bound.

These estimates split events into a main part and an error part in the proofs of large deviation
principles, as in the passage from weak to full principles and in exponential equivalence.

## Main results

* `TauCeti.Probability.limsup_coe_mul_log_add`: the principle of the largest term for two
  summands.
* `TauCeti.Probability.liminf_coe_mul_log_add_le`: its liminf companion.
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
  limsup_le_limsup (.of_forall fun i => mul_le_mul_of_nonneg_left (ENNReal.log_monotone (h i))
    (by exact_mod_cast (ε i).coe_nonneg))

private theorem rpow_add_le_two_rpow_mul_max (a b : ℝ≥0∞) (r : ℝ≥0) :
    (a + b) ^ (r : ℝ) ≤ 2 ^ (r : ℝ) * max (a ^ (r : ℝ)) (b ^ (r : ℝ)) := by
  have hab : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left a b) (le_max_right a b)
  calc (a + b) ^ (r : ℝ) ≤ (2 * max a b) ^ (r : ℝ) := ENNReal.rpow_le_rpow hab r.coe_nonneg
    _ = 2 ^ (r : ℝ) * (max a b) ^ (r : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ r.coe_nonneg
    _ = 2 ^ (r : ℝ) * max (a ^ (r : ℝ)) (b ^ (r : ℝ)) :=
      congrArg (2 ^ (r : ℝ) * ·) (ENNReal.monotone_rpow_of_nonneg r.coe_nonneg).map_max

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

private theorem limsup_two_rpow_mul_le (hε : Tendsto ε l (𝓝 0)) (w : ι → ℝ≥0∞) :
    limsup (fun i => 2 ^ (ε i : ℝ) * w i) l ≤ limsup w l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have h1 := (tendsto_two_rpow hε).limsup_eq
  calc limsup (fun i => 2 ^ (ε i : ℝ) * w i) l
      ≤ limsup (fun i => (2 : ℝ≥0∞) ^ (ε i : ℝ)) l * limsup w l :=
        ENNReal.limsup_mul_le' (by simp [h1]) (by simp [h1])
    _ = limsup w l := by rw [h1, one_mul]

private theorem liminf_two_rpow_mul_le (hε : Tendsto ε l (𝓝 0)) (w : ι → ℝ≥0∞) :
    liminf (fun i => 2 ^ (ε i : ℝ) * w i) l ≤ liminf w l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have h1 := (tendsto_two_rpow hε).limsup_eq
  calc liminf (fun i => 2 ^ (ε i : ℝ) * w i) l
      ≤ limsup (fun i => (2 : ℝ≥0∞) ^ (ε i : ℝ)) l * liminf w l :=
        ENNReal.liminf_mul_le (by simp [h1]) (by simp [h1])
    _ = liminf w l := by rw [h1, one_mul]

/-- The liminf of a pointwise maximum is at most the larger of the liminf of the first sequence
and the limsup of the second. -/
private theorem liminf_max_le_max_liminf_limsup (u v : ι → ℝ≥0∞) :
    liminf (fun i => max (u i) (v i)) l ≤ max (liminf u l) (limsup v l) := by
  refine le_of_forall_lt fun c hc => ?_
  by_contra! h
  obtain ⟨d, hcd, hd⟩ := exists_between hc
  have hu : ∀ᶠ i in l, d ≤ u i := by
    filter_upwards [eventually_lt_of_lt_liminf hd,
      eventually_lt_of_limsup_lt ((le_max_right _ _).trans h |>.trans_lt hcd)] with i h₁ h₂
    exact ((lt_max_iff.1 h₁).resolve_right h₂.not_gt).le
  exact (hcd.trans_le (le_liminf_of_le (by isBoundedDefault) hu)).not_ge
    ((le_max_left _ _).trans h)

/-- **The principle of the largest term.** At a speed tending to `0`, the limsup rate of a sum of
two nonnegative sequences is the larger of their limsup rates. -/
theorem limsup_coe_mul_log_add (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l =
      max (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  refine le_antisymm ?_ (max_le (limsup_coe_mul_log_mono fun i => le_self_add)
    (limsup_coe_mul_log_mono fun i => le_add_self))
  rw [limsup_coe_mul_log, limsup_coe_mul_log, limsup_coe_mul_log,
    ← ENNReal.log_monotone.map_max, ENNReal.log_le_log_iff]
  calc limsup (fun i => (u i + v i) ^ (ε i : ℝ)) l
      ≤ limsup (fun i => 2 ^ (ε i : ℝ) * max (u i ^ (ε i : ℝ)) (v i ^ (ε i : ℝ))) l :=
        limsup_le_limsup (.of_forall fun i => rpow_add_le_two_rpow_mul_max _ _ _)
    _ ≤ limsup (fun i => max (u i ^ (ε i : ℝ)) (v i ^ (ε i : ℝ))) l :=
        limsup_two_rpow_mul_le hε _
    _ = _ := limsup_max

/-- At a speed tending to `0`, the liminf rate of a sum of two nonnegative sequences is at most
the larger of the liminf rate of the first and the limsup rate of the second. If the second rate
is below the first, the second summand does not change the liminf rate. -/
theorem liminf_coe_mul_log_add_le (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l ≤
      max (liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  rw [liminf_coe_mul_log, liminf_coe_mul_log, limsup_coe_mul_log,
    ← ENNReal.log_monotone.map_max, ENNReal.log_le_log_iff]
  calc liminf (fun i => (u i + v i) ^ (ε i : ℝ)) l
      ≤ liminf (fun i => 2 ^ (ε i : ℝ) * max (u i ^ (ε i : ℝ)) (v i ^ (ε i : ℝ))) l :=
        liminf_le_liminf (.of_forall fun i => rpow_add_le_two_rpow_mul_max _ _ _)
    _ ≤ liminf (fun i => max (u i ^ (ε i : ℝ)) (v i ^ (ε i : ℝ))) l :=
        liminf_two_rpow_mul_le hε _
    _ ≤ _ := liminf_max_le_max_liminf_limsup _ _

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
