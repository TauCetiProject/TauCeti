/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Order.LiminfLimsup

/-!
# The principle of the largest term

At an inverse speed `ε i` tending to `0`, a finite nonzero constant factor `c` does not change
exponential rates: `ε log (c * u)` and `ε log u` have the same limsup and the same liminf, since
`c ^ ε → 1`. Hence the exponential rate of a sum of two nonnegative quantities is the larger of the
two rates, since the sum lies between the larger term and twice it:
`limsup ε log (a + b) = max (limsup ε log a) (limsup ε log b)`.
For a nonempty finite sum the rate of the sum is the largest of the rates. The empty sum has rate
`⊥` once the inverse speed is eventually positive. The liminf companion bounds
`liminf ε log (a + b)` by the liminf rate of `a` and the limsup rate of `b`. It lets an
exponentially negligible error be absorbed in a lower bound. At an inverse speed that is only
eventually bounded, a sum of two sequences of rate `⊥` still has rate `⊥`.

These estimates split events into a main part and an error part in the proofs of large deviation
principles, as in the passage from weak to full principles and in exponential equivalence.

## Main results

* `TauCeti.ENNReal.limsup_coe_mul_log_const_mul`, `TauCeti.ENNReal.liminf_coe_mul_log_const_mul`:
  a finite nonzero constant factor does not change the limsup or liminf rate.
* `TauCeti.ENNReal.limsup_coe_mul_log_add`: the principle of the largest term for two
  summands.
* `TauCeti.ENNReal.liminf_coe_mul_log_add_le`: its liminf companion.
* `TauCeti.ENNReal.limsup_coe_mul_log_add_eq_bot`: at an eventually bounded inverse speed, a sum of
  two sequences of rate `⊥` has rate `⊥`.
* `TauCeti.ENNReal.limsup_coe_mul_log_sum`: the principle for a finite sum.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Lemma 1.2.15.
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.ENNReal

variable {ι : Type*} {l : Filter ι} {ε : ι → ℝ≥0}

/-- At an inverse speed tending to `0`, the powers `c ^ ε i` of a finite nonzero `c` tend
to `1`. -/
private theorem tendsto_rpow_coe_nhds_one (hε : Tendsto ε l (𝓝 0)) {c : ℝ≥0∞} (h0 : c ≠ 0)
    (htop : c ≠ ∞) : Tendsto (fun i => c ^ (ε i : ℝ)) l (𝓝 1) := by
  simpa only [Function.comp_def, NNReal.coe_zero, ENNReal.rpow_zero] using
    ((ENNReal.continuous_const_rpow c h0 htop).tendsto 0).comp (NNReal.tendsto_coe.2 hε)

/-- At an inverse speed tending to `0`, a finite nonzero constant factor `c` does not change the
limsup rate: `limsup ε log (c * u) = limsup ε log u`. -/
theorem limsup_coe_mul_log_const_mul (hε : Tendsto ε l (𝓝 0)) {c : ℝ≥0∞} (h0 : c ≠ 0)
    (htop : c ≠ ∞) (u : ι → ℝ≥0∞) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (c * u i)) l =
      limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  -- The factor `c ^ ε i` tends to `1`.
  have h1 := tendsto_rpow_coe_nhds_one hε h0 htop
  rw [limsup_coe_mul_log, limsup_coe_mul_log]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (ε _).coe_nonneg]
  refine congrArg ENNReal.log (le_antisymm ?_ ?_)
  · calc limsup (fun i => c ^ (ε i : ℝ) * u i ^ (ε i : ℝ)) l
        ≤ limsup (fun i => c ^ (ε i : ℝ)) l * limsup (fun i => u i ^ (ε i : ℝ)) l :=
          ENNReal.limsup_mul_le' (by simp [h1.limsup_eq]) (by simp [h1.limsup_eq])
      _ = _ := by rw [h1.limsup_eq, one_mul]
  · calc limsup (fun i => u i ^ (ε i : ℝ)) l
        = limsup (fun i => u i ^ (ε i : ℝ)) l * liminf (fun i => c ^ (ε i : ℝ)) l := by
          rw [h1.liminf_eq, mul_one]
      _ ≤ limsup (fun i => u i ^ (ε i : ℝ) * c ^ (ε i : ℝ)) l := ENNReal.le_limsup_mul
      _ = _ := by simp only [mul_comm]

/-- At an inverse speed tending to `0`, a finite nonzero constant factor `c` does not change the
liminf rate: `liminf ε log (c * u) = liminf ε log u`. -/
theorem liminf_coe_mul_log_const_mul (hε : Tendsto ε l (𝓝 0)) {c : ℝ≥0∞} (h0 : c ≠ 0)
    (htop : c ≠ ∞) (u : ι → ℝ≥0∞) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (c * u i)) l =
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  -- The factor `c ^ ε i` tends to `1`.
  have h1 := tendsto_rpow_coe_nhds_one hε h0 htop
  rw [liminf_coe_mul_log, liminf_coe_mul_log]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (ε _).coe_nonneg]
  refine congrArg ENNReal.log (le_antisymm ?_ ?_)
  · calc liminf (fun i => c ^ (ε i : ℝ) * u i ^ (ε i : ℝ)) l
        ≤ limsup (fun i => c ^ (ε i : ℝ)) l * liminf (fun i => u i ^ (ε i : ℝ)) l :=
          ENNReal.liminf_mul_le (by simp [h1.limsup_eq]) (by simp [h1.limsup_eq])
      _ = _ := by rw [h1.limsup_eq, one_mul]
  · calc liminf (fun i => u i ^ (ε i : ℝ)) l
        = liminf (fun i => c ^ (ε i : ℝ)) l * liminf (fun i => u i ^ (ε i : ℝ)) l := by
          rw [h1.liminf_eq, one_mul]
      _ ≤ _ := ENNReal.le_liminf_mul

/-- **The principle of the largest term.** At an inverse speed tending to `0`, the limsup rate of a
sum of two nonnegative sequences is the larger of their limsup rates. -/
theorem limsup_coe_mul_log_add (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l =
      max (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  refine le_antisymm ?_ (max_le (limsup_coe_mul_log_mono (.of_forall fun i => le_self_add))
    (limsup_coe_mul_log_mono (.of_forall fun i => le_add_self)))
  -- Bound the sum by twice the larger term; the rate of a maximum is the maximum of the rates.
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (2 * max (u i) (v i))) l :=
        limsup_coe_mul_log_mono (.of_forall fun i =>
          (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm)
    _ = limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (max (u i) (v i))) l :=
        limsup_coe_mul_log_const_mul hε two_ne_zero ENNReal.ofNat_ne_top _
    _ = _ :=
        (limsup_congr (.of_forall fun i => (coe_mul_log_monotone (ε i)).map_max)).trans
          limsup_max

/-- At an inverse speed tending to `0`, the liminf rate of a sum of two nonnegative sequences is at
most the larger of the liminf rate of the first and the limsup rate of the second. If the second
rate is below the first, the second summand does not change the liminf rate. -/
theorem liminf_coe_mul_log_add_le (u v : ι → ℝ≥0∞) (hε : Tendsto ε l (𝓝 0)) :
    liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l ≤
      max (liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l)
        (limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l) := by
  calc liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l
      ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (2 * max (u i) (v i))) l :=
        liminf_coe_mul_log_mono (.of_forall fun i =>
          (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm)
    _ = liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (max (u i) (v i))) l :=
        liminf_coe_mul_log_const_mul hε two_ne_zero ENNReal.ofNat_ne_top _
    _ = liminf (fun i => max (((ε i : ℝ) : EReal) * ENNReal.log (u i))
          (((ε i : ℝ) : EReal) * ENNReal.log (v i))) l :=
        liminf_congr (.of_forall fun i => (coe_mul_log_monotone (ε i)).map_max)
    _ ≤ _ := liminf_max_le_max_liminf_limsup _ _

/-- At an eventually bounded inverse speed, the sum of two nonnegative sequences of limsup rate `⊥`
has limsup rate `⊥`. Unlike `limsup_coe_mul_log_add`, this needs no vanishing inverse speed. -/
theorem limsup_coe_mul_log_add_eq_bot {u v : ι → ℝ≥0∞} (hε : IsBoundedUnder (· ≤ ·) l ε)
    (hu : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i)) l = ⊥)
    (hv : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (v i)) l = ⊥) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u i + v i)) l = ⊥ := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rw [limsup_coe_mul_log, ENNReal.log_eq_bot_iff] at hu hv ⊢
  -- The powers of `u` and of `v` tend to `0`, hence so does their sum.
  have hsum : Tendsto (fun i => u i ^ (ε i : ℝ) + v i ^ (ε i : ℝ)) l (𝓝 0) := by
    simpa only [add_zero] using (tendsto_of_le_liminf_of_limsup_le zero_le hu.le).add
      (tendsto_of_le_liminf_of_limsup_le zero_le hv.le)
  obtain ⟨B, hB⟩ := hε
  refine le_antisymm ?_ bot_le
  -- Bound `(u + v) ^ ε` by `2 ^ ε * (u ^ ε + v ^ ε)`, and the factor `2 ^ ε` by `2 ^ B`.
  calc limsup (fun i => (u i + v i) ^ (ε i : ℝ)) l
      ≤ limsup (fun i => 2 ^ (B : ℝ) * (u i ^ (ε i : ℝ) + v i ^ (ε i : ℝ))) l := by
        refine limsup_le_limsup ?_
        filter_upwards [hB] with i hi
        refine (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ (ε i).coe_nonneg).trans ?_
        gcongr
        · norm_num
        · exact_mod_cast hi
    _ = 0 := by
      rw [ENNReal.limsup_const_mul_of_ne_top (ENNReal.rpow_ne_top_of_nonneg B.coe_nonneg
        ENNReal.ofNat_ne_top), hsum.limsup_eq, mul_zero]

/-- **The principle of the largest term** for a finite sum. At an inverse speed tending to `0`,
the limsup rate of a nonempty finite sum of nonnegative sequences is the largest of their limsup
rates. The empty sum has rate `⊥` once the inverse speed is eventually positive, which is
assumed only when `s` is empty. -/
theorem limsup_coe_mul_log_sum {κ : Type*} (u : κ → ι → ℝ≥0∞) (s : Finset κ)
    (hε : Tendsto ε l (𝓝 0)) (hpos : s = ∅ → ∀ᶠ i in l, 0 < ε i) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (∑ j ∈ s, u j i)) l =
      ⨆ j ∈ s, limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (u j i)) l := by
  classical
  refine le_antisymm ?_ (iSup₂_le fun j hj => limsup_coe_mul_log_mono (.of_forall fun i =>
    Finset.single_le_sum (f := fun j => u j i) (fun _ _ => bot_le) hj))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · -- The empty sum has rate `⊥` at an eventually positive inverse speed.
    refine (limsup_congr ?_).trans_le (limsup_const_bot.trans_le bot_le)
    filter_upwards [hpos rfl] with i hi
    simpa using EReal.mul_bot_of_pos (by exact_mod_cast hi)
  clear hpos
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hj _ ih =>
    simp only [Finset.cons_eq_insert, Finset.sum_insert hj, Finset.iSup_insert]
    exact (limsup_coe_mul_log_add _ _ hε).le.trans (sup_le_sup le_rfl ih)

end TauCeti.ENNReal
