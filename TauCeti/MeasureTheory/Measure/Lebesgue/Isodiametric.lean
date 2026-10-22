/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

/-!
# The isodiametric inequality

In a finite-dimensional real inner product space of dimension `n`, a set of diameter `d`
has volume at most that of a ball of radius `d / 2`:
`volume s ≤ ω_n (d / 2) ^ n`, where `ω_n = volume (ball 0 1)`.
The constant is sharp: in a nontrivial space a closed ball of radius `r` has diameter `2 r`
(`Metric.diam_closedBall_eq`).

No measurability is assumed: the outer volume of `s` is bounded through its closure,
which has the same diameter. Brunn–Minkowski for the closure and its reflection,
each scaled by `1 / 2`, shows that half the difference body has at least the volume
of the closure, and half the difference body lies in the closed ball of radius `d / 2`.

We give the bound against a closed ball of any center, the normalized form
with `ω_n`, a hypothesis-free extended form using `Metric.ediam`, and a real-valued form.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the Brunn–Minkowski inequality and the difference-body argument
  deducing the isodiametric inequality from it.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Isodiametric inequality**: a bounded set has at most the volume of a closed ball whose
radius is half its diameter. The set need not be measurable; its outer volume is bounded. -/
theorem volume_le_volume_closedBall_diam_div_two {s : Set E} (hs : Bornology.IsBounded s)
    (x : E) : volume s ≤ volume (closedBall x (diam s / 2)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hr : 0 ≤ diam s / 2 := by positivity
  by_cases hn : Module.finrank ℝ E = 0
  · -- In dimension zero every closed ball of nonnegative radius is the whole space.
    have : Subsingleton E := Module.finrank_zero_iff.1 hn
    exact measure_mono fun y _ ↦ by simp [Subsingleton.elim y x, hr]
  -- Apply Brunn–Minkowski to the closure and its reflection, both scaled by `1 / 2`.
  have hK : NullMeasurableSet (closure s) volume :=
    isClosed_closure.measurableSet.nullMeasurableSet
  have hp : 0 < (Module.finrank ℝ E : ℝ)⁻¹ := by positivity
  have hBM := volume_rpow_add_volume_rpow_le hn hne.closure.smul_set
    (Measure.NullMeasurableSet.const_smul hK (1 / 2 : ℝ)) hne.closure.smul_set
    (Measure.NullMeasurableSet.const_smul hK (-(1 / 2) : ℝ))
  have hhalf : |(1 / 2 : ℝ)| + |-(1 / 2 : ℝ)| = 1 := by norm_num
  rw [volume_smul_rpow hn, volume_smul_rpow hn, ← add_mul,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), hhalf, ENNReal.ofReal_one,
    one_mul] at hBM
  -- Half the difference body lies in the closed ball of radius `diam s / 2`.
  have hsub : (1 / 2 : ℝ) • closure s + (-(1 / 2) : ℝ) • closure s ⊆
      closedBall 0 (diam s / 2) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    have hab := dist_le_diam_of_mem hs.closure ha hb
    rw [diam_closure, dist_eq_norm] at hab
    dsimp only
    rw [mem_closedBall_zero_iff, neg_smul, ← sub_eq_add_neg, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by norm_num)]
    linarith
  have hroot : volume s ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤
      volume (closedBall x (diam s / 2)) ^ (Module.finrank ℝ E : ℝ)⁻¹ :=
    calc
      volume s ^ (Module.finrank ℝ E : ℝ)⁻¹ ≤ volume (closure s) ^ (Module.finrank ℝ E : ℝ)⁻¹ :=
        ENNReal.rpow_le_rpow (measure_mono subset_closure) hp.le
      _ ≤ _ := hBM
      _ ≤ volume (closedBall (0 : E) (diam s / 2)) ^ (Module.finrank ℝ E : ℝ)⁻¹ :=
        ENNReal.rpow_le_rpow (measure_mono hsub) hp.le
      _ = _ := by rw [Measure.addHaar_closedBall_center volume x]
  exact (ENNReal.rpow_le_rpow_iff hp).1 hroot

/-- **Isodiametric inequality** in normalized form: a bounded set `s` in dimension `n` has
volume at most `(diam s / 2) ^ n * ω_n`, where `ω_n` is the volume of the unit ball. -/
theorem volume_le_ofReal_diam_div_two_pow_mul_volume_ball {s : Set E}
    (hs : Bornology.IsBounded s) :
    volume s ≤
      ENNReal.ofReal ((diam s / 2) ^ Module.finrank ℝ E) * volume (ball (0 : E) 1) := by
  rw [← Measure.addHaar_closedBall volume 0 (by positivity)]
  exact volume_le_volume_closedBall_diam_div_two hs 0

/-- **Isodiametric inequality** in extended form, without boundedness: a set `s` in
dimension `n` has outer volume at most `(ediam s / 2) ^ n * ω_n`. For an unbounded set in
positive dimension the right side is infinite. -/
theorem volume_le_ediam_div_two_pow_mul_volume_ball (s : Set E) :
    volume s ≤ (ediam s / 2) ^ Module.finrank ℝ E * volume (ball (0 : E) 1) := by
  by_cases hs : Bornology.IsBounded s
  · rw [← ENNReal.ofReal_toReal hs.ediam_ne_top, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_div_of_pos two_pos,
      ← ENNReal.ofReal_pow (div_nonneg ENNReal.toReal_nonneg zero_le_two)]
    exact volume_le_ofReal_diam_div_two_pow_mul_volume_ball hs
  by_cases hn : Module.finrank ℝ E = 0
  · -- In dimension zero the unit ball is the whole space.
    have : Subsingleton E := Module.finrank_zero_iff.1 hn
    rw [hn, pow_zero, one_mul]
    exact measure_mono fun y _ ↦ by simp [Subsingleton.elim y 0]
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hn)
  rw [ediam_of_unbounded hs, ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top,
    ENNReal.top_pow hn, ENNReal.top_mul (measure_ball_pos volume 0 one_pos).ne']
  exact le_top

/-- Real-valued **isodiametric inequality**: a bounded set `s` in dimension `n` has volume at
most `(diam s / 2) ^ n` times the volume of the unit ball. Bounded sets have finite volume,
so no finiteness hypothesis is needed. -/
theorem volume_real_le_diam_div_two_pow_mul_volume_real_ball {s : Set E}
    (hs : Bornology.IsBounded s) :
    volume.real s ≤ (diam s / 2) ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) := by
  have h := volume_le_ofReal_diam_div_two_pow_mul_volume_ball hs
  have hfin : ENNReal.ofReal ((diam s / 2) ^ Module.finrank ℝ E) * volume (ball (0 : E) 1) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hd : 0 ≤ (diam s / 2) ^ Module.finrank ℝ E := by positivity
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] using
    ENNReal.toReal_mono hfin h

end TauCeti
