/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic
-- Proof-only: equality in Brunn–Minkowski for convex bodies forces a translate.
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Homothety
-- Proof-only: a subset of a ball with the ball's volume agrees with it a.e.
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

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

## Equality

Equality forces a ball. If a bounded set `s` has outer volume at least that of a ball of radius
`d / 2`, `d = diam s`, then its closed convex hull `H` has the same volume and diameter, so
Brunn–Minkowski for `H` and `-H` with weight `1 / 2` is an equality. For convex bodies of positive
volume this makes `-H` a translate `v +ᵥ H`, so `H` is symmetric about `-(1 / 2) • v`; a symmetric
set of diameter `d` lies in the closed ball of radius `d / 2` about its center of symmetry. Hence
`s` lies in a closed ball of radius `d / 2`
(`TauCeti.exists_subset_closedBall_diam_div_two_of_volume_ge`), a containment that fails for
general sets of diameter `d`, such as equilateral triangles.

For a Lebesgue-measurable bounded set, equality holds exactly when the set agrees a.e. with a
closed ball of radius `diam s / 2`
(`TauCeti.volume_eq_volume_closedBall_diam_div_two_iff_exists_ae_eq`). The radius is tied to the
diameter of `s` itself: a null modification can enlarge the diameter without changing the volume.
For a nonempty closed bounded set, in particular a convex body, equality holds exactly when the
set is a closed ball of radius `diam s / 2`
(`TauCeti.volume_eq_volume_closedBall_diam_div_two_iff_exists_eq`).

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the Brunn–Minkowski inequality and the difference-body argument
  deducing the isodiametric inequality from it.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Theorem 7.1.1, for the equality case of Brunn–Minkowski for convex bodies.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Half the difference of two points at distance at most `d` has norm at most `d / 2`. -/
private lemma norm_half_smul_sub_le {a b : E} {d : ℝ} (h : ‖a - b‖ ≤ d) :
    ‖(1 / 2 : ℝ) • (a - b)‖ ≤ d / 2 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith

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
    rw [mem_closedBall_zero_iff, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    exact norm_half_smul_sub_le hab
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

/-- **Isodiametric equality forces a ball, containment form.** If a bounded set `s` has outer volume
at least that of a closed ball of radius `diam s / 2`, then `s` is contained in some closed ball of
radius `diam s / 2`. No measurability is assumed. -/
theorem exists_subset_closedBall_diam_div_two_of_volume_ge {s : Set E}
    (hs : Bornology.IsBounded s) {x : E} (hvol : volume (closedBall x (diam s / 2)) ≤ volume s) :
    ∃ c, s ⊆ closedBall c (diam s / 2) := by
  rcases eq_or_ne (volume s) 0 with h0 | h0
  · -- A null extremal set has diameter zero, so it lies in a ball of radius zero.
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨x, empty_subset _⟩
    have hd : diam s = 0 := by
      refine le_antisymm (not_lt.1 fun hpos ↦ ?_) diam_nonneg
      exact (measure_closedBall_pos volume x (half_pos hpos)).ne' (le_zero_iff.1 (h0 ▸ hvol))
    refine ⟨a, fun y hy ↦ ?_⟩
    rw [mem_closedBall, hd, zero_div]
    exact hd ▸ dist_le_diam_of_mem hs hy ha
  -- Pass to the closed convex hull `H`, which has the same diameter and the same volume.
  set H := closure (convexHull ℝ s) with hH
  have hHc : IsCompact H := (isBounded_convexHull.2 hs).isCompact_closure
  have hHconv : Convex ℝ H := (convex_convexHull ℝ s).closure
  have hHd : diam H = diam s := by rw [hH, diam_closure, convexHull_diam]
  have hsH : s ⊆ H := (subset_convexHull ℝ s).trans subset_closure
  have hHvol : volume H = volume (closedBall (0 : E) (diam s / 2)) := by
    refine le_antisymm ?_ ?_
    · simpa only [hHd] using volume_le_volume_closedBall_diam_div_two hHc.isBounded 0
    · rw [← Measure.addHaar_closedBall_center volume x]
      exact hvol.trans (measure_mono hsH)
  have hH0 : volume H ≠ 0 := ne_bot_of_le_ne_bot h0 (measure_mono hsH)
  -- Half the difference body lies in the ball of radius `diam s / 2`, so Brunn–Minkowski for
  -- `H` and `-H` with weight `1 / 2` is an equality, and `-H` is a translate of `H`.
  have hsub : (1 - 1 / 2 : ℝ) • H + (1 / 2 : ℝ) • (-H) ⊆ closedBall 0 (diam s / 2) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    have hab := dist_le_diam_of_mem hHc.isBounded ha (Set.mem_neg.1 hb)
    rw [hHd, dist_eq_norm] at hab
    have : (1 - 1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (1 / 2 : ℝ) • (a - -b) := by module
    dsimp only
    rw [mem_closedBall_zero_iff, this]
    exact norm_half_smul_sub_le hab
  have hneg : volume (-H) = volume H := Measure.measure_neg volume H
  obtain ⟨v, hv⟩ := hHconv.exists_eq_vadd_of_volume_le hHc hH0 hHconv.neg
    hHc.neg (hneg ▸ hH0) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by
      rw [hneg, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), sub_add_cancel,
        ENNReal.rpow_one, hHvol]
      exact measure_mono hsub)
  -- Hence `H` is symmetric about `-(1 / 2) • v` and lies in the ball of radius `diam s / 2`.
  refine ⟨-((1 / 2 : ℝ) • v), hsH.trans fun y hy ↦ ?_⟩
  have hy' : -v + -y ∈ H := (mem_vadd_set_iff_neg_vadd_mem).1 (hv ▸ Set.neg_mem_neg.2 hy)
  have hyz := dist_le_diam_of_mem hHc.isBounded hy hy'
  rw [hHd, dist_eq_norm] at hyz
  rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add]
  have : y + (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • (y - (-v + -y)) := by module
  rw [this]
  exact norm_half_smul_sub_le hyz

/-- **Equality in the isodiametric inequality, a.e. form.** A bounded Lebesgue-measurable set `s`
has the volume of a closed ball of radius `diam s / 2` exactly when it agrees a.e. with such a
ball. -/
theorem volume_eq_volume_closedBall_diam_div_two_iff_exists_ae_eq {s : Set E}
    (hs : Bornology.IsBounded s) (hsm : NullMeasurableSet s volume) (x : E) :
    volume s = volume (closedBall x (diam s / 2)) ↔
      ∃ c, s =ᵐ[volume] closedBall c (diam s / 2) := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := exists_subset_closedBall_diam_div_two_of_volume_ge hs h.ge
    exact ⟨c, volume.ae_eq_closedBall_of_subset_of_measure_eq hsm hc h⟩
  · rw [measure_congr hc, Measure.addHaar_closedBall_center volume c,
      Measure.addHaar_closedBall_center volume x]

/-- **Equality in the isodiametric inequality for closed sets.** A nonempty closed bounded set `s`,
for instance a convex body, has the volume of a closed ball of radius `diam s / 2` exactly when it
is such a ball. -/
theorem volume_eq_volume_closedBall_diam_div_two_iff_exists_eq {s : Set E} (hsc : IsClosed s)
    (hs : Bornology.IsBounded s) (hne : s.Nonempty) (x : E) :
    volume s = volume (closedBall x (diam s / 2)) ↔ ∃ c, s = closedBall c (diam s / 2) := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := exists_subset_closedBall_diam_div_two_of_volume_ge hs h.ge
    refine ⟨c, hc.antisymm ?_⟩
    rcases (diam_nonneg (s := s)).eq_or_lt with hd | hd
    · -- In radius zero the ball is the center, which lies in `s` since `s` is nonempty.
      obtain ⟨a, ha⟩ := hne
      have hac := hc ha
      rw [← hd, zero_div, closedBall_zero, mem_singleton_iff] at hac
      rw [← hd, zero_div, closedBall_zero, singleton_subset_iff, ← hac]
      exact ha
    -- The open set `ball c (diam s / 2) \ s` is null, hence empty, and `s` is closed.
    have hae : s =ᵐ[volume] closedBall c (diam s / 2) :=
      volume.ae_eq_closedBall_of_subset_of_measure_eq hsc.nullMeasurableSet hc h
    have hball : ball c (diam s / 2) ⊆ s := sdiff_eq_empty.1 <|
      (isOpen_ball.sdiff hsc).eq_empty_of_measure_zero <|
        measure_mono_null (sdiff_subset_sdiff_left ball_subset_closedBall) (ae_eq_set.1 hae).2
    rw [← closure_ball c (half_pos hd).ne']
    exact closure_minimal hball hsc
  · rw [Measure.addHaar_closedBall_center volume x, ← Measure.addHaar_closedBall_center volume c,
      ← hc]

end TauCeti
