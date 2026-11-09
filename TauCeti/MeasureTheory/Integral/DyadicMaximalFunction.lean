/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
public import TauCeti.MeasureTheory.Integral.MaximalFunction

/-!
# The dyadic maximal function

The **dyadic maximal function** of `f : ℝⁿ → F` is

`M_d f x = sup_{Q ∋ x} ⨍_Q ‖f‖`,

the supremum of the averages of `‖f‖` over the dyadic cubes containing `x`, one of each level
(`TauCeti.dyadicMaximalFunction`). Its superlevel sets are the unions of the Calderón–Zygmund
cubes: for `f` with finite `L¹` norm and `t ≠ 0`, `{M_d f > t}` is the disjoint union of the
maximal dyadic cubes on which `‖f‖` has average above `t`
(`TauCeti.setOf_lt_dyadicMaximalFunction_eq`). This makes `M_d` the operator behind the
stopping-time arguments of harmonic analysis, and gives its weak type `(1, 1)` bound with
constant `1` (`TauCeti.mul_volume_lt_dyadicMaximalFunction_le`).

On `ℝⁿ` with the sup norm, the dyadic and the centred maximal function `TauCeti.maximalFunction`
are comparable with dimensional constants:

* pointwise, `M_d f ≤ 2ⁿ M f`, since a dyadic cube of side `2ᵏ` containing `x` lies in the ball
  of radius `2ᵏ` about `x` (`TauCeti.dyadicMaximalFunction_le_two_pow_mul_maximalFunction`);
* in measure, `|{M f > 3ⁿ t}| ≤ 3ⁿ |{M_d f > t}|`, since `{M f > 3ⁿ t}` lies in the union of the
  threefold enlargements of the Calderón–Zygmund cubes at height `t`
  (`TauCeti.volume_lt_maximalFunction_le_mul_volume_lt_dyadicMaximalFunction`).

The second comparison cannot be made pointwise: the dyadic cubes containing a point only exhaust
its closed orthant, so `M_d f` vanishes on any orthant disjoint from the support of `f`, while
`M f` is positive everywhere unless `f = 0` almost everywhere.

## Main declarations

* `TauCeti.dyadicMaximalFunction`: the dyadic maximal function, with
  `TauCeti.setLAverage_le_dyadicMaximalFunction`, `TauCeti.dyadicMaximalFunction_le` and
  `TauCeti.lt_dyadicMaximalFunction_iff` as its interface.
* `TauCeti.measurable_dyadicMaximalFunction`: `M_d f` is Borel measurable.
* `TauCeti.setOf_lt_dyadicMaximalFunction_eq`: its superlevel sets are the unions of the
  Calderón–Zygmund cubes.
* `TauCeti.mul_volume_lt_dyadicMaximalFunction_le`: the weak type `(1, 1)` bound.
* `TauCeti.dyadicMaximalFunction_le_two_pow_mul_maximalFunction`,
  `TauCeti.volume_lt_maximalFunction_le_mul_volume_lt_dyadicMaximalFunction`: the comparison with
  the centred maximal function.

## References

* E. Stein, *Harmonic Analysis*, Chapter I.
* L. Grafakos, *Classical Fourier Analysis*, Section 2.1.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {ι : Type*} [Fintype ι] {F : Type*} [ENorm F] {f : (ι → ℝ) → F} {x : ι → ℝ}
  {k : ℤ} {m : ι → ℤ} {a t : ℝ≥0∞}

/-- The **dyadic maximal function** of `f`: the supremum of the averages of `‖f‖` over the dyadic
cubes containing `x`, one of each level. -/
noncomputable def dyadicMaximalFunction (f : (ι → ℝ) → F) (x : ι → ℝ) : ℝ≥0∞ :=
  ⨆ k : ℤ, ⨍⁻ y in dyadicCube k (dyadicIndex k x), ‖f y‖ₑ ∂volume

theorem dyadicMaximalFunction_def (f : (ι → ℝ) → F) (x : ι → ℝ) :
    dyadicMaximalFunction f x = ⨆ k : ℤ, ⨍⁻ y in dyadicCube k (dyadicIndex k x), ‖f y‖ₑ ∂volume :=
  (rfl)

/-- The average of `‖f‖` over a dyadic cube containing `x` is at most the dyadic maximal function
at `x`. -/
theorem setLAverage_le_dyadicMaximalFunction (f : (ι → ℝ) → F) (hx : x ∈ dyadicCube k m) :
    ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume ≤ dyadicMaximalFunction f x := by
  rw [← mem_dyadicCube.1 hx]
  exact le_iSup (fun k => ⨍⁻ y in dyadicCube k (dyadicIndex k x), ‖f y‖ₑ ∂volume) k

/-- The dyadic maximal function at `x` is at most any bound for the averages of `‖f‖` over the
dyadic cubes containing `x`. -/
theorem dyadicMaximalFunction_le
    (h : ∀ k m, x ∈ dyadicCube k m → ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume ≤ a) :
    dyadicMaximalFunction f x ≤ a :=
  iSup_le fun k => h k _ (mem_dyadicCube_dyadicIndex k x)

/-- The dyadic maximal function exceeds `t` at `x` exactly when the average of `‖f‖` over some
dyadic cube containing `x` does. -/
theorem lt_dyadicMaximalFunction_iff :
    t < dyadicMaximalFunction f x ↔
      ∃ k m, x ∈ dyadicCube k m ∧ t < ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume := by
  refine ⟨fun h => ?_, fun ⟨k, m, hx, hlt⟩ => hlt.trans_le
    (setLAverage_le_dyadicMaximalFunction f hx)⟩
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 h
  exact ⟨k, _, mem_dyadicCube_dyadicIndex k x, hk⟩

/-- The dyadic maximal function is Borel measurable: at each level it depends on `x` only through
the dyadic index, and it is a countable supremum over the levels. No hypothesis on `f` is
needed. -/
@[fun_prop]
theorem measurable_dyadicMaximalFunction (f : (ι → ℝ) → F) :
    Measurable (dyadicMaximalFunction f) := by
  refine Measurable.iSup fun k => (measurable_of_countable
    fun m : ι → ℤ => ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume).comp ?_
  refine measurable_to_countable' fun m => ?_
  rw [show dyadicIndex k ⁻¹' {m} = dyadicCube k m from Set.ext fun _ => mem_dyadicCube.symm]
  exact measurableSet_dyadicCube k m

/-- **The dyadic maximal function is controlled by the centred one**: `M_d f ≤ 2ⁿ M f`, for the
sup norm on `ℝⁿ`. A dyadic cube of side `2ᵏ` containing `x` lies in the ball of radius `2ᵏ`
about `x`, whose volume is `2ⁿ` times that of the cube. -/
theorem dyadicMaximalFunction_le_two_pow_mul_maximalFunction (f : (ι → ℝ) → F) (x : ι → ℝ) :
    dyadicMaximalFunction f x ≤ 2 ^ Fintype.card ι * maximalFunction volume f x := by
  refine dyadicMaximalFunction_le fun k m hx => ?_
  have hk : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hQB : dyadicCube k m ⊆ ball x (2 ^ k) := fun y hy =>
    mem_ball.2 (dist_lt_of_mem_dyadicCube hy hx)
  have hvol : volume (ball x (2 ^ k)) = 2 ^ Fintype.card ι * volume (dyadicCube k m) := by
    rw [Real.volume_pi_ball _ hk, volume_dyadicCube, mul_pow, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  calc ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume
      ≤ volume (ball x (2 ^ k)) / volume (dyadicCube k m) *
          ⨍⁻ y in ball x (2 ^ k), ‖f y‖ₑ ∂volume :=
        setLAverage_le_div_mul_setLAverage_of_subset hQB measure_ball_lt_top.ne
    _ ≤ 2 ^ Fintype.card ι * maximalFunction volume f x := by
        rw [hvol, ENNReal.mul_div_cancel_right (volume_dyadicCube_pos k m).ne'
          (volume_dyadicCube_ne_top k m)]
        gcongr
        exact setLAverage_le_maximalFunction volume f x hk

/-- In positive dimension, the superlevel set of the dyadic maximal function of a function with
finite `L¹` norm at a height `t ≠ 0` is the union of the Calderón–Zygmund cubes of `‖f‖` at
height `t`. -/
theorem setOf_lt_dyadicMaximalFunction_eq [Nonempty ι] (hf : ∫⁻ y, ‖f y‖ₑ ≠ ∞) (ht : t ≠ 0) :
    {x | t < dyadicMaximalFunction f x} =
      ⋃ q ∈ calderonZygmundCubes (fun y => ‖f y‖ₑ) t, dyadicCube q.1 q.2 := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, lt_dyadicMaximalFunction_iff, exists_prop]
  constructor
  · rintro ⟨k, m, hx, hlt⟩
    obtain ⟨q, hq, -, hsub⟩ := exists_mem_calderonZygmundCubes_of_lt_setLAverage hf ht hlt
    exact ⟨q, hq, hsub hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨q.1, q.2, hx, lt_setLAverage_of_mem_calderonZygmundCubes hq⟩

/-- **The weak type `(1, 1)` bound for the dyadic maximal function**, with constant `1`:
`t |{M_d f > t}| ≤ ‖f‖₁`. -/
theorem mul_volume_lt_dyadicMaximalFunction_le (f : (ι → ℝ) → F) (t : ℝ≥0∞) :
    t * volume {x | t < dyadicMaximalFunction f x} ≤ ∫⁻ y, ‖f y‖ₑ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero every dyadic cube is the whole space, of volume `1`, so `M_d f` is the
    -- constant `‖f‖₁`.
    have hQ (k : ℤ) (m : ι → ℤ) : dyadicCube k m = univ :=
      eq_univ_of_forall fun y => mem_dyadicCube.2 (Subsingleton.elim _ _)
    have hvol : volume (univ : Set (ι → ℝ)) = 1 := by
      rw [← hQ 0 0, volume_dyadicCube, Fintype.card_eq_zero, pow_zero, ENNReal.ofReal_one]
    have hM (x : ι → ℝ) : dyadicMaximalFunction f x = ∫⁻ y, ‖f y‖ₑ := by
      simp only [dyadicMaximalFunction, hQ, Measure.restrict_univ, laverage_eq, hvol, div_one,
        iSup_const]
    simp only [hM]
    by_cases hlt : t < ∫⁻ y, ‖f y‖ₑ
    · simp [hlt, hvol, hlt.le]
    · simp [hlt]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rcases eq_or_ne (∫⁻ y, ‖f y‖ₑ) ∞ with hf | hf
  · simp [hf]
  rw [setOf_lt_dyadicMaximalFunction_eq hf ht]
  exact mul_volume_biUnion_calderonZygmundCubes_le.trans (setLIntegral_le_lintegral _ _)

/-- **A ball average from the dyadic averages at a comparable scale.** If `r ≤ 2ᵏ < 2r` and the
average of `‖f‖` is at most `t` on every dyadic cube of level `k` meeting the ball `B(x, r)`,
then it is at most `3ⁿ t` on `B(x, r)`: those cubes cover the ball and lie in `B(x, 3r)`. -/
private theorem setLAverage_ball_le_of_forall_dyadicCube {r : ℝ} (hr : 0 < r)
    (hk : (2 : ℝ) ^ k < 2 * r) (h : ∀ m, (dyadicCube k m ∩ ball x r).Nonempty →
      ⨍⁻ y in dyadicCube k m, ‖f y‖ₑ ∂volume ≤ t) :
    ⨍⁻ y in ball x r, ‖f y‖ₑ ∂volume ≤ 3 ^ Fintype.card ι * t := by
  set M := {m : ι → ℤ | (dyadicCube k m ∩ ball x r).Nonempty}
  have hcover : ball x r ⊆ ⋃ m ∈ M, dyadicCube k m := fun y hy =>
    mem_biUnion (x := dyadicIndex k y) ⟨y, mem_dyadicCube_dyadicIndex k y, hy⟩
      (mem_dyadicCube_dyadicIndex k y)
  have hinside : ⋃ m ∈ M, dyadicCube k m ⊆ ball x (3 * r) := by
    refine iUnion₂_subset fun m ⟨y, hyQ, hyB⟩ z hz => mem_ball.2 ?_
    calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < 2 ^ k + r := add_lt_add (dist_lt_of_mem_dyadicCube hz hyQ) (mem_ball.1 hyB)
      _ ≤ 3 * r := by linarith
  have hdisj : M.PairwiseDisjoint fun m => dyadicCube k m := fun m _ m' _ hne =>
    disjoint_dyadicCube.2 hne
  have hvol : volume (ball x (3 * r)) = 3 ^ Fintype.card ι * volume (ball x r) := by
    rw [Real.volume_pi_ball _ (by positivity), Real.volume_pi_ball _ hr,
      show 2 * (3 * r) = 3 * (2 * r) by ring, mul_pow, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hint : ∫⁻ y in ball x r, ‖f y‖ₑ ≤ 3 ^ Fintype.card ι * t * volume (ball x r) := by
    calc ∫⁻ y in ball x r, ‖f y‖ₑ ≤ ∫⁻ y in ⋃ m ∈ M, dyadicCube k m, ‖f y‖ₑ :=
          lintegral_mono_set hcover
      _ = ∑' m : M, ∫⁻ y in dyadicCube k (m : ι → ℤ), ‖f y‖ₑ :=
          lintegral_biUnion M.to_countable (fun m _ => measurableSet_dyadicCube k m) hdisj _
      _ ≤ ∑' m : M, t * volume (dyadicCube k (m : ι → ℤ)) := by
          refine tsum_le_tsum fun m => ?_
          rw [← measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _), mul_comm]
          exact mul_le_mul_left (h m m.2) _
      _ = t * volume (⋃ m ∈ M, dyadicCube k m) := by
          rw [measure_biUnion M.to_countable hdisj fun m _ => measurableSet_dyadicCube k m,
            ENNReal.tsum_mul_left]
      _ ≤ t * volume (ball x (3 * r)) := by gcongr
      _ = 3 ^ Fintype.card ι * t * volume (ball x r) := by rw [hvol]; ring
  rw [setLAverage_eq]
  exact ENNReal.div_le_of_le_mul hint

/-- **The centred maximal function is controlled by the dyadic one in measure**: in positive
dimension, for `f` with finite `L¹` norm and `t ≠ 0`,

`|{M f > 3ⁿ t}| ≤ 3ⁿ |{M_d f > t}|`,

for the sup norm on `ℝⁿ`. The superlevel set `{M_d f > t}` is the union of the Calderón–Zygmund
cubes `Q` of `‖f‖` at height `t`, and `{M f > 3ⁿ t}` lies in the union of the concentric cubes
`3Q` of three times the side: a ball `B(x, r)` with `r ≤ 2ᵏ < 2r` and `x` outside every `3Q`
meets only dyadic cubes of level `k` on which `‖f‖` has average at most `t`.

Together with the pointwise bound `M_d f ≤ 2ⁿ M f`
(`TauCeti.dyadicMaximalFunction_le_two_pow_mul_maximalFunction`), this makes the two maximal
functions comparable in distribution. They are not comparable pointwise: the dyadic cubes
containing `x` only exhaust the closed orthant of `x`, so `M_d f` vanishes on an orthant
disjoint from the support of `f`, where `M f` does not. -/
theorem volume_lt_maximalFunction_le_mul_volume_lt_dyadicMaximalFunction [Nonempty ι]
    (hf : ∫⁻ y, ‖f y‖ₑ ≠ ∞) (ht : t ≠ 0) :
    volume {x | 3 ^ Fintype.card ι * t < maximalFunction volume f x} ≤
      3 ^ Fintype.card ι * volume {x | t < dyadicMaximalFunction f x} := by
  set n := Fintype.card ι
  set C := calderonZygmundCubes (fun y => ‖f y‖ₑ) t
  -- The centre of the dyadic cube `q`; the ball about it of radius three halves of the side of
  -- `q` is the concentric cube `3Q`.
  set c : ℤ × (ι → ℤ) → ι → ℝ := fun q i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1
  have hsub : {x | 3 ^ n * t < maximalFunction volume f x} ⊆
      ⋃ q ∈ C, ball (c q) (3 * 2 ^ q.1 / 2) := by
    intro x hx
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    obtain ⟨r, hr, hlt⟩ := lt_maximalFunction_iff.1 hx
    -- A scale `2ᵏ` with `r ≤ 2ᵏ < 2r`.
    obtain ⟨j, hj1, hj2⟩ := exists_mem_Ioc_zpow hr one_lt_two
    have hk1 : r ≤ 2 ^ (j + 1) := hj2
    have hk2 : (2 : ℝ) ^ (j + 1) < 2 * r := by
      rw [zpow_add_one₀ two_ne_zero]
      linarith
    refine (hlt.trans_le (setLAverage_ball_le_of_forall_dyadicCube hr hk2 fun m hm => ?_)).false
    -- A dyadic cube of level `k` meeting `B(x, r)` with average above `t` would lie in a
    -- Calderón–Zygmund cube `Q` with `x ∈ 3Q`.
    obtain ⟨y, hyQ, hyB⟩ := hm
    refine le_of_not_gt fun hlt' => ?_
    obtain ⟨q, hq, hkq, hQq⟩ := exists_mem_calderonZygmundCubes_of_lt_setLAverage hf ht hlt'
    have hyq := mem_closedBall.1 (dyadicCube_subset_closedBall q.1 q.2 (hQq hyQ))
    have h2k : (2 : ℝ) ^ (j + 1) ≤ 2 ^ q.1 := zpow_le_zpow_right₀ one_le_two hkq
    refine hnot q hq (mem_ball.2 ?_)
    calc dist x (c q) ≤ dist x y + dist y (c q) := dist_triangle _ _ _
      _ < r + 2 ^ q.1 / 2 := add_lt_add_of_lt_of_le (mem_ball'.1 hyB) hyq
      _ ≤ 3 * 2 ^ q.1 / 2 := by linarith
  have hvol (q : ℤ × (ι → ℤ)) :
      volume (ball (c q) (3 * 2 ^ q.1 / 2)) = 3 ^ n * volume (dyadicCube q.1 q.2) := by
    rw [Real.volume_pi_ball _ (by positivity), volume_dyadicCube,
      show 2 * (3 * (2 : ℝ) ^ q.1 / 2) = 3 * 2 ^ q.1 by ring, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  calc volume {x | 3 ^ n * t < maximalFunction volume f x}
      ≤ volume (⋃ q ∈ C, ball (c q) (3 * 2 ^ q.1 / 2)) := measure_mono hsub
    _ ≤ ∑' q : C, volume (ball (c q) (3 * 2 ^ q.1.1 / 2)) :=
        measure_biUnion_le _ C.to_countable _
    _ = 3 ^ n * volume (⋃ q ∈ C, dyadicCube q.1 q.2) := by
        rw [measure_biUnion C.to_countable pairwiseDisjoint_calderonZygmundCubes
          fun q _ => measurableSet_dyadicCube q.1 q.2, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun q => hvol q
    _ = 3 ^ n * volume {x | t < dyadicMaximalFunction f x} := by
        rw [setOf_lt_dyadicMaximalFunction_eq hf ht]

end TauCeti
