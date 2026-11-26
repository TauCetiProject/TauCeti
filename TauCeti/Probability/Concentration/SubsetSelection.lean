/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Concentration of finite subset selections

Pairwise independent membership indicators control the discrepancy of the selected count in
all fibres of a finite partition. For balanced fibres, sampling with different probabilities
on different fibres yields a subset whose relative fibre sizes approximate the normalized
sampling profile. The absolute discrepancies are estimated by Chebyshev's inequality.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace TauCeti

/-- Express the intersection count as a sum of membership indicators. -/
private theorem card_filter_mem_eq_sum_indicator {Ω α : Type*} [DecidableEq α]
    (S : Ω → Finset α) (s : Finset α) :
    (fun x ↦ ((s.filter fun a ↦ a ∈ S x).card : ℝ)) =
      ∑ a ∈ s, {x | a ∈ S x}.indicator (1 : Ω → ℝ) := by
  funext x
  rw [Finset.natCast_card_filter, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ ↦ by simp only [indicator_apply, mem_ofPred_eq, Pi.one_apply]

/-- The integral of the count of selected elements in `s` is the sum of their membership
measures. No independence is required. -/
theorem integral_card_filter_mem {Ω α : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [DecidableEq α] (S : Ω → Finset α)
    (s : Finset α) (hm : ∀ a ∈ s, MeasurableSet {x | a ∈ S x}) :
    (∫ x, ((s.filter fun a ↦ a ∈ S x).card : ℝ) ∂μ) = ∑ a ∈ s, μ.real {x | a ∈ S x} := by
  rw [card_filter_mem_eq_sum_indicator]
  let I (a : α) := {x | a ∈ S x}.indicator (1 : Ω → ℝ)
  have hsum := integral_finsetSum (μ := μ) s (f := I)
    (fun a ha ↦ (integrable_const (1 : ℝ)).indicator (hm a ha))
  simp only [← Finset.sum_apply _ s I] at hsum
  exact hsum.trans (Finset.sum_congr rfl fun a ha ↦ integral_indicator_one (hm a ha))

/-- If the membership indicators for elements of `s` are pairwise independent, the variance
of the count of selected elements in `s` is at most the sum of their membership probabilities. -/
theorem variance_card_filter_mem_le {Ω α : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [DecidableEq α] (S : Ω → Finset α)
    (s : Finset α) (hm : ∀ a ∈ s, MeasurableSet {x | a ∈ S x})
    (hi : (s : Set α).Pairwise fun a b ↦ IndepFun ({x | a ∈ S x}.indicator (1 : Ω → ℝ))
      ({x | b ∈ S x}.indicator (1 : Ω → ℝ)) μ) :
    Var[fun x ↦ ((s.filter fun a ↦ a ∈ S x).card : ℝ); μ] ≤ ∑ a ∈ s, μ.real {x | a ∈ S x} := by
  let I (a : α) := {x | a ∈ S x}.indicator (1 : Ω → ℝ)
  have hLp (a : α) (ha : a ∈ s) : MemLp (I a) 2 μ :=
    (memLp_const 1).indicator (hm a ha).nullMeasurableSet
  rw [card_filter_mem_eq_sum_indicator, IndepFun.variance_sum hLp hi]
  refine Finset.sum_le_sum fun a ha ↦
    (variance_le_expectation_sq (hLp a ha).aestronglyMeasurable).trans_eq ?_
  have hsquare : (fun x ↦ I a x ^ 2) = I a := by
    funext x
    by_cases hx : a ∈ S x <;> simp [I, hx]
  exact (congrArg (integral μ) hsquare).trans (integral_indicator_one (hm a ha))

/-- For a finite partition, the probability that all selected fibre counts differ from their
means by at most `r` is at least one minus the expected size of the selection divided by `r²`.
Only pairwise independence is required. -/
theorem le_measureReal_forall_abs_card_filter_sub_sum_le {Ω α Q : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype α] [Finite Q] [DecidableEq Q]
    (S : Ω → Finset α) (p : α → Q) {r : ℝ}
    (hr : 0 < r) (hm : ∀ a, MeasurableSet {x | a ∈ S x})
    (hi : Pairwise fun a b : α ↦ IndepFun ({x | a ∈ S x}.indicator (1 : Ω → ℝ))
      ({x | b ∈ S x}.indicator (1 : Ω → ℝ)) μ) :
    1 - (∑ a, μ.real {x | a ∈ S x}) / r ^ 2 ≤ μ.real {x | ∀ q : Q,
      |((S x).filter fun a ↦ p a = q).card -
        ∑ a ∈ Finset.univ.filter (fun a ↦ p a = q), μ.real {w | a ∈ S w}| ≤ r} := by
  classical
  let := Fintype.ofFinite Q
  let T (q : Q) := Finset.univ.filter (fun a ↦ p a = q)
  set M : Q → ℝ := fun q ↦ ∑ a ∈ T q, μ.real {x | a ∈ S x} with hM
  set X : Q → Ω → ℝ := fun q x ↦ (((S x).filter fun a ↦ p a = q).card : ℝ) with hX
  have hfilter (q : Q) (x : Ω) : (T q).filter (fun a ↦ a ∈ S x) =
      (S x).filter (fun a ↦ p a = q) := by ext a; simp [T, and_comm]
  have hcount (q : Q) : X q = ∑ a ∈ T q, {x | a ∈ S x}.indicator (1 : Ω → ℝ) := by
    simpa only [hX, hfilter] using card_filter_mem_eq_sum_indicator S (T q)
  have hm' (a : α) : Measurable ({x | a ∈ S x}.indicator (1 : Ω → ℝ)) :=
    measurable_const.indicator (hm a)
  have hmeas (q : Q) : Measurable (X q) := by
    simpa only [hcount, ← Finset.sum_apply] using Finset.measurable_sum (T q) (fun a _ ↦ hm' a)
  have hprob (q : Q) : μ.real {x | r < |X q x - M q|} ≤ M q / r ^ 2 := by
    have hLp : MemLp (X q) 2 μ := by
      rw [hcount]
      exact memLp_finsetSum' _ fun a _ ↦ (memLp_const 1).indicator (hm a).nullMeasurableSet
    have he : (∫ x, X q x ∂μ) = M q := by
      simpa only [hX, hM, hfilter] using integral_card_filter_mem S (T q) (fun a _ ↦ hm a)
    have hv : Var[X q; μ] ≤ M q := by
      simpa only [hX, hM, hfilter] using
        variance_card_filter_mem_le S (T q) (fun a _ ↦ hm a) (hi.set_pairwise _)
    have hc := meas_ge_le_variance_div_sq hLp hr
    rw [he] at hc
    refine ENNReal.toReal_le_of_le_ofReal
      (div_nonneg ((variance_nonneg _ _).trans hv) (sq_nonneg r)) ?_
    calc
      _ ≤ μ {x | r ≤ |X q x - M q|} := measure_mono fun _ hx ↦ (mem_ofPred_eq.mp hx).le
      _ ≤ _ := hc.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hv (sq_nonneg r)))
  let B := ⋃ q, {x | r < |X q x - M q|}
  have hB : MeasurableSet B := MeasurableSet.iUnion fun q ↦
    measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hmeas q).sub_const _))
  have hle : μ.real B ≤ (∑ a, μ.real {x | a ∈ S x}) / r ^ 2 := calc
    _ ≤ ∑ q, μ.real {x | r < |X q x - M q|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ q, M q / r ^ 2 := Finset.sum_le_sum fun q _ ↦ hprob q
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_fiberwise Finset.univ p, hM]
  have hgood : {x | ∀ q : Q, |X q x - M q| ≤ r} = Bᶜ := by
    ext x
    simp [B, not_lt]
  rw [hgood, measureReal_compl hB, probReal_univ]
  exact sub_le_sub_left hle _

/-- The size and relative errors follow deterministically from the absolute errors of the
individual fibre counts. -/
private theorem card_fiber_bounds_of_abs_sub_le {Q : Type*} [Fintype Q] (c ω : Q → ℝ)
    {a D E ω₀ : ℝ} (hE : E = a * ∑ j, ω j) (hD : 0 < D) (hω₀ : 0 < ω₀)
    (hω : ∀ q, ω q ∈ Icc ω₀ 1) (ho : 0 < (Fintype.card Q : ℝ))
    (hW₀ : (Fintype.card Q : ℝ) * ω₀ ≤ ∑ j, ω j) (hE₀ : ω₀ * D ≤ E)
    (hsize : 16 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D)
    (hclose : ∀ q, |c q - a * ω q| ≤ 2 * Real.sqrt D) :
    E / 2 ≤ (∑ j, c j) ∧ (∑ j, c j) ≤ 3 * E / 2 ∧
      (36 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D → 2 * E / 3 ≤ (∑ j, c j)) ∧
      ∀ q, |c q - (ω q / ∑ j, ω j) * ∑ j, c j| ≤
        (4 * (1 + ω₀) / ω₀ ^ 2 / Real.sqrt D) * ∑ j, c j := by
  let o : ℝ := Fintype.card Q
  let W := ∑ q, ω q
  let M (q : Q) := a * ω q
  have hsumErr : (∑ q, |c q - M q|) ≤ o * (2 * Real.sqrt D) := by
    simpa [o, nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ hclose q
  have htot : |(∑ j, c j) - E| ≤ o * (2 * Real.sqrt D) := by
    simpa only [Finset.sum_sub_distrib, M, ← Finset.mul_sum, ← hE] using
      (Finset.abs_sum_le_sum_abs (fun q ↦ c q - M q) Finset.univ).trans hsumErr
  have hscale (k : ℝ) (h : (2 * k) ^ 2 * o ^ 2 / ω₀ ^ 2 ≤ D) : 2 * k * o * Real.sqrt D ≤ E := by
    have hs : 2 * k * o / ω₀ ≤ Real.sqrt D :=
      Real.le_sqrt_of_sq_le (by simpa only [div_pow, mul_pow] using h)
    have ht := mul_le_mul_of_nonneg_right ((div_le_iff₀ hω₀).mp hs) (Real.sqrt_nonneg D)
    rw [mul_right_comm (Real.sqrt D), Real.mul_self_sqrt hD.le, mul_comm D] at ht
    exact ht.trans hE₀
  have hhalf := hscale 2
    (by simpa only [show (2 * 2 : ℝ) ^ 2 = 16 by norm_num, o] using hsize)
  have hcard₀ : E / 2 ≤ (∑ j, c j) := by linarith [(abs_le.mp htot).1]
  refine ⟨hcard₀, by linarith [(abs_le.mp htot).2], fun h ↦ ?_, fun q ↦ ?_⟩
  · have hthird := hscale 3
      (by simpa only [show (2 * 3 : ℝ) ^ 2 = 36 by norm_num, o] using h)
    linarith [(abs_le.mp htot).1]
  · have hW : 0 < W := (mul_pos ho hω₀).trans_le hW₀
    have hν : ω q / W * E = M q := calc
      _ = ω q / W * (a * W) := congrArg (fun t ↦ ω q / W * t) hE
      _ = M q := by rw [mul_left_comm, div_mul_cancel₀ _ hW.ne']
    have hν₀ : 0 ≤ ω q / W := div_nonneg (hω₀.le.trans (hω q).1) hW.le
    have hν₁ : (ω q / W) * o ≤ 1 / ω₀ := by
      calc
        _ = ω q * o / W := by ring
        _ ≤ 1 * o / (o * ω₀) := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hω q).2 ho.le) (mul_pos ho hω₀) hW₀
        _ = _ := by field_simp [(ne_of_gt ho : o ≠ 0)]
    calc
      _ = |(c q - M q) - (ω q / W) * ((∑ j, c j) - E)| := by
        congr 1
        rw [mul_sub, hν]
        ring
      _ ≤ |c q - M q| + (ω q / W) * |(∑ j, c j) - E| := by
        simpa only [abs_mul, abs_of_nonneg hν₀] using abs_sub (c q - M q)
          ((ω q / W) * ((∑ j, c j) - E))
      _ ≤ 2 * Real.sqrt D * (1 + 1 / ω₀) := by
        have h := mul_le_mul_of_nonneg_right hν₁ (by positivity : 0 ≤ 2 * Real.sqrt D)
        have hb := add_le_add (hclose q) (mul_le_mul_of_nonneg_left htot hν₀)
        rw [← mul_assoc] at hb
        linarith
      _ = (4 * (1 + ω₀) / ω₀ ^ 2 / Real.sqrt D) * (ω₀ * D / 2) := by
        field_simp [ne_of_gt (Real.sqrt_pos.2 hD)]
        rw [Real.sq_sqrt hD.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- For fibres of size `m` and pairwise independent selection with probabilities `δ * ω (p a)`,
where `ω q ∈ [ω₀, 1]` and `ω₀ > 0`, put `D = δ * |α|`. If `16 * |Q|² / ω₀² ≤ D`, then with
probability at least `3/4` the total count is within half its expectation `δ * m * ∑ j, ω j`.
On the same event, each fibre count differs from `ω q / (∑ j, ω j)` times the total by at most
`4 * (1 + ω₀) / (ω₀² * √D)` times the total, and if `36 * |Q|² / ω₀² ≤ D`, the total is at least
two thirds of its expectation. For a quotient map by a subgroup this bounds the coset counts. -/
theorem three_div_four_le_measureReal_card_fiber_bounds {Ω α Q : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype α] [Fintype Q] [DecidableEq Q]
    (S : Ω → Finset α) (p : α → Q) {m : ℕ}
    (hf : ∀ q, (Finset.univ.filter fun a ↦ p a = q).card = m)
    (ω : Q → ℝ) {ω₀ δ : ℝ} (hω₀ : 0 < ω₀) (hω : ∀ q, ω q ∈ Icc ω₀ 1)
    (hsize : 16 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ δ * Fintype.card α)
    (hm : ∀ a, MeasurableSet {x | a ∈ S x})
    (hi : Pairwise fun a b : α ↦ IndepFun ({x | a ∈ S x}.indicator (1 : Ω → ℝ))
      ({x | b ∈ S x}.indicator (1 : Ω → ℝ)) μ)
    (hprob : ∀ a, μ.real {x | a ∈ S x} = δ * ω (p a)) :
    let D := δ * Fintype.card α
    let E := δ * m * ∑ q, ω q
    3 / 4 ≤ μ.real {x | E / 2 ≤ (S x).card ∧ (S x).card ≤ 3 * E / 2 ∧
      (36 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D → 2 * E / 3 ≤ (S x).card) ∧
      ∀ q : Q, |((S x).filter fun a ↦ p a = q).card - (ω q / ∑ j, ω j) * (S x).card| ≤
        (4 * (1 + ω₀) / ω₀ ^ 2 / Real.sqrt D) * (S x).card} := by
  dsimp only
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · have : IsEmpty α := ⟨fun a ↦ isEmptyElim (p a)⟩
    norm_num [Finset.eq_empty_of_isEmpty, probReal_univ]
  let D := δ * Fintype.card α
  let o : ℝ := Fintype.card Q
  let W := ∑ q, ω q
  set E := δ * m * (∑ q, ω q) with hE
  set M : Q → ℝ := fun q ↦ δ * m * ω q with hMdef
  have ho : 0 < o := by dsimp [o]; exact_mod_cast Fintype.card_pos
  have hD : 0 < D := (by positivity : 0 < 16 * o ^ 2 / ω₀ ^ 2).trans_le hsize
  have hδ : 0 < δ := pos_of_mul_pos_left hD (by positivity)
  have hcard : Fintype.card α = Fintype.card Q * m := by
    simpa [hf, nsmul_eq_mul] using Finset.card_eq_sum_card_fiberwise
      (f := p) (s := Finset.univ) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
  have hD' : D = δ * m * o := by simp only [D, hcard, Nat.cast_mul, o]; ring
  have hW₀ : o * ω₀ ≤ W := by
    simpa [o, W, nsmul_eq_mul] using Finset.univ.card_nsmul_le_sum ω ω₀ (fun q _ ↦ (hω q).1)
  have hW₁ : W ≤ o := by
    simpa [W, o] using Finset.univ.sum_le_card_nsmul ω 1 (fun q _ ↦ (hω q).2)
  have hE₀ : ω₀ * D ≤ E := by
    rw [hD']; calc
      _ = (δ * m) * (o * ω₀) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hW₀ (by positivity)
  have hE₁ : E ≤ D := hD'.symm ▸ mul_le_mul_of_nonneg_left hW₁ (by positivity)
  have hM (q : Q) : ∑ a ∈ Finset.univ.filter (fun a ↦ p a = q), μ.real {x | a ∈ S x} = M q := by
    calc
      _ = ∑ _a ∈ Finset.univ.filter (fun a ↦ p a = q), δ * ω q :=
        Finset.sum_congr rfl fun a ha ↦ by rw [hprob, (Finset.mem_filter.mp ha).2]
      _ = _ := by simp only [Finset.sum_const, hf, nsmul_eq_mul, hMdef]; ring
  have hmean : (∑ a, μ.real {x | a ∈ S x}) = E := by
    rw [← Finset.sum_fiberwise Finset.univ p, hE, Finset.mul_sum]
    simpa only [← hMdef] using Finset.sum_congr rfl (fun q _ ↦ hM q)
  have hr : 0 < 2 * Real.sqrt D := by positivity
  have hg := le_measureReal_forall_abs_card_filter_sub_sum_le S p hr hm hi
  have hs : (2 * Real.sqrt D) ^ 2 = 4 * D := by rw [mul_pow, Real.sq_sqrt hD.le]; norm_num
  simp only [hmean, hs, hM] at hg
  have hratio : E / (4 * D) ≤ 1 / 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
  refine (by linarith only [hratio] : 3 / 4 ≤ 1 - E / (4 * D)).trans
    (hg.trans (measureReal_mono ?_))
  intro x hx
  let c (q : Q) : ℝ := ((S x).filter fun a ↦ p a = q).card
  have hc : (∑ q, c q) = (S x).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := p) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _),
      Nat.cast_sum]
  simp only [mem_ofPred_eq, hMdef] at hx
  have hb := card_fiber_bounds_of_abs_sub_le c ω hE hD hω₀ hω ho hW₀ hE₀ hsize hx
  rw [hc] at hb
  exact hb

end TauCeti
