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

/-- For a finite random subset, the expected count in a fixed set is the sum of its membership
probabilities. If the membership indicators are pairwise independent, its variance is at most
that expected count. -/
theorem integral_card_filter_mem_and_variance_le {Ω α : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [DecidableEq α] (S : Ω → Finset α)
    (s : Finset α) (hm : ∀ a, MeasurableSet {x | a ∈ S x})
    (hi : Pairwise fun a b : α ↦ IndepFun ({x | a ∈ S x}.indicator (1 : Ω → ℝ))
      ({x | b ∈ S x}.indicator (1 : Ω → ℝ)) μ) :
    let X := fun x ↦ ((s.filter fun a ↦ a ∈ S x).card : ℝ)
    (∫ x, X x ∂μ) = ∑ a ∈ s, μ.real {x | a ∈ S x} ∧
      Var[X; μ] ≤ ∑ a ∈ s, μ.real {x | a ∈ S x} := by
  let I (a : α) := {x | a ∈ S x}.indicator (1 : Ω → ℝ)
  have hLp (a : α) : MemLp (I a) 2 μ := (memLp_const 1).indicator (hm a).nullMeasurableSet
  have hcard : (fun x ↦ ((s.filter fun a ↦ a ∈ S x).card : ℝ)) = ∑ a ∈ s, I a := by
    ext x
    simp only [Finset.sum_apply, I, indicator_apply, mem_ofPred_eq, Pi.one_apply, Finset.sum_boole]
  dsimp only
  rw [hcard]
  constructor
  · have he := integral_finsetSum s (fun a _ ↦ (hLp a).integrable (by norm_num))
    simp only [← Finset.sum_apply] at he
    exact he.trans (Finset.sum_congr rfl fun a _ ↦ integral_indicator_one (hm a))
  · rw [IndepFun.variance_sum (fun a _ ↦ hLp a) (fun a _ b _ hab ↦ hi hab)]
    refine Finset.sum_le_sum fun a _ ↦
      (variance_le_expectation_sq (hLp a).aestronglyMeasurable).trans_eq ?_
    have hsquare : (fun x ↦ I a x ^ 2) = I a := by
      funext x
      by_cases hx : a ∈ S x <;> simp [I, hx]
    exact (congrArg (integral μ) hsquare).trans (integral_indicator_one (hm a))

open scoped Classical in
/-- For a finite partition, the probability that some selected fibre count differs from its
mean by more than `r` is at most the expected size of the selection divided by `r²`.
Only pairwise independence is required. -/
theorem measure_card_filter_mem_close {Ω α Q : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype α] [Finite Q]
    (S : Ω → Finset α) (p : α → Q) {r : ℝ}
    (hr : 0 < r) (hm : ∀ a, MeasurableSet {x | a ∈ S x})
    (hi : Pairwise fun a b : α ↦ IndepFun ({x | a ∈ S x}.indicator (1 : Ω → ℝ))
      ({x | b ∈ S x}.indicator (1 : Ω → ℝ)) μ) :
    1 - (∑ a, μ.real {x | a ∈ S x}) / r ^ 2 ≤ μ.real {x | ∀ q : Q,
      |((S x).filter fun a ↦ p a = q).card -
        ∑ a ∈ Finset.univ.filter (fun a ↦ p a = q), μ.real {w | a ∈ S w}| ≤ r} := by
  classical
  let _ := Fintype.ofFinite Q
  let T (q : Q) := Finset.univ.filter (fun a ↦ p a = q)
  let M (q : Q) := ∑ a ∈ T q, μ.real {x | a ∈ S x}
  let X (q : Q) (x : Ω) := (((S x).filter fun a ↦ p a = q).card : ℝ)
  have hfilter (q : Q) (x : Ω) : (T q).filter (fun a ↦ a ∈ S x) =
      (S x).filter (fun a ↦ p a = q) := by ext a; simp [T, and_comm]
  have hcount (q : Q) : X q = ∑ a ∈ T q, {x | a ∈ S x}.indicator (1 : Ω → ℝ) := by
    funext x
    simp only [Finset.sum_apply, indicator_apply, mem_ofPred_eq, Pi.one_apply, Finset.sum_boole,
      hfilter, X]
  have hm' (a : α) : Measurable ({x | a ∈ S x}.indicator (1 : Ω → ℝ)) :=
    measurable_const.indicator (hm a)
  have hmeas (q : Q) : Measurable (X q) := by
    simpa only [hcount, ← Finset.sum_apply] using Finset.measurable_sum (T q) (fun a _ ↦ hm' a)
  have hprob (q : Q) : μ.real {x | r < |X q x - M q|} ≤ M q / r ^ 2 := by
    have hLp : MemLp (X q) 2 μ := by
      rw [hcount]
      exact memLp_finsetSum' _ fun a _ ↦ (memLp_const 1).indicator (hm a).nullMeasurableSet
    obtain ⟨he, hv⟩ := integral_card_filter_mem_and_variance_le S (T q) hm hi
    simp only [hfilter] at he hv
    have he' : (∫ x, X q x ∂μ) = M q := he
    have hc := meas_ge_le_variance_div_sq hLp hr
    rw [he'] at hc
    have hnonneg : 0 ≤ Var[X q; μ] / r ^ 2 := div_nonneg (variance_nonneg _ _) (sq_nonneg r)
    have hreal : μ.real {x | r ≤ |X q x - M q|} ≤ Var[X q; μ] / r ^ 2 := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    refine (measureReal_mono (s₂ := {x | r ≤ |X q x - M q|}) ?_).trans <|
      hreal.trans (div_le_div_of_nonneg_right hv (sq_nonneg r))
    exact fun _ hx ↦ (mem_ofPred_eq.mp hx).le
  let B := ⋃ q, {x | r < |X q x - M q|}
  have hB : MeasurableSet B := MeasurableSet.iUnion fun q ↦
    measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hmeas q).sub_const _))
  have hle : μ.real B ≤ (∑ a, μ.real {x | a ∈ S x}) / r ^ 2 := calc
    _ ≤ ∑ q, μ.real {x | r < |X q x - M q|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ q, M q / r ^ 2 := Finset.sum_le_sum fun q _ ↦ hprob q
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_fiberwise Finset.univ p]
  have hgood : {x | ∀ q : Q, |X q x - M q| ≤ r} = Bᶜ := by
    ext x
    simp [B, not_lt]
  rw [hgood, measureReal_compl hB, probReal_univ]
  exact sub_le_sub_left hle _

/-- Convert the squared sampling-size condition into the corresponding bound on the total
absolute error allowed in the coset estimates. -/
private theorem coset_total_error_le {k o D ω₀ : ℝ} (hω₀ : 0 < ω₀)
    (hsize : (2 * k) ^ 2 * o ^ 2 / ω₀ ^ 2 ≤ D) :
    k * (o * (2 * Real.sqrt D)) ≤ ω₀ * D := by
  have hD : 0 ≤ D := (by positivity : 0 ≤ (2 * k) ^ 2 * o ^ 2 / ω₀ ^ 2).trans hsize
  have hsq : (2 * k * o) ^ 2 ≤ (ω₀ * Real.sqrt D) ^ 2 := by
    rw [mul_pow (2 * k), mul_pow ω₀, Real.sq_sqrt hD]
    have h := (div_le_iff₀ (by positivity : 0 < ω₀ ^ 2)).1 hsize
    simpa only [mul_comm D] using h
  have hright : 0 ≤ ω₀ * Real.sqrt D := by positivity
  have h := (le_abs_self (2 * k * o)).trans <|
    (sq_le_sq₀ (abs_nonneg _) hright).1 (by simpa only [sq_abs] using hsq)
  have hs := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg D)
  rw [mul_assoc ω₀, Real.mul_self_sqrt hD] at hs
  nlinarith only [hs]

/-- The size and relative errors follow deterministically from the absolute errors of the
individual fibre counts. -/
private theorem coset_count_bounds_of_close {Q : Type*} [Fintype Q] (c ω : Q → ℝ)
    {a D ω₀ : ℝ} (hD : 0 < D) (hω₀ : 0 < ω₀) (hω : ∀ q, ω q ∈ Icc ω₀ 1)
    (hE₀ : ω₀ * D ≤ a * ∑ j, ω j)
    (hsize : 16 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D)
    (hclose : ∀ q, |c q - a * ω q| ≤ 2 * Real.sqrt D) :
    let E := a * ∑ j, ω j
    E / 2 ≤ (∑ j, c j) ∧ (∑ j, c j) ≤ 3 * E / 2 ∧
      (36 * (Fintype.card Q : ℝ) ^ 2 / ω₀ ^ 2 ≤ D → 2 * E / 3 ≤ (∑ j, c j)) ∧
      ∀ q, |c q - (ω q / ∑ j, ω j) * ∑ j, c j| ≤
        (4 * (1 + ω₀) / ω₀ ^ 2 / Real.sqrt D) * ∑ j, c j := by
  dsimp only
  let o : ℝ := Fintype.card Q
  let W := ∑ q, ω q
  let E := a * W
  let M (q : Q) := a * ω q
  have hsum : ∑ q, M q = E := by simp [M, E, W, Finset.mul_sum]
  have hsumErr : (∑ q, |c q - M q|) ≤ o * (2 * Real.sqrt D) := by
    simpa [o, nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ hclose q
  have htot : |(∑ j, c j) - E| ≤ o * (2 * Real.sqrt D) := by
    simpa only [Finset.sum_sub_distrib, hsum] using
      (Finset.abs_sum_le_sum_abs (fun q ↦ c q - M q) Finset.univ).trans hsumErr
  have hhalf := (coset_total_error_le (k := 2) hω₀ (by norm_num; exact hsize)).trans hE₀
  have hcard₀ : E / 2 ≤ (∑ j, c j) := by linarith [(abs_le.mp htot).1]
  refine ⟨hcard₀, by linarith [(abs_le.mp htot).2], fun h ↦ ?_, fun q ↦ ?_⟩
  · have hthird := (coset_total_error_le (k := 3) hω₀ (by norm_num; exact h)).trans hE₀
    linarith [(abs_le.mp htot).1]
  · have : Nonempty Q := ⟨q⟩
    have ho : 0 < o := by dsimp [o]; exact_mod_cast Fintype.card_pos
    have hW₀ : o * ω₀ ≤ W := by
      simpa [o, W, nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ (hω q).1
    have hW : 0 < W := (mul_pos ho hω₀).trans_le hW₀
    have hν : ω q / W * E = M q := by dsimp only [E, M]; field_simp
    have hν₀ : 0 ≤ ω q / W := div_nonneg (hω₀.le.trans (hω q).1) hW.le
    have hν₁ : (ω q / W) * o ≤ 1 / ω₀ := by
      calc
        _ = ω q * o / W := by ring
        _ ≤ 1 * o / (o * ω₀) := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hω q).2 ho.le) (mul_pos ho hω₀) hW₀
        _ = _ := by field_simp
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


open scoped Classical in
/-- With equal-sized fibres and selection probability `δ * ω (p a)` for element `a`, the expected
count in fibre `q` is `δ * m * ω q`. If the expected count is large relative to the number of
fibres, with probability at least `3/4` the total is within half its expectation and every fibre
has the prescribed relative count up to the displayed precision. Under the stronger size
condition the count is at least two thirds of its expectation. -/
theorem measure_good_coset_selection {Ω α Q : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype α] [Fintype Q]
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
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · have : IsEmpty α := ⟨fun a ↦ isEmptyElim (p a)⟩
    norm_num [Finset.eq_empty_of_isEmpty, probReal_univ]
  let D := δ * Fintype.card α
  let o : ℝ := Fintype.card Q
  let W := ∑ q, ω q
  let E := δ * m * W
  let M (q : Q) := δ * m * ω q
  have ho : 0 < o := by dsimp [o]; exact_mod_cast Fintype.card_pos
  have hD : 0 < D := (by positivity : 0 < 16 * o ^ 2 / ω₀ ^ 2).trans_le hsize
  have hδ : 0 < δ := pos_of_mul_pos_left hD (by positivity)
  have hcard : Fintype.card α = Fintype.card Q * m := by
    simpa [hf, nsmul_eq_mul] using
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α) Finset.univ p).symm
  have hD' : D = δ * m * o := by simp only [D, hcard, Nat.cast_mul, o]; ring
  have hW₀ : o * ω₀ ≤ W := by
    simpa [o, W, nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ (hω q).1
  have hW₁ : W ≤ o := by
    simpa [W, o] using (Finset.sum_le_sum (s := Finset.univ) fun q _ ↦ (hω q).2)
  have hE₀ : ω₀ * D ≤ E := by
    rw [hD']; calc
      _ = (δ * m) * (o * ω₀) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hW₀ (by positivity)
  have hE₁ : E ≤ D := hD'.symm ▸ mul_le_mul_of_nonneg_left hW₁ (by positivity)
  have hM (q : Q) : ∑ a ∈ Finset.univ.filter (fun a ↦ p a = q), μ.real {x | a ∈ S x} = M q := by
    calc
      _ = ∑ _a ∈ Finset.univ.filter (fun a ↦ p a = q), δ * ω q :=
        Finset.sum_congr rfl fun a ha ↦ by rw [hprob, (Finset.mem_filter.mp ha).2]
      _ = _ := by simp only [Finset.sum_const, hf, nsmul_eq_mul, M]; ring
  have hsum : ∑ q, M q = E := by simp [M, E, W, Finset.mul_sum]
  have hmean : (∑ a, μ.real {x | a ∈ S x}) = E := by
    rw [← Finset.sum_fiberwise Finset.univ p, ← hsum]
    exact Finset.sum_congr rfl fun q _ ↦ hM q
  have hr : 0 < 2 * Real.sqrt D := by positivity
  have hg := measure_card_filter_mem_close S p hr hm hi
  have hs : (2 * Real.sqrt D) ^ 2 = 4 * D := by rw [mul_pow, Real.sq_sqrt hD.le]; norm_num
  simp only [hmean, hs, hM] at hg
  have hratio : E / (4 * D) ≤ 1 / 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
  refine (by linarith only [hratio] : 3 / 4 ≤ 1 - E / (4 * D)).trans
    (hg.trans (measureReal_mono ?_))
  intro x hx
  let c (q : Q) : ℝ := ((S x).filter fun a ↦ p a = q).card
  have hc : (∑ q, c q) = (S x).card := by
    dsimp only [c]
    exact_mod_cast (by simpa using
      Finset.sum_card_fiberwise_eq_card_filter (S x) (Finset.univ : Finset Q) p :
      (∑ q, ((S x).filter fun a ↦ p a = q).card) = (S x).card)
  simpa only [mem_ofPred_eq, hc, c, D] using
    coset_count_bounds_of_close c ω hD hω₀ hω hE₀ hsize hx

end TauCeti
