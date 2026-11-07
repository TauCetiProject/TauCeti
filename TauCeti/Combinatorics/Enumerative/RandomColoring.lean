/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.SubGaussian
import TauCeti.Probability.McDiarmid

/-!
# Colorings with small discrepancy on every test set

Let `p` be a probability distribution on a finite palette `κ`, and color the points of a set `ι`
independently at random according to `p`. For a finite set `T ⊆ ι` and a color `c`, the number
of points of `T` with color `c` has mean `p c * #T`, and by Hoeffding's inequality it deviates
from its mean by at least `a` with probability at most `2 * exp (-2 a² / #T)`
(`TauCeti.measureReal_le_abs_card_filter_sub_le`). A union bound over a finite family of test
sets and over the palette therefore gives a single coloring whose color counts are within `a` of
their means on every test set, as soon as the number of tests times the palette size times
`2 * exp (-2 a² / N)` is less than one, where `N` bounds the sizes of the test sets
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`).

This is the probabilistic method for colorings of low discrepancy. It supplies quasi-random
colorings with prescribed color densities, for example colorings of the pairs between two vertex
sets in which every color has nearly the same density on every large rectangle.

## Main results

* `TauCeti.measureReal_le_abs_card_filter_sub_le`: Hoeffding's inequality for the number of
  points of a test set with a given color, under the product of a `PMF`.
* `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`: a coloring of `ι` whose color counts
  on every test set are within `a` of their means.

## Implementation notes

The color count is a function of the coloring with bounded differences: recoloring one point of
`T` changes it by at most one. McDiarmid's inequality
`TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences` therefore makes it sub-Gaussian
with variance proxy `#T / 4` under the product measure, and Mathlib's Chernoff bound
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` gives both tails. The existence statement
first restricts to the finite union of the test sets, where the product measure exists, and
extends the coloring found there by an arbitrary color.

## References

* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Theorem 13.1.1
  and Appendix A.
* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Amer.
  Statist. Assoc. 58 (1963), 13–30.
-/

public section

open Finset Real MeasureTheory

namespace TauCeti

variable {ι κ : Type*} [DecidableEq κ]

open scoped Classical in
/-- Recoloring one point changes the count of points of `T` with color `c` by at most one, and
only if the point lies in `T`. -/
private theorem abs_sum_ite_sub_sum_ite_le (T : Finset ι) (c : κ) (i : ι) (x x' : ι → κ)
    (hxx' : ∀ l, l ≠ i → x l = x' l) :
    |(∑ e ∈ T, if x e = c then (1 : ℝ) else 0) - ∑ e ∈ T, if x' e = c then (1 : ℝ) else 0| ≤
      if i ∈ T then 1 else 0 := by
  rw [← sum_sub_distrib]
  split_ifs with hi
  · rw [sum_eq_single_of_mem i hi fun e _ he ↦ by simp [hxx' e he]]
    split_ifs <;> norm_num
  · rw [sum_eq_zero fun e he ↦ by simp [hxx' e (ne_of_mem_of_not_mem he hi)], abs_zero]

open scoped Classical in
/-- The variance proxy of the bounded differences of a color count is `#T / 4`. -/
private theorem sum_toNNReal_ite_sq_div_four [Fintype ι] (T : Finset ι) :
    (((∑ e, (if e ∈ T then (1 : ℝ) else 0).toNNReal ^ 2 / 4 : NNReal)) : ℝ) = #T / 4 := by
  have h1 (e : ι) : (((if e ∈ T then (1 : ℝ) else 0).toNNReal : NNReal) : ℝ) ^ 2 =
      if e ∈ T then 1 else 0 := by
    split_ifs <;> simp
  rw [NNReal.coe_sum]
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, h1]
  rw [← sum_div, sum_ite_mem, univ_inter, sum_const, nsmul_one]

/-- **Hoeffding's inequality for a color count.** Color the points of a finite type `ι`
independently according to a `PMF` `q` on `κ`. The number of points of `T` with color `c`
deviates from its mean `q c * #T` by at least `a ≥ 0` with probability at most
`2 * exp (-2 a² / #T)`. -/
theorem measureReal_le_abs_card_filter_sub_le [Fintype ι] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (q : PMF κ) (T : Finset ι) (c : κ) {a : ℝ} (ha : 0 ≤ a) :
    (Measure.pi fun _ : ι ↦ q.toMeasure).real
        {x | a ≤ |(#{e ∈ T | x e = c} : ℝ) - (q c).toReal * #T|} ≤
      2 * exp (-2 * a ^ 2 / #T) := by
  classical
  set μ := Measure.pi fun _ : ι ↦ q.toMeasure
  have hind (e : ι) : (fun x : ι → κ ↦ if x e = c then (1 : ℝ) else 0) =
      ((Function.eval e : (ι → κ) → κ) ⁻¹' {c}).indicator 1 := by
    ext x
    simp only [Set.indicator_apply, Set.mem_preimage, Function.eval, Set.mem_singleton_iff,
      Pi.one_apply]
  have hmeas (e : ι) : MeasurableSet ((Function.eval e : (ι → κ) → κ) ⁻¹' {c}) :=
    measurable_pi_apply e (measurableSet_singleton c)
  set f : (ι → κ) → ℝ := fun x ↦ ∑ e ∈ T, if x e = c then (1 : ℝ) else 0 with hf
  have hfm : Measurable f := Finset.measurable_sum T fun e _ ↦ by
    rw [hind]
    exact measurable_one.indicator (hmeas e)
  -- Recoloring one point changes the count by at most one, and only for points of `T`.
  have hbd (i : ι) (x x' : ι → κ) (hxx' : ∀ l, l ≠ i → x l = x' l) :
      |f x - f x'| ≤ if i ∈ T then 1 else 0 := abs_sum_ite_sub_sum_ite_le T c i x x' hxx'
  have hsub := Probability.hasSubgaussianMGF_of_bounded_differences q.toMeasure f hfm _ hbd
  -- The mean of the count is `q c * #T`, and the variance proxy is `#T / 4`.
  have hmean : ∫ x, f x ∂μ = (q c).toReal * #T := by
    rw [hf, integral_finsetSum _ fun e _ ↦ by
      rw [hind]; exact (integrable_const 1).indicator (hmeas e)]
    rw [sum_congr rfl fun e _ ↦ by
      rw [hind, integral_indicator_one (hmeas e), measureReal_def,
        (measurePreserving_eval _ e).measure_preimage (measurableSet_singleton c).nullMeasurableSet,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton c)]]
    rw [sum_const, nsmul_eq_mul, mul_comm]
  have hvar := sum_toNNReal_ite_sq_div_four T
  have hexp : -a ^ 2 / (2 * (#T / 4 : ℝ)) = -2 * a ^ 2 / #T := by ring
  have h₁ := hsub.measure_ge_le ha
  have h₂ := hsub.neg.measure_ge_le ha
  rw [hmean, hvar, hexp] at h₁ h₂
  -- A deviation of at least `a` is an excess or a shortfall of at least `a`.
  calc μ.real {x | a ≤ |(#{e ∈ T | x e = c} : ℝ) - (q c).toReal * #T|}
      ≤ μ.real ({x | a ≤ f x - (q c).toReal * #T} ∪
          {x | a ≤ (-fun x ↦ f x - (q c).toReal * #T) x}) := by
        refine measureReal_mono fun x (hx : a ≤ |_|) ↦ ?_
        rw [← sum_boole] at hx
        rcases le_abs'.1 hx with h | h
        · exact Or.inr (by simp only [Pi.neg_apply, Set.mem_ofPred_eq]; linarith)
        · exact Or.inl h
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-2 * a ^ 2 / #T) := by linarith

/-- The finite case of `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`, by a union bound
under the product measure. -/
private theorem exists_forall_abs_card_filter_sub_mul_card_lt_of_finite [Fintype κ] [Finite ι]
    {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {I : Type*} [Fintype I]
    (T : I → Finset ι) {N : ℕ} (hT : ∀ i, #(T i) ≤ N) {a : ℝ} (ha : 0 < a)
    (h : 2 * Fintype.card I * Fintype.card κ * exp (-2 * a ^ 2 / N) < 1) :
    ∃ x : ι → κ, ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| < a := by
  have := Fintype.ofFinite ι
  let : MeasurableSpace κ := ⊤
  have : MeasurableSingletonClass κ := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  let q : PMF κ := PMF.ofFintype (fun k ↦ ENNReal.ofReal (p k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hp k, hp1, ENNReal.ofReal_one])
  have hq (c : κ) : (q c).toReal = p c := by simp [q, ENNReal.toReal_ofReal (hp c)]
  set μ := Measure.pi fun _ : ι ↦ q.toMeasure
  set A : I × κ → Set (ι → κ) :=
    fun ic ↦ {x | a ≤ |(#{e ∈ T ic.1 | x e = ic.2} : ℝ) - p ic.2 * #(T ic.1)|}
  -- Each bad event has probability at most `2 * exp (-2 a² / N)`.
  have hA (ic : I × κ) : μ.real (A ic) ≤ 2 * exp (-2 * a ^ 2 / N) := by
    obtain ⟨i, c⟩ := ic
    rcases (#(T i)).eq_zero_or_pos with h0 | hpos
    · have : A (i, c) = ∅ := by
        rw [card_eq_zero] at h0
        ext x
        simp [A, h0, ha.not_ge]
      rw [this, measureReal_empty]
      positivity
    have hb := measureReal_le_abs_card_filter_sub_le q (T i) c ha.le
    simp only [hq] at hb
    refine hb.trans ?_
    have hT' : (#(T i) : ℝ) ≤ N := by exact_mod_cast hT i
    have hpos' : (0 : ℝ) < #(T i) := by exact_mod_cast hpos
    rw [neg_mul, neg_div, neg_div]
    gcongr
  by_contra! hbad
  -- Every coloring lies in some bad event, so the bad events cover the whole probability space.
  have hcover : (Set.univ : Set (ι → κ)) ⊆ ⋃ ic, A ic := fun x _ ↦ by
    obtain ⟨i, c, hic⟩ := hbad x
    exact Set.mem_iUnion.2 ⟨(i, c), hic⟩
  refine h.not_ge ?_
  calc 1 = μ.real Set.univ := probReal_univ.symm
    _ ≤ μ.real (⋃ ic, A ic) := measureReal_mono hcover
    _ ≤ ∑ ic, μ.real (A ic) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ _ic : I × κ, 2 * exp (-2 * a ^ 2 / N) := sum_le_sum fun ic _ ↦ hA ic
    _ = 2 * Fintype.card I * Fintype.card κ * exp (-2 * a ^ 2 / N) := by
        simp only [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring

/-- **Colorings with small discrepancy.** Let `p` be a probability distribution on a finite
palette `κ` and `T i ⊆ ι`, for `i` in a finite index type `I`, test sets of size at most `N`.
If `2 * card I * card κ * exp (-2 a² / N) < 1` for some `a > 0`, then some coloring `x : ι → κ`
has, on every test set `T i` and for every color `c`, a number of points of color `c` within
`a` of `p c * #(T i)`. -/
theorem exists_forall_abs_card_filter_sub_mul_card_lt [Fintype κ] {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {I : Type*} [Fintype I] (T : I → Finset ι) {N : ℕ}
    (hT : ∀ i, #(T i) ≤ N) {a : ℝ} (ha : 0 < a)
    (h : 2 * Fintype.card I * Fintype.card κ * exp (-2 * a ^ 2 / N) < 1) :
    ∃ x : ι → κ, ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| < a := by
  classical
  have : Nonempty κ := by
    by_contra! hκ
    simp at hp1
  -- Color the finite union `U` of the test sets, and give every other point an arbitrary color.
  set U := univ.biUnion T
  have hU {i : I} {e : ι} (he : e ∈ T i) : e ∈ U := mem_biUnion.2 ⟨i, mem_univ i, he⟩
  obtain ⟨y, hy⟩ := exists_forall_abs_card_filter_sub_mul_card_lt_of_finite hp hp1
    (fun i ↦ (T i).subtype (· ∈ U)) (fun i ↦ (card_subtype _ _).trans_le
      ((card_filter_le _ _).trans (hT i))) ha h
  refine ⟨fun e ↦ if he : e ∈ U then y ⟨e, he⟩ else Classical.arbitrary κ, fun i c ↦ ?_⟩
  have hcard : #((T i).subtype (· ∈ U)) = #(T i) := by
    rw [card_subtype, filter_true_of_mem fun e he ↦ hU he]
  have hcount : #{e ∈ T i | (if he : e ∈ U then y ⟨e, he⟩ else Classical.arbitrary κ) = c} =
      #{e ∈ (T i).subtype (· ∈ U) | y e = c} := by
    refine (card_bij (fun e _ ↦ e.1) (fun e he ↦ ?_) (fun _ _ _ _ ↦ Subtype.ext)
      fun e he ↦ ?_).symm
    · obtain ⟨he, hc⟩ := mem_filter.1 he
      exact mem_filter.2 ⟨mem_subtype.1 he, by simpa [e.2] using hc⟩
    · obtain ⟨he, hc⟩ := mem_filter.1 he
      exact ⟨⟨e, hU he⟩, mem_filter.2 ⟨mem_subtype.2 he, by simpa [hU he] using hc⟩, rfl⟩
  simpa [hcount, hcard] using hy i c

end TauCeti
