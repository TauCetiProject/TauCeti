/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled low-discrepancy recolorings

Given an initial coloring `x₀ : ι → κ` on a finite set `S` whose color frequencies are close to a
reference distribution `p₀`, and a target probability distribution `p` on the finite palette `κ`, we
construct a new coloring `x : ι → κ` agreeing with `x₀` outside `S` that simultaneously:

* matches the target color counts `p c * #(T i)` on a finite family of test subsets `T i ⊆ S`, up
  to a small probabilistic error plus the initial discrepancy of `x₀` from `p₀` on `T i`;
* recolors little more than the total-variation fraction `(∑ c, |p₀ c - p c|) / 2` of `S`.

Rather than building conditional product measures, we define the explicit optimal-coupling
transition kernel `TauCeti.couplingKernel p₀ p c₀ : κ → ℝ` from initial color `c₀` to new color `c`
and apply `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt` independently on each initial
color fiber `{e ∈ S | x₀ e = c₀}`. Keeping `min (p₀ c₀) (p c₀)` of the mass at `c₀` and routing the
excess `max 0 (p₀ c₀ - p c₀)` proportionally to `max 0 (p c - p₀ c)` pushes `p₀` forward to `p`
while retaining `min (p₀ c₀) (p c₀)` on the diagonal.

## Main definitions

* `TauCeti.couplingKernel`: transition probabilities transporting a distribution `p₀` to `p` with
  diagonal retention `min (p₀ c₀) (p c₀)`.

## Main results

* `TauCeti.couplingKernel_nonneg` and `TauCeti.sum_couplingKernel`: each row of `couplingKernel` is
  a probability distribution on `κ`.
* `TauCeti.sum_mul_couplingKernel`: `couplingKernel p₀ p` pushes `p₀` forward to `p`.
* `TauCeti.mul_couplingKernel_self`: the mass kept at color `c₀` is `min (p₀ c₀) (p c₀)`.
* `TauCeti.exists_coupled_recoloring_abs_card_filter_sub_lt`: existence of a coupled recoloring on
  `S` with bounded test-set discrepancy and edit distance controlled by total variation.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), §I.2 (maximal coupling of discrete
  distributions).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Appendix A.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*}

private theorem min_add_max_sub (a b : ℝ) : min a b + max 0 (a - b) = a := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonpos.2 h), add_zero]
  · rw [min_eq_right h, max_eq_right (sub_nonneg.2 h), add_sub_cancel]

private theorem max_sub_mul_max_sub (a b : ℝ) : max 0 (a - b) * max 0 (b - a) = 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonpos.2 h), zero_mul]
  · rw [max_eq_left (sub_nonpos.2 h), mul_zero]

private theorem max_sub_add_max_sub (a b : ℝ) : max 0 (a - b) + max 0 (b - a) = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonpos.2 h), max_eq_right (sub_nonneg.2 h), zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
  · rw [max_eq_right (sub_nonneg.2 h), max_eq_left (sub_nonpos.2 h), add_zero,
      abs_of_nonneg (sub_nonneg.2 h)]

private theorem max_sub_sub_max_sub (a b : ℝ) : max 0 (b - a) - max 0 (a - b) = b - a := by
  linarith [min_add_max_sub a b, min_add_max_sub b a, min_comm a b]

/-- For two distributions with the same total mass, the total positive excess equals the total
shortfall. -/
theorem sum_max_sub_eq [Fintype κ] {p₀ p : κ → ℝ} (hsum : ∑ c, p₀ c = ∑ c, p c) :
    ∑ c, max 0 (p₀ c - p c) = ∑ c, max 0 (p c - p₀ c) := by
  have h : ∑ c, (max 0 (p c - p₀ c) - max 0 (p₀ c - p c)) = 0 := by
    simp_rw [max_sub_sub_max_sub, sum_sub_distrib, hsum, sub_self]
  rw [sum_sub_distrib] at h
  linarith

/-- For two distributions with the same total mass, the total shortfall is half the
`L¹` distance. -/
theorem sum_max_sub_eq_half_sum_abs [Fintype κ] {p₀ p : κ → ℝ} (hsum : ∑ c, p₀ c = ∑ c, p c) :
    ∑ c, max 0 (p₀ c - p c) = (∑ c, |p₀ c - p c|) / 2 := by
  have h₁ := sum_max_sub_eq hsum
  have h₂ : ∑ c, (max 0 (p₀ c - p c) + max 0 (p c - p₀ c)) = ∑ c, |p₀ c - p c| :=
    sum_congr rfl fun c _ ↦ max_sub_add_max_sub (p₀ c) (p c)
  rw [sum_add_distrib] at h₂
  linarith

section Kernel

variable [Fintype κ]

open scoped Classical in
/-- The maximal-coupling transition kernel from a source distribution `p₀` to a target distribution
`p`: from initial color `c₀`, keep `min (p₀ c₀) (p c₀) / p₀ c₀` at `c₀` and distribute the excess
proportionally to `max 0 (p c - p₀ c)`. Degenerate rows (`p₀ c₀ = 0` or zero total variation) fall
back to `p` or the identity kernel so every row sums to `1`. -/
noncomputable def couplingKernel (p₀ p : κ → ℝ) (c₀ c : κ) : ℝ :=
  if p₀ c₀ = 0 then p c
  else if ∑ d, max 0 (p d - p₀ d) = 0 then
    if c = c₀ then 1 else 0
  else
    (if c = c₀ then min (p₀ c₀) (p c₀) else 0) / p₀ c₀ +
      max 0 (p₀ c₀ - p c₀) / p₀ c₀ * (max 0 (p c - p₀ c) / ∑ d, max 0 (p d - p₀ d))

/-- Unfolding lemma for `TauCeti.couplingKernel`. -/
theorem couplingKernel_def [DecidableEq κ] (p₀ p : κ → ℝ) (c₀ c : κ) :
    couplingKernel p₀ p c₀ c =
      if p₀ c₀ = 0 then p c
      else if ∑ d, max 0 (p d - p₀ d) = 0 then
        if c = c₀ then 1 else 0
      else
        (if c = c₀ then min (p₀ c₀) (p c₀) else 0) / p₀ c₀ +
          max 0 (p₀ c₀ - p c₀) / p₀ c₀ * (max 0 (p c - p₀ c) / ∑ d, max 0 (p d - p₀ d)) := by
  unfold couplingKernel
  congr

/-- Every entry of `couplingKernel p₀ p` is nonnegative when `p₀` and `p` are nonnegative. -/
theorem couplingKernel_nonneg {p₀ p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p₀ c) (hp : ∀ c, 0 ≤ p c)
    (c₀ c : κ) : 0 ≤ couplingKernel p₀ p c₀ c := by
  classical
  rw [couplingKernel_def]
  split_ifs with h0 htv hc
  · exact hp c
  · norm_num
  · norm_num
  · have hp₀' : 0 ≤ p₀ c₀ := hp₀ c₀
    have hmin : 0 ≤ min (p₀ c₀) (p c₀) := le_min (hp₀ c₀) (hp c₀)
    have htv' : 0 ≤ ∑ d, max 0 (p d - p₀ d) := sum_nonneg fun _ _ ↦ le_max_left 0 _
    positivity
  · have hp₀' : 0 ≤ p₀ c₀ := hp₀ c₀
    have htv' : 0 ≤ ∑ d, max 0 (p d - p₀ d) := sum_nonneg fun _ _ ↦ le_max_left 0 _
    positivity

/-- Each row of `couplingKernel p₀ p` sums to `1` whenever `p` sums to `1`. -/
theorem sum_couplingKernel {p₀ p : κ → ℝ} (hp1 : ∑ c, p c = 1) (c₀ : κ) :
    ∑ c, couplingKernel p₀ p c₀ c = 1 := by
  classical
  simp_rw [couplingKernel_def]
  by_cases h0 : p₀ c₀ = 0
  · simpa [h0] using hp1
  by_cases htv : ∑ d, max 0 (p d - p₀ d) = 0
  · simp [h0, htv]
  simp only [h0, htv, ↓reduceIte]
  simp_rw [sum_add_distrib, ← mul_sum, ← sum_div]
  simp only [sum_ite_eq', mem_univ, ↓reduceIte]
  rw [div_self htv, mul_one, ← add_div, min_add_max_sub, div_self h0]

/-- Every entry of `couplingKernel p₀ p` is at most `1` when `p₀, p ≥ 0` and `∑ c, p c = 1`. -/
theorem couplingKernel_le_one {p₀ p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p₀ c) (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (c₀ c : κ) : couplingKernel p₀ p c₀ c ≤ 1 :=
  sum_couplingKernel (p₀ := p₀) hp1 c₀ ▸
    single_le_sum (fun d _ ↦ couplingKernel_nonneg hp₀ hp c₀ d) (mem_univ c)

private theorem mul_couplingKernel_of_sum_ne_zero [DecidableEq κ] {p₀ p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (htv : ∑ d, max 0 (p d - p₀ d) ≠ 0) (c₀ c : κ) :
    p₀ c₀ * couplingKernel p₀ p c₀ c =
      (if c = c₀ then min (p₀ c₀) (p c₀) else 0) +
        max 0 (p₀ c₀ - p c₀) * (max 0 (p c - p₀ c) / ∑ d, max 0 (p d - p₀ d)) := by
  by_cases h0 : p₀ c₀ = 0
  · have hmin : min (0 : ℝ) (p c₀) = 0 := min_eq_left (hp c₀)
    have hmax : max (0 : ℝ) (0 - p c₀) = 0 := max_eq_left (by linarith [hp c₀])
    rw [h0, zero_mul, hmax, zero_mul, add_zero]
    split_ifs with hc
    · exact hmin.symm
    · rfl
  · simp only [couplingKernel_def, h0, htv, ↓reduceIte]
    rw [mul_add, mul_div_cancel₀ _ h0, ← mul_assoc, mul_div_cancel₀ _ h0]

private theorem eq_of_sum_max_sub_eq_zero {p₀ p : κ → ℝ} (hsum : ∑ c, p₀ c = ∑ c, p c)
    (htv : ∑ d, max 0 (p d - p₀ d) = 0) (c : κ) : p c = p₀ c := by
  have h₁ : max 0 (p c - p₀ c) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun _ _ ↦ le_max_left 0 _).1 htv c (mem_univ c)
  have h₂ : max 0 (p₀ c - p c) = 0 :=
    (sum_eq_zero_iff_of_nonneg fun _ _ ↦ le_max_left 0 _).1
      ((sum_max_sub_eq hsum).trans htv) c (mem_univ c)
  linarith [max_sub_sub_max_sub (p₀ c) (p c)]

/-- **Pushforward identity.** Weighting the rows of `couplingKernel p₀ p` by `p₀` recovers `p`. -/
theorem sum_mul_couplingKernel {p₀ p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, p₀ c = ∑ c, p c) (c : κ) :
    ∑ c₀, p₀ c₀ * couplingKernel p₀ p c₀ c = p c := by
  classical
  by_cases htv : ∑ d, max 0 (p d - p₀ d) = 0
  · have heq : ∀ c₀, p₀ c₀ * couplingKernel p₀ p c₀ c = if c = c₀ then p₀ c₀ else 0 := fun c₀ ↦ by
      by_cases h0 : p₀ c₀ = 0
      · split_ifs <;> simp [h0]
      · simp [couplingKernel_def, h0, htv, mul_ite]
    simp_rw [heq]
    simp [eq_of_sum_max_sub_eq_zero hsum htv c]
  · simp_rw [mul_couplingKernel_of_sum_ne_zero hp htv, sum_add_distrib, ← sum_mul]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [sum_max_sub_eq hsum, mul_div_cancel₀ _ htv, min_comm, min_add_max_sub]

/-- **Diagonal retention.** The coupled joint mass kept at color `c₀` is `min (p₀ c₀) (p c₀)`. -/
theorem mul_couplingKernel_self {p₀ p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, p₀ c = ∑ c, p c) (c₀ : κ) :
    p₀ c₀ * couplingKernel p₀ p c₀ c₀ = min (p₀ c₀) (p c₀) := by
  classical
  by_cases htv : ∑ d, max 0 (p d - p₀ d) = 0
  · have hpc := eq_of_sum_max_sub_eq_zero hsum htv c₀
    by_cases h0 : p₀ c₀ = 0
    · rw [h0, zero_mul, min_eq_left (hp c₀)]
    · simp [couplingKernel_def, h0, htv, hpc]
  · rw [mul_couplingKernel_of_sum_ne_zero hp htv]
    have hzero : max 0 (p₀ c₀ - p c₀) * (max 0 (p c₀ - p₀ c₀) / ∑ d, max 0 (p d - p₀ d)) = 0 := by
      rw [← mul_div_assoc, max_sub_mul_max_sub, zero_div]
    simp [hzero]

end Kernel

/-! ### Fiberwise coupled recoloring -/

section Recoloring

variable [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- Partition the points of `U ⊆ S` where the fiberwise recoloring hits `t c₀` by initial color. -/
private theorem card_filter_fiberwise_recolor (x₀ : ι → κ) {S U : Finset ι} (hU : U ⊆ S)
    (y : κ → ι → κ) (t : κ → κ) :
    #{e ∈ U | (if e ∈ S then y (x₀ e) e else x₀ e) = t (x₀ e)} =
      ∑ c₀, #{e ∈ {e ∈ U | x₀ e = c₀} | y c₀ e = t c₀} := by
  have hfib := sum_card_fiberwise_eq_card_filter
    ({e ∈ U | (if e ∈ S then y (x₀ e) e else x₀ e) = t (x₀ e)}) univ x₀
  rw [filter_true_of_mem fun _ _ ↦ mem_univ _] at hfib
  refine hfib.symm.trans (sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun e ↦ ?_))
  simp only [mem_filter]
  exact ⟨fun ⟨⟨he, hx⟩, hx₀⟩ ↦ ⟨⟨he, hx₀⟩, by simpa [hU he, hx₀] using hx⟩,
    fun ⟨⟨he, hx₀⟩, hy⟩ ↦ ⟨⟨he, by simpa [hU he, hx₀] using hy⟩, hx₀⟩⟩

open scoped Classical in
/-- Bound the number of points of `S` moved by a fiberwise recoloring `y` whose diagonal retention
on each color fiber `c₀` is within `b` of `couplingKernel p₀ p c₀ c₀`. -/
private theorem card_filter_fiberwise_recolor_ne_lt [Nonempty κ] (x₀ : ι → κ) (S : Finset ι)
    {p₀ p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p₀ c) (hp₀1 : ∑ c, p₀ c = 1)
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (y : κ → ι → κ) {b : ℝ}
    (hy : ∀ c₀, |(#{e ∈ {e ∈ S | x₀ e = c₀} | y c₀ e = c₀} : ℝ) -
      couplingKernel p₀ p c₀ c₀ * #{e ∈ S | x₀ e = c₀}| < b) :
    (#{e ∈ S | (if e ∈ S then y (x₀ e) e else x₀ e) ≠ x₀ e} : ℝ) <
      (∑ c₀, |p₀ c₀ - p c₀|) / 2 * #S +
        ∑ c₀, |(#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S| +
        Fintype.card κ * b := by
  have hsum : ∑ c, p₀ c = ∑ c, p c := hp₀1.trans hp1.symm
  have hstay := congrArg (Nat.cast (R := ℝ))
    (card_filter_fiberwise_recolor x₀ (subset_rfl : S ⊆ S) y id)
  rw [Nat.cast_sum] at hstay
  have hcompl : (#{e ∈ S | (if e ∈ S then y (x₀ e) e else x₀ e) ≠ x₀ e} : ℝ) =
      #S - #{e ∈ S | (if e ∈ S then y (x₀ e) e else x₀ e) = x₀ e} :=
    eq_sub_of_add_eq' (mod_cast card_filter_add_card_filter_not _)
  have hlow (c₀ : κ) : min (p₀ c₀) (p c₀) * #S -
      |(#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S| - b <
        (#{e ∈ {e ∈ S | x₀ e = c₀} | y c₀ e = c₀} : ℝ) := by
    have hker : couplingKernel p₀ p c₀ c₀ * #{e ∈ S | x₀ e = c₀} = min (p₀ c₀) (p c₀) * #S +
        couplingKernel p₀ p c₀ c₀ * ((#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S) := by
      rw [← mul_couplingKernel_self hp hsum c₀]; ring
    have hk_le : |couplingKernel p₀ p c₀ c₀ * ((#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S)| ≤
        |(#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S| := by
      rw [abs_mul, abs_of_nonneg (couplingKernel_nonneg hp₀ hp c₀ c₀)]
      exact mul_le_of_le_one_left (abs_nonneg _) (couplingKernel_le_one hp₀ hp hp1 c₀ c₀)
    linarith [(abs_lt.1 (hy c₀)).1, (abs_le.1 hk_le).1]
  have hsum_low := sum_lt_sum_of_nonempty (s := univ) univ_nonempty fun c₀ _ ↦ hlow c₀
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← sum_mul] at hsum_low
  have htot : (#S : ℝ) = (∑ c₀, min (p₀ c₀) (p c₀)) * #S + (∑ c₀, |p₀ c₀ - p c₀|) / 2 * #S := by
    rw [← sum_max_sub_eq_half_sum_abs hsum, ← add_mul, ← sum_add_distrib]
    simp_rw [min_add_max_sub, hp₀1, one_mul]
  dsimp only [id] at hstay
  linarith

/-- **Coupled low-discrepancy recoloring.** Let `x₀ : ι → κ` be an initial coloring, `S` a finite
set of size at most `N`, `p₀` and `p` probability distributions on `κ`, and `T i ⊆ S` a finite
family of test sets. If `2 * (card I + 1) * card κ * exp (-2 b² / N) < 1` for `b > 0`, then there is
a coloring `x : ι → κ` agreeing with `x₀` outside `S` such that:

* on every test set `T i` and for every color `c`, the count of `c` under `x` deviates from
  `p c * #(T i)` by less than `card κ * b` plus the `L¹` discrepancy of `x₀` from `p₀` on `T i`;
* the number of points of `S` recolored by `x` is less than the total-variation count
  `(∑ c, |p₀ c - p c|) / 2 * #S`, plus the `L¹` discrepancy of `x₀` from `p₀` on `S` and
  `card κ * b`. -/
theorem exists_coupled_recoloring_abs_card_filter_sub_lt (x₀ : ι → κ) (S : Finset ι)
    {p₀ p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p₀ c) (hp₀1 : ∑ c, p₀ c = 1)
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {I : Type*} [Fintype I] (T : I → Finset ι) (hT : ∀ i, T i ⊆ S)
    {N : ℕ} (hS : #S ≤ N) {b : ℝ} (hb : 0 < b)
    (h : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ * exp (-2 * b ^ 2 / N) < 1) :
    ∃ x : ι → κ, (∀ e ∉ S, x e = x₀ e) ∧
      (∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| <
        Fintype.card κ * b +
          ∑ c₀, |(#{e ∈ T i | x₀ e = c₀} : ℝ) - p₀ c₀ * #(T i)|) ∧
      (#{e ∈ S | x e ≠ x₀ e} : ℝ) <
        (∑ c₀, |p₀ c₀ - p c₀|) / 2 * #S +
          ∑ c₀, |(#{e ∈ S | x₀ e = c₀} : ℝ) - p₀ c₀ * #S| +
          Fintype.card κ * b := by
  classical
  have : Nonempty κ := by
    by_contra! hκ
    simp at hp1
  let F : κ → Option I → Finset ι := fun c₀ o ↦ o.casesOn {e ∈ S | x₀ e = c₀}
    fun i ↦ {e ∈ T i | x₀ e = c₀}
  have hF (c₀ : κ) (o : Option I) : #(F c₀ o) ≤ N :=
    o.casesOn ((card_filter_le _ _).trans hS)
      fun i ↦ (card_filter_le _ _).trans ((card_le_card (hT i)).trans hS)
  have hexp : 2 * Fintype.card (Option I) * Fintype.card κ * exp (-2 * b ^ 2 / N) < 1 := by
    simpa [Fintype.card_option] using h
  choose y hy using fun c₀ ↦ exists_forall_abs_card_filter_sub_mul_card_lt
    (couplingKernel_nonneg hp₀ hp c₀) (sum_couplingKernel hp1 c₀) (F c₀) (hF c₀) hb hexp
  have hsum : ∑ c, p₀ c = ∑ c, p c := hp₀1.trans hp1.symm
  refine ⟨fun e ↦ if e ∈ S then y (x₀ e) e else x₀ e, fun e he ↦ by simp [he], fun i c ↦ ?_,
    card_filter_fiberwise_recolor_ne_lt x₀ S hp₀ hp₀1 hp hp1 y fun c₀ ↦ hy c₀ none c₀⟩
  have hpart := congrArg (Nat.cast (R := ℝ))
    (card_filter_fiberwise_recolor x₀ (hT i) y fun _ ↦ c)
  rw [Nat.cast_sum] at hpart
  have hdecomp : (#{e ∈ T i | (if e ∈ S then y (x₀ e) e else x₀ e) = c} : ℝ) - p c * #(T i) =
      ∑ c₀, ((#{e ∈ F c₀ (some i) | y c₀ e = c} : ℝ) -
          couplingKernel p₀ p c₀ c * #(F c₀ (some i))) +
        ∑ c₀, couplingKernel p₀ p c₀ c * ((#{e ∈ T i | x₀ e = c₀} : ℝ) - p₀ c₀ * #(T i)) := by
    rw [hpart, ← sum_mul_couplingKernel hp hsum c, sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun c₀ _ ↦ by dsimp [F]; ring
  have h₁ : |∑ c₀, ((#{e ∈ F c₀ (some i) | y c₀ e = c} : ℝ) -
      couplingKernel p₀ p c₀ c * #(F c₀ (some i)))| < Fintype.card κ * b :=
    (abs_sum_le_sum_abs _ _).trans_lt
      ((sum_lt_sum_of_nonempty univ_nonempty fun c₀ _ ↦ hy c₀ (some i) c).trans_eq
        (by simp [sum_const, nsmul_eq_mul]))
  have h₂ : |∑ c₀, couplingKernel p₀ p c₀ c *
      ((#{e ∈ T i | x₀ e = c₀} : ℝ) - p₀ c₀ * #(T i))| ≤
        ∑ c₀, |(#{e ∈ T i | x₀ e = c₀} : ℝ) - p₀ c₀ * #(T i)| :=
    (abs_sum_le_sum_abs _ _).trans <| sum_le_sum fun c₀ _ ↦ by
      rw [abs_mul, abs_of_nonneg (couplingKernel_nonneg hp₀ hp c₀ c)]
      exact mul_le_of_le_one_left (abs_nonneg _) (couplingKernel_le_one hp₀ hp hp1 c₀ c)
  exact hdecomp ▸ (abs_add_le _ _).trans_lt (add_lt_add_of_lt_of_le h₁ h₂)

end Recoloring

end TauCeti
