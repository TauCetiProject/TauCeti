/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import TauCeti.Combinatorics.Enumerative.RandomColoring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coupled random recolorings with prescribed target densities

Given an initial coloring `x₀ : ι → κ` of a finite ground set `E` and a target probability
distribution `p` on the finite palette `κ`, one often wants a new coloring `x` whose color counts
on a family of test subsets `T i ⊆ E` match `p c * #(T i)`, while editing as few points of `E` as
possible. An independent random coloring achieves the target counts on all test sets, but disagrees
with `x₀` even when `x₀` already has the target color frequencies on `E`.

This file constructs `x` by pushing `x₀` through an optimal Markov transition coupling `M` from the
empirical color distribution `q` of `x₀` on `E` to `p`: colors with `q c₀ ≤ p c₀` are left
untouched (`M c₀ c₀ = 1`), while surplus colors (`p c₀ < q c₀`) retain color `c₀` with probability
`p c₀ / q c₀` and redistribute their excess `q c₀ - p c₀` proportionally to the deficits
`max 0 (p c - q c)`. Applying the discrepancy bound for independent colorings
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`) separately to each color fiber of `x₀`
yields a coloring `x` agreeing with `x₀` outside `E` such that:

* the number of edited points on `E` is within `a` of the total-variation coupling cost
  `(∑ c, |#{e ∈ E | x₀ e = c} - p c * #E|) / 2`, and
* on every test set `T i`, the count of each color `c` under `x` is within `a` of the pushed-forward
  empirical count `∑ c₀, M c₀ c * #{e ∈ T i | x₀ e = c₀}`; in particular, whenever `x₀` is already
  regular on `T i` (within `b` of its empirical frequencies on `E`), `x` has counts within
  `card κ * b + a` of `p c * #(T i)`.

## Main results

* `TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt`: existence of a coupled recoloring and
  Markov transition matrix controlling both edit distance on `E` and test-set counts.
* `TauCeti.exists_coupled_coloring_abs_card_filter_sub_mul_card_le`: direct form transferring
  empirical regularity of `x₀` on a test set `T i` to target-density regularity of `x`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), §4 (slicing and density adjustment in regular approximation).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Appendix A.
-/

public section

open Finset Real

namespace TauCeti

section CouplingKernel

variable {κ : Type*} [Fintype κ]

/-- Half the `ℓ¹` distance between two distributions `q` and `p` with equal total mass, written as
the total deficit `∑ c, max 0 (p c - q c)`. -/
private noncomputable def totalVariationHalf (q p : κ → ℝ) : ℝ :=
  ∑ c, max 0 (p c - q c)

private theorem totalVariationHalf_nonneg (q p : κ → ℝ) : 0 ≤ totalVariationHalf q p :=
  sum_nonneg fun _ _ ↦ le_max_left 0 _

private theorem sum_max_sub_eq_totalVariationHalf {q p : κ → ℝ} (hsum : ∑ c, q c = ∑ c, p c) :
    ∑ c, max 0 (q c - p c) = totalVariationHalf q p := by
  have hpt (c : κ) : max 0 (q c - p c) - max 0 (p c - q c) = q c - p c := by
    rcases le_total (q c) (p c) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have hdiff : ∑ c, max 0 (q c - p c) - totalVariationHalf q p = ∑ c, q c - ∑ c, p c := by
    rw [totalVariationHalf, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun c _ ↦ hpt c
  linarith

private theorem two_mul_totalVariationHalf {q p : κ → ℝ} (hsum : ∑ c, q c = ∑ c, p c) :
    2 * totalVariationHalf q p = ∑ c, |q c - p c| := by
  have hpt (c : κ) : max 0 (q c - p c) + max 0 (p c - q c) = |q c - p c| := by
    rcases le_total (q c) (p c) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonneg (by linarith)]
      ring
  calc 2 * totalVariationHalf q p
      = ∑ c, max 0 (q c - p c) + ∑ c, max 0 (p c - q c) := by
          rw [sum_max_sub_eq_totalVariationHalf hsum, totalVariationHalf]
          ring
    _ = ∑ c, (max 0 (q c - p c) + max 0 (p c - q c)) := sum_add_distrib.symm
    _ = ∑ c, |q c - p c| := sum_congr rfl fun c _ ↦ hpt c

variable [DecidableEq κ]

/-- Optimal Markov transition matrix pushing `q` to `p`: non-surplus colors stay put, while surplus
colors retain `p c₀ / q c₀` of their mass and send the excess proportionally to `max 0 (p c - q c)`.
-/
private noncomputable def transitionCoupling (q p : κ → ℝ) (c₀ c : κ) : ℝ :=
  if q c₀ ≤ p c₀ then
    if c = c₀ then 1 else 0
  else if c = c₀ then
    p c₀ / q c₀
  else
    ((q c₀ - p c₀) / q c₀) * (max 0 (p c - q c) / totalVariationHalf q p)

private theorem transitionCoupling_nonneg {q p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (c₀ c : κ) :
    0 ≤ transitionCoupling q p c₀ c := by
  unfold transitionCoupling
  split_ifs with hqp hcc
  · norm_num
  · norm_num
  · exact div_nonneg (hp c₀) (by linarith [hp c₀])
  · have hq₀ : 0 < q c₀ := by linarith [hp c₀]
    have hsub : 0 ≤ q c₀ - p c₀ := by linarith
    exact mul_nonneg (div_nonneg hsub hq₀.le)
      (div_nonneg (le_max_left 0 _) (totalVariationHalf_nonneg q p))

private theorem sum_transitionCoupling {q p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, q c = ∑ c, p c) (c₀ : κ) :
    ∑ c, transitionCoupling q p c₀ c = 1 := by
  by_cases hqp : q c₀ ≤ p c₀
  · simp [transitionCoupling, hqp]
  push Not at hqp
  have hq₀ : 0 < q c₀ := by linarith [hp c₀]
  have hΔ : 0 < totalVariationHalf q p := by
    rw [← sum_max_sub_eq_totalVariationHalf hsum]
    refine lt_of_lt_of_le (by linarith [le_max_right 0 (q c₀ - p c₀)] : 0 < max 0 (q c₀ - p c₀)) ?_
    exact single_le_sum (f := fun c ↦ max (0 : ℝ) (q c - p c))
      (fun _ _ ↦ le_max_left 0 _) (mem_univ c₀)
  have hterm (c : κ) : transitionCoupling q p c₀ c =
      (if c = c₀ then p c₀ / q c₀ else 0) +
        ((q c₀ - p c₀) / q c₀) * (max 0 (p c - q c) / totalVariationHalf q p) := by
    by_cases hc : c = c₀
    · subst hc
      simp [transitionCoupling, hqp.not_ge, sub_nonpos.2 hqp.le]
    · simp [transitionCoupling, hqp.not_ge, hc]
  have hdef : ∑ c, max 0 (p c - q c) = totalVariationHalf q p := rfl
  simp only [hterm, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, ← mul_sum, ← sum_div, hdef]
  rw [div_self hΔ.ne', mul_one, ← add_div, add_sub_cancel, div_self hq₀.ne']

private theorem sum_mul_transitionCoupling {q p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hsum : ∑ c, q c = ∑ c, p c) (c : κ) :
    ∑ c₀, q c₀ * transitionCoupling q p c₀ c = p c := by
  by_cases hpc : p c < q c
  · have hqc : 0 < q c := by linarith [hp c]
    rw [sum_eq_single c]
    · simp [transitionCoupling, hpc.not_ge, mul_div_cancel₀ _ hqc.ne']
    · intro c₀ _ hc₀
      by_cases hqp : q c₀ ≤ p c₀ <;>
        simp [transitionCoupling, hqp, hc₀.symm, sub_nonpos.2 hpc.le]
    · exact fun hc ↦ absurd (mem_univ c) hc
  push Not at hpc
  by_cases hΔ : totalVariationHalf q p = 0
  · have hle (c₀ : κ) : q c₀ ≤ p c₀ := by
      have hmax : max 0 (q c₀ - p c₀) ≤ 0 :=
        (single_le_sum (f := fun c' ↦ max (0 : ℝ) (q c' - p c'))
          (fun _ _ ↦ le_max_left 0 _) (mem_univ c₀)).trans_eq
          ((sum_max_sub_eq_totalVariationHalf hsum).trans hΔ)
      linarith [le_max_right 0 (q c₀ - p c₀)]
    have hpq : p c ≤ q c := by
      have hmax : max 0 (p c - q c) ≤ 0 :=
        (single_le_sum (f := fun c' ↦ max (0 : ℝ) (p c' - q c'))
          (fun _ _ ↦ le_max_left 0 _) (mem_univ c)).trans_eq hΔ
      linarith [le_max_right 0 (p c - q c)]
    simp [transitionCoupling, hle, le_antisymm hpc hpq]
  · have hΔpos : 0 < totalVariationHalf q p :=
      lt_of_le_of_ne (totalVariationHalf_nonneg q p) (Ne.symm hΔ)
    have hterm (c₀ : κ) : q c₀ * transitionCoupling q p c₀ c =
        (if c = c₀ then q c else 0) +
          max 0 (q c₀ - p c₀) * ((p c - q c) / totalVariationHalf q p) := by
      by_cases hqp : q c₀ ≤ p c₀
      · rw [max_eq_left (sub_nonpos.2 hqp), zero_mul, add_zero]
        by_cases hcc : c = c₀ <;> simp [transitionCoupling, hqp, hcc]
      · push Not at hqp
        have hq₀ : 0 < q c₀ := by linarith [hp c₀]
        have hcc : c ≠ c₀ := fun h ↦ by subst h; linarith
        rw [max_eq_right (sub_nonneg.2 hqp.le)]
        simp only [transitionCoupling, hqp.not_ge, ↓reduceIte, hcc, zero_add,
          max_eq_right (sub_nonneg.2 hpc)]
        field_simp
    simp_rw [hterm, sum_add_distrib]
    simp [← sum_mul, sum_max_sub_eq_totalVariationHalf hsum, mul_div_cancel₀ _ hΔpos.ne']

private theorem mul_one_sub_transitionCoupling_self {q p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (c₀ : κ) :
    q c₀ * (1 - transitionCoupling q p c₀ c₀) = max 0 (q c₀ - p c₀) := by
  by_cases hqp : q c₀ ≤ p c₀
  · rw [max_eq_left (sub_nonpos.2 hqp)]
    simp [transitionCoupling, hqp]
  · push Not at hqp
    have hq₀ : 0 < q c₀ := by linarith [hp c₀]
    rw [max_eq_right (sub_nonneg.2 hqp.le)]
    simp only [transitionCoupling, hqp.not_ge, ↓reduceIte]
    field_simp

end CouplingKernel

section Glue

variable {ι κ : Type*} [DecidableEq κ]

open Classical in
/-- Reassemble fiberwise recolorings `y c₀` on `E` according to the initial color `x₀ e`, keeping
`x₀` outside `E`. -/
private noncomputable def glueColoring (E : Finset ι) (x₀ : ι → κ) (y : κ → ι → κ) (e : ι) : κ :=
  if e ∈ E then y (x₀ e) e else x₀ e

private theorem card_filter_glueColoring_eq_sum [Fintype κ] (E : Finset ι) (x₀ : ι → κ)
    (y : κ → ι → κ) {S : Finset ι} (hSE : S ⊆ E) (c : κ) :
    #{e ∈ S | glueColoring E x₀ y e = c} =
      ∑ c₀ : κ, #{e ∈ S.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c} := by
  classical
  rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) (fun _ _ ↦ mem_univ _)]
  refine sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun e ↦ ?_)
  simp only [mem_filter]
  exact ⟨fun ⟨⟨heS, hglue⟩, hx₀⟩ ↦ ⟨⟨heS, hx₀⟩, by simpa [glueColoring, hSE heS, hx₀] using hglue⟩,
    fun ⟨⟨heS, hx₀⟩, hy⟩ ↦ ⟨⟨heS, by simpa [glueColoring, hSE heS, hx₀] using hy⟩, hx₀⟩⟩

private theorem card_filter_glueColoring_ne_eq_sum [Fintype κ] (E : Finset ι) (x₀ : ι → κ)
    (y : κ → ι → κ) :
    (#{e ∈ E | glueColoring E x₀ y e ≠ x₀ e} : ℝ) =
      ∑ c₀ : κ, ((#{e ∈ E | x₀ e = c₀} : ℝ) -
        #{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c₀}) := by
  classical
  have hpart : #{e ∈ E | glueColoring E x₀ y e ≠ x₀ e} =
      ∑ c₀ : κ, #{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e ≠ c₀} := by
    rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun e ↦ ?_)
    simp only [mem_filter]
    exact ⟨fun ⟨⟨heE, hne⟩, hx₀⟩ ↦ ⟨⟨heE, hx₀⟩, by simpa [glueColoring, heE, hx₀] using hne⟩,
      fun ⟨⟨heE, hx₀⟩, hne⟩ ↦ ⟨⟨heE, by simpa [glueColoring, heE, hx₀] using hne⟩, hx₀⟩⟩
  rw [hpart, Nat.cast_sum]
  refine sum_congr rfl fun c₀ _ ↦ ?_
  have hadd : (#{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c₀} : ℝ) +
      #{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e ≠ c₀} = #{e ∈ E | x₀ e = c₀} := by
    exact_mod_cast card_filter_add_card_filter_not
      (s := E.filter fun e ↦ x₀ e = c₀) (p := fun e ↦ y c₀ e = c₀)
  linarith

end Glue

section Main

variable {ι κ : Type*} [Fintype κ]

private theorem nonempty_of_coupled_union_bound [Nonempty κ] {E : Finset ι} {I : Type*} [Fintype I]
    {a : ℝ} (h : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (a / Fintype.card κ) ^ 2 / #E) < 1) : E.Nonempty := by
  by_contra! hempty
  rw [hempty, card_empty, Nat.cast_zero, div_zero, exp_zero, mul_one] at h
  have hI1 : (1 : ℝ) ≤ (Fintype.card I + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
  nlinarith

variable [DecidableEq κ]

/-- Sum the fiberwise edit bounds for `glueColoring` into the half-`ℓ¹` coupling cost plus `a`. -/
private theorem card_filter_glueColoring_ne_le {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) {E : Finset ι} (hE : E.Nonempty) (x₀ : ι → κ) (y : κ → ι → κ)
    {a : ℝ} (hfib : ∀ c₀,
      |(#{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c₀} : ℝ) -
        transitionCoupling (fun c ↦ (#{e ∈ E | x₀ e = c} : ℝ) / #E) p c₀ c₀ *
          #{e ∈ E | x₀ e = c₀}| < a / Fintype.card κ) :
    (#{e ∈ E | glueColoring E x₀ y e ≠ x₀ e} : ℝ) ≤
      (∑ c, |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E|) / 2 + a := by
  have hκ : Nonempty κ := by by_contra! he; simp at hp1
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hEpos : (0 : ℝ) < #E := Nat.cast_pos.2 hE.card_pos
  let q : κ → ℝ := fun c ↦ (#{e ∈ E | x₀ e = c} : ℝ) / #E
  have hqsum : ∑ c, q c = 1 := by
    simp only [q, ← sum_div]
    have hcard : ∑ c : κ, #{e ∈ E | x₀ e = c} = #E :=
      (card_eq_sum_card_fiberwise (f := x₀) (t := univ) (fun _ _ ↦ mem_univ _)).symm
    rw [← Nat.cast_sum, hcard, div_self hEpos.ne']
  have hsum : ∑ c, q c = ∑ c, p c := hqsum.trans hp1.symm
  have hstep (c₀ : κ) : (#{e ∈ E | x₀ e = c₀} : ℝ) -
      #{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c₀} ≤
      max 0 (q c₀ - p c₀) * #E + a / Fintype.card κ := by
    have hnone := (abs_lt.1 (hfib c₀)).1
    have hid := congrArg (· * (#E : ℝ)) (mul_one_sub_transitionCoupling_self (q := q) hp c₀)
    have hqE : q c₀ * #E = #{e ∈ E | x₀ e = c₀} := div_mul_cancel₀ _ hEpos.ne'
    have hlin : q c₀ * (1 - transitionCoupling q p c₀ c₀) * #E =
        (#{e ∈ E | x₀ e = c₀} : ℝ) -
          transitionCoupling q p c₀ c₀ * #{e ∈ E | x₀ e = c₀} := by
      calc q c₀ * (1 - transitionCoupling q p c₀ c₀) * #E
          = (1 - transitionCoupling q p c₀ c₀) * (q c₀ * #E) := by ring
        _ = _ := by rw [hqE]; ring
    linarith
  rw [card_filter_glueColoring_ne_eq_sum]
  calc ∑ c₀ : κ, ((#{e ∈ E | x₀ e = c₀} : ℝ) -
          #{e ∈ E.filter (fun e ↦ x₀ e = c₀) | y c₀ e = c₀})
      ≤ ∑ c₀ : κ, (max 0 (q c₀ - p c₀) * #E + a / Fintype.card κ) :=
        sum_le_sum fun c₀ _ ↦ hstep c₀
    _ = totalVariationHalf q p * #E + a := by
        rw [sum_add_distrib, ← sum_mul, sum_max_sub_eq_totalVariationHalf hsum, sum_const,
          card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hKpos.ne']
    _ = (∑ c, |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E|) / 2 + a := by
        have htvE := congrArg (· * (#E : ℝ)) (two_mul_totalVariationHalf hsum)
        have habs : (∑ c, |q c - p c|) * #E =
            ∑ c, |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E| := by
          rw [sum_mul]
          refine sum_congr rfl fun c _ ↦ ?_
          calc |q c - p c| * #E = |(q c - p c) * #E| := by rw [abs_mul, abs_of_pos hEpos]
            _ = |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E| := by
                rw [sub_mul, div_mul_cancel₀ _ hEpos.ne']
        linarith

/-- **Coupled random recoloring.** Let `p` be a probability distribution on a finite palette `κ`,
`x₀ : ι → κ` an initial coloring on a finite ground set `E`, and `T : I → Finset ι` a finite family
of test subsets `T i ⊆ E`. If `2 * (card I + 1) * card κ * exp (-2 * (a / card κ)² / #E) < 1` for
`a > 0`, there exist a coloring `x : ι → κ` agreeing with `x₀` outside `E` and a Markov transition
matrix `M : κ → κ → ℝ` pushing the empirical counts of `x₀` on `E` to `p · #E`, such that at most
`(∑ c, |#{e ∈ E | x₀ e = c} - p c * #E|) / 2 + a` points of `E` are recolored and every test count
`#{e ∈ T i | x e = c}` is within `a` of `∑ c₀, M c₀ c * #{e ∈ T i | x₀ e = c₀}`. -/
theorem exists_coupled_coloring_abs_card_filter_sub_lt {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (E : Finset ι) (x₀ : ι → κ) {I : Type*} [Fintype I]
    (T : I → Finset ι) (hT : ∀ i, T i ⊆ E) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (a / Fintype.card κ) ^ 2 / #E) < 1) :
    ∃ (x : ι → κ) (M : κ → κ → ℝ),
      (∀ e ∉ E, x e = x₀ e) ∧
      (∀ c₀ c, 0 ≤ M c₀ c) ∧
      (∀ c₀, ∑ c, M c₀ c = 1) ∧
      (∀ c, ∑ c₀, (#{e ∈ E | x₀ e = c₀} : ℝ) * M c₀ c = p c * #E) ∧
      (#{e ∈ E | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E|) / 2 + a ∧
      ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) -
        ∑ c₀, M c₀ c * #{e ∈ T i | x₀ e = c₀}| < a := by
  classical
  have hκ : Nonempty κ := by by_contra! he; simp at hp1
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hE : E.Nonempty := nonempty_of_coupled_union_bound h
  have hEpos : (0 : ℝ) < #E := Nat.cast_pos.2 hE.card_pos
  let q : κ → ℝ := fun c ↦ (#{e ∈ E | x₀ e = c} : ℝ) / #E
  have hsum : ∑ c, q c = ∑ c, p c := by
    have hcard : ∑ c : κ, #{e ∈ E | x₀ e = c} = #E :=
      (card_eq_sum_card_fiberwise (f := x₀) (t := univ) (fun _ _ ↦ mem_univ _)).symm
    rw [hp1, ← sum_div, ← Nat.cast_sum, hcard, div_self hEpos.ne']
  -- Sample a low-discrepancy coloring on each `x₀`-color fiber against all test intersections.
  let TFiber (c₀ : κ) : Option I → Finset ι := fun o ↦
    o.elim {e ∈ E | x₀ e = c₀} fun i ↦ {e ∈ T i | x₀ e = c₀}
  have hTFiber (c₀ : κ) (o : Option I) : #(TFiber c₀ o) ≤ #E :=
    o.casesOn (card_filter_le _ _) fun i ↦ (card_filter_le _ _).trans (card_le_card (hT i))
  have hexists (c₀ : κ) : ∃ yc : ι → κ, ∀ (o : Option I) (c : κ),
      |(#{e ∈ TFiber c₀ o | yc e = c} : ℝ) - transitionCoupling q p c₀ c * #(TFiber c₀ o)| <
        a / Fintype.card κ :=
    exists_forall_abs_card_filter_sub_mul_card_lt (transitionCoupling_nonneg hp c₀)
      (sum_transitionCoupling hp hsum c₀) (TFiber c₀) (hTFiber c₀) (div_pos ha hKpos)
      (by simpa [Fintype.card_option] using h)
  choose y hy using hexists
  refine ⟨glueColoring E x₀ y, transitionCoupling q p, fun e he ↦ by simp [glueColoring, he],
    transitionCoupling_nonneg hp, fun c₀ ↦ sum_transitionCoupling hp hsum c₀, fun c ↦ ?_,
    card_filter_glueColoring_ne_le hp hp1 hE x₀ y (fun c₀ ↦ hy c₀ none c₀), fun i c ↦ ?_⟩
  · have hmul := congrArg (· * (#E : ℝ)) (sum_mul_transitionCoupling hp hsum c)
    rw [sum_mul] at hmul
    exact (sum_congr rfl fun c₀ _ ↦ by simp only [q]; field_simp).trans hmul
  · rw [card_filter_glueColoring_eq_sum E x₀ y (hT i) c, Nat.cast_sum, ← sum_sub_distrib]
    calc |∑ c₀ : κ, ((#{e ∈ (T i).filter (fun e ↦ x₀ e = c₀) | y c₀ e = c} : ℝ) -
            transitionCoupling q p c₀ c * #{e ∈ T i | x₀ e = c₀})|
        ≤ ∑ c₀ : κ, |(#{e ∈ TFiber c₀ (some i) | y c₀ e = c} : ℝ) -
            transitionCoupling q p c₀ c * #(TFiber c₀ (some i))| := abs_sum_le_sum_abs _ _
      _ < ∑ _c₀ : κ, a / Fintype.card κ :=
          sum_lt_sum_of_nonempty univ_nonempty fun c₀ _ ↦ hy c₀ (some i) c
      _ = a := by rw [sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hKpos.ne']

/-- **Coupled random recoloring preserving test regularity.** Under the hypotheses of
`TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt`, the coupled recoloring `x` edits at most
`(∑ c, |#{e ∈ E | x₀ e = c} - p c * #E|) / 2 + a` points of `E`, and on any test set `T i` where
every initial color count is within `b` of its empirical expectation on `E`, every color count of
`x` on `T i` is within `card κ * b + a` of `p c * #(T i)`. -/
theorem exists_coupled_coloring_abs_card_filter_sub_mul_card_le {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) (E : Finset ι) (x₀ : ι → κ) {I : Type*} [Fintype I]
    (T : I → Finset ι) (hT : ∀ i, T i ⊆ E) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (a / Fintype.card κ) ^ 2 / #E) < 1) :
    ∃ x : ι → κ,
      (∀ e ∉ E, x e = x₀ e) ∧
      (#{e ∈ E | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ E | x₀ e = c} : ℝ) - p c * #E|) / 2 + a ∧
      ∀ (i : I) {b : ℝ},
        (∀ c₀, |(#{e ∈ T i | x₀ e = c₀} : ℝ) -
          ((#{e ∈ E | x₀ e = c₀} : ℝ) / #E) * #(T i)| ≤ b) →
        ∀ c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| ≤ Fintype.card κ * b + a := by
  obtain ⟨x, M, hout, hM₀, hM₁, hMstat, hedit, htest⟩ :=
    exists_coupled_coloring_abs_card_filter_sub_lt hp hp1 E x₀ T hT ha h
  refine ⟨x, hout, hedit, fun i {b} hb c ↦ ?_⟩
  have hκ : Nonempty κ := by by_contra! he; simp at hp1
  have hMle (c₀ : κ) : M c₀ c ≤ 1 :=
    hM₁ c₀ ▸ single_le_sum (fun c' _ ↦ hM₀ c₀ c') (mem_univ c)
  have hEpos : (0 : ℝ) < #E := Nat.cast_pos.2 (nonempty_of_coupled_union_bound h).card_pos
  have hpT : ∑ c₀ : κ, M c₀ c * (((#{e ∈ E | x₀ e = c₀} : ℝ) / #E) * #(T i)) =
      p c * #(T i) := by
    calc ∑ c₀ : κ, M c₀ c * (((#{e ∈ E | x₀ e = c₀} : ℝ) / #E) * #(T i))
        = (∑ c₀ : κ, (#{e ∈ E | x₀ e = c₀} : ℝ) * M c₀ c) / #E * #(T i) := by
            rw [sum_div, sum_mul]
            refine sum_congr rfl fun c₀ _ ↦ by ring
      _ = p c * #(T i) := by rw [hMstat c, mul_div_cancel_right₀ _ hEpos.ne']
  have hpush : |(∑ c₀ : κ, M c₀ c * (#{e ∈ T i | x₀ e = c₀} : ℝ)) - p c * #(T i)| ≤
      Fintype.card κ * b := by
    rw [← hpT, ← sum_sub_distrib]
    calc |∑ c₀ : κ, (M c₀ c * (#{e ∈ T i | x₀ e = c₀} : ℝ) -
            M c₀ c * (((#{e ∈ E | x₀ e = c₀} : ℝ) / #E) * #(T i)))|
        ≤ ∑ c₀ : κ, |M c₀ c * ((#{e ∈ T i | x₀ e = c₀} : ℝ) -
            ((#{e ∈ E | x₀ e = c₀} : ℝ) / #E) * #(T i))| :=
            (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun _ _ ↦ by rw [← mul_sub])
      _ ≤ ∑ _c₀ : κ, b := sum_le_sum fun c₀ _ ↦ by
            rw [abs_mul, abs_of_nonneg (hM₀ c₀ c)]
            exact (mul_le_mul (hMle c₀) (hb c₀) (abs_nonneg _) zero_le_one).trans_eq (one_mul b)
      _ = Fintype.card κ * b := by rw [sum_const, card_univ, nsmul_eq_mul]
  exact (abs_sub_le _ (∑ c₀ : κ, M c₀ c * #{e ∈ T i | x₀ e = c₀}) _).trans
    (by linarith [htest i c])

end Main

end TauCeti
