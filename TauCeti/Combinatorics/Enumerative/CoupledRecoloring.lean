/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Probability.MaximalCoupling

/-!
# Coupled recolorings with small discrepancy and few edits

Let `x₀ : ι → κ` be a coloring of a finite set `Ω` whose color classes already have small
discrepancy on a finite family of test sets `T i ⊆ Ω`, and let `p` be a target probability
distribution on `κ`. Resampling all of `Ω` independently from `p` approximates the target color
counts `p c * #(T i)` within a prescribed discrepancy bound on every test set
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`), but may recolor a constant fraction
of `Ω` even when the empirical distribution `q` of `x₀` on `Ω` is already close to `p`.

This file constructs a coupled recoloring that edits at most half the `ℓ¹` distance between the
empirical counts and `p · #Ω`, up to an additive `card κ * a` error, while approximating the
target counts `p c * #(T i)` within the error bound `card κ * (a + b)` on every test set:

* Let `q c = #{e ∈ Ω | x₀ e = c} / #Ω` be the empirical distribution of `x₀` on `Ω`, and let
  `M : κ → κ → ℝ` be a maximal coupling transition kernel pushing `q` forward to `p`
  (`TauCeti.exists_sum_eq_one_and_sum_mul_eq_and_min_le_mul`), so
  `min (q c₀) (p c₀) ≤ q c₀ * M c₀ c₀` for every `c₀`.
* On each source color class `Ω_{c₀}`, apply `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`
  with distribution `M c₀` to the restricted test sets `T i ∩ Ω_{c₀}` together with `Ω_{c₀}` itself.

Gluing the fiberwise recolorings yields a deterministic coloring `x` agreeing with `x₀` outside `Ω`
that keeps at least `∑ c₀, (min (q c₀) (p c₀) * #Ω - a)` points unchanged—hence edits at most
`(∑ c, |#{e ∈ Ω | x₀ e = c} - p c * #Ω|) / 2 + card κ * a` points by
`Finset.sub_sum_min_eq_sum_abs_div_two`—and whose color counts on every `T i` lie within
`card κ * (a + b)` of `p c * #(T i)` (`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`).

## Main results

* `TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`: coupled low-discrepancy recoloring
  toward a target distribution with total-variation edit bound.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.2 (coupled edge-modification in strong regularity).
* T. Lindvall, *Lectures on the Coupling Method*, Dover (2002), Chapter I, Theorem 5.2 (maximal
  coupling of discrete distributions).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 (regular approximation via coupled recoloring).
-/

public section

open Finset Real

namespace TauCeti

/-- Low-discrepancy recoloring on a single fiber `{e ∈ Ω | x₀ e = c₀}` with distribution `μ`,
simultaneously controlling the stay-put count on the fiber and all restricted test sets `T i`. -/
private theorem exists_fiber_recoloring_abs_card_filter_sub_lt {ι κ I : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype I] (Ω : Finset ι) (x₀ : ι → κ) (c₀ : κ)
    {μ : κ → ℝ} (hμ₀ : ∀ c, 0 ≤ μ c) (hμ₁ : ∑ c, μ c = 1)
    (T : I → Finset ι) (hT : ∀ i, T i ⊆ Ω) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #Ω) < 1) :
    ∃ y : ι → κ,
      |(#{e ∈ Ω | x₀ e = c₀ ∧ y e = c₀} : ℝ) - μ c₀ * #{e ∈ Ω | x₀ e = c₀}| < a ∧
      ∀ i d, |(#{e ∈ T i | x₀ e = c₀ ∧ y e = d} : ℝ) - μ d * #{e ∈ T i | x₀ e = c₀}| < a := by
  let S : Option I → Finset ι :=
    fun o ↦ o.elim {e ∈ Ω | x₀ e = c₀} fun i ↦ {e ∈ T i | x₀ e = c₀}
  have hS (o : Option I) : #(S o) ≤ #Ω := by
    cases o with
    | none => exact card_filter_le _ _
    | some i => exact (card_filter_le _ _).trans (card_le_card (hT i))
  have hcard : (Fintype.card (Option I) : ℝ) = Fintype.card I + 1 := by simp
  obtain ⟨y, hy⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hμ₀ hμ₁ S hS ha
    (by simpa [hcard] using h)
  refine ⟨y, ?_, fun i d ↦ ?_⟩
  · simpa only [S, Option.elim_none, filter_filter] using hy none c₀
  · simpa only [S, Option.elim_some, filter_filter] using hy (some i) d

/-- Convert fiberwise stay-put lower bounds from a maximal coupling into the `L¹` edit bound on
`Ω`. -/
private theorem card_filter_ne_le_of_fiber_stay {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Ω : Finset ι) (x₀ x : ι → κ) (y : κ → ι → κ) (hxΩ : ∀ e ∈ Ω, x e = y (x₀ e) e)
    {q p : κ → ℝ} {M : κ → κ → ℝ} {a : ℝ}
    (hN : (0 : ℝ) < #Ω) (hq1 : ∑ c, q c = 1) (hp1 : ∑ c, p c = 1)
    (hqmul : ∀ c, q c * #Ω = (#{e ∈ Ω | x₀ e = c} : ℝ))
    (hMstay : ∀ c₀, min (q c₀) (p c₀) ≤ q c₀ * M c₀ c₀)
    (hy_stay : ∀ c₀,
      |(#{e ∈ Ω | x₀ e = c₀ ∧ y c₀ e = c₀} : ℝ) - M c₀ c₀ * #{e ∈ Ω | x₀ e = c₀}| < a) :
    (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) ≤
      (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a := by
  have hstay_card : #{e ∈ Ω | x e = x₀ e} = ∑ c₀ : κ, #{e ∈ Ω | x₀ e = c₀ ∧ y c₀ e = c₀} := by
    rw [filter_congr (q := fun e ↦ y (x₀ e) e = x₀ e) fun e he ↦ by rw [hxΩ e he]]
    exact card_filter_apply_eq_sum_card_filter (f := x₀) (t := univ)
      (P := fun c₀ e ↦ y c₀ e = c₀) fun _ _ _ ↦ mem_univ _
  have hpart : (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) + (#{e ∈ Ω | x e = x₀ e} : ℝ) = #Ω := by
    exact_mod_cast (add_comm _ _).trans (card_filter_add_card_filter_not (s := Ω)
      (fun e ↦ x e = x₀ e))
  have hstay_lb :
      (∑ c₀ : κ, min (q c₀) (p c₀)) * #Ω - Fintype.card κ * a ≤ (#{e ∈ Ω | x e = x₀ e} : ℝ) := by
    have hcard_a : (Fintype.card κ : ℝ) * a = ∑ _c₀ : κ, a := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    rw [hstay_card, Nat.cast_sum, sum_mul, hcard_a, ← sum_sub_distrib]
    refine sum_le_sum fun c₀ _ ↦ ?_
    have h1 := (abs_lt.1 (hy_stay c₀)).1
    have h2 : min (q c₀) (p c₀) * #Ω ≤ M c₀ c₀ * #{e ∈ Ω | x₀ e = c₀} := by
      calc min (q c₀) (p c₀) * #Ω ≤ (q c₀ * M c₀ c₀) * #Ω :=
            mul_le_mul_of_nonneg_right (hMstay c₀) hN.le
        _ = M c₀ c₀ * (q c₀ * #Ω) := by ring
        _ = M c₀ c₀ * #{e ∈ Ω | x₀ e = c₀} := by rw [hqmul]
    linarith
  have htv := sub_sum_min_eq_sum_abs_div_two hq1 hp1
  have hL1 : (∑ c : κ, |q c - p c|) / 2 * #Ω =
      (∑ c : κ, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 := by
    rw [div_mul_eq_mul_div, sum_mul]
    congr 1
    refine sum_congr rfl fun c _ ↦ ?_
    calc |q c - p c| * #Ω = |q c - p c| * |(#Ω : ℝ)| := by rw [abs_of_pos hN]
      _ = |(q c - p c) * #Ω| := (abs_mul _ _).symm
      _ = |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω| := by rw [sub_mul, hqmul]
  calc (#{e ∈ Ω | x e ≠ x₀ e} : ℝ)
      = (#Ω : ℝ) - (#{e ∈ Ω | x e = x₀ e} : ℝ) := by linarith
    _ ≤ (1 - ∑ c₀ : κ, min (q c₀) (p c₀)) * #Ω + Fintype.card κ * a := by linarith
    _ = (∑ c : κ, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a := by
        rw [htv, hL1]

/-- **Coupled low-discrepancy recoloring.** Let `x₀ : ι → κ` be a coloring whose color classes on
a finite set `Ω` have discrepancy at most `b` from their empirical frequencies on every test set
`T i ⊆ Ω`, and let `p` be a probability distribution on `κ`. If
`2 * (card I + 1) * card κ * exp (-2 a² / #Ω) < 1` for some `a > 0`, then there is a coloring
`x : ι → κ` agreeing with `x₀` outside `Ω` that edits at most
`(∑ c, |#{e ∈ Ω | x₀ e = c} - p c * #Ω|) / 2 + card κ * a` points of `Ω` and whose color counts
on every test set `T i` lie within `card κ * (a + b)` of `p c * #(T i)`. -/
theorem exists_recoloring_abs_card_filter_sub_mul_card_le {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (Ω : Finset ι) (x₀ : ι → κ) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {I : Type*} [Fintype I] (T : I → Finset ι) (hT : ∀ i, T i ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hx₀ : ∀ i c,
      |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω * #(T i)| ≤ b)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #Ω) < 1) :
    ∃ x : ι → κ, (∀ e ∉ Ω, x e = x₀ e) ∧
      (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a ∧
      ∀ i d, |(#{e ∈ T i | x e = d} : ℝ) - p d * #(T i)| ≤ Fintype.card κ * (a + b) := by
  classical
  have : Nonempty κ := by by_contra! hκ; simp at hp1
  have hΩpos : 0 < #Ω := by
    by_contra! hΩ0
    have hΩz : #Ω = 0 := Nat.eq_zero_of_le_zero hΩ0
    have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
    simp only [hΩz, Nat.cast_zero, div_zero, exp_zero, mul_one] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hN : (0 : ℝ) < #Ω := Nat.cast_pos.2 hΩpos
  set q : κ → ℝ := fun c ↦ (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω
  have hq : ∀ c, 0 ≤ q c := fun c ↦ div_nonneg (Nat.cast_nonneg _) hN.le
  have hq1 : ∑ c, q c = 1 := by
    simp only [q, ← sum_div]
    rw [div_eq_one_iff_eq hN.ne', ← Nat.cast_sum,
      card_eq_sum_card_fiberwise (f := x₀) (t := (univ : Finset κ)) fun _ _ ↦ mem_univ _]
  have hqmul (c : κ) : q c * #Ω = (#{e ∈ Ω | x₀ e = c} : ℝ) := div_mul_cancel₀ _ hN.ne'
  obtain ⟨M, hM₀, hM₁, hMp, hMstay⟩ :=
    exists_sum_eq_one_and_sum_mul_eq_and_min_le_mul hq hq1 hp hp1
  have hMle1 (c₀ c : κ) : M c₀ c ≤ 1 :=
    hM₁ c₀ ▸ single_le_sum (fun d _ ↦ hM₀ c₀ d) (mem_univ c)
  choose y hy_stay hy_test using fun c₀ ↦
    exists_fiber_recoloring_abs_card_filter_sub_lt Ω x₀ c₀ (hM₀ c₀) (hM₁ c₀) T hT ha h
  let x : ι → κ := fun e ↦ if e ∈ Ω then y (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ by simp [x, he],
    card_filter_ne_le_of_fiber_stay Ω x₀ x y (fun e he ↦ by simp [x, he])
      hN hq1 hp1 hqmul hMstay hy_stay, fun i d ↦ ?_⟩
  have hfib : #{e ∈ T i | x e = d} = ∑ c₀ : κ, #{e ∈ T i | x₀ e = c₀ ∧ y c₀ e = d} := by
    rw [filter_congr (q := fun e ↦ y (x₀ e) e = d) fun e he ↦ by simp [x, hT i he]]
    exact card_filter_apply_eq_sum_card_filter (f := x₀) (t := univ)
      (P := fun c₀ e ↦ y c₀ e = d) fun _ _ _ ↦ mem_univ _
  have hμsum : ∑ c₀ : κ, M c₀ d * (q c₀ * #(T i)) = p d * #(T i) := by
    rw [← hMp d, sum_mul]
    exact sum_congr rfl fun c₀ _ ↦ by ring
  rw [hfib, Nat.cast_sum, ← hμsum, ← sum_sub_distrib]
  calc |∑ c₀ : κ, ((#{e ∈ T i | x₀ e = c₀ ∧ y c₀ e = d} : ℝ) - M c₀ d * (q c₀ * #(T i)))|
      ≤ ∑ c₀ : κ, |(#{e ∈ T i | x₀ e = c₀ ∧ y c₀ e = d} : ℝ) - M c₀ d * (q c₀ * #(T i))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c₀ : κ, (a + b) := sum_le_sum fun c₀ _ ↦ by
        have h1 := (hy_test c₀ i d).le
        have h2 : |M c₀ d * #{e ∈ T i | x₀ e = c₀} - M c₀ d * (q c₀ * #(T i))| ≤ b := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (hM₀ c₀ d)]
          exact (mul_le_mul_of_nonneg_left (hx₀ i c₀) (hM₀ c₀ d)).trans
            (mul_le_of_le_one_left hb (hMle1 c₀ d))
        exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
    _ = Fintype.card κ * (a + b) := by rw [sum_const, card_univ, nsmul_eq_mul]

end TauCeti
