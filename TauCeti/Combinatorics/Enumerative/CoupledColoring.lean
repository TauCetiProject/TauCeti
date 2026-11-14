/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled colorings with small discrepancy and few edits

Let `x₀ : ι → κ` be an existing coloring of a finite set `S ⊆ ι` with a finite palette `κ`, and
let `p` be a target probability distribution on `κ`. When the empirical color counts of `x₀` on `S`
are already close to `p · #S`, and when `x₀` already has nearly uniform color proportions across a
family of test sets `T i ⊆ S`, one wants a new coloring `x` whose color counts on every `T i` are
close to `p · #(T i)` while recoloring as few points of `S` as possible.

An independent random coloring with distribution `p`
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`) achieves the discrepancy bound on the test
sets, but forgets `x₀` and edits a constant fraction of `S` even when `x₀` already has the target
proportions. Instead, choose an optimal Markov transition
kernel `K : κ → κ → ℝ` from the empirical counts `n c = #{e ∈ S | x₀ e = c}` to `p · #S` that
moves only the excess mass off the diagonal (`TauCeti.exists_transition_kernel_sum_sub_diag_le`),
and recolor each color fiber `{e ∈ S | x₀ e = c₀}` independently with distribution `K c₀` using the
low-discrepancy coloring theorem. Summing the fiberwise bounds controls both the number of edited
points on `S` (half the `L¹`-distance between the empirical and target counts, up to random-coloring
slack) and the discrepancy of every color on every `T i` (bounded by the total fiberwise discrepancy
of `x₀` on `T i` plus the random-coloring slack).

This is the randomized coupling step behind regular approximation of graphs and hypergraphs: when a
fine regular pair has densities close to those of its coarse parent block, coupled recoloring shifts
its densities to the coarse target while editing negligibly many pairs.

## Main results

* `TauCeti.exists_transition_kernel_sum_sub_diag_le`: an optimal Markov transition kernel pushing a
  nonnegative count vector `n` to `(∑ d, n d) • p` while moving at most half the `L¹`-gap off the
  diagonal.
* `TauCeti.exists_coupled_coloring_abs_card_filter_sub_le`: a recoloring supported on `S` with
  edit count controlled by the total-variation gap on `S` and test-set discrepancies controlled by
  the initial discrepancies of `x₀` on the test sets.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 (coupled randomized recoloring).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Theorem 13.1.1.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*}

/-- Pointwise identities relating `max (a - b) 0`, `max (b - a) 0`, `|a - b|`, and `min a b`. -/
private theorem max_sub_identities (a b : ℝ) :
    (max (a - b) 0 - max (b - a) 0 = a - b) ∧
    (max (a - b) 0 + max (b - a) 0 = |a - b|) ∧
    (min a b + max (a - b) 0 = a) ∧
    (min a b + max (b - a) 0 = b) := by
  rcases le_total a b with hle | hle
  · rw [min_eq_left hle, max_eq_right (sub_nonpos.2 hle), max_eq_left (sub_nonneg.2 hle),
      abs_of_nonpos (sub_nonpos.2 hle)]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [min_eq_right hle, max_eq_left (sub_nonneg.2 hle), max_eq_right (sub_nonpos.2 hle),
      abs_of_nonneg (sub_nonneg.2 hle)]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Total-variation identity: when `∑ c, n c = ∑ c, m c`, the positive and negative parts of
`n - m` each sum to half the `L¹`-distance `∑ c, |n c - m c|`. -/
private theorem sum_max_sub_eq_of_sum_eq [Fintype κ] {n m : κ → ℝ}
    (hsum : ∑ c, n c = ∑ c, m c) :
    ∑ c, max (m c - n c) 0 = ∑ c, max (n c - m c) 0 ∧
    ∑ c, max (n c - m c) 0 = (∑ c, |n c - m c|) / 2 := by
  have hsub : ∑ c, (max (n c - m c) 0 - max (m c - n c) 0) = 0 := by
    simp_rw [(max_sub_identities _ _).1, sum_sub_distrib, hsum, sub_self]
  have heq : ∑ c, max (m c - n c) 0 = ∑ c, max (n c - m c) 0 := by
    rw [sum_sub_distrib] at hsub
    linarith
  have hadd : ∑ c, (max (n c - m c) 0 + max (m c - n c) 0) = ∑ c, |n c - m c| :=
    sum_congr rfl fun c _ ↦ (max_sub_identities (n c) (m c)).2.1
  rw [sum_add_distrib, heq] at hadd
  exact ⟨heq, by linarith⟩

/-- For a nonnegative vector `w` with sum `T`, `w c * T / T = w c` even when `T = 0`. -/
private theorem mul_div_eq_of_sum_eq [Fintype κ] {w : κ → ℝ} (hw : ∀ d, 0 ≤ w d) {T : ℝ}
    (hT : ∑ d, w d = T) (c : κ) : w c * T / T = w c := by
  by_cases h0 : T = 0
  · rw [h0, div_zero]
    exact (le_antisymm ((single_le_sum (fun d _ ↦ hw d) (mem_univ c)).trans_eq (hT.trans h0))
      (hw c)).symm
  · exact mul_div_cancel_right₀ _ h0

/-- **Optimal coupling kernel.** Given nonnegative counts `n : κ → ℝ` and a probability
distribution `p : κ → ℝ` on a finite palette `κ`, there is a Markov transition kernel
`K : κ → κ → ℝ` pushing `n` to `(∑ d, n d) • p` while moving at most half the `L¹`-distance
`∑ c, |n c - p c * ∑ d, n d|` off the diagonal. -/
theorem exists_transition_kernel_sum_sub_diag_le [Fintype κ] {n p : κ → ℝ}
    (hn : ∀ c, 0 ≤ n c) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∃ K : κ → κ → ℝ,
      (∀ c₀ c, 0 ≤ K c₀ c) ∧
      (∀ c₀, ∑ c, K c₀ c = 1) ∧
      (∀ c, ∑ c₀, n c₀ * K c₀ c = p c * ∑ d, n d) ∧
      ∑ c₀, (1 - K c₀ c₀) * n c₀ ≤ (∑ c, |n c - p c * ∑ d, n d|) / 2 := by
  classical
  let m (c : κ) : ℝ := p c * ∑ d, n d
  have hm (c : κ) : 0 ≤ m c := mul_nonneg (hp c) (sum_nonneg fun d _ ↦ hn d)
  let u (c : κ) : ℝ := max (n c - m c) 0
  let v (c : κ) : ℝ := max (m c - n c) 0
  have hu (c : κ) : 0 ≤ u c := le_max_right _ _
  have hv (c : κ) : 0 ≤ v c := le_max_right _ _
  obtain ⟨hsum_v, hTV_eq⟩ :=
    sum_max_sub_eq_of_sum_eq (by simp only [m, ← sum_mul, hp1, one_mul] : ∑ c, n c = ∑ c, m c)
  set TV : ℝ := ∑ c, u c
  have hTV0 : 0 ≤ TV := sum_nonneg fun c _ ↦ hu c
  let K (c₀ c : κ) : ℝ :=
    if n c₀ = 0 then p c
    else ((if c = c₀ then min (n c₀) (m c₀) else 0) + u c₀ * v c / TV) / n c₀
  have hjoint (c₀ c : κ) :
      n c₀ * K c₀ c = (if c = c₀ then min (n c₀) (m c₀) else 0) + u c₀ * v c / TV := by
    by_cases h0 : n c₀ = 0
    · have hu0 : u c₀ = 0 := by dsimp [u]; rw [h0]; exact max_eq_right (by linarith [hm c₀])
      simp [h0, hu0, hm c₀]
    · simp only [K, h0, ↓reduceIte, mul_div_cancel₀ _ h0]
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · intro c₀ c
    by_cases h0 : n c₀ = 0
    · simp [K, h0, hp c]
    · simp only [K, h0, ↓reduceIte]
      refine div_nonneg (add_nonneg ?_ (div_nonneg (mul_nonneg (hu c₀) (hv c)) hTV0)) (hn c₀)
      split_ifs
      · exact le_min (hn c₀) (hm c₀)
      · exact le_rfl
  · intro c₀
    by_cases h0 : n c₀ = 0
    · simp [K, h0, hp1]
    · refine mul_left_cancel₀ h0 ?_
      rw [mul_sum, sum_congr rfl fun c _ ↦ hjoint c₀ c, sum_add_distrib, Fintype.sum_ite_eq',
        ← sum_div, ← mul_sum, hsum_v, mul_div_eq_of_sum_eq hu rfl c₀,
        (max_sub_identities (n c₀) (m c₀)).2.2.1, mul_one]
  · intro c
    rw [sum_congr rfl fun c₀ _ ↦ hjoint c₀ c, sum_add_distrib, Fintype.sum_ite_eq, ← sum_div,
      ← sum_mul, mul_comm TV (v c), mul_div_eq_of_sum_eq hv hsum_v c,
      (max_sub_identities (n c) (m c)).2.2.2]
  · rw [← hTV_eq]
    refine sum_le_sum fun c₀ _ ↦ ?_
    have hj := hjoint c₀ c₀
    have hpos : 0 ≤ u c₀ * v c₀ / TV := div_nonneg (mul_nonneg (hu c₀) (hv c₀)) hTV0
    have hm_u := (max_sub_identities (n c₀) (m c₀)).2.2.1
    simp only [↓reduceIte] at hj
    linarith

variable [DecidableEq κ]

/-- Partition a count on `U` into the color fibers of `x₀`. -/
private theorem card_filter_eq_sum_fiber [Fintype κ] (U : Finset ι) (x₀ : ι → κ) (q : ι → Prop)
    [DecidablePred q] :
    (#{e ∈ U | q e} : ℝ) = ∑ c₀ : κ, (#{e ∈ U | x₀ e = c₀ ∧ q e} : ℝ) := by
  simp_rw [← sum_boole]
  rw [sum_comm]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [← Fintype.sum_ite_eq (x₀ e) fun _ ↦ if q e then (1 : ℝ) else 0]
  exact sum_congr rfl fun c₀ _ ↦ by
    by_cases h₁ : x₀ e = c₀ <;> by_cases h₂ : q e <;> simp [h₁, h₂]

/-- Bound the color-`c` discrepancy of a fiberwise-coupled coloring `x` on `U ⊆ S` by summing the
fiberwise deviations against a Markov transition kernel `K`. -/
private theorem abs_card_filter_coupled_sub_le [Fintype κ] {S U : Finset ι} (hUS : U ⊆ S)
    (x₀ x : ι → κ) (y : κ → ι → κ) (hx : ∀ e ∈ U, x e = y (x₀ e) e) {p : κ → ℝ}
    {K : κ → κ → ℝ} (hK0 : ∀ c₀ c, 0 ≤ K c₀ c) (hK1 : ∀ c₀, ∑ c, K c₀ c = 1)
    (hKmarg : ∀ c, ∑ c₀, (#{e ∈ S | x₀ e = c₀} : ℝ) * K c₀ c = p c * #S)
    {a : ℝ} (ha : 0 ≤ a)
    (hy : ∀ c₀ c,
      |(#{e ∈ U | x₀ e = c₀ ∧ y c₀ e = c} : ℝ) - K c₀ c * #{e ∈ U | x₀ e = c₀}| ≤ a) (c : κ) :
    |(#{e ∈ U | x e = c} : ℝ) - p c * #U| ≤
      (∑ c₀, |(#{e ∈ U | x₀ e = c₀} : ℝ) - (#{e ∈ S | x₀ e = c₀} : ℝ) / #S * #U|) +
        Fintype.card κ * a := by
  rcases (#S).eq_zero_or_pos with hS0 | hSpos
  · have hU : U = ∅ := subset_empty.1 (card_eq_zero.1 hS0 ▸ hUS)
    simp only [hU, filter_empty, card_empty, Nat.cast_zero, mul_zero, sub_zero, abs_zero,
      sum_const_zero, zero_add]
    positivity
  have hSpos' : (0 : ℝ) < #S := Nat.cast_pos.2 hSpos
  let n (c₀ : κ) : ℝ := #{e ∈ S | x₀ e = c₀}
  have hUfib : (#{e ∈ U | x e = c} : ℝ) = ∑ c₀, (#{e ∈ U | x₀ e = c₀ ∧ y c₀ e = c} : ℝ) := by
    rw [card_filter_eq_sum_fiber U x₀ (fun e ↦ x e = c)]
    refine sum_congr rfl fun c₀ _ ↦ congrArg Nat.cast (congrArg card (filter_congr fun e he ↦ ?_))
    rw [hx e he]
    exact and_congr_right fun hc ↦ by rw [hc]
  have htarget : p c * #U = ∑ c₀, K c₀ c * (n c₀ / #S * #U) := by
    calc p c * #U = (p c * #S) / #S * #U := by rw [mul_div_cancel_right₀ _ hSpos'.ne']
      _ = (∑ c₀, n c₀ * K c₀ c) / #S * #U := by rw [hKmarg c]
      _ = ∑ c₀, K c₀ c * (n c₀ / #S * #U) := by
          rw [sum_div, sum_mul]
          exact sum_congr rfl fun c₀ _ ↦ by ring
  have hKle1 (c₀ : κ) : K c₀ c ≤ 1 :=
    (single_le_sum (fun d _ ↦ hK0 c₀ d) (mem_univ c)).trans_eq (hK1 c₀)
  rw [hUfib, htarget, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum
    (g := fun c₀ ↦ |(#{e ∈ U | x₀ e = c₀} : ℝ) - n c₀ / #S * #U| + a) fun c₀ _ ↦ ?_) ?_)
  · have h₁ := hy c₀ c
    have htri : |(#{e ∈ U | x₀ e = c₀ ∧ y c₀ e = c} : ℝ) - K c₀ c * (n c₀ / #S * #U)| ≤
        |(#{e ∈ U | x₀ e = c₀ ∧ y c₀ e = c} : ℝ) - K c₀ c * #{e ∈ U | x₀ e = c₀}| +
          |K c₀ c * #{e ∈ U | x₀ e = c₀} - K c₀ c * (n c₀ / #S * #U)| := by
      simpa [sub_add_sub_cancel] using abs_add_le
        ((#{e ∈ U | x₀ e = c₀ ∧ y c₀ e = c} : ℝ) - K c₀ c * #{e ∈ U | x₀ e = c₀})
        (K c₀ c * #{e ∈ U | x₀ e = c₀} - K c₀ c * (n c₀ / #S * #U))
    rw [← mul_sub, abs_mul, abs_of_nonneg (hK0 c₀ c)] at htri
    have h₂ : K c₀ c * |(#{e ∈ U | x₀ e = c₀} : ℝ) - n c₀ / #S * #U| ≤
        1 * |(#{e ∈ U | x₀ e = c₀} : ℝ) - n c₀ / #S * #U| :=
      mul_le_mul_of_nonneg_right (hKle1 c₀) (abs_nonneg _)
    dsimp only [n] at htri h₂ ⊢
    linarith
  · rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]

/-- **Coupled colorings with small discrepancy and few edits.** Let `x₀ : ι → κ` be a coloring,
`S ⊆ ι` a finite set of size at most `N`, `p` a probability distribution on `κ`, and `T i ⊆ S` a
finite family of test sets. If `2 * (card I + 1) * card κ * exp (-2 a² / N) < 1` for `a > 0`,
there is a coloring `x : ι → κ` agreeing with `x₀` outside `S` such that:
1. the number of edited points on `S` is at most half the `L¹`-gap between the color counts of
   `x₀` on `S` and `p · #S`, plus `card κ * a`; and
2. on every `T i` and for every color `c`, the count of `c` under `x` is within the initial
   fiberwise discrepancy of `x₀` on `T i` plus `card κ * a` of `p c * #(T i)`. -/
theorem exists_coupled_coloring_abs_card_filter_sub_le [Fintype κ] (S : Finset ι) (x₀ : ι → κ)
    {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {I : Type*} [Fintype I]
    (T : I → Finset ι) (hTS : ∀ i, T i ⊆ S) {N : ℕ} (hSN : #S ≤ N) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ * exp (-2 * a ^ 2 / N) < 1) :
    ∃ x : ι → κ,
      (∀ e ∉ S, x e = x₀ e) ∧
      (#{e ∈ S | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ S | x₀ e = c} : ℝ) - p c * #S|) / 2 + Fintype.card κ * a ∧
      ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| ≤
        (∑ c₀, |(#{e ∈ T i | x₀ e = c₀} : ℝ) - (#{e ∈ S | x₀ e = c₀} : ℝ) / #S * #(T i)|) +
          Fintype.card κ * a := by
  classical
  let n (c : κ) : ℝ := #{e ∈ S | x₀ e = c}
  have hsum_n : ∑ d, n d = #S := by
    simpa [n] using (card_filter_eq_sum_fiber S x₀ fun _ ↦ True).symm
  obtain ⟨K, hK0, hK1, hKmarg, hKdiag⟩ :=
    exists_transition_kernel_sum_sub_diag_le (n := n) (fun _ ↦ Nat.cast_nonneg _) hp hp1
  rw [hsum_n] at hKmarg hKdiag
  let F (c₀ : κ) : Option I → Finset ι :=
    fun o ↦ o.elim {e ∈ S | x₀ e = c₀} fun i ↦ {e ∈ T i | x₀ e = c₀}
  have hFN (c₀ : κ) (o : Option I) : #(F c₀ o) ≤ N := by
    cases o with
    | none => exact (card_filter_le _ _).trans hSN
    | some i => exact (card_filter_le _ _).trans ((card_le_card (hTS i)).trans hSN)
  have hub : 2 * Fintype.card (Option I) * Fintype.card κ * exp (-2 * a ^ 2 / N) < 1 := by
    simpa [Fintype.card_option] using h
  choose y hy using fun c₀ ↦
    exists_forall_abs_card_filter_sub_mul_card_lt (hK0 c₀) (hK1 c₀) (F c₀) (hFN c₀) ha hub
  let x : ι → κ := fun e ↦ if e ∈ S then y (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ by simp [x, he], ?_, ?_⟩
  · have hfib : (#{e ∈ S | x e ≠ x₀ e} : ℝ) = ∑ c₀, (#{e ∈ F c₀ none | y c₀ e ≠ c₀} : ℝ) := by
      rw [card_filter_eq_sum_fiber S x₀ (fun e ↦ x e ≠ x₀ e)]
      refine sum_congr rfl fun c₀ _ ↦ congrArg Nat.cast (congrArg card (ext fun e ↦ ?_))
      simp only [F, Option.elim_none, mem_filter, x]
      by_cases he : e ∈ S <;> by_cases hc : x₀ e = c₀ <;> simp [he, hc]
    have hstay (c₀ : κ) : (#{e ∈ F c₀ none | y c₀ e ≠ c₀} : ℝ) ≤ (1 - K c₀ c₀) * n c₀ + a := by
      have hpart : #{e ∈ F c₀ none | y c₀ e = c₀} + #{e ∈ F c₀ none | y c₀ e ≠ c₀} =
          #(F c₀ none) := card_filter_add_card_filter_not (fun e ↦ y c₀ e = c₀)
      have hcast : (#{e ∈ F c₀ none | y c₀ e = c₀} : ℝ) + #{e ∈ F c₀ none | y c₀ e ≠ c₀} =
          #(F c₀ none) := by exact_mod_cast hpart
      have hdev := (abs_lt.1 (hy c₀ none c₀)).1
      dsimp only [F, Option.elim_none, n] at hdev hcast ⊢
      linarith
    calc (#{e ∈ S | x e ≠ x₀ e} : ℝ)
        ≤ ∑ c₀, ((1 - K c₀ c₀) * n c₀ + a) := hfib ▸ sum_le_sum fun c₀ _ ↦ hstay c₀
      _ = ∑ c₀, (1 - K c₀ c₀) * n c₀ + Fintype.card κ * a := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      _ ≤ _ := by linarith [hKdiag]
  · intro i c
    exact abs_card_filter_coupled_sub_le (hTS i) x₀ x y (fun e he ↦ by simp [x, hTS i he])
      hK0 hK1 hKmarg ha.le
      (fun c₀ c' ↦ by simpa only [F, Option.elim_some, filter_filter] using (hy c₀ (some i) c').le)
      c

end TauCeti
