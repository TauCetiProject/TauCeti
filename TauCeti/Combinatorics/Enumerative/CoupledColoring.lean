/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled low-discrepancy recolorings

Let `y : ι → κ` be an existing coloring on a finite window `W ⊆ ι`, and let `p` be a target
probability distribution on the finite palette `κ`. An independent random coloring with
distribution `p` achieves small discrepancy around `p` on every test subset `T i ⊆ W`
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`), but edits a constant fraction of `W`
even when the empirical color distribution of `y` on `W` is already close to `p`.

Coupling the empirical distribution `q` of `y` on `W` to `p` through a maximal Markov transition
kernel `M : κ → κ → ℝ` (`TauCeti.exists_coupling_kernel`) fixes this: points of `W` currently of
color `c₀` are recolored independently with distribution `M c₀`, while points outside `W` retain
their colors. Because `q c₀ * M c₀ c₀ ≥ min (q c₀) (p c₀)`, the number of edited points of `W` is
at most the total variation count `(1 / 2) ∑ c, |#{e ∈ W | y e = c} - p c * #W|` plus `a`. At the
same time, because `∑ c₀, q c₀ * M c₀ c = p c` and `0 ≤ M c₀ c ≤ 1`, any test subset `T i ⊆ W` on
which `y` already has small color-count deviations from `q` inherits small color-count deviations
from `p` (`TauCeti.exists_recoloring_card_filter_ne_lt`).

## Main results

* `TauCeti.exists_coupling_kernel`: Doeblin's maximal Markov kernel coupling a probability
  distribution `q` on a finite palette `κ` to a target distribution `p`.
* `TauCeti.exists_recoloring_card_filter_ne_lt`: recoloring `y` on `W` so that edits on `W` are
  within `a` of the total variation distance to `p`, while every test set `T i ⊆ W` has color
  counts close to `p` up to `a` plus `y`'s own discrepancy on `T i`.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Dover (2002), Chapter I, Theorem 5.2 (maximal
  coupling of discrete distributions).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.3 (density-adjusting regular approximation).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Appendix A.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*}

/-- **Maximal coupling kernel.** Given probability distributions `q` and `p` on a finite type `κ`,
there is a Markov transition kernel `M : κ → κ → ℝ` pushing `q` forward to `p` whose stay-put mass
at every state `c₀` is at least `min (q c₀) (p c₀)`. -/
theorem exists_coupling_kernel [Fintype κ] {q p : κ → ℝ}
    (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∃ M : κ → κ → ℝ, (∀ c₀ c, 0 ≤ M c₀ c) ∧ (∀ c₀, ∑ c, M c₀ c = 1) ∧
      (∀ c, ∑ c₀, q c₀ * M c₀ c = p c) ∧ ∀ c₀, min (q c₀) (p c₀) ≤ q c₀ * M c₀ c₀ := by
  classical
  let m : κ → ℝ := fun c ↦ min (q c) (p c)
  set s : ℝ := ∑ c, (p c - m c)
  have hqm (c : κ) : 0 ≤ q c - m c := sub_nonneg.2 (min_le_left _ _)
  have hpm (c : κ) : 0 ≤ p c - m c := sub_nonneg.2 (min_le_right _ _)
  have hsq : ∑ c, (q c - m c) = s := by simp only [s, sum_sub_distrib, hp1, hq1]
  have hs₀ : 0 ≤ s := sum_nonneg fun c _ ↦ hpm c
  have hrem (c₀ c : κ) : 0 ≤ if s = 0 then (0 : ℝ) else (q c₀ - m c₀) * (p c - m c) / s := by
    split_ifs; exacts [le_rfl, div_nonneg (mul_nonneg (hqm c₀) (hpm c)) hs₀]
  let num (c₀ c : κ) : ℝ :=
    (if c = c₀ then m c₀ else 0) + if s = 0 then 0 else (q c₀ - m c₀) * (p c - m c) / s
  let M (c₀ c : κ) : ℝ := if q c₀ = 0 then p c else num c₀ c / q c₀
  have hmul (c₀ c : κ) : q c₀ * M c₀ c = num c₀ c := by
    dsimp only [M]; split_ifs with hq0
    · have hm0 : m c₀ = 0 := le_antisymm ((min_le_left _ _).trans_eq hq0) (le_min (hq c₀) (hp c₀))
      simp [num, hq0, hm0]
    · exact mul_div_cancel₀ _ hq0
  refine ⟨M, fun c₀ c ↦ ?_, fun c₀ ↦ ?_, fun c ↦ ?_, fun c₀ ↦ ?_⟩
  · dsimp only [M]; split_ifs
    · exact hp c
    · refine div_nonneg (add_nonneg ?_ (hrem c₀ c)) (hq c₀)
      split_ifs; exacts [le_min (hq c₀) (hp c₀), le_rfl]
  · dsimp only [M]; split_ifs with hq0
    · exact hp1
    · rw [← sum_div, div_eq_one_iff_eq hq0]
      simp only [num, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
      split_ifs with hs0
      · rw [sum_const_zero]
        linarith [(sum_eq_zero_iff_of_nonneg fun c _ ↦ hqm c).1 (hsq.trans hs0) c₀ (mem_univ _)]
      · simp_rw [mul_div_assoc, ← mul_sum, ← sum_div]
        rw [show ∑ c, (p c - m c) = s from rfl, div_self hs0]; ring
  · simp_rw [hmul, num]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
    split_ifs with hs0
    · rw [sum_const_zero]
      linarith [(sum_eq_zero_iff_of_nonneg fun c _ ↦ hpm c).1 hs0 c (mem_univ _)]
    · simp_rw [mul_div_assoc]
      rw [← sum_mul, hsq, mul_comm s, div_mul_cancel₀ _ hs0]; ring
  · rw [hmul]; dsimp only [num]; rw [ite_eq_left rfl]; linarith [hrem c₀ c₀]

/-- For two functions with the same finite sum `S`, `S - ∑ c, min (u c) (v c)` is half the `L¹`
distance `∑ c, |u c - v c|`. -/
private theorem sub_sum_min_eq_sum_abs_div_two [Fintype κ] {u v : κ → ℝ} {S : ℝ}
    (hu : ∑ c, u c = S) (hv : ∑ c, v c = S) :
    S - ∑ c, min (u c) (v c) = (∑ c, |u c - v c|) / 2 := by
  have hpt (c : κ) : u c + v c - 2 * min (u c) (v c) = |u c - v c| := by
    rcases le_total (u c) (v c) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  have hsum : ∑ c, (u c + v c - 2 * min (u c) (v c)) = ∑ c, |u c - v c| :=
    sum_congr rfl fun c _ ↦ hpt c
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hu, hv] at hsum
  linarith

/-- Partitioning a subset `S` by `y` splits the count of points where `z (y e) e` satisfies a
predicate into the sum over source colors `c₀ : κ`. -/
private theorem card_filter_apply_eq_sum [Fintype κ] [DecidableEq κ] (y : ι → κ) (S : Finset ι)
    (P : κ → ι → Prop) [∀ c e, Decidable (P c e)] :
    #{e ∈ S | P (y e) e} = ∑ c₀, #{e ∈ S | y e = c₀ ∧ P c₀ e} := by
  rw [card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ ↦ mem_univ _]
  refine sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun e ↦ ?_)
  simp only [mem_filter]
  exact ⟨fun ⟨⟨he, hP⟩, hy⟩ ↦ ⟨he, hy, hy ▸ hP⟩, fun ⟨he, hy, hP⟩ ↦ ⟨⟨he, hy.symm ▸ hP⟩, hy⟩⟩

/-- From stay-put counts exceeding `M c₀ c₀ * #{e ∈ W | y e = c₀} - a / card κ` on every source
fiber, deduce the total-variation upper bound on the edited points of `W`. -/
private theorem card_filter_ne_lt_of_diag [Fintype κ] [DecidableEq κ] [Nonempty κ] {p : κ → ℝ}
    (hp1 : ∑ c, p c = 1) (y : ι → κ) (z : κ → ι → κ) {W : Finset ι} [DecidablePred (· ∈ W)]
    (hWne : W.Nonempty) {M : κ → κ → ℝ}
    (hMdiag : ∀ c₀, min ((#{e ∈ W | y e = c₀} : ℝ) / #W) (p c₀) ≤
      ((#{e ∈ W | y e = c₀} : ℝ) / #W) * M c₀ c₀)
    {a : ℝ} (hz : ∀ c₀, |(#{e ∈ W | y e = c₀ ∧ z c₀ e = c₀} : ℝ) -
      M c₀ c₀ * #{e ∈ W | y e = c₀}| < a / Fintype.card κ) :
    (#{e ∈ W | (if e ∈ W then z (y e) e else y e) ≠ y e} : ℝ) <
      (∑ c, |(#{e ∈ W | y e = c} : ℝ) - p c * #W|) / 2 + a := by
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hWpos : (0 : ℝ) < #W := Nat.cast_pos.2 hWne.card_pos
  let x : ι → κ := fun e ↦ if e ∈ W then z (y e) e else y e
  have hstay_eq : #{e ∈ W | x e = y e} = ∑ c₀, #{e ∈ W | y e = c₀ ∧ z c₀ e = c₀} := by
    rw [← card_filter_apply_eq_sum y W (fun c₀ e ↦ z c₀ e = c₀)]
    exact congrArg card (filter_congr fun e he ↦ by simp [x, he])
  have hstay_c (c₀ : κ) : min (#{e ∈ W | y e = c₀} : ℝ) (p c₀ * #W) - a / Fintype.card κ <
      (#{e ∈ W | y e = c₀ ∧ z c₀ e = c₀} : ℝ) := by
    have hdev := (abs_lt.1 (hz c₀)).1
    have hmin := mul_le_mul_of_nonneg_right (hMdiag c₀) hWpos.le
    rw [min_mul_of_nonneg _ _ hWpos.le, div_mul_cancel₀ _ hWpos.ne', mul_assoc,
      mul_comm (M c₀ c₀), ← mul_assoc, div_mul_cancel₀ _ hWpos.ne', mul_comm _ (M c₀ c₀)] at hmin
    linarith
  have hstay := sum_lt_sum_of_nonempty univ_nonempty fun c₀ _ ↦ hstay_c c₀
  rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hKpos.ne',
    ← Nat.cast_sum, ← hstay_eq] at hstay
  have hpart : (#{e ∈ W | x e = y e} : ℝ) + #{e ∈ W | x e ≠ y e} = #W := by
    exact_mod_cast card_filter_add_card_filter_not (fun e ↦ x e = y e)
  have hsumW : ∑ c, (#{e ∈ W | y e = c} : ℝ) = #W := by
    exact_mod_cast (card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ ↦ mem_univ _).symm
  have htv := sub_sum_min_eq_sum_abs_div_two hsumW (by rw [← sum_mul, hp1, one_mul])
  linarith

/-- Propagate fiberwise color-count bounds on `T ⊆ W` through a Markov kernel `M` pushing `y`'s
empirical distribution on `W` forward to `p`. -/
private theorem abs_card_filter_sub_lt_of_kernel [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {p : κ → ℝ} (y : ι → κ) (z : κ → ι → κ) {W T : Finset ι} [DecidablePred (· ∈ W)]
    (hTW : T ⊆ W) {M : κ → κ → ℝ} (hM₀ : ∀ c₀ c, 0 ≤ M c₀ c) (hM₁ : ∀ c₀, ∑ c, M c₀ c = 1)
    (c : κ) (hMq : ∑ c₀, (#{e ∈ W | y e = c₀} : ℝ) / #W * M c₀ c = p c) {a : ℝ}
    (hz : ∀ c₀, |(#{e ∈ T | y e = c₀ ∧ z c₀ e = c} : ℝ) -
      M c₀ c * #{e ∈ T | y e = c₀}| < a / Fintype.card κ) :
    |(#{e ∈ T | (if e ∈ W then z (y e) e else y e) = c} : ℝ) - p c * #T| <
      a + ∑ c₀, |(#{e ∈ T | y e = c₀} : ℝ) - (#{e ∈ W | y e = c₀} : ℝ) / #W * #T| := by
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hT_eq : #{e ∈ T | (if e ∈ W then z (y e) e else y e) = c} =
      ∑ c₀, #{e ∈ T | y e = c₀ ∧ z c₀ e = c} := by
    rw [← card_filter_apply_eq_sum y T (fun c₀ e ↦ z c₀ e = c)]
    exact congrArg card (filter_congr fun e he ↦ by simp [hTW he])
  have hpT : p c * #T = ∑ c₀, M c₀ c * ((#{e ∈ W | y e = c₀} : ℝ) / #W * #T) := by
    rw [← hMq, sum_mul]
    exact sum_congr rfl fun c₀ _ ↦ by ring
  rw [hT_eq, Nat.cast_sum, hpT, ← sum_sub_distrib]
  calc |∑ c₀, ((#{e ∈ T | y e = c₀ ∧ z c₀ e = c} : ℝ) -
          M c₀ c * ((#{e ∈ W | y e = c₀} : ℝ) / #W * #T))|
      ≤ ∑ c₀, |(#{e ∈ T | y e = c₀ ∧ z c₀ e = c} : ℝ) -
          M c₀ c * ((#{e ∈ W | y e = c₀} : ℝ) / #W * #T)| := abs_sum_le_sum_abs _ _
    _ < ∑ c₀, (a / Fintype.card κ +
          |(#{e ∈ T | y e = c₀} : ℝ) - (#{e ∈ W | y e = c₀} : ℝ) / #W * #T|) := by
        refine sum_lt_sum_of_nonempty univ_nonempty fun c₀ _ ↦ ?_
        have hMle1 : M c₀ c ≤ 1 := hM₁ c₀ ▸ single_le_sum (fun c' _ ↦ hM₀ c₀ c') (mem_univ c)
        have heq : (#{e ∈ T | y e = c₀ ∧ z c₀ e = c} : ℝ) -
            M c₀ c * ((#{e ∈ W | y e = c₀} : ℝ) / #W * #T) =
            ((#{e ∈ T | y e = c₀ ∧ z c₀ e = c} : ℝ) - M c₀ c * #{e ∈ T | y e = c₀}) +
              M c₀ c * ((#{e ∈ T | y e = c₀} : ℝ) -
                (#{e ∈ W | y e = c₀} : ℝ) / #W * #T) := by ring
        have htri := (heq ▸ abs_add_le _ _).trans_eq
          (by rw [abs_mul, abs_of_nonneg (hM₀ c₀ c)])
        linarith [hz c₀, mul_le_mul_of_nonneg_right hMle1
          (abs_nonneg ((#{e ∈ T | y e = c₀} : ℝ) - (#{e ∈ W | y e = c₀} : ℝ) / #W * #T))]
    _ = a + ∑ c₀, |(#{e ∈ T | y e = c₀} : ℝ) - (#{e ∈ W | y e = c₀} : ℝ) / #W * #T| := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hKpos.ne']

/-- **Coupled low-discrepancy recoloring.** Let `p` be a probability distribution on a finite
palette `κ`, let `y : ι → κ` be a coloring, let `W` be a finite set of size at most `N`, and let
`T i ⊆ W` (`i : I`) be a finite family of test subsets. If
`2 * (card I + 1) * card κ * exp (-2 * (a / card κ) ^ 2 / N) < 1` for some `a > 0`, then there is
a coloring `x : ι → κ` agreeing with `y` outside `W` such that:

* the number of edited points of `W` is strictly less than the total variation count
  `(∑ c, |#{e ∈ W | y e = c} - p c * #W|) / 2 + a`, and
* on every test set `T i` and color `c`, the count of color `c` under `x` differs from
  `p c * #(T i)` by strictly less than `a` plus the sum over `c₀` of `y`'s own count deviations on
  `T i` from its empirical density on `W`. -/
theorem exists_recoloring_card_filter_ne_lt [Fintype κ] [DecidableEq κ] {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (y : ι → κ) (W : Finset ι) {I : Type*}
    [Fintype I] (T : I → Finset ι) (hTW : ∀ i, T i ⊆ W) {N : ℕ} (hW : #W ≤ N)
    {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ *
      exp (-2 * (a / Fintype.card κ) ^ 2 / N) < 1) :
    ∃ x : ι → κ, (∀ e, e ∉ W → x e = y e) ∧
      (#{e ∈ W | x e ≠ y e} : ℝ) < (∑ c, |(#{e ∈ W | y e = c} : ℝ) - p c * #W|) / 2 + a ∧
      ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - p c * #(T i)| <
        a + ∑ c₀, |(#{e ∈ T i | y e = c₀} : ℝ) -
          (#{e ∈ W | y e = c₀} : ℝ) / #W * #(T i)| := by
  classical
  rcases W.eq_empty_or_nonempty with rfl | hWne
  · refine ⟨y, fun _ _ ↦ rfl, by simpa using ha, fun i c ↦ ?_⟩
    rw [subset_empty.1 (hTW i)]
    simpa using ha
  have : Nonempty κ :=
    Classical.byContradiction fun hκ ↦ by have := not_nonempty_iff.1 hκ; simp at hp1
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hWpos : (0 : ℝ) < #W := Nat.cast_pos.2 hWne.card_pos
  have hsumW : ∑ c, (#{e ∈ W | y e = c} : ℝ) = #W := by
    exact_mod_cast (card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ ↦ mem_univ _).symm
  obtain ⟨M, hM₀, hM₁, hMq, hMdiag⟩ := exists_coupling_kernel
    (fun c ↦ div_nonneg (Nat.cast_nonneg _) hWpos.le)
    (by rw [← sum_div, hsumW, div_self hWpos.ne']) hp hp1
  let S (c₀ : κ) : Option I → Finset ι :=
    Option.elim' {e ∈ W | y e = c₀} fun i ↦ {e ∈ T i | y e = c₀}
  have hScard (c₀ : κ) (j : Option I) : #(S c₀ j) ≤ N :=
    Option.casesOn j ((card_filter_le _ _).trans hW) fun i ↦
      (card_filter_le _ _).trans ((card_le_card (hTW i)).trans hW)
  choose z hz using fun c₀ ↦ exists_forall_abs_card_filter_sub_mul_card_lt (hM₀ c₀) (hM₁ c₀)
    (S c₀) (hScard c₀) (div_pos ha hKpos) (by simpa [Fintype.card_option, Nat.cast_add] using h)
  refine ⟨fun e ↦ if e ∈ W then z (y e) e else y e, fun e he ↦ ite_eq_right he,
    card_filter_ne_lt_of_diag (M := M) (a := a) hp1 y z hWne hMdiag
      (fun c₀ ↦ by simpa only [S, Option.elim'_none, filter_filter] using hz c₀ none c₀),
    fun i c ↦ abs_card_filter_sub_lt_of_kernel y z (hTW i) hM₀ hM₁ c (hMq c)
      (fun c₀ ↦ by simpa only [S, Option.elim'_some, filter_filter] using hz c₀ (some i) c)⟩

end TauCeti
