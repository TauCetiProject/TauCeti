/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled colorings of low discrepancy

Let `Z` be a finite set already colored by `y : ι → κ`, and let `q : κ → ℝ` be a target
probability distribution on the finite palette `κ`. Coloring `Z` independently at random from `q`
gives color counts close to `q c * #(T i)` on a family of test sets `T i`
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`), but edits a large proportion of `Z` even
when the empirical distribution `p a = #{e ∈ Z | y e = a} / #Z` is already close to `q`.

To preserve agreement with `y` while adjusting densities to `q` and retaining quasi-randomness on
test sets, we couple `p` to `q` through a maximal-coupling transition matrix `M : κ → κ → ℝ`
(`TauCeti.exists_transition_coupling`): each color `a` keeps itself with mass `min (p a) (q a)`
and redistributes its excess `max (p a - q a) 0` across colors proportionally to their deficits
`max (q c - p c) 0`. Applying `exists_forall_abs_card_filter_sub_mul_card_lt` on each color fiber of
`y` with distribution `M a` and assembling the fiberwise colorings along `y` yields a coloring
`x : ι → κ` (`TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt`) that simultaneously:

* edits fewer than `(1 / 2) * ∑ c, |#{e ∈ Z | y e = c} - q c * #Z| + card κ * a` points of `Z`,
  matching the total variation distance between `p` and `q` up to the concentration tolerance; and
* controls the discrepancy `|#{e ∈ T i | x e = c} - q c * #(T i)|` on every test set `T i` in terms
  of the fiber discrepancies of `y` on `T i` plus `card κ * a`.

## Main results

* `TauCeti.exists_transition_coupling`: maximal-coupling Markov transition kernel between two
  probability distributions on a finite type.
* `TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt`: a coloring close to `y` on `Z` whose
  color counts on every test set `T i` track `q` whenever the fibers of `y` are quasi-random.
* `TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt_of_le`: specialization under a uniform
  bound on the fiber discrepancies of `y`.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), §I.2 (maximal coupling of discrete
  distributions).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Theorem 13.1.1.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*}

section TransitionCoupling

variable [Fintype κ]

/-- Pointwise algebraic identities relating `min u v`, the excess `max (u - v) 0`, the deficit
`max (v - u) 0`, and `|u - v|`. -/
private theorem excess_deficit_identities (u v : ℝ) :
    max (u - v) 0 - max (v - u) 0 = u - v ∧
      max (u - v) 0 + max (v - u) 0 = |u - v| ∧
      min u v + max (u - v) 0 = u ∧
      min u v + max (v - u) 0 = v ∧
      max (u - v) 0 * max (v - u) 0 = 0 := by
  rcases le_total u v with huv | hvu
  · have h₁ : max (u - v) 0 = 0 := max_eq_right (sub_nonpos.2 huv)
    have h₂ : max (v - u) 0 = v - u := max_eq_left (sub_nonneg.2 huv)
    have h₃ : |u - v| = v - u := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 huv)]
    rw [h₁, h₂, h₃, min_eq_left huv]
    refine ⟨by ring, by ring, by ring, by ring, by ring⟩
  · have h₁ : max (u - v) 0 = u - v := max_eq_left (sub_nonneg.2 hvu)
    have h₂ : max (v - u) 0 = 0 := max_eq_right (sub_nonpos.2 hvu)
    have h₃ : |u - v| = u - v := abs_of_nonneg (sub_nonneg.2 hvu)
    rw [h₁, h₂, h₃, min_eq_right hvu]
    refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- **Maximal-coupling transition kernel.** For any two probability distributions `p` and `q` on a
finite type `κ`, there is a Markov transition kernel `M : κ → κ → ℝ` pushing `p` forward to `q`
whose diagonal mass at each `a` satisfies `p a * M a a = min (p a) (q a)`, so that the total
off-diagonal mass `∑ a, p a * (1 - M a a)` equals the total variation distance
`(1 / 2) * ∑ a, |p a - q a|`. -/
theorem exists_transition_coupling {p q : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) :
    ∃ M : κ → κ → ℝ,
      (∀ a c, 0 ≤ M a c) ∧
      (∀ a, ∑ c, M a c = 1) ∧
      (∀ c, ∑ a, p a * M a c = q c) ∧
      (∀ a, p a * M a a = min (p a) (q a)) ∧
      ∑ a, p a * (1 - M a a) = (1 / 2) * ∑ a, |p a - q a| := by
  classical
  let ex : κ → ℝ := fun a ↦ max (p a - q a) 0
  let df : κ → ℝ := fun c ↦ max (q c - p c) 0
  have hex₀ (a : κ) : 0 ≤ ex a := le_max_right _ _
  have hdf₀ (c : κ) : 0 ≤ df c := le_max_right _ _
  have hsum_eq : ∑ a, ex a = ∑ c, df c := by
    have hsub : ∑ a, (ex a - df a) = 0 := by
      rw [sum_congr rfl fun a _ ↦ (excess_deficit_identities (p a) (q a)).1,
        sum_sub_distrib, hp1, hq1, sub_self]
    linarith [sum_sub_distrib (s := univ) (f := ex) (g := df)]
  set tv := ∑ a, ex a
  have htv_abs : 2 * tv = ∑ a, |p a - q a| := by
    calc 2 * tv = ∑ a, ex a + ∑ a, df a := by rw [← hsum_eq]; ring
      _ = ∑ a, (ex a + df a) := sum_add_distrib.symm
      _ = ∑ a, |p a - q a| := sum_congr rfl fun a _ ↦ (excess_deficit_identities (p a) (q a)).2.1
  -- When `tv = 0`, `p = q` everywhere; otherwise redistribute excess proportionally to deficit.
  by_cases htv : tv = 0
  · have hpq (a : κ) : p a = q a := by
      have hex_zero : ex a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hex₀ b) (mem_univ a)).trans_eq htv) (hex₀ a)
      have hdf_zero : df a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hdf₀ b) (mem_univ a)).trans_eq
          (hsum_eq.symm.trans htv)) (hdf₀ a)
      linarith [(excess_deficit_identities (p a) (q a)).1]
    refine ⟨fun a c ↦ if c = a then 1 else 0, fun a c ↦ by dsimp only; split_ifs <;> norm_num,
      fun a ↦ by simp, fun c ↦ by simp [hpq], fun a ↦ by simp [hpq], ?_⟩
    have habs : ∑ a, |p a - q a| = 0 := by linarith
    simp [habs]
  · have : 0 < tv := (sum_nonneg fun a _ ↦ hex₀ a).lt_of_ne' htv
    let M : κ → κ → ℝ := fun a c ↦
      if p a = 0 then q c
      else (if c = a then min (p a) (q a) else 0) / p a + ex a / p a * (df c / tv)
    have hM_nonneg (a c : κ) : 0 ≤ M a c := by
      dsimp only [M]
      split_ifs with hpa hca
      · exact hq c
      · have hpa' : 0 < p a := (hp a).lt_of_ne' hpa
        have hmin : 0 ≤ min (p a) (q a) := le_min (hp a) (hq a)
        positivity
      · have hpa' : 0 < p a := (hp a).lt_of_ne' hpa
        positivity
    have hM_sum (a : κ) : ∑ c, M a c = 1 := by
      dsimp only [M]
      by_cases hpa : p a = 0
      · simp [hpa, hq1]
      · simp only [hpa, ↓reduceIte, sum_add_distrib, ← sum_div, ← mul_sum]
        rw [Fintype.sum_ite_eq' a fun _ ↦ min (p a) (q a), ← hsum_eq,
          div_self htv, mul_one, ← add_div,
          (excess_deficit_identities (p a) (q a)).2.2.1, div_self hpa]
    -- Whether `p a = 0` or `p a > 0`, `p a * M a c` takes the same polynomial form.
    have hpM (a c : κ) :
        p a * M a c = (if c = a then min (p c) (q c) else 0) + ex a * (df c / tv) := by
      dsimp only [M]
      by_cases hpa : p a = 0
      · have hex_a : ex a = 0 := max_eq_right (by linarith [hq a])
        split_ifs with hca
        · subst hca; simp [hpa, hex_a, hq c]
        · simp [hpa, hex_a]
      · simp only [hpa, ↓reduceIte]
        have : p a * ((if c = a then min (p a) (q a) else 0) / p a + ex a / p a * (df c / tv)) =
            (if c = a then min (p a) (q a) else 0) + ex a * (df c / tv) := by
          field_simp [hpa]
        rw [this]
        split_ifs with hca
        · subst hca; rfl
        · rfl
    have hM_marg (c : κ) : ∑ a, p a * M a c = q c := by
      simp_rw [hpM]
      rw [sum_add_distrib, Fintype.sum_ite_eq c fun _ ↦ min (p c) (q c), ← sum_mul,
        show ∑ a, ex a = tv from rfl, mul_div_cancel₀ _ htv,
        (excess_deficit_identities (p c) (q c)).2.2.2.1]
    have hM_diag (a : κ) : p a * M a a = min (p a) (q a) := by
      simp only [hpM, ↓reduceIte]
      have hzero : ex a * df a = 0 := (excess_deficit_identities (p a) (q a)).2.2.2.2
      calc min (p a) (q a) + ex a * (df a / tv)
          = min (p a) (q a) + ex a * df a / tv := by ring
        _ = min (p a) (q a) := by rw [hzero, zero_div, add_zero]
    refine ⟨M, hM_nonneg, hM_sum, hM_marg, hM_diag, ?_⟩
    have hterm (a : κ) : p a * (1 - M a a) = ex a := by
      calc p a * (1 - M a a) = p a - p a * M a a := by ring
        _ = p a - min (p a) (q a) := by rw [hM_diag]
        _ = ex a := by linarith [(excess_deficit_identities (p a) (q a)).2.2.1]
    simp_rw [hterm]
    linarith

/-- Every entry of a row-stochastic nonnegative vector lies in `[0, 1]`. -/
private theorem le_one_of_nonneg_of_sum_eq_one {M : κ → ℝ} (h₀ : ∀ c, 0 ≤ M c)
    (h₁ : ∑ c, M c = 1) (c : κ) : M c ≤ 1 :=
  (single_le_sum (fun b _ ↦ h₀ b) (mem_univ c)).trans_eq h₁

/-- Under the concentration hypothesis, the ambient set `Z` is nonempty when `κ` is nonempty. -/
private theorem card_pos_of_concentration [Nonempty κ] {Z : Finset ι} {m : ℕ} {a : ℝ}
    (h : 2 * (m + 1 : ℕ) * Fintype.card κ * exp (-2 * a ^ 2 / #Z) < 1) : 0 < #Z := by
  by_contra! hZ
  have hZ0 : #Z = 0 := Nat.eq_zero_of_le_zero hZ
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  have hκ : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
  rw [hZ0, Nat.cast_zero, div_zero, exp_zero, mul_one] at h
  nlinarith

end TransitionCoupling

section CoupledColoring

variable [Fintype κ] [DecidableEq κ]

/-- Splitting a filtered count along the fibers of an auxiliary coloring `y : ι → κ`. -/
private theorem card_filter_eq_sum_fiber (s : Finset ι) (y : ι → κ) (P : ι → Prop)
    [DecidablePred P] :
    #{e ∈ s | P e} = ∑ b, #{e ∈ {e ∈ s | y e = b} | P e} := by
  rw [card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ ↦ mem_univ _]
  refine sum_congr rfl fun b _ ↦ congr_arg card ?_
  ext e
  simp [and_comm, and_left_comm]

/-- **Coupled coloring of low discrepancy.** Let `Z` be a finite set colored by `y : ι → κ`, let
`q : κ → ℝ` be a probability distribution on `κ`, and let `T : I → Finset ι` be a finite family of
test sets of size at most `#Z`. If `2 * (card I + 1) * card κ * exp (-2 a² / #Z) < 1` for some
`a > 0`, then there is a coloring `x : ι → κ` that:

1. edits fewer than `(1 / 2) * ∑ c, |#{e ∈ Z | y e = c} - q c * #Z| + card κ * a` points of `Z`;
2. on every test set `T i` and color `c`, deviates from `q c * #(T i)` by less than `card κ * a`
   plus the sum over `b : κ` of the fiber discrepancies
   `|#{e ∈ T i | y e = b} - (#{e ∈ Z | y e = b} / #Z) * #(T i)|`. -/
theorem exists_coupled_coloring_abs_card_filter_sub_lt (Z : Finset ι) (y : ι → κ)
    {q : κ → ℝ} (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) {I : Type*} [Fintype I]
    (T : I → Finset ι) (hT : ∀ i, #(T i) ≤ #Z) {a : ℝ} (ha : 0 < a)
    (hconc : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ * exp (-2 * a ^ 2 / #Z) < 1) :
    ∃ x : ι → κ,
      (#{e ∈ Z | x e ≠ y e} : ℝ) <
        (1 / 2) * (∑ c, |(#{e ∈ Z | y e = c} : ℝ) - q c * #Z|) + Fintype.card κ * a ∧
      ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - q c * #(T i)| <
        Fintype.card κ * a +
          ∑ b, |(#{e ∈ T i | y e = b} : ℝ) - (#{e ∈ Z | y e = b} : ℝ) / #Z * #(T i)| := by
  have : Nonempty κ := by
    by_contra! hκ
    simp at hq1
  have hZpos : 0 < #Z := card_pos_of_concentration hconc
  have hZcast : (0 : ℝ) < #Z := Nat.cast_pos.2 hZpos
  -- Empirical distribution `p` of `y` on `Z`, and its maximal coupling `M` to `q`.
  let p : κ → ℝ := fun b ↦ (#{e ∈ Z | y e = b} : ℝ) / #Z
  have hpZ (b : κ) : p b * #Z = #{e ∈ Z | y e = b} := div_mul_cancel₀ _ hZcast.ne'
  have hp0 (b : κ) : 0 ≤ p b := div_nonneg (Nat.cast_nonneg _) hZcast.le
  have hp1 : ∑ b, p b = 1 := by
    dsimp only [p]
    rw [← sum_div, ← Nat.cast_sum,
      ← card_eq_sum_card_fiberwise (f := y) (t := univ) fun _ _ ↦ mem_univ _, div_self hZcast.ne']
  obtain ⟨M, hM0, hM1, hMmarg, -, hMtv⟩ := exists_transition_coupling hp0 hp1 hq hq1
  -- On each color fiber `b`, sample a low-discrepancy coloring `f b` from `M b`, testing both the
  -- full fiber in `Z` (`Option.none`) and its trace on each `T i` (`Option.some i`).
  let T' (b : κ) : Option I → Finset ι := fun
    | none => {e ∈ Z | y e = b}
    | some i => {e ∈ T i | y e = b}
  have hT'_le (b : κ) (o : Option I) : #(T' b o) ≤ #Z := by
    cases o with
    | none => exact card_filter_le _ _
    | some i => exact (card_filter_le _ _).trans (hT i)
  have hcard_opt : (Fintype.card (Option I) : ℝ) = (Fintype.card I + 1 : ℕ) := by
    rw [Fintype.card_option]
  have hexists (b : κ) :
      ∃ fb : ι → κ, ∀ o c, |(#{e ∈ T' b o | fb e = c} : ℝ) - M b c * #(T' b o)| < a :=
    exists_forall_abs_card_filter_sub_mul_card_lt (hM0 b) (hM1 b) (T' b) (hT'_le b) ha
      (by simpa only [hcard_opt] using hconc)
  choose f hf using hexists
  -- Stitch the fiber colorings together along `y`.
  refine ⟨fun e ↦ f (y e) e, ?_, ?_⟩
  · -- Edit bound: on fiber `b`, points keeping color `b` are within `a` of `M b b * #{y = b}`.
    have hfiber_edit (b : κ) :
        (#{e ∈ {e ∈ Z | y e = b} | f (y e) e ≠ y e} : ℝ) < p b * (1 - M b b) * #Z + a := by
      have hcongr : {e ∈ {e ∈ Z | y e = b} | f (y e) e ≠ y e} =
          {e ∈ T' b none | f b e ≠ b} :=
        filter_congr fun e he ↦ by simp [(mem_filter.1 he).2]
      have hpart := card_filter_add_card_filter_not (s := T' b none) fun e ↦ f b e = b
      have hkeep := (abs_lt.1 (hf b none b)).1
      have hZb : (#(T' b none) : ℝ) = p b * #Z := (hpZ b).symm
      rw [hcongr]
      have hpartR : (#{e ∈ T' b none | f b e = b} : ℝ) + #{e ∈ T' b none | f b e ≠ b} =
          #(T' b none) := by exact_mod_cast hpart
      rw [hZb] at hkeep hpartR
      linarith [show M b b * (p b * #Z) + p b * (1 - M b b) * #Z = p b * #Z by ring]
    have hsplit : (#{e ∈ Z | f (y e) e ≠ y e} : ℝ) =
        ∑ b, (#{e ∈ {e ∈ Z | y e = b} | f (y e) e ≠ y e} : ℝ) := by
      exact_mod_cast card_filter_eq_sum_fiber Z y fun e ↦ f (y e) e ≠ y e
    have htvZ : (∑ b, p b * (1 - M b b) * #Z) =
        (1 / 2) * ∑ c, |(#{e ∈ Z | y e = c} : ℝ) - q c * #Z| := by
      rw [← sum_mul, hMtv, mul_assoc, sum_mul]
      congr 1
      refine sum_congr rfl fun c _ ↦ ?_
      calc |p c - q c| * (#Z : ℝ)
          = |p c - q c| * |(#Z : ℝ)| := by rw [abs_of_pos hZcast]
        _ = |(p c - q c) * #Z| := (abs_mul _ _).symm
        _ = |(#{e ∈ Z | y e = c} : ℝ) - q c * #Z| := by rw [sub_mul, hpZ]
    rw [hsplit]
    calc (∑ b, (#{e ∈ {e ∈ Z | y e = b} | f (y e) e ≠ y e} : ℝ))
        < ∑ b, (p b * (1 - M b b) * #Z + a) :=
          sum_lt_sum_of_nonempty univ_nonempty fun b _ ↦ hfiber_edit b
      _ = (∑ b, p b * (1 - M b b) * #Z) + Fintype.card κ * a := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      _ = (1 / 2) * (∑ c, |(#{e ∈ Z | y e = c} : ℝ) - q c * #Z|) + Fintype.card κ * a := by
          rw [htvZ]
  · -- Test-set discrepancy: sum the concentration error and the scaled fiber error of `y`.
    intro i c
    have hsplit : (#{e ∈ T i | f (y e) e = c} : ℝ) =
        ∑ b, (#{e ∈ T' b (some i) | f b e = c} : ℝ) := by
      rw [card_filter_eq_sum_fiber (T i) y fun e ↦ f (y e) e = c, Nat.cast_sum]
      refine sum_congr rfl fun b _ ↦ ?_
      congr 2
      exact filter_congr fun e he ↦ by simp [(mem_filter.1 he).2]
    have hqc : q c * #(T i) = ∑ b, M b c * (p b * #(T i)) := by
      rw [← hMmarg c, sum_mul]
      exact sum_congr rfl fun b _ ↦ by ring
    have hterm (b : κ) :
        |(#{e ∈ T' b (some i) | f b e = c} : ℝ) - M b c * (p b * #(T i))| <
          a + |(#{e ∈ T i | y e = b} : ℝ) - p b * #(T i)| := by
      have h₁ := hf b (some i) c
      have hMle : M b c ≤ 1 := le_one_of_nonneg_of_sum_eq_one (hM0 b) (hM1 b) c
      have h₂ : |M b c * (#(T' b (some i)) : ℝ) - M b c * (p b * #(T i))| ≤
          |(#{e ∈ T i | y e = b} : ℝ) - p b * #(T i)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (hM0 b c)]
        exact mul_le_of_le_one_left (abs_nonneg _) hMle
      calc |(#{e ∈ T' b (some i) | f b e = c} : ℝ) - M b c * (p b * #(T i))|
          ≤ |(#{e ∈ T' b (some i) | f b e = c} : ℝ) - M b c * #(T' b (some i))| +
              |M b c * #(T' b (some i)) - M b c * (p b * #(T i))| := abs_sub_le _ _ _
        _ < a + |(#{e ∈ T i | y e = b} : ℝ) - p b * #(T i)| := add_lt_add_of_lt_of_le h₁ h₂
    rw [hsplit, hqc, ← sum_sub_distrib]
    calc |∑ b, ((#{e ∈ T' b (some i) | f b e = c} : ℝ) - M b c * (p b * #(T i)))|
        ≤ ∑ b, |(#{e ∈ T' b (some i) | f b e = c} : ℝ) - M b c * (p b * #(T i))| :=
          abs_sum_le_sum_abs _ _
      _ < ∑ b, (a + |(#{e ∈ T i | y e = b} : ℝ) - p b * #(T i)|) :=
          sum_lt_sum_of_nonempty univ_nonempty fun b _ ↦ hterm b
      _ = Fintype.card κ * a +
            ∑ b, |(#{e ∈ T i | y e = b} : ℝ) - (#{e ∈ Z | y e = b} : ℝ) / #Z * #(T i)| := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]

/-- **Coupled coloring under a uniform fiber-discrepancy bound.** If each color fiber of `y` has
discrepancy at most `d` on every test set `T i` relative to its empirical density on `Z`, then the
coupled coloring `x` from `TauCeti.exists_coupled_coloring_abs_card_filter_sub_lt` has discrepancy
strictly less than `card κ * (a + d)` on every test set `T i`. -/
theorem exists_coupled_coloring_abs_card_filter_sub_lt_of_le (Z : Finset ι) (y : ι → κ)
    {q : κ → ℝ} (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) {I : Type*} [Fintype I]
    (T : I → Finset ι) (hT : ∀ i, #(T i) ≤ #Z) {a d : ℝ} (ha : 0 < a)
    (hd : ∀ i b, |(#{e ∈ T i | y e = b} : ℝ) - (#{e ∈ Z | y e = b} : ℝ) / #Z * #(T i)| ≤ d)
    (hconc : 2 * (Fintype.card I + 1 : ℕ) * Fintype.card κ * exp (-2 * a ^ 2 / #Z) < 1) :
    ∃ x : ι → κ,
      (#{e ∈ Z | x e ≠ y e} : ℝ) <
        (1 / 2) * (∑ c, |(#{e ∈ Z | y e = c} : ℝ) - q c * #Z|) + Fintype.card κ * a ∧
      ∀ i c, |(#{e ∈ T i | x e = c} : ℝ) - q c * #(T i)| < Fintype.card κ * (a + d) := by
  obtain ⟨x, hedit, hdisc⟩ :=
    exists_coupled_coloring_abs_card_filter_sub_lt Z y hq hq1 T hT ha hconc
  refine ⟨x, hedit, fun i c ↦ (hdisc i c).trans_le ?_⟩
  calc Fintype.card κ * a +
        ∑ b, |(#{e ∈ T i | y e = b} : ℝ) - (#{e ∈ Z | y e = b} : ℝ) / #Z * #(T i)|
      ≤ Fintype.card κ * a + ∑ _b : κ, d := add_le_add_right (sum_le_sum fun b _ ↦ hd i b) _
    _ = Fintype.card κ * (a + d) := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

end CoupledColoring

end TauCeti
