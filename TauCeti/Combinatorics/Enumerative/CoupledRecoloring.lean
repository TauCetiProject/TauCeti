/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Coupled recolorings with small discrepancy and few edits

Let `x₀ : ι → κ` be a coloring of a finite set `Ω` whose color classes already have small
discrepancy on a finite family of test sets `T i ⊆ Ω`, and let `p` be a target probability
distribution on `κ`. Resampling all of `Ω` independently from `p` approximates the target color
counts `p c * #(T i)` within a prescribed discrepancy bound on every test set
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`), but may recolor a constant fraction
of `Ω` even when the empirical distribution `q` of `x₀` on `Ω` is already close to `p`.

To preserve agreement with `x₀` while adjusting densities to `p` and retaining quasi-randomness on
test sets, we couple `q` to `p` through a maximal-coupling Markov transition kernel
`M : κ → κ → ℝ` (`TauCeti.exists_transition_coupling`): each color `a` keeps itself with mass
`min (q a) (p a)` and redistributes its excess `max (q a - p a) 0` across colors proportionally to
their deficits `max (p c - q c) 0`. Applying `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`
on each color fiber `Ω_a` of `x₀` with distribution `M a` to the restricted test sets `T i ∩ Ω_a`
together with `Ω_a` itself yields a deterministic coloring `x` agreeing with `x₀` outside `Ω`
(`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_lt`) that simultaneously:

* edits strictly fewer than `(∑ c, |#{e ∈ Ω | x₀ e = c} - p c * #Ω|) / 2 + card κ * a` points of
  `Ω`, matching half the `ℓ¹` distance between `q` and `p` up to concentration slack; and
* controls the discrepancy `|#{e ∈ T i | x e = d} - p d * #(T i)|` on every test set `T i` by
  `card κ * a` plus the sum over `c : κ` of the fiber discrepancies of `x₀` on `T i`.

Specializing to a uniform fiber-discrepancy bound `b` gives
`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`.

## Main results

* `TauCeti.exists_transition_coupling`: maximal-coupling Markov transition kernel between two
  probability distributions on a finite type.
* `TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_lt`: coupled low-discrepancy recoloring
  toward a target distribution with total-variation edit bound and fiberwise discrepancy control.
* `TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`: specialization under a uniform
  fiber-discrepancy bound.

## References

* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), §I.2 (maximal coupling of discrete
  distributions).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.2 (coupled edge-modification in strong regularity).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 and Lemma 4.2.
-/

public section

open Finset Real

namespace TauCeti

section TransitionCoupling

variable {κ : Type*} [Fintype κ]

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
  have hbal : ∑ a, (p a - q a) = 0 := by rw [sum_sub_distrib, hp1, hq1, sub_self]
  have hmin_ex (a : κ) : min (p a) (q a) + ex a = p a := by
    have hmax : ex a = max (p a) (q a) - q a := by
      simpa only [ex, sub_self] using max_sub_sub_right (p a) (q a) (q a)
    linarith [min_add_max (p a) (q a)]
  have hmin_df (c : κ) : min (p c) (q c) + df c = q c := by
    have hmax : df c = max (q c) (p c) - p c := by
      simpa only [df, sub_self] using max_sub_sub_right (q c) (p c) (p c)
    linarith [min_add_max (q c) (p c), min_comm (p c) (q c)]
  have hsum_eq : ∑ a, ex a = ∑ c, df c := by
    simpa only [ex, df, neg_sub] using (sum_max_neg_eq_sum_max univ (fun a ↦ p a - q a) hbal).symm
  set tv := ∑ a, ex a with htv_def
  have htv_abs : 2 * tv = ∑ a, |p a - q a| := by
    simpa only [tv, ex, nsmul_eq_mul, Nat.cast_ofNat] using
      two_nsmul_sum_max_eq_sum_abs univ (fun a ↦ p a - q a) hbal
  -- When `tv = 0`, `p = q` everywhere; otherwise redistribute excess proportionally to deficit.
  by_cases htv : tv = 0
  · have hpq (a : κ) : p a = q a := by
      have hex_zero : ex a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hex₀ b) (mem_univ a)).trans_eq htv) (hex₀ a)
      have hdf_zero : df a = 0 :=
        le_antisymm ((single_le_sum (fun b _ ↦ hdf₀ b) (mem_univ a)).trans_eq
          (hsum_eq.symm.trans htv)) (hdf₀ a)
      linarith [hmin_ex a, hmin_df a]
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
          div_self htv, mul_one, ← add_div, hmin_ex a, div_self hpa]
    -- Whether `p a = 0` or `p a > 0`, `p a * M a c` takes the same form.
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
      rw [sum_add_distrib, Fintype.sum_ite_eq c fun _ ↦ min (p c) (q c), ← sum_mul, ← htv_def,
        mul_div_cancel₀ _ htv, hmin_df c]
    have hM_diag (a : κ) : p a * M a a = min (p a) (q a) := by
      simp only [hpM, ↓reduceIte]
      have hzero : ex a * df a = 0 := by
        rcases le_total (p a) (q a) with h | h
        · simp [ex, max_eq_right (sub_nonpos.2 h)]
        · simp [df, max_eq_right (sub_nonpos.2 h)]
      calc min (p a) (q a) + ex a * (df a / tv)
          = min (p a) (q a) + ex a * df a / tv := by ring
        _ = min (p a) (q a) := by rw [hzero, zero_div, add_zero]
    refine ⟨M, hM_nonneg, hM_sum, hM_marg, hM_diag, ?_⟩
    have hterm (a : κ) : p a * (1 - M a a) = ex a := by
      calc p a * (1 - M a a) = p a - p a * M a a := by ring
        _ = p a - min (p a) (q a) := by rw [hM_diag]
        _ = ex a := by linarith [hmin_ex a]
    simp_rw [hterm]
    linarith

end TransitionCoupling

/-- **Coupled low-discrepancy recoloring (fiberwise discrepancy bound).** Let `x₀ : ι → κ` be a
coloring of a finite set `Ω`, let `p` be a probability distribution on `κ`, and let
`T : I → Finset ι` be a finite family of test subsets of `Ω`. If
`2 * (card I + 1) * card κ * exp (-2 a² / #Ω) < 1` for some `a > 0`, then there is a coloring
`x : ι → κ` agreeing with `x₀` outside `Ω` that:

1. edits strictly fewer than `(∑ c, |#{e ∈ Ω | x₀ e = c} - p c * #Ω|) / 2 + card κ * a` points
   of `Ω`; and
2. on every test set `T i` and color `d`, deviates from `p d * #(T i)` by strictly less than
   `card κ * a` plus the sum over `c : κ` of the fiber discrepancies
   `|#{e ∈ T i | x₀ e = c} - (#{e ∈ Ω | x₀ e = c} / #Ω) * #(T i)|`. -/
theorem exists_recoloring_abs_card_filter_sub_mul_card_lt {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (Ω : Finset ι) (x₀ : ι → κ) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {I : Type*} [Fintype I] (T : I → Finset ι) (hT : ∀ i, T i ⊆ Ω)
    {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #Ω) < 1) :
    ∃ x : ι → κ, (∀ e ∉ Ω, x e = x₀ e) ∧
      (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) <
        (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a ∧
      ∀ i d, |(#{e ∈ T i | x e = d} : ℝ) - p d * #(T i)| <
        Fintype.card κ * a +
          ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω * #(T i)| := by
  classical
  have : Nonempty κ := by by_contra! hκ; simp at hp1
  have hΩpos : 0 < #Ω := by
    by_contra! hΩ0
    have hΩz : #Ω = 0 := Nat.eq_zero_of_le_zero hΩ0
    have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
    simp only [hΩz, Nat.cast_zero, div_zero, exp_zero, mul_one] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hN : (0 : ℝ) < #Ω := Nat.cast_pos.2 hΩpos
  -- Empirical law `q` of `x₀` on `Ω` and its maximal-coupling transition kernel `M` to `p`.
  let q : κ → ℝ := fun c ↦ (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω
  have hqΩ (c : κ) : q c * #Ω = #{e ∈ Ω | x₀ e = c} := div_mul_cancel₀ _ hN.ne'
  have hq0 (c : κ) : 0 ≤ q c := div_nonneg (Nat.cast_nonneg _) hN.le
  have hq1 : ∑ c, q c = 1 := by
    dsimp only [q]
    rw [← sum_div, ← Nat.cast_sum,
      ← card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _, div_self hN.ne']
  obtain ⟨M, hM0, hM1, hMmarg, -, hMtv⟩ := exists_transition_coupling hq0 hq1 hp hp1
  -- On each color fiber `c`, draw a low-discrepancy coloring `f c` from `M c`, testing both the
  -- full fiber in `Ω` (`Option.none`) and its trace on each `T i` (`Option.some i`).
  let T' (c : κ) : Option I → Finset ι := fun
    | none => {e ∈ Ω | x₀ e = c}
    | some i => {e ∈ T i | x₀ e = c}
  have hT'_le (c : κ) (o : Option I) : #(T' c o) ≤ #Ω := by
    cases o with
    | none => exact card_filter_le _ _
    | some i => exact (card_filter_le _ _).trans (card_le_card (hT i))
  have hcard_opt : (Fintype.card (Option I) : ℝ) = Fintype.card I + 1 := by simp
  have hexists (c : κ) :
      ∃ fc : ι → κ, ∀ o d, |(#{e ∈ T' c o | fc e = d} : ℝ) - M c d * #(T' c o)| < a :=
    exists_forall_abs_card_filter_sub_mul_card_lt (hM0 c) (hM1 c) (T' c) (hT'_le c) ha
      (by simpa only [hcard_opt] using h)
  choose f hf using hexists
  let x : ι → κ := fun e ↦ if e ∈ Ω then f (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ by simp [x, he], ?_, ?_⟩
  · -- Edit bound: on fiber `c`, points keeping color `c` are within `a` of `M c c * #{x₀ = c}`.
    have hfiber_edit (c : κ) :
        (#{e ∈ {e ∈ Ω | x₀ e = c} | x e ≠ x₀ e} : ℝ) < q c * (1 - M c c) * #Ω + a := by
      have hcongr : {e ∈ {e ∈ Ω | x₀ e = c} | x e ≠ x₀ e} = {e ∈ T' c none | f c e ≠ c} :=
        filter_congr fun e he ↦ by
          obtain ⟨heΩ, hxc⟩ := mem_filter.1 he
          simp [x, heΩ, hxc]
      have hpart := card_filter_add_card_filter_not (s := T' c none) fun e ↦ f c e = c
      have hkeep := (abs_lt.1 (hf c none c)).1
      have hΩc : (#(T' c none) : ℝ) = q c * #Ω := (hqΩ c).symm
      rw [hcongr]
      have hpartR : (#{e ∈ T' c none | f c e = c} : ℝ) + #{e ∈ T' c none | f c e ≠ c} =
          #(T' c none) := by exact_mod_cast hpart
      rw [hΩc] at hkeep hpartR
      have hring : M c c * (q c * #Ω) + q c * (1 - M c c) * #Ω = q c * #Ω := by ring
      linarith [hring]
    have hsplit : (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) =
        ∑ c, (#{e ∈ {e ∈ Ω | x₀ e = c} | x e ≠ x₀ e} : ℝ) := by
      rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
      exact congr_arg Nat.cast (sum_congr rfl fun c _ ↦
        congr_arg card (by ext; simp [and_right_comm]))
    have htvΩ : (∑ c, q c * (1 - M c c) * #Ω) =
        (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 := by
      rw [← sum_mul, hMtv, one_div_mul_eq_div, div_mul_eq_mul_div, sum_mul]
      congr 1
      refine sum_congr rfl fun c _ ↦ ?_
      calc |q c - p c| * (#Ω : ℝ)
          = |q c - p c| * |(#Ω : ℝ)| := by rw [abs_of_pos hN]
        _ = |(q c - p c) * #Ω| := (abs_mul _ _).symm
        _ = |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω| := by rw [sub_mul, hqΩ]
    rw [hsplit]
    calc (∑ c, (#{e ∈ {e ∈ Ω | x₀ e = c} | x e ≠ x₀ e} : ℝ))
        < ∑ c, (q c * (1 - M c c) * #Ω + a) :=
          sum_lt_sum_of_nonempty univ_nonempty fun c _ ↦ hfiber_edit c
      _ = (∑ c, q c * (1 - M c c) * #Ω) + Fintype.card κ * a := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      _ = (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a := by
          rw [htvΩ]
  · -- Test-set discrepancy: sum the concentration error and the scaled fiber error of `x₀`.
    intro i d
    have hsplit : (#{e ∈ T i | x e = d} : ℝ) =
        ∑ c, (#{e ∈ T' c (some i) | f c e = d} : ℝ) := by
      rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
      refine congr_arg Nat.cast (sum_congr rfl fun c _ ↦ congr_arg card ?_)
      ext e
      simp only [T', mem_filter]
      refine ⟨fun ⟨⟨he, hxe⟩, hxc⟩ ↦ ⟨⟨he, hxc⟩, ?_⟩,
        fun ⟨⟨he, hxc⟩, hfc⟩ ↦ ⟨⟨he, ?_⟩, hxc⟩⟩
      · have heΩ : e ∈ Ω := hT i he
        simpa [x, heΩ, hxc] using hxe
      · have heΩ : e ∈ Ω := hT i he
        simpa [x, heΩ, hxc] using hfc
    have hpd : p d * #(T i) = ∑ c, M c d * (q c * #(T i)) := by
      rw [← hMmarg d, sum_mul]
      exact sum_congr rfl fun c _ ↦ by ring
    have hterm (c : κ) :
        |(#{e ∈ T' c (some i) | f c e = d} : ℝ) - M c d * (q c * #(T i))| <
          a + |(#{e ∈ T i | x₀ e = c} : ℝ) - q c * #(T i)| := by
      have h₁ := hf c (some i) d
      have hMle : M c d ≤ 1 := (single_le_sum (fun b _ ↦ hM0 c b) (mem_univ d)).trans_eq (hM1 c)
      have h₂ : |M c d * (#(T' c (some i)) : ℝ) - M c d * (q c * #(T i))| ≤
          |(#{e ∈ T i | x₀ e = c} : ℝ) - q c * #(T i)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (hM0 c d)]
        exact mul_le_of_le_one_left (abs_nonneg _) hMle
      calc |(#{e ∈ T' c (some i) | f c e = d} : ℝ) - M c d * (q c * #(T i))|
          ≤ |(#{e ∈ T' c (some i) | f c e = d} : ℝ) - M c d * #(T' c (some i))| +
              |M c d * #(T' c (some i)) - M c d * (q c * #(T i))| := abs_sub_le _ _ _
        _ < a + |(#{e ∈ T i | x₀ e = c} : ℝ) - q c * #(T i)| := add_lt_add_of_lt_of_le h₁ h₂
    rw [hsplit, hpd, ← sum_sub_distrib]
    calc |∑ c, ((#{e ∈ T' c (some i) | f c e = d} : ℝ) - M c d * (q c * #(T i)))|
        ≤ ∑ c, |(#{e ∈ T' c (some i) | f c e = d} : ℝ) - M c d * (q c * #(T i))| :=
          abs_sum_le_sum_abs _ _
      _ < ∑ c, (a + |(#{e ∈ T i | x₀ e = c} : ℝ) - q c * #(T i)|) :=
          sum_lt_sum_of_nonempty univ_nonempty fun c _ ↦ hterm c
      _ = Fintype.card κ * a +
            ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω * #(T i)| := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]

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
    {a b : ℝ} (ha : 0 < a) (_hb : 0 ≤ b)
    (hx₀ : ∀ i c,
      |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω * #(T i)| ≤ b)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #Ω) < 1) :
    ∃ x : ι → κ, (∀ e ∉ Ω, x e = x₀ e) ∧
      (#{e ∈ Ω | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a ∧
      ∀ i d, |(#{e ∈ T i | x e = d} : ℝ) - p d * #(T i)| ≤ Fintype.card κ * (a + b) := by
  obtain ⟨x, hagree, hedit, hdisc⟩ :=
    exists_recoloring_abs_card_filter_sub_mul_card_lt Ω x₀ hp hp1 T hT ha h
  refine ⟨x, hagree, hedit.le, fun i d ↦ (hdisc i d).le.trans ?_⟩
  calc Fintype.card κ * a +
        ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω * #(T i)|
      ≤ Fintype.card κ * a + ∑ _c : κ, b := add_le_add_right (sum_le_sum fun c _ ↦ hx₀ i c) _
    _ = Fintype.card κ * (a + b) := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

end TauCeti
