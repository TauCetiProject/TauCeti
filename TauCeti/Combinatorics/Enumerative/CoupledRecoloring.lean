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

Let `x₀ : ι → κ` be a coloring of a set `ι` into a finite palette `κ`, let `S` be a finite subset
of `ι`, and let `p` be a target probability distribution on `κ`. A fresh random coloring of `S`
with distribution `p` gives every test set `T i ⊆ S` color counts close to `p c' * #(T i)`,
by `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`, at the cost of disagreeing with `x₀` on
a constant fraction of `S` even when the empirical color counts of `x₀` on `S` are already close
to `p`.

This file couples the new coloring to `x₀` along a maximal-coupling transition kernel on `κ`. Each
color class `S_c = {e ∈ S | x₀ e = c}` is recolored independently: when `S_c` has at most the
target mass `p c * #S`, all points of `S_c` keep color `c`; when `S_c` has surplus mass
`#S_c - p c * #S > 0`, a fraction `p c * #S / #S_c` keeps color `c` and the surplus is distributed
across deficit colors proportionally to `max (p c' * #S - #S_{c'}) 0`. Applying
`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt` on each fiber `S_c` simultaneously controls
both the number of points of `S` that change color and the color counts on every test set `T i`:

* the number of edited points on `S` is at most the total-variation count
  `(∑ c, |#{e ∈ S | x₀ e = c} - p c * #S|) / 2` plus `card κ * a`;
* on each test set `T i ⊆ S`, the count of every color `c'` deviates from `p c' * #(T i)` by at
  most `card κ * a` plus the sum over `c` of the empirical discrepancies of `x₀` on `T i` relative
  to `S`.

In regular-approximation arguments, `x₀` is already quasi-random on `S` while its density on `S`
must be shifted slightly to match a coarse block or polyad density `p`; the coupled recoloring
realizes the target density `p` on all test sets while editing only the density-shift mass plus the
sampling slack.

## Main results

* `TauCeti.exists_coupled_recoloring_abs_card_filter_sub_le`: a recoloring of `S` coupled to `x₀`
  with total-variation edit count and controlled discrepancy on a finite family of subsets of `S`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
* T. Lindvall, *Lectures on the Coupling Method*, Wiley (1992), §I.5 (maximal coupling).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), §13.1.
-/

public section

open Finset Real

namespace TauCeti

variable {ι κ : Type*} [Fintype κ]

section Kernel

variable (m p : κ → ℝ)

/-- Total deficit `∑ b, max (p b - m b) 0` between target masses `p` and empirical masses `m`. -/
private def couplingDeficit : ℝ :=
  ∑ b, max (p b - m b) 0

open Classical in
/-- Maximal-coupling transition probability from color `c` to color `c'` taking mass vector `m` to
mass vector `p` of equal total mass. -/
private noncomputable def couplingKernel (c c' : κ) : ℝ :=
  if m c ≤ p c then
    if c' = c then 1 else 0
  else
    (if c' = c then p c / m c else 0) +
      ((m c - p c) / m c) * (max (p c' - m c') 0 / couplingDeficit m p)

private theorem couplingDeficit_eq_surplus (hsum : ∑ b, m b = ∑ b, p b) :
    couplingDeficit m p = ∑ b, max (m b - p b) 0 := by
  have hpoint (b : κ) : max (p b - m b) 0 - max (m b - p b) 0 = p b - m b := by
    rcases le_total (m b) (p b) with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), sub_zero]
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
      ring
  have hzero : ∑ b, (max (p b - m b) 0 - max (m b - p b) 0) = 0 := by
    rw [sum_congr rfl fun b _ ↦ hpoint b, sum_sub_distrib, hsum, sub_self]
  rw [sum_sub_distrib, sub_eq_zero] at hzero
  exact hzero

private theorem couplingDeficit_eq_half_sum_abs (hsum : ∑ b, m b = ∑ b, p b) :
    ∑ b, max (m b - p b) 0 = (∑ b, |m b - p b|) / 2 := by
  have hpoint (b : κ) : max (m b - p b) 0 + max (p b - m b) 0 = |m b - p b| := by
    rcases le_total (p b) (m b) with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), add_zero,
        abs_of_nonneg (sub_nonneg.2 h)]
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h), zero_add,
        abs_of_nonpos (sub_nonpos.2 h)]
      ring
  have hadd : ∑ b, max (m b - p b) 0 + couplingDeficit m p = ∑ b, |m b - p b| := by
    rw [couplingDeficit, ← sum_add_distrib]
    exact sum_congr rfl fun b _ ↦ hpoint b
  rw [couplingDeficit_eq_surplus m p hsum] at hadd
  linarith

private theorem couplingDeficit_pos_of_lt (hsum : ∑ b, m b = ∑ b, p b) {c : κ} (hc : p c < m c) :
    0 < couplingDeficit m p := by
  rw [couplingDeficit_eq_surplus m p hsum]
  have hpos : 0 < max (m c - p c) 0 := lt_max_of_lt_left (sub_pos.2 hc)
  exact hpos.trans_le
    (single_le_sum (f := fun b ↦ max (m b - p b) 0) (fun _ _ ↦ le_max_right _ _) (mem_univ c))

private theorem couplingKernel_nonneg (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b)
    (c c' : κ) : 0 ≤ couplingKernel m p c c' := by
  classical
  unfold couplingKernel
  by_cases hle : m c ≤ p c
  · rw [ite_eq_left hle]
    split_ifs <;> norm_num
  · rw [ite_eq_right hle]
    have hlt : p c < m c := not_le.1 hle
    have hmc : 0 < m c := (hp c).trans_lt hlt
    have hD : 0 < couplingDeficit m p := couplingDeficit_pos_of_lt m p hsum hlt
    have h1 : 0 ≤ if c' = c then p c / m c else 0 := by
      split_ifs
      · exact div_nonneg (hp c) hmc.le
      · exact le_rfl
    have h2 : 0 ≤ (m c - p c) / m c * (max (p c' - m c') 0 / couplingDeficit m p) :=
      mul_nonneg (div_nonneg (sub_nonneg.2 hlt.le) hmc.le) (div_nonneg (le_max_right _ _) hD.le)
    exact add_nonneg h1 h2

private theorem sum_couplingKernel (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b) (c : κ) :
    ∑ c', couplingKernel m p c c' = 1 := by
  classical
  unfold couplingKernel
  by_cases hle : m c ≤ p c
  · simp [hle]
  · have hlt : p c < m c := not_le.1 hle
    have hmc : 0 < m c := (hp c).trans_lt hlt
    have hD : 0 < couplingDeficit m p := couplingDeficit_pos_of_lt m p hsum hlt
    simp only [hle, ↓reduceIte, sum_add_distrib, sum_ite_eq', mem_univ, ← mul_sum, ← sum_div]
    change p c / m c + (m c - p c) / m c * (couplingDeficit m p / couplingDeficit m p) = 1
    rw [div_self hD.ne', mul_one, ← add_div, add_sub_cancel, div_self hmc.ne']

private theorem couplingKernel_le_one (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, m b = ∑ b, p b)
    (c c' : κ) : couplingKernel m p c c' ≤ 1 := by
  rw [← sum_couplingKernel m p hp hsum c]
  exact single_le_sum (fun b _ ↦ couplingKernel_nonneg m p hp hsum c b) (mem_univ c')

private theorem mul_couplingKernel_self (hp : ∀ b, 0 ≤ p b) (c : κ) :
    m c * couplingKernel m p c c = min (m c) (p c) := by
  classical
  unfold couplingKernel
  by_cases hle : m c ≤ p c
  · simp [hle]
  · have hlt : p c < m c := not_le.1 hle
    have hmc : 0 < m c := (hp c).trans_lt hlt
    have hmax : max (p c - m c) 0 = 0 := max_eq_right (sub_nonpos.2 hlt.le)
    simp only [hle, ↓reduceIte, hmax, zero_div, mul_zero, add_zero, min_eq_right hlt.le]
    exact mul_div_cancel₀ (p c) hmc.ne'

private theorem sum_mul_couplingKernel (hp : ∀ b, 0 ≤ p b)
    (hsum : ∑ b, m b = ∑ b, p b) (c' : κ) :
    ∑ c, m c * couplingKernel m p c c' = p c' := by
  classical
  have hterm (c : κ) : m c * couplingKernel m p c c' =
      (if c' = c then min (m c) (p c) else 0) +
        max (m c - p c) 0 *
          (if couplingDeficit m p = 0 then 0 else max (p c' - m c') 0 / couplingDeficit m p) := by
    unfold couplingKernel
    by_cases hle : m c ≤ p c
    · rw [ite_eq_left hle, min_eq_left hle, max_eq_right (sub_nonpos.2 hle), zero_mul, add_zero]
      split_ifs <;> ring
    · have hlt : p c < m c := not_le.1 hle
      have hmc : 0 < m c := (hp c).trans_lt hlt
      have hD : 0 < couplingDeficit m p := couplingDeficit_pos_of_lt m p hsum hlt
      rw [ite_eq_right hle, ite_eq_right hD.ne', min_eq_right hlt.le,
        max_eq_left (sub_nonneg.2 hlt.le), mul_add]
      congr 1
      · split_ifs
        · exact mul_div_cancel₀ (p c) hmc.ne'
        · ring
      · rw [← mul_assoc, mul_div_cancel₀ _ hmc.ne']
  simp only [hterm, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte, ← sum_mul,
    ← couplingDeficit_eq_surplus m p hsum]
  by_cases hD : couplingDeficit m p = 0
  · rw [ite_eq_left hD, mul_zero, add_zero]
    have hle1 : p c' - m c' ≤ 0 :=
      (le_max_left _ 0).trans <|
        (single_le_sum (f := fun b ↦ max (p b - m b) 0) (fun _ _ ↦ le_max_right _ _)
          (mem_univ c')).trans_eq hD
    have hle2 : m c' - p c' ≤ 0 :=
      (le_max_left _ 0).trans <|
        (single_le_sum (f := fun b ↦ max (m b - p b) 0) (fun _ _ ↦ le_max_right _ _)
          (mem_univ c')).trans_eq ((couplingDeficit_eq_surplus m p hsum).symm.trans hD)
    have heq : m c' = p c' := by linarith
    simp [heq]
  · rw [ite_eq_right hD, mul_div_cancel₀ _ hD]
    rcases le_total (m c') (p c') with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.2 h)]
      ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.2 h), add_zero]

end Kernel

open Classical in
/-- **Coupled low-discrepancy recoloring.** Let `x₀ : ι → κ` be a coloring, `S` a finite subset of
`ι`, `p` a probability distribution on `κ`, and `T : I → Finset ι` a finite family of subsets of
`S`. If `2 * (card I + 1) * card κ * exp (-2 a² / #S) < 1` for some `a > 0`, then there is a
coloring `x : ι → κ` agreeing with `x₀` outside `S` such that:

* the number of edited points on `S` is at most
  `(∑ c, |#{e ∈ S | x₀ e = c} - p c * #S|) / 2 + card κ * a`;
* on every test set `T i` and for every color `c'`, `#{e ∈ T i | x e = c'}` is within `card κ * a`
  plus the sum of empirical discrepancies of `x₀` on `T i` of `p c' * #(T i)`. -/
theorem exists_coupled_recoloring_abs_card_filter_sub_le (S : Finset ι) (x₀ : ι → κ) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {I : Type*} [Fintype I] (T : I → Finset ι)
    (hT : ∀ i, T i ⊆ S) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #S) < 1) :
    ∃ x : ι → κ, (∀ e ∉ S, x e = x₀ e) ∧
      (#{e ∈ S | x e ≠ x₀ e} : ℝ) ≤
        (∑ c, |(#{e ∈ S | x₀ e = c} : ℝ) - p c * #S|) / 2 + Fintype.card κ * a ∧
      ∀ i c', |(#{e ∈ T i | x e = c'} : ℝ) - p c' * #(T i)| ≤
        Fintype.card κ * a +
          ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - (#{e ∈ S | x₀ e = c} : ℝ) / #S * #(T i)| := by
  classical
  have hκ : 0 < Fintype.card κ := by
    by_contra! h0
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 (Nat.eq_zero_of_le_zero h0)
    simp at hp1
  have hSpos : 0 < #S := by
    by_contra! h0
    have hS0 : #S = 0 := Nat.eq_zero_of_le_zero h0
    have hge : (1 : ℝ) ≤ 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #S) := by
      rw [hS0, Nat.cast_zero, div_zero, exp_zero, mul_one]
      have : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 hκ
      have : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      nlinarith
    exact h.not_ge hge
  have hSposR : (0 : ℝ) < #S := Nat.cast_pos.2 hSpos
  let Sc (c : κ) : Finset ι := {e ∈ S | x₀ e = c}
  let m (c : κ) : ℝ := #(Sc c)
  let P (c : κ) : ℝ := p c * #S
  have hP_nonneg (c : κ) : 0 ≤ P c := mul_nonneg (hp c) hSposR.le
  have hSc_disj : ((univ : Finset κ) : Set κ).PairwiseDisjoint Sc := fun c₁ _ c₂ _ hne ↦
    disjoint_left.2 fun e he₁ he₂ ↦ hne ((mem_filter.1 he₁).2.symm.trans (mem_filter.1 he₂).2)
  have hSc_union : univ.biUnion Sc = S := by
    ext e
    simp [Sc]
  have hm_sum : ∑ c, m c = #S := by
    dsimp [m]
    rw [← Nat.cast_sum, ← card_biUnion hSc_disj, hSc_union]
  have hP_sum : ∑ c, P c = #S := by
    dsimp [P]
    rw [← sum_mul, hp1, one_mul]
  have hmP_sum : ∑ c, m c = ∑ c, P c := hm_sum.trans hP_sum.symm
  -- Sample an independent recoloring on each fiber `Sc c`, testing `Sc c` itself (`none`) and all
  -- intersections `T i ∩ Sc c` (`some i`).
  let Topt (c : κ) : Option I → Finset ι
    | none => Sc c
    | some i => T i ∩ Sc c
  have hTopt_le (c : κ) (o : Option I) : #(Topt c o) ≤ #S := by
    cases o with
    | none => exact card_le_card (filter_subset _ S)
    | some i => exact card_le_card (inter_subset_right.trans (filter_subset _ S))
  have hub : 2 * Fintype.card (Option I) * Fintype.card κ * exp (-2 * a ^ 2 / #S) < 1 := by
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    exact h
  have hex (c : κ) : ∃ y : ι → κ, ∀ o c',
      |(#{e ∈ Topt c o | y e = c'} : ℝ) - couplingKernel m P c c' * #(Topt c o)| < a :=
    exists_forall_abs_card_filter_sub_mul_card_lt (couplingKernel_nonneg m P hP_nonneg hmP_sum c)
      (sum_couplingKernel m P hP_nonneg hmP_sum c) (Topt c) (hTopt_le c) ha hub
  choose y hy using hex
  let x (e : ι) : κ := if e ∈ S then y (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ ite_eq_right he, ?_, ?_⟩
  · -- Bound the number of edited points on `S` via the complement `{e ∈ S | x e = x₀ e}`.
    have hkeep_union : {e ∈ S | x e = x₀ e} = univ.biUnion fun c ↦ {e ∈ Sc c | y c e = c} := by
      ext e
      simp only [mem_filter, mem_biUnion, mem_univ, true_and, Sc, x]
      constructor
      · rintro ⟨heS, hxe⟩
        rw [ite_eq_left heS] at hxe
        exact ⟨x₀ e, ⟨heS, rfl⟩, hxe⟩
      · rintro ⟨c, ⟨heS, rfl⟩, hyc⟩
        rw [ite_eq_left heS]
        exact ⟨heS, hyc⟩
    have hkeep_disj : ((univ : Finset κ) : Set κ).PairwiseDisjoint
        (fun c ↦ {e ∈ Sc c | y c e = c}) :=
      fun c₁ hc₁ c₂ hc₂ hne ↦ (hSc_disj hc₁ hc₂ hne).mono (filter_subset _ _) (filter_subset _ _)
    have hpart : #{e ∈ S | x e ≠ x₀ e} + #{e ∈ S | x e = x₀ e} = #S := by
      rw [add_comm]
      exact card_filter_add_card_filter_not fun e ↦ x e = x₀ e
    have hedits : (#{e ∈ S | x e ≠ x₀ e} : ℝ) =
        ∑ c, (m c - (#{e ∈ Sc c | y c e = c} : ℝ)) := by
      have h1 : (#{e ∈ S | x e ≠ x₀ e} : ℝ) = #S - #{e ∈ S | x e = x₀ e} :=
        eq_sub_of_add_eq (by exact_mod_cast hpart)
      rw [h1, hkeep_union, card_biUnion hkeep_disj, Nat.cast_sum, ← hm_sum, ← sum_sub_distrib]
    have hfiber (c : κ) :
        m c - (#{e ∈ Sc c | y c e = c} : ℝ) ≤ max (m c - P c) 0 + a := by
      have hnone := (abs_lt.1 (hy c none c)).1
      dsimp [Topt] at hnone
      have hself : couplingKernel m P c c * #(Sc c) = min (m c) (P c) := by
        rw [mul_comm]
        exact mul_couplingKernel_self m P hP_nonneg c
      have hminmax : m c - min (m c) (P c) = max (m c - P c) 0 := by
        rcases le_total (m c) (P c) with hle | hle
        · rw [min_eq_left hle, sub_self, max_eq_right (sub_nonpos.2 hle)]
        · rw [min_eq_right hle, max_eq_left (sub_nonneg.2 hle)]
      linarith
    calc (#{e ∈ S | x e ≠ x₀ e} : ℝ)
        ≤ ∑ c, (max (m c - P c) 0 + a) := by
          rw [hedits]
          exact sum_le_sum fun c _ ↦ hfiber c
      _ = (∑ c, max (m c - P c) 0) + Fintype.card κ * a := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      _ = (∑ c, |m c - P c|) / 2 + Fintype.card κ * a := by
          rw [couplingDeficit_eq_half_sum_abs m P hmP_sum]
  · -- Bound the color count of `c'` on `T i` by decomposing along `T i ∩ Sc c`.
    intro i c'
    have hTi_union : {e ∈ T i | x e = c'} =
        univ.biUnion fun c ↦ {e ∈ T i ∩ Sc c | y c e = c'} := by
      ext e
      simp only [mem_filter, mem_biUnion, mem_univ, true_and, mem_inter, Sc, x]
      constructor
      · rintro ⟨heT, hxe⟩
        have heS : e ∈ S := hT i heT
        rw [ite_eq_left heS] at hxe
        exact ⟨x₀ e, ⟨heT, heS, rfl⟩, hxe⟩
      · rintro ⟨c, ⟨heT, heS, rfl⟩, hyc⟩
        rw [ite_eq_left heS]
        exact ⟨heT, hyc⟩
    have hTi_disj : ((univ : Finset κ) : Set κ).PairwiseDisjoint
        (fun c ↦ {e ∈ T i ∩ Sc c | y c e = c'}) :=
      fun c₁ hc₁ c₂ hc₂ hne ↦ (hSc_disj hc₁ hc₂ hne).mono
        (filter_subset _ _ |>.trans inter_subset_right)
        (filter_subset _ _ |>.trans inter_subset_right)
    have hcount : (#{e ∈ T i | x e = c'} : ℝ) =
        ∑ c, (#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) := by
      rw [hTi_union, card_biUnion hTi_disj, Nat.cast_sum]
    have htarget : p c' * #(T i) =
        ∑ c, couplingKernel m P c c' * (m c / #S * #(T i)) := by
      have hmP := sum_mul_couplingKernel m P hP_nonneg hmP_sum c'
      have hp_eq : p c' = (∑ c, m c * couplingKernel m P c c') / #S := by
        rw [hmP]
        dsimp [P]
        exact (mul_div_cancel_right₀ (p c') hSposR.ne').symm
      rw [hp_eq, div_mul_eq_mul_div, sum_mul, sum_div]
      refine sum_congr rfl fun c _ ↦ ?_
      ring
    have hTi_Sc (c : κ) : T i ∩ Sc c = {e ∈ T i | x₀ e = c} := by
      ext e
      simp only [mem_inter, mem_filter, Sc]
      exact ⟨fun ⟨heT, _, hc⟩ ↦ ⟨heT, hc⟩, fun ⟨heT, hc⟩ ↦ ⟨heT, hT i heT, hc⟩⟩
    rw [hcount, htarget, ← sum_sub_distrib]
    calc |∑ c, ((#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) -
            couplingKernel m P c c' * (m c / #S * #(T i)))|
        ≤ ∑ c, |(#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) -
            couplingKernel m P c c' * (m c / #S * #(T i))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, (a + |(#{e ∈ T i | x₀ e = c} : ℝ) - m c / #S * #(T i)|) := by
          refine sum_le_sum fun c _ ↦ ?_
          have hsome := (hy c (some i) c').le
          dsimp [Topt] at hsome
          have hK0 : 0 ≤ couplingKernel m P c c' :=
            couplingKernel_nonneg m P hP_nonneg hmP_sum c c'
          have hK1 : couplingKernel m P c c' ≤ 1 :=
            couplingKernel_le_one m P hP_nonneg hmP_sum c c'
          have hsplit : (#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) -
              couplingKernel m P c c' * (m c / #S * #(T i)) =
            ((#{e ∈ T i ∩ Sc c | y c e = c'} : ℝ) - couplingKernel m P c c' * #(T i ∩ Sc c)) +
              couplingKernel m P c c' * ((#(T i ∩ Sc c) : ℝ) - m c / #S * #(T i)) := by ring
          rw [hsplit]
          refine (abs_add_le _ _).trans (add_le_add hsome ?_)
          rw [abs_mul, abs_of_nonneg hK0, hTi_Sc c]
          exact mul_le_of_le_one_left (abs_nonneg _) hK1
      _ = Fintype.card κ * a +
            ∑ c, |(#{e ∈ T i | x₀ e = c} : ℝ) - m c / #S * #(T i)| := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]

end TauCeti
