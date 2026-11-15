/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
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
distribution on `κ`. Resampling all of `Ω` independently from `p` achieves the target densities
on every test set (`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`), but may recolor a
constant fraction of `Ω` even when the empirical distribution `q` of `x₀` on `Ω` is already
close to `p`.

This file constructs a coupled recoloring that edits essentially the minimum possible number of
points—half the `ℓ¹` distance between the empirical counts and `p · #Ω`—while still achieving
the target densities `p` on every test set:

* Deficit and exact color classes (`q c ≤ p c`) are left untouched.
* Each excess color class `Ω_c` (`q c > p c`) is recolored independently according to the
  transition distribution `π_c` that keeps color `c` with probability `p c / q c` and distributes
  the remaining `(q c - p c) / q c` mass across the deficit colors proportionally to their
  deficits `max (p d - q d) 0`.

Applying `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt` on each excess class to the
restricted test sets `T i ∩ Ω_c` together with `Ω_c` itself gives a deterministic coloring `x`
agreeing with `x₀` outside `Ω` that edits at most
`(∑ c, |#{e ∈ Ω | x₀ e = c} - p c * #Ω|) / 2 + card κ * a` points and whose color counts on
every `T i` lie within `card κ * (a + b)` of `p c * #(T i)`
(`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`).

## Main results

* `TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`: coupled low-discrepancy recoloring
  toward a target distribution with total-variation edit bound.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.2 (coupled edge-modification in strong regularity).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.3 (regular approximation via coupled recoloring).
-/

public section

open Finset Real

namespace TauCeti

section Helpers

variable {κ : Type*} [DecidableEq κ]

/-- The transition distribution from an excess color `c` (`p c < q c`) toward `p`: keep `c` with
probability `p c / q c` and send the excess proportionally to `max (p d - q d) 0`. -/
private noncomputable def excessTransition (p q : κ → ℝ) (Δ : ℝ) (c d : κ) : ℝ :=
  (if d = c then p c / q c else 0) + (q c - p c) / q c * (max (p d - q d) 0 / Δ)

private theorem excessTransition_nonneg {p q : κ → ℝ} {Δ : ℝ} {c : κ}
    (hpc : 0 ≤ p c) (hqc : p c < q c) (hΔ : 0 ≤ Δ) (d : κ) :
    0 ≤ excessTransition p q Δ c d := by
  have hq0 : 0 < q c := hpc.trans_lt hqc
  have hsub : 0 ≤ q c - p c := sub_nonneg.2 hqc.le
  unfold excessTransition
  refine add_nonneg ?_ (mul_nonneg (div_nonneg hsub hq0.le) (div_nonneg (le_max_right _ _) hΔ))
  split_ifs <;> positivity

private theorem excessTransition_self {p q : κ → ℝ} {Δ : ℝ} {c : κ} (hqc : p c < q c) :
    excessTransition p q Δ c c = p c / q c := by
  have hmax : max (p c - q c) 0 = 0 := max_eq_right (by linarith)
  simp [excessTransition, hmax]

variable [Fintype κ]

private theorem sum_excessTransition {p q : κ → ℝ} {Δ : ℝ} {c : κ}
    (hpc : 0 ≤ p c) (hqc : p c < q c) (hΔdef : Δ = ∑ d, max (p d - q d) 0) (hΔ : 0 < Δ) :
    ∑ d, excessTransition p q Δ c d = 1 := by
  have hq0 : q c ≠ 0 := (hpc.trans_lt hqc).ne'
  unfold excessTransition
  rw [sum_add_distrib, Fintype.sum_ite_eq', ← mul_sum, ← sum_div, ← hΔdef, div_self hΔ.ne',
    mul_one, ← add_div, add_sub_cancel, div_self hq0]

private theorem excessTransition_le_one {p q : κ → ℝ} {Δ : ℝ} {c : κ}
    (hpc : 0 ≤ p c) (hqc : p c < q c) (hΔdef : Δ = ∑ d, max (p d - q d) 0) (hΔ : 0 < Δ)
    (d : κ) :
    excessTransition p q Δ c d ≤ 1 := by
  rw [← sum_excessTransition hpc hqc hΔdef hΔ]
  exact single_le_sum (fun d' _ ↦ excessTransition_nonneg hpc hqc hΔ.le d') (mem_univ d)

/-- Weighted by the source frequencies `q c`, the coupled transitions from excess colors plus the
untouched deficit colors reconstruct `p d` for every target color `d`. -/
private theorem sum_coupledTargetWeight {p q : κ → ℝ} {Δ : ℝ}
    (hp : ∀ c, 0 ≤ p c) (hpq : ∑ c, p c = ∑ c, q c) (hΔdef : Δ = ∑ d, max (p d - q d) 0)
    (d : κ) :
    (∑ c, if p c < q c then excessTransition p q Δ c d * q c
      else if d = c then q c else 0) = p d := by
  have hbal : ∑ c, (p c - q c) = 0 := by rw [sum_sub_distrib, sub_eq_zero.2 hpq]
  have hΔalt : Δ = ∑ c, max (q c - p c) 0 := by
    rw [hΔdef, ← sum_max_neg_eq_sum_max univ _ hbal]
    simp only [neg_sub]
  have hΔ0 : 0 ≤ Δ := hΔdef ▸ sum_nonneg fun _ _ ↦ le_max_right _ _
  have hterm (c : κ) :
      (if p c < q c then excessTransition p q Δ c d * q c else if d = c then q c else 0) =
        (if d = c then min (q c) (p c) else 0) +
          max (q c - p c) 0 * (max (p d - q d) 0 / Δ) := by
    by_cases hlt : p c < q c
    · have hq0 : q c ≠ 0 := ((hp c).trans_lt hlt).ne'
      simp only [hlt, ↓reduceIte, min_eq_right hlt.le, max_eq_left (sub_nonneg.2 hlt.le)]
      unfold excessTransition
      rcases eq_or_ne d c with rfl | hne
      · simp only [↓reduceIte]; field_simp
      · simp only [hne, ↓reduceIte, zero_add]; field_simp
    · have hle : q c ≤ p c := not_lt.1 hlt
      simp only [hlt, ↓reduceIte, min_eq_left hle, max_eq_right (sub_nonpos.2 hle), zero_mul,
        add_zero]
  simp_rw [hterm]
  rw [sum_add_distrib, Fintype.sum_ite_eq, ← sum_mul, ← hΔalt]
  obtain hΔz | hΔpos := hΔ0.eq_or_lt
  · have hpd : p d ≤ q d := by
      have : max (p d - q d) 0 ≤ Δ := hΔdef ▸
        single_le_sum (f := fun b ↦ max (p b - q b) (0 : ℝ)) (fun _ _ ↦ le_max_right _ 0)
          (mem_univ d)
      linarith [le_max_left (p d - q d) 0]
    have hqd : q d ≤ p d := by
      have : max (q d - p d) 0 ≤ Δ := hΔalt ▸
        single_le_sum (f := fun b ↦ max (q b - p b) (0 : ℝ)) (fun _ _ ↦ le_max_right _ 0)
          (mem_univ d)
      linarith [le_max_left (q d - p d) 0]
    simp [le_antisymm hqd hpd]
  · rw [mul_div_cancel₀ _ hΔpos.ne']
    rcases le_total (q d) (p d) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.2 h)]; ring
    · rw [min_eq_right h, max_eq_right (sub_nonpos.2 h)]; ring

/-- Draw a low-discrepancy recoloring on an excess fiber `Ω_c`, or keep `c` on a deficit fiber. -/
private theorem exists_fiber_recoloring {ι : Type*} (Ω : Finset ι) (x₀ : ι → κ)
    {p q : κ → ℝ} {Δ : ℝ} (hp : ∀ c, 0 ≤ p c) (hN : (0 : ℝ) < #Ω)
    (hqdef : ∀ c, q c = (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω)
    (hΔdef : Δ = ∑ d, max (p d - q d) 0) (hΔalt : Δ = ∑ c, max (q c - p c) 0)
    {I : Type*} [Fintype I] (T : I → Finset ι) (hT : ∀ i, T i ⊆ Ω) {a : ℝ} (ha : 0 < a)
    (h : 2 * (Fintype.card I + 1) * Fintype.card κ * exp (-2 * a ^ 2 / #Ω) < 1) (c : κ) :
    ∃ y : ι → κ, (¬p c < q c → y = fun _ ↦ c) ∧
      (p c < q c →
        |(#{e ∈ Ω | x₀ e = c ∧ y e = c} : ℝ) - p c * #Ω| < a ∧
        ∀ i d, |(#{e ∈ T i | x₀ e = c ∧ y e = d} : ℝ) -
          excessTransition p q Δ c d * #{e ∈ T i | x₀ e = c}| < a) := by
  by_cases hlt : p c < q c
  · have hΔpos : 0 < Δ := by
      have hle : max (q c - p c) 0 ≤ Δ := hΔalt ▸
        single_le_sum (f := fun b ↦ max (q b - p b) (0 : ℝ)) (fun _ _ ↦ le_max_right _ 0)
          (mem_univ c)
      linarith [le_max_left (q c - p c) 0]
    let S : Option I → Finset ι :=
      fun o ↦ o.elim {e ∈ Ω | x₀ e = c} fun i ↦ {e ∈ T i | x₀ e = c}
    have hS (o : Option I) : #(S o) ≤ #Ω := by
      cases o with
      | none => exact card_filter_le _ _
      | some i => exact (card_filter_le _ _).trans (card_le_card (hT i))
    have hcard : (Fintype.card (Option I) : ℝ) = Fintype.card I + 1 := by simp
    obtain ⟨y, hy⟩ := exists_forall_abs_card_filter_sub_mul_card_lt
      (p := excessTransition p q Δ c)
      (excessTransition_nonneg (hp c) hlt hΔpos.le)
      (sum_excessTransition (hp c) hlt hΔdef hΔpos) S hS ha (by simpa [hcard] using h)
    refine ⟨y, fun h' ↦ (h' hlt).elim, fun _ ↦ ⟨?_, fun i d ↦ ?_⟩⟩
    · have h0 : |(#{e ∈ {e ∈ Ω | x₀ e = c} | y e = c} : ℝ) -
          excessTransition p q Δ c c * #{e ∈ Ω | x₀ e = c}| < a := by
        simpa only [S, Option.elim_none] using hy none c
      have hqc : excessTransition p q Δ c c * #{e ∈ Ω | x₀ e = c} = p c * #Ω := by
        have hq0 : q c ≠ 0 := ((hp c).trans_lt hlt).ne'
        have hcardc : (#{e ∈ Ω | x₀ e = c} : ℝ) = q c * #Ω := by
          rw [hqdef c, div_mul_cancel₀ _ hN.ne']
        rw [excessTransition_self hlt, hcardc, ← mul_assoc, div_mul_cancel₀ _ hq0]
      rw [filter_filter, hqc] at h0
      exact h0
    · have hi : |(#{e ∈ {e ∈ T i | x₀ e = c} | y e = d} : ℝ) -
          excessTransition p q Δ c d * #{e ∈ T i | x₀ e = c}| < a := by
        simpa only [S, Option.elim_some] using hy (some i) d
      rwa [filter_filter] at hi
  · exact ⟨fun _ ↦ c, fun _ ↦ rfl, fun h' ↦ (hlt h').elim⟩

/-- Sum the fiberwise edit bounds over `c : κ` and convert `∑ c, max (q c - p c) 0` into half the
`ℓ¹` count deviation via `Finset.two_nsmul_sum_max_eq_sum_abs`. -/
private theorem card_edit_le_of_fiber_recoloring {ι : Type*} [DecidableEq ι]
    (Ω : Finset ι) (x₀ : ι → κ) (y : κ → ι → κ) {p q : κ → ℝ} {a : ℝ} (ha : 0 < a)
    (hN : (0 : ℝ) < #Ω) (hqdef : ∀ c, q c = (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω)
    (hbal : ∑ c, (q c - p c) = 0)
    (hy_def : ∀ c, ¬p c < q c → y c = fun _ ↦ c)
    (hy_stay : ∀ c, p c < q c →
      |(#{e ∈ Ω | x₀ e = c ∧ y c e = c} : ℝ) - p c * #Ω| < a) :
    (#{e ∈ Ω | (if e ∈ Ω then y (x₀ e) e else x₀ e) ≠ x₀ e} : ℝ) ≤
      (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a := by
  set x : ι → κ := fun e ↦ if e ∈ Ω then y (x₀ e) e else x₀ e
  have hfib : #{e ∈ Ω | x e ≠ x₀ e} = ∑ c, #{e ∈ Ω | x₀ e = c ∧ y c e ≠ c} := by
    rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
    refine sum_congr rfl fun c _ ↦ congrArg card (ext fun e ↦ ?_)
    by_cases he : e ∈ Ω <;> simp +contextual [x, he, and_comm]
  have hbound (c : κ) :
      (#{e ∈ Ω | x₀ e = c ∧ y c e ≠ c} : ℝ) ≤ max (q c - p c) 0 * #Ω + a := by
    by_cases hlt : p c < q c
    · have hpart :
          #{e ∈ Ω | x₀ e = c ∧ y c e ≠ c} + #{e ∈ Ω | x₀ e = c ∧ y c e = c} =
            #{e ∈ Ω | x₀ e = c} := by
        simpa only [filter_filter, add_comm] using
          card_filter_add_card_filter_not (s := {e ∈ Ω | x₀ e = c}) (fun e ↦ y c e = c)
      have hpartR :
          (#{e ∈ Ω | x₀ e = c ∧ y c e ≠ c} : ℝ) + #{e ∈ Ω | x₀ e = c ∧ y c e = c} =
            q c * #Ω := by
        rw [← Nat.cast_add, hpart, hqdef c, div_mul_cancel₀ _ hN.ne']
      rw [max_eq_left (sub_nonneg.2 hlt.le)]
      linarith [(abs_lt.1 (hy_stay c hlt)).1]
    · rw [hy_def c hlt]
      simp only [ne_self_iff_false, and_false, filter_false, card_empty, Nat.cast_zero]
      exact add_nonneg (mul_nonneg (le_max_right _ _) hN.le) ha.le
  have h2 := two_nsmul_sum_max_eq_sum_abs univ (fun c ↦ q c - p c) hbal
  rw [nsmul_eq_mul, Nat.cast_ofNat] at h2
  have hhalf : ∑ c, max (q c - p c) 0 = (∑ c, |q c - p c|) / 2 := by linarith
  rw [hfib, Nat.cast_sum]
  calc (∑ c, (#{e ∈ Ω | x₀ e = c ∧ y c e ≠ c} : ℝ))
      ≤ ∑ c, (max (q c - p c) 0 * #Ω + a) := sum_le_sum fun c _ ↦ hbound c
    _ = (∑ c, max (q c - p c) 0) * #Ω + Fintype.card κ * a := by
        rw [sum_add_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
    _ = (∑ c, |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω|) / 2 + Fintype.card κ * a := by
        rw [hhalf, div_mul_eq_mul_div, sum_mul]
        congr 2
        refine sum_congr rfl fun c _ ↦ ?_
        calc |q c - p c| * #Ω = |(q c - p c) * #Ω| := by rw [abs_mul, abs_of_pos hN]
          _ = |(#{e ∈ Ω | x₀ e = c} : ℝ) - p c * #Ω| := by
              rw [sub_mul, hqdef c, div_mul_cancel₀ _ hN.ne']

end Helpers

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
  -- `#Ω > 0`, since for `Ω = ∅` the exponential in `h` is `1` and the product is at least `2`.
  have hΩpos : 0 < #Ω := by
    by_contra! hΩ0
    have hΩz : #Ω = 0 := Nat.eq_zero_of_le_zero hΩ0
    have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
    simp only [hΩz, Nat.cast_zero, div_zero, exp_zero, mul_one] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hN : (0 : ℝ) < #Ω := Nat.cast_pos.2 hΩpos
  set q : κ → ℝ := fun c ↦ (#{e ∈ Ω | x₀ e = c} : ℝ) / #Ω
  have hqsum : ∑ c, q c = 1 := by
    simp only [q, ← sum_div]
    rw [div_eq_one_iff_eq hN.ne', ← Nat.cast_sum,
      card_eq_sum_card_fiberwise (f := x₀) (t := (univ : Finset κ)) fun _ _ ↦ mem_univ _]
  have hbal_pq : ∑ c, (p c - q c) = 0 := by rw [sum_sub_distrib, hp1, hqsum, sub_self]
  have hbal_qp : ∑ c, (q c - p c) = 0 := by rw [sum_sub_distrib, hqsum, hp1, sub_self]
  set Δ : ℝ := ∑ d, max (p d - q d) 0 with hΔdef
  have hΔalt : Δ = ∑ c, max (q c - p c) 0 := by
    rw [hΔdef, ← sum_max_neg_eq_sum_max univ _ hbal_pq]
    simp only [neg_sub]
  choose y hy_def hy_exc using
    exists_fiber_recoloring Ω x₀ hp hN (fun _ ↦ rfl) hΔdef hΔalt T hT ha h
  let x : ι → κ := fun e ↦ if e ∈ Ω then y (x₀ e) e else x₀ e
  refine ⟨x, fun e he ↦ by simp [x, he],
    card_edit_le_of_fiber_recoloring Ω x₀ y ha hN (fun _ ↦ rfl) hbal_qp hy_def
      (fun c hlt ↦ (hy_exc c hlt).1),
    fun i d ↦ ?_⟩
  -- Decompose `{e ∈ T i | x e = d}` by `x₀ e = c` and sum the fiberwise errors `≤ a + b`.
  have hfib : #{e ∈ T i | x e = d} = ∑ c, #{e ∈ T i | x₀ e = c ∧ y c e = d} := by
    rw [card_eq_sum_card_fiberwise (f := x₀) (t := univ) fun _ _ ↦ mem_univ _]
    refine sum_congr rfl fun c _ ↦ congrArg card (ext fun e ↦ ?_)
    by_cases he : e ∈ T i
    · have heΩ : e ∈ Ω := hT i he
      simp +contextual [x, he, heΩ, and_comm]
    · simp [he]
  let μ (c : κ) : ℝ :=
    (if p c < q c then excessTransition p q Δ c d * q c else if d = c then q c else 0) * #(T i)
  have hμsum : ∑ c, μ c = p d * #(T i) := by
    simp only [μ, ← sum_mul]
    rw [sum_coupledTargetWeight hp (hp1.trans hqsum.symm) hΔdef d]
  have herr (c : κ) : |(#{e ∈ T i | x₀ e = c ∧ y c e = d} : ℝ) - μ c| ≤ a + b := by
    by_cases hlt : p c < q c
    · have hΔpos : 0 < Δ := by
        have hle : max (q c - p c) 0 ≤ Δ := hΔalt ▸
          single_le_sum (f := fun b ↦ max (q b - p b) (0 : ℝ)) (fun _ _ ↦ le_max_right _ 0)
            (mem_univ c)
        linarith [le_max_left (q c - p c) 0]
      have h1 := ((hy_exc c hlt).2 i d).le
      have hπ0 := excessTransition_nonneg (hp c) hlt hΔpos.le d
      have hπ1 := excessTransition_le_one (hp c) hlt hΔdef hΔpos d
      have h2 : |excessTransition p q Δ c d * #{e ∈ T i | x₀ e = c} - μ c| ≤ b := by
        simp only [μ, hlt, ↓reduceIte]
        rw [mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg hπ0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hπ1).trans (hx₀ i c)
      exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
    · simp only [μ, hlt, ↓reduceIte, hy_def c hlt]
      rcases eq_or_ne d c with rfl | hne
      · simpa only [↓reduceIte, and_true] using (hx₀ i d).trans (by linarith)
      · simp only [hne, ↓reduceIte, zero_mul, sub_zero, ne_comm.1 hne, and_false, filter_false,
          card_empty, Nat.cast_zero, abs_zero]
        exact add_nonneg ha.le hb
  rw [hfib, Nat.cast_sum, ← hμsum, ← sum_sub_distrib]
  calc |∑ c, ((#{e ∈ T i | x₀ e = c ∧ y c e = d} : ℝ) - μ c)|
      ≤ ∑ c, |(#{e ∈ T i | x₀ e = c ∧ y c e = d} : ℝ) - μ c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : κ, (a + b) := sum_le_sum fun c _ ↦ herr c
    _ = Fintype.card κ * (a + b) := by rw [sum_const, card_univ, nsmul_eq_mul]

end TauCeti
