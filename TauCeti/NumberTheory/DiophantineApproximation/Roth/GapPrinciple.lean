/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.ApproximationClass

import Mathlib.Algebra.Algebra.IsSimpleRing
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.SpecialFunctions.Log.MultiplicativeGap
import TauCeti.NumberTheory.Height.FundamentalInequality
import TauCeti.NumberTheory.Height.NumberField

/-!
# The strong gap principle for Roth's inequality over a number field

Let `K` be a number field, `F` a field extension of `K`, and fix finite sets `Sinf` of infinite
places and `Sfin` of finite places of `K`, at each such place `v` an absolute value `w v` of `F`
lying over `v` and a target `α v ∈ F`. Roth's inequality for `β ∈ K` with exponent `κ` is

`(∏ v ∈ Sinf, min 1 (w v (β - α v)) ^ mult v) * ∏ v ∈ Sfin, min 1 (w v (β - α v)) ≤ H(β) ^ (-κ)`,

with `H = mulHeight₁` the relative height. Its local factors are indexed by the disjoint union
`Sinf ⊕ Sfin` of the two sets of places (`NumberField.approxFactor`), and the class
`NumberField.approxClass` of `β` at side `1 / N` is the class `TauCeti.profileClass` of this
family: the cell of side `1 / N` containing its logarithmic profile, or a corner of the simplex
when `β` is one of the targets.

Two distinct solutions in one class are far apart in height. If `β ≠ β'` lie in one class with
`h(β) ≤ h(β')`, then, in absolute logarithmic heights,

`h(β') ≥ ((1 - |S| / N) κ - 1) h(β) - log 4`,

where `|S|` is the number of places. At every place the truncated distance `min 1 |β - β'|_v`
is at most the larger of the local factors of `β` and `β'`, times `2` at an infinite place, and
in one class both local factors are at most a power of `H(β)` fixed by the class. The
fundamental inequality for `β - β' ∈ K` bounds the product of the truncated distances below by
`H(β - β')⁻¹`, and `H(β - β') ≤ 2 ^ [K : ℚ] H(β) H(β')`. The class enters through the upper half of
Bombieri–Gubler (6.9), which bounds every local factor by a power of the product, and through
(6.10), which says that the exponents add up to at least `1 - |S| / N`.

For `c = (1 - |S| / N) κ - 1 > 1` the gap is multiplicative above a threshold, so the set of
solutions whose height lies in a window `(X, A X]` has `Set.ncard` at most
`⌈log A / log ((c + 1) / 2)⌉` times the number of classes. Since `Set.ncard` is `0` on infinite
sets, this does not prove that the set is finite; finiteness (from Northcott) is not proved here.

## Main results

* `NumberField.mulHeight₁_rpow_le_four_pow_mul_mulHeight₁_of_approxClass_eq`: the gap principle
  in relative multiplicative heights, `H(β) ^ ((1 - |S| / N) κ - 1) ≤ 4 ^ [K : ℚ] H(β')`.
* `NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq`: the strong gap principle in absolute
  logarithmic heights.
* `NumberField.ncard_setOf_absLogHeight₁_mem_Ioc_le`: the count of the solutions whose absolute
  logarithmic height lies in a window.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), Lemma 6.5.6 and Theorem 6.5.4.
* H. Davenport and K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika 2
  (1955).
* The statements follow Ralf Stephan's formalization `DiophantineApproximation/GapPrinciple.lean`
  and `DiophantineApproximation/CountingApproximations.lean` in `rwst/Subspace-Theorems` at
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Finset Real Height Module

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]
variable {Sinf : Finset (InfinitePlace K)} {Sfin : Finset (FinitePlace K)}
  (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)

/-! ### The gap principle -/

/-- At a place of `Sinf`, the truncated local factor of `β - β'`, with exponent `mult v`, is at
most `2 ^ mult v` times the larger of the local approximation factors of `β` and `β'`. -/
private theorem min_one_apply_sub_pow_le_inl (v : Sinf) [(w v.val.val).LiesOver v.val.val]
    (β β' : K) :
    min 1 (v.val (β - β')) ^ v.val.mult ≤ 2 ^ v.val.mult *
      max (approxFactor Sinf Sfin w α β (.inl v)) (approxFactor Sinf Sfin w α β' (.inl v)) := by
  set u := algebraMap K F β - α v.val.val
  set u' := algebraMap K F β' - α v.val.val
  have hsub : v.val (β - β') ≤ w v.val.val u + w v.val.val u' := by
    rw [InfinitePlace.coe_apply, ← AbsoluteValue.LiesOver.apply_algebraMap (w
        := w v.val.val) v.val.val,
      show algebraMap K F (β - β') = u - u' by simp [u, u']]
    exact (w v.val.val).sub_le_add u u'
  -- `min 1 (s + s') ≤ min 1 s + min 1 s'` for nonnegative `s` and `s'`.
  have hmin : min 1 (v.val (β - β')) ≤ 2 * max (min 1 (w v.val.val u)) (min 1 (w v.val.val u'))
      := by
    have := (w v.val.val).nonneg u
    have := (w v.val.val).nonneg u'
    grind
  have h₀ : 0 ≤ min 1 (w v.val.val u) := le_min zero_le_one (apply_nonneg _ _)
  have h₀' : 0 ≤ min 1 (w v.val.val u') := le_min zero_le_one (apply_nonneg _ _)
  rw [approxFactor_inl, approxFactor_inl, ← max_pow_of_nonneg h₀ h₀', ← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (apply_nonneg _ _)) hmin _

/-- At a place of `Sfin`, the truncated local factor of `β - β'` is at most the larger of the
local approximation factors of `β` and `β'`, since an absolute value over a finite place is
nonarchimedean. -/
private theorem min_one_apply_sub_le_inr (v : Sfin) [(w v.val.val).LiesOver v.val.val] (β β' : K) :
    min 1 (v.val (β - β')) ≤
      max (approxFactor Sinf Sfin w α β (.inr v)) (approxFactor Sinf Sfin w α β' (.inr v)) := by
  set u := algebraMap K F β - α v.val.val
  set u' := algebraMap K F β' - α v.val.val
  have hna : IsNonarchimedean (w v.val.val) :=
    AbsoluteValue.isNonarchimedean_of_liesOver (u := v.val.val) v.val.add_le
  have hsub : v.val (β - β') ≤ max (w v.val.val u) (w v.val.val u') := by
    rw [FinitePlace.coe_apply, ← AbsoluteValue.LiesOver.apply_algebraMap (w
        := w v.val.val) v.val.val,
      show algebraMap K F (β - β') = u + -u' by simp [u, u', sub_eq_add_neg]]
    simpa only [AbsoluteValue.map_neg] using hna u (-u')
  simp only [approxFactor_inr, ← min_max_distrib_left]
  exact min_le_min_left 1 hsub

/-- Under the hypotheses of the gap principle, the larger of the local approximation factors of
`β` and `β'` at a place is at most `H(β) ^ (-κ c / N)`, where `c` is the common class. -/
private theorem max_approxFactor_le {N : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) {β β' : K}
    (hβ : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ))
    (hβ' : ∏ a, approxFactor Sinf Sfin w α β' a ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : mulHeight₁ β ≤ mulHeight₁ β') (a : Sinf ⊕ Sfin) :
    max (approxFactor Sinf Sfin w α β a) (approxFactor Sinf Sfin w α β' a) ≤
      (mulHeight₁ β ^ (-κ)) ^ ((approxClass Sinf Sfin w α N β a : ℝ) / N) := by
  have hexp : 0 ≤ (approxClass Sinf Sfin w α N β a : ℝ) / N := by positivity
  have h₀ (γ : K) : 0 ≤ ∏ b, approxFactor Sinf Sfin w α γ b :=
    prod_nonneg fun b _ ↦ approxFactor_nonneg w α γ b
  refine max_le ?_ ?_
  · refine (TauCeti.le_rpow_profileClass_div N (approxFactor_nonneg w α β)
      (approxFactor_le_one w α β) a).trans ?_
    rw [← approxClass_def]
    exact rpow_le_rpow (h₀ β) hβ hexp
  · refine (TauCeti.le_rpow_profileClass_div N (approxFactor_nonneg w α β')
      (approxFactor_le_one w α β') a).trans ?_
    rw [← approxClass_def, ← hclass]
    refine (rpow_le_rpow (h₀ β') hβ' hexp).trans (rpow_le_rpow (by positivity) ?_ hexp)
    exact rpow_le_rpow_of_nonpos (mulHeight₁_pos β) hle (neg_nonpos.mpr hκ)

/-- The product over the places of the bounds of `max_approxFactor_le` is at most
`H(β) ^ (-(1 - |S| / N) κ)`, by (6.10). -/
private theorem prod_rpow_approxClass_le {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ) {β : K}
    (hβ : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ)) :
    ∏ a, (mulHeight₁ β ^ (-κ)) ^ ((approxClass Sinf Sfin w α N β a : ℝ) / N) ≤
      mulHeight₁ β ^ (-((1 - (#Sinf + #Sfin : ℝ) / N) * κ)) := by
  have hH := mulHeight₁_pos β
  rw [← rpow_sum_of_pos (rpow_pos_of_pos hH _), ← rpow_mul hH.le]
  rcases (one_le_mulHeight₁ β).eq_or_lt with hH1 | hH1
  · simp [← hH1]
  rcases hκ.eq_or_lt with rfl | hκ
  · simp
  refine rpow_le_rpow_of_exponent_le (one_le_mulHeight₁ β) ?_
  rw [neg_mul, neg_le_neg_iff, mul_comm]
  refine mul_le_mul_of_nonneg_left (le_of_lt ?_) hκ.le
  have hprod : ∏ a, approxFactor Sinf Sfin w α β a < 1 :=
    hβ.trans_lt (rpow_lt_one_of_one_lt_of_neg hH1 (neg_neg_of_pos hκ))
  simpa only [Fintype.card_sum, Fintype.card_coe, Nat.cast_add, approxClass_def] using
    TauCeti.one_sub_card_div_lt_sum_profileClass_div hN (approxFactor_nonneg w α β) hprod

/-- The fundamental inequality for `β - β'` under the hypotheses of the gap principle: the
local factors of `β - β'` at the places of `Sinf` and `Sfin` are bounded by those of `β` and
`β'`, which one class pins to powers of `H(β)`. -/
private theorem inv_mulHeight₁_sub_le
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ) {β β' : K} (hne : β ≠ β')
    (hβ : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ))
    (hβ' : ∏ a, approxFactor Sinf Sfin w α β' a ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : mulHeight₁ β ≤ mulHeight₁ β') :
    (mulHeight₁ (β - β'))⁻¹ ≤
      2 ^ finrank ℚ K * mulHeight₁ β ^ (-((1 - (#Sinf + #Sfin : ℝ) / N) * κ)) := by
  set B : Sinf ⊕ Sfin → ℝ := fun a ↦
    (mulHeight₁ β ^ (-κ)) ^ ((approxClass Sinf Sfin w α N β a : ℝ) / N)
  have hB₀ a : 0 ≤ B a := by positivity
  have hmax := max_approxFactor_le w α hκ hβ hβ' hclass hle
  have hinf : ∏ v ∈ Sinf, min 1 (v (β - β')) ^ v.mult ≤
      2 ^ finrank ℚ K * ∏ v : Sinf, B (.inl v) := by
    rw [← Finset.prod_coe_sort Sinf]
    calc ∏ v : Sinf, min 1 (v.val (β - β')) ^ v.val.mult
        ≤ ∏ v : Sinf, 2 ^ v.val.mult * B (.inl v) := by
          refine Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (le_min zero_le_one
            (apply_nonneg _ _)) _) fun v _ ↦ ?_
          have := hwInf v.val v.property
          exact (min_one_apply_sub_pow_le_inl w α v β β').trans
            (mul_le_mul_of_nonneg_left (hmax _) (by positivity))
      _ = 2 ^ (∑ v : Sinf, v.val.mult) * ∏ v : Sinf, B (.inl v) := by
          rw [prod_mul_distrib, prod_pow_eq_pow_sum]
      _ ≤ 2 ^ finrank ℚ K * ∏ v : Sinf, B (.inl v) := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two ?_)
            (prod_nonneg fun _ _ ↦ hB₀ _)
          rw [← InfinitePlace.sum_mult_eq, Finset.sum_coe_sort Sinf (fun v ↦ v.mult)]
          exact sum_le_sum_of_subset (subset_univ _)
  have hfin : ∏ v ∈ Sfin, min 1 (v (β - β')) ≤ ∏ v : Sfin, B (.inr v) := by
    rw [← Finset.prod_coe_sort Sfin]
    refine Finset.prod_le_prod₀ (fun v _ ↦ le_min zero_le_one (apply_nonneg _ _)) fun v _ ↦ ?_
    have := hwFin v.val v.property
    exact (min_one_apply_sub_le_inr w α v β β').trans (hmax _)
  refine (inv_mulHeight₁_le_prod_min_one_apply Sinf Sfin (sub_ne_zero.mpr hne)).trans ?_
  calc (∏ v ∈ Sinf, min 1 (v (β - β')) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v (β - β'))
      ≤ (2 ^ finrank ℚ K * ∏ v : Sinf, B (.inl v)) * ∏ v : Sfin, B (.inr v) :=
        mul_le_mul hinf hfin (prod_nonneg fun v _ ↦ le_min zero_le_one (apply_nonneg _ _))
          (by positivity [prod_nonneg fun v (_ : v ∈ univ) ↦ hB₀ (.inl v)])
    _ = 2 ^ finrank ℚ K * ∏ a, B a := by rw [Fintype.prod_sum_type, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prod_rpow_approxClass_le w α hN hκ hβ) (by positivity)

/-- **The gap principle in relative multiplicative heights.** Let `w v` lie over `v` at every
place of `Sinf` and `Sfin`, let `0 < N` and `0 ≤ κ`, and let `β ≠ β'` be two solutions of Roth's
inequality with exponent `κ` in one approximation class of side `1 / N`, with
`H(β) ≤ H(β')`. Then `H(β) ^ ((1 - |S| / N) κ - 1) ≤ 4 ^ [K : ℚ] H(β')`, where `|S|` is the number
of places of `Sinf` and `Sfin` and `H` is the relative height. -/
theorem mulHeight₁_rpow_le_four_pow_mul_mulHeight₁_of_approxClass_eq
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ) {β β' : K} (hne : β ≠ β')
    (hβ : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ))
    (hβ' : ∏ a, approxFactor Sinf Sfin w α β' a ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : mulHeight₁ β ≤ mulHeight₁ β') :
    mulHeight₁ β ^ ((1 - (#Sinf + #Sfin : ℝ) / N) * κ - 1) ≤
      4 ^ finrank ℚ K * mulHeight₁ β' := by
  set x := (1 - (#Sinf + #Sfin : ℝ) / N) * κ
  have hlow := inv_mulHeight₁_sub_le w α hwInf hwFin hN hκ hne hβ hβ' hclass hle
  have hup : mulHeight₁ (β - β') ≤ 2 ^ finrank ℚ K * mulHeight₁ β * mulHeight₁ β' := by
    simpa only [totalWeight_eq_finrank] using mulHeight₁_sub_le β β'
  have hH := mulHeight₁_pos β
  -- `1 = H(β - β') H(β - β')⁻¹`, bounded by the two estimates.
  have hone : 1 ≤ 4 ^ finrank ℚ K * mulHeight₁ β' * (mulHeight₁ β * mulHeight₁ β ^ (-x)) := by
    have h := mul_le_mul hup hlow (inv_nonneg.mpr (mulHeight₁_pos _).le) (by positivity)
    rw [mul_inv_cancel₀ (mulHeight₁_pos _).ne'] at h
    calc (1 : ℝ) ≤ _ := h
      _ = _ := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
  have hcancel : mulHeight₁ β ^ (x - 1) * (mulHeight₁ β * mulHeight₁ β ^ (-x)) = 1 := by
    rw [← mul_assoc, ← rpow_add_one hH.ne', ← rpow_add hH, show x - 1 + 1 + -x = 0 by ring,
      rpow_zero]
  calc mulHeight₁ β ^ (x - 1)
      ≤ mulHeight₁ β ^ (x - 1) * (4 ^ finrank ℚ K * mulHeight₁ β' *
          (mulHeight₁ β * mulHeight₁ β ^ (-x))) :=
        le_mul_of_one_le_right (by positivity) hone
    _ = 4 ^ finrank ℚ K * mulHeight₁ β' := by
        rw [mul_left_comm, hcancel, mul_one]

/-- **The strong gap principle** (Bombieri–Gubler, Lemma 6.5.6). Let `w v` lie over `v` at every
place of `Sinf` and `Sfin`, let `0 < N` and `0 ≤ κ`, and let `β ≠ β'` be two solutions of Roth's
inequality with exponent `κ` in one approximation class of side `1 / N`, with `h(β) ≤ h(β')` in
absolute logarithmic heights. Then `h(β') ≥ ((1 - |S| / N) κ - 1) h(β) - log 4`, where `|S|` is
the number of places of `Sinf` and `Sfin`. -/
theorem mul_absLogHeight₁_sub_le_of_approxClass_eq
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ) {β β' : K} (hne : β ≠ β')
    (hβ : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ))
    (hβ' : ∏ a, approxFactor Sinf Sfin w α β' a ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β') :
    ((1 - (#Sinf + #Sfin : ℝ) / N) * κ - 1) * absLogHeight₁ β - log 4 ≤ absLogHeight₁ β' := by
  have hd : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  set x := (1 - (#Sinf + #Sfin : ℝ) / N) * κ
  have h := log_le_log (by positivity)
    (mulHeight₁_rpow_le_four_pow_mul_mulHeight₁_of_approxClass_eq w α hwInf hwFin hN hκ hne hβ
      hβ' hclass (absLogHeight₁_le_absLogHeight₁_iff.mp hle))
  rw [log_rpow (mulHeight₁_pos β), log_mul (by positivity) (mulHeight₁_pos β').ne', log_pow] at h
  rw [absLogHeight₁_eq_div, absLogHeight₁_eq_div, logHeight₁_eq_log_mulHeight₁,
    logHeight₁_eq_log_mulHeight₁]
  field_simp
  linarith

/-- **The count of solutions in a window** (Bombieri–Gubler, proof of Theorem 6.5.4). Let `w v`
lie over `v` at every place of `Sinf` and `Sfin`, let `0 < N` and `0 ≤ κ`, and write
`c + 1 = (1 - |S| / N) κ` with `c > 1`, where `|S|` is the number of places. For
`X ≥ log 16 / (c - 1)`, the solutions of Roth's inequality with exponent `κ` whose absolute
logarithmic height lies in `(X, A X]` form a set whose `Set.ncard` is at most
`⌈log A / log ((c + 1) / 2)⌉` times `(N + |S|).choose |S|`. Since `Set.ncard` is `0` on infinite
sets, the statement does not say that this set is finite. -/
theorem ncard_setOf_absLogHeight₁_mem_Ioc_le
    (hwInf : ∀ v ∈ Sinf, (w v.val).LiesOver v.val) (hwFin : ∀ v ∈ Sfin, (w v.val).LiesOver v.val)
    {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ) (hc : 2 < (1 - (#Sinf + #Sfin : ℝ) / N) * κ)
    {X A : ℝ} (hX : log 16 / ((1 - (#Sinf + #Sfin : ℝ) / N) * κ - 2) ≤ X) :
    {β : K | ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ) ∧
        absLogHeight₁ β ∈ Set.Ioc X (A * X)}.ncard ≤
      ⌈log A / log ((1 - (#Sinf + #Sfin : ℝ) / N) * κ / 2)⌉₊ *
        (N + (#Sinf + #Sfin)).choose (#Sinf + #Sfin) := by
  set x := (1 - (#Sinf + #Sfin : ℝ) / N) * κ
  set s := {β : K | ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ) ∧
    absLogHeight₁ β ∈ Set.Ioc X (A * X)}
  have h16 : log 16 = 2 * log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, log_pow]
    norm_num
  have hmem {β : K} (hβ : β ∈ s) : ∏ a, approxFactor Sinf Sfin w α β a ≤ mulHeight₁ β ^ (-κ) ∧
      absLogHeight₁ β ∈ Set.Ioc X (A * X) := hβ
  have hX₀ : 0 < X := (div_pos (log_pos (by norm_num)) (by linarith)).trans_le hX
  refine (Set.ncard_le_ceil_mul_ncard_of_gap absLogHeight₁ (approxClass Sinf Sfin w α N) hX₀
    (by linarith : 1 < x / 2) (fun β hβ ↦ (hmem hβ).2) fun β hβ β' hβ' hne hclass hle ↦ ?_).trans
    (Nat.mul_le_mul_left _ (ncard_image_approxClass_le w α s N))
  have hgap := mul_absLogHeight₁_sub_le_of_approxClass_eq w α hwInf hwFin hN hκ hne (hmem hβ).1
    (hmem hβ').1 hclass hle
  -- Above the threshold, `(x - 2) h(β) ≥ log 16 = 2 log 4`, so the additive loss is absorbed.
  have hlarge : log 16 ≤ (x - 2) * absLogHeight₁ β := by
    rw [div_le_iff₀ (by linarith)] at hX
    nlinarith [(hmem hβ).2.1]
  nlinarith

end NumberField
