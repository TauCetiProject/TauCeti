/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.LocalFactor

import TauCeti.NumberTheory.Height.FundamentalInequality
import TauCeti.NumberTheory.Height.NumberField

/-!
# The strong gap principle

Let `K` be a number field, `F` a field extension of `K`, and `Sinf`, `Sfin` finite sets of
infinite and finite places of `K`. At each place `v` of `Sinf ∪ Sfin` fix an absolute value `w v`
of `F` lying over `v` and a target `α v ∈ F`, and call `β ∈ K` a solution if

```text
(∏ v ∈ Sinf, min 1 (w v (β - α v)) ^ mult v) * ∏ v ∈ Sfin, min 1 (w v (β - α v)) ≤ H(β) ^ (-κ),
```

where `H` is Mathlib's relative height `Height.mulHeight₁` and `κ ≥ 0`. The **strong gap
principle** says that two distinct solutions in one approximation class
(`NumberField.approxClass`) are far apart in height: if `β ≠ β'` lie in one class of side `1 / N`
and `H(β) ≤ H(β')`, then

```text
H(β) ^ ((1 - |S| / N) κ - 1) ≤ 4 ^ [K : ℚ] · H(β'),
```

where `|S| = #Sinf + #Sfin`; that is, in absolute logarithmic heights,
`h(β') ≥ ((1 - |S| / N) κ - 1) h(β) - log 4`. For `κ > 2` and `N` large the factor
`(1 - |S| / N) κ - 1` exceeds `1`, so the heights of the solutions in one class grow
geometrically. This bounds the number of solutions in a range of heights without Roth's theorem.

The proof is the fundamental inequality for `β - β' ∈ K` over the places of `S`, against the
triangle inequality at each of them, which is ultrametric at the finite places: a place where
both `β` and `β'` are close to the target is one where `β - β'` is small, and the class makes the
two solutions close to the targets at the same places, to the same proportion of the total.

## Main results

* `NumberField.mulHeight₁_rpow_le_of_approxClass_eq`: the strong gap principle in relative
  multiplicative heights.
* `NumberField.mul_absLogHeight₁_sub_le_of_approxClass_eq`: the strong gap principle in absolute
  logarithmic heights.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 6.5.6.
* H. Davenport and K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika 2
  (1955), 160–167.
-/

public section

open Finset Real Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### The strong gap principle -/

variable {F : Type*} [Field F] [Algebra K F] {Sinf : Finset (InfinitePlace K)}
  {Sfin : Finset (FinitePlace K)} {w : AbsoluteValue K ℝ → AbsoluteValue F ℝ}
  {α : AbsoluteValue K ℝ → F}

/-- The local step of the strong gap principle: at a place of `S` where `β` and `β'` both have
local factor at most `B`, the truncated distance `min 1 |β - β'|_v`, weighted by `sPlaceWeight`,
is at most `B`, times `2 ^ mult v` at an infinite place. The factor `2 ^ mult v` comes from the
triangle inequality, which is ultrametric at a finite place. -/
private theorem min_one_apply_sub_pow_le {β β' : K} {s : ↥Sinf ⊕ ↥Sfin}
    (hw : (w (sPlaceAbsValue s)).LiesOver (sPlaceAbsValue s)) {B : ℝ}
    (hβ : approxFactor Sinf Sfin w α β s ≤ B) (hβ' : approxFactor Sinf Sfin w α β' s ≤ B) :
    min 1 (sPlaceAbsValue s (β - β')) ^ sPlaceWeight s ≤
      Sum.elim (fun v ↦ (2 : ℝ) ^ v.1.mult) (fun _ ↦ 1) s * B := by
  rw [approxFactor_def] at hβ hβ'
  -- Write `β - β'` as the difference of the two distances to the target `a`.
  set u := sPlaceAbsValue s
  set a := α u
  set p := min 1 (w u (algebraMap K F β - a))
  set q := min 1 (w u (algebraMap K F β' - a))
  have hΔ : u (β - β') = w u ((algebraMap K F β - a) - (algebraMap K F β' - a)) := by
    rw [sub_sub_sub_cancel_right, ← map_sub, AbsoluteValue.LiesOver.apply_algebraMap u]
  have h₀ : 0 ≤ min 1 (u (β - β')) := le_min zero_le_one (apply_nonneg _ _)
  have hmax : max p q ^ sPlaceWeight s ≤ B := by
    rcases max_choice p q with h | h <;> rw [h]
    exacts [hβ, hβ']
  rcases s with v | v
  · -- At an infinite place: `min 1 |β - β'|_v ≤ 2 max p q` by the triangle inequality.
    rw [sPlaceWeight_inl] at hmax ⊢
    have hle : min 1 (u (β - β')) ≤ 2 * max p q := by
      have htri := hΔ.trans_le ((w u).sub_le _ 0 _)
      simp only [sub_zero, zero_sub, AbsoluteValue.map_neg] at htri
      rcases le_or_gt 1 (w u (algebraMap K F β - a)) with hx | hx
      · linarith [min_le_left 1 (u (β - β')), le_max_left p q, (min_eq_left hx : p = 1)]
      rcases le_or_gt 1 (w u (algebraMap K F β' - a)) with hy | hy
      · linarith [min_le_left 1 (u (β - β')), le_max_right p q, (min_eq_left hy : q = 1)]
      linarith [min_le_right 1 (u (β - β')), le_max_left p q, le_max_right p q,
        (min_eq_right hx.le : p = _), (min_eq_right hy.le : q = _)]
    calc min 1 (u (β - β')) ^ v.1.mult
        ≤ (2 * max p q) ^ v.1.mult := pow_le_pow_left₀ h₀ hle _
      _ ≤ 2 ^ v.1.mult * B := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
  · -- At a finite place: `min 1 |β - β'|_v ≤ max p q` by the ultrametric inequality.
    have hu : IsNonarchimedean u := by
      rw [show u = v.1.1 from sPlaceAbsValue_inr v]
      exact fun x y ↦ FinitePlace.add_le v.1 x y
    have hw' : IsNonarchimedean (w u) := AbsoluteValue.isNonarchimedean_of_liesOver hu
    have hle : min 1 (u (β - β')) ≤ max p q := by
      have h : u (β - β') ≤ max (w u (algebraMap K F β - a)) (w u (algebraMap K F β' - a)) := by
        rw [hΔ, sub_eq_add_neg, ← (w u).map_neg (algebraMap K F β' - a)]
        exact hw' _ _
      exact (min_le_min_left 1 h).trans_eq (min_max_distrib_left _ _ _)
    rw [sPlaceWeight_inr, pow_one] at hmax ⊢
    rw [Sum.elim_inr, one_mul]
    exact hle.trans hmax

/-- The truncated distance between two elements of `K`, multiplied over the places of `S` and
weighted by `mult` at the infinite places, is at most `2 ^ [K : ℚ]` times the product of common
bounds `B s` for their local factors. -/
private theorem prod_min_one_apply_sub_le (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) {β β' : K} {B : ↥Sinf ⊕ ↥Sfin → ℝ}
    (hB : ∀ s, 0 ≤ B s) (hβ : ∀ s, approxFactor Sinf Sfin w α β s ≤ B s)
    (hβ' : ∀ s, approxFactor Sinf Sfin w α β' s ≤ B s) :
    (∏ v ∈ Sinf, min 1 (v (β - β')) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v (β - β')) ≤
      2 ^ Module.finrank ℚ K * ∏ s, B s := by
  have h := prod_pow_sPlaceWeight (Sinf := Sinf) (Sfin := Sfin) fun v ↦ min 1 (v (β - β'))
  simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply] at h ⊢
  rw [← h]
  calc ∏ s, min 1 (sPlaceAbsValue s (β - β')) ^ sPlaceWeight s
      ≤ ∏ s, Sum.elim (fun v ↦ (2 : ℝ) ^ v.1.mult) (fun _ ↦ 1) s * B s := by
        refine prod_le_prod₀ (fun s _ ↦ pow_nonneg (le_min zero_le_one (apply_nonneg _ _)) _)
          fun s _ ↦ min_one_apply_sub_pow_le ?_ (hβ s) (hβ' s)
        rcases s with v | v
        · rw [sPlaceAbsValue_inl]
          exact hwInf v.1 v.2
        · rw [sPlaceAbsValue_inr]
          exact hwFin v.1 v.2
    _ ≤ 2 ^ Module.finrank ℚ K * ∏ s, B s := by
        rw [prod_mul_distrib, Fintype.prod_sum_type]
        refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun s _ ↦ hB s)
        simp only [Sum.elim_inl, Sum.elim_inr, prod_const_one, mul_one, prod_pow_eq_pow_sum,
          univ_eq_attach]
        refine pow_le_pow_right₀ (by norm_num) ?_
        rw [sum_attach Sinf (fun v ↦ v.mult)]
        exact (sum_le_sum_of_subset (subset_univ _)).trans_eq InfinitePlace.sum_mult_eq

/-- A local factor of a solution `γ` of Roth's inequality of height at least `H` is at most
`(H ^ (-κ)) ^ (c s / N)`, where `c` is the class of `γ`: (6.9) with the product of the local
factors bounded by `H(γ) ^ (-κ)`. -/
private theorem approxFactor_le_rpow_rpow_approxClass {N : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) {H : ℝ}
    (hH : 0 < H) {γ : K}
    (hγ : ∏ s, approxFactor Sinf Sfin w α γ s ≤ mulHeight₁ γ ^ (-κ)) (hHγ : H ≤ mulHeight₁ γ)
    (s : ↥Sinf ⊕ ↥Sfin) :
    approxFactor Sinf Sfin w α γ s ≤ (H ^ (-κ)) ^ ((approxClass Sinf Sfin w α N γ s : ℝ) / N) :=
  (approxFactor_le_rpow_approxClass N γ s).trans <|
    (rpow_le_rpow (prod_nonneg fun t _ ↦ approxFactor_nonneg γ t) hγ (by positivity)).trans
      (rpow_le_rpow (rpow_nonneg (mulHeight₁_pos γ).le _)
        (rpow_le_rpow_of_nonpos hH hHγ (neg_nonpos.mpr hκ)) (by positivity))

/-- **The strong gap principle** (Bombieri–Gubler, Lemma 6.5.6), in relative multiplicative
heights. Let `β ≠ β'` in `K` both satisfy Roth's inequality
`∏ v, min 1 (w v (β - α v)) ^ mult v ≤ H(β) ^ (-κ)` over `Sinf ∪ Sfin`, with `κ ≥ 0` and each
`w v` lying over `v`, and lie in one approximation class of side `1 / N`. If `H(β) ≤ H(β')`, then
`H(β) ^ ((1 - |S| / N) κ - 1) ≤ 4 ^ [K : ℚ] · H(β')`, where `|S| = #Sinf + #Sfin`. -/
theorem mulHeight₁_rpow_le_of_approxClass_eq (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ)
    {β β' : K} (hne : β ≠ β')
    (hβ : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ))
    (hβ' : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β' - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β' - α v.1)) ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : mulHeight₁ β ≤ mulHeight₁ β') :
    mulHeight₁ β ^ ((1 - ((#Sinf + #Sfin : ℕ) : ℝ) / N) * κ - 1) ≤
      4 ^ Module.finrank ℚ K * mulHeight₁ β' := by
  set H := mulHeight₁ β
  set d := Module.finrank ℚ K
  set c := approxClass Sinf Sfin w α N β
  have hH : 1 ≤ H := one_le_mulHeight₁ β
  have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  -- The degenerate cases, where the height of `β` is `1` or the exponent is `-1`.
  rcases hH.eq_or_lt with hH1 | hH1
  · rw [← hH1, one_rpow]
    nlinarith [one_le_mulHeight₁ β']
  rcases hκ.eq_or_lt with rfl | hκ
  · rw [mul_zero, zero_sub, rpow_neg_one]
    nlinarith [inv_le_one_of_one_le₀ hH, one_le_mulHeight₁ β']
  rw [← prod_approxFactor] at hβ hβ'
  have hB : 0 < H ^ (-κ) := rpow_pos_of_pos (by positivity) _
  -- The fundamental inequality for `β - β'`, against the local bounds of (6.9) at every place.
  have hgap : H ^ (κ * ∑ s, (c s : ℝ) / N) ≤ 4 ^ d * H * mulHeight₁ β' := by
    have hfund := (inv_mulHeight₁_le_prod_min_one_apply Sinf Sfin (sub_ne_zero.mpr hne)).trans
      (prod_min_one_apply_sub_le hwInf hwFin (fun s ↦ rpow_nonneg hB.le _)
        (approxFactor_le_rpow_rpow_approxClass hκ.le (by positivity) hβ le_rfl)
        (hclass ▸ approxFactor_le_rpow_rpow_approxClass hκ.le (by positivity) hβ' hle))
    rw [← rpow_sum_of_pos hB, ← rpow_mul (by positivity), neg_mul, rpow_neg (by positivity),
      inv_le_iff_one_le_mul₀' (mulHeight₁_pos _)] at hfund
    have hsub := mulHeight₁_sub_le β β'
    rw [totalWeight_eq_finrank] at hsub
    calc H ^ (κ * ∑ s, (c s : ℝ) / N)
        ≤ H ^ (κ * ∑ s, (c s : ℝ) / N) *
            (mulHeight₁ (β - β') * (2 ^ d * (H ^ (κ * ∑ s, (c s : ℝ) / N))⁻¹)) :=
          le_mul_of_one_le_right (by positivity) hfund
      _ = 2 ^ d * mulHeight₁ (β - β') := by field_simp
      _ ≤ 2 ^ d * (2 ^ d * H * mulHeight₁ β') := by gcongr
      _ = 4 ^ d * H * mulHeight₁ β' := by
          rw [show (4 : ℝ) ^ d = 2 ^ d * 2 ^ d by rw [← mul_pow]; norm_num]
          ring
  -- The class sums to more than `N - |S|` by (6.10), which bounds the exponent from below.
  have hsum : (1 - ((#Sinf + #Sfin : ℕ) : ℝ) / N) * κ ≤ κ * ∑ s, (c s : ℝ) / N := by
    have hlt := lt_sum_approxClass_add_card N
      (hβ.trans_lt (rpow_lt_one_of_one_lt_of_neg hH1 (neg_lt_zero.mpr hκ)))
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    rw [← Finset.sum_div, one_sub_div (by positivity), div_le_div_iff_of_pos_right
      (by positivity), sub_le_iff_le_add]
    exact_mod_cast hlt.le
  rw [rpow_sub_one (by positivity), div_le_iff₀ (by positivity)]
  calc H ^ ((1 - ((#Sinf + #Sfin : ℕ) : ℝ) / N) * κ)
      ≤ H ^ (κ * ∑ s, (c s : ℝ) / N) := rpow_le_rpow_of_exponent_le hH hsum
    _ ≤ 4 ^ d * H * mulHeight₁ β' := hgap
    _ = 4 ^ d * mulHeight₁ β' * H := by ring

/-- **The strong gap principle** (Bombieri–Gubler, Lemma 6.5.6; Davenport–Roth), in absolute
logarithmic heights. Let `β ≠ β'` in `K` both satisfy Roth's inequality
`∏ v, min 1 (w v (β - α v)) ^ mult v ≤ H(β) ^ (-κ)` over `Sinf ∪ Sfin`, with `κ ≥ 0` and each
`w v` lying over `v`, and lie in one approximation class of side `1 / N`. If `h(β) ≤ h(β')`, then
`h(β') ≥ ((1 - |S| / N) κ - 1) h(β) - log 4`, where `|S| = #Sinf + #Sfin`. -/
theorem mul_absLogHeight₁_sub_le_of_approxClass_eq (hwInf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1) {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 ≤ κ)
    {β β' : K} (hne : β ≠ β')
    (hβ : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α v.1)) ≤ mulHeight₁ β ^ (-κ))
    (hβ' : (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β' - α v.1)) ^ v.mult) *
      ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β' - α v.1)) ≤ mulHeight₁ β' ^ (-κ))
    (hclass : approxClass Sinf Sfin w α N β = approxClass Sinf Sfin w α N β')
    (hle : absLogHeight₁ β ≤ absLogHeight₁ β') :
    ((1 - ((#Sinf + #Sfin : ℕ) : ℝ) / N) * κ - 1) * absLogHeight₁ β - log 4 ≤
      absLogHeight₁ β' := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [absLogHeight₁_eq_div, absLogHeight₁_eq_div, div_le_div_iff_of_pos_right hd,
    logHeight₁_eq_log_mulHeight₁, logHeight₁_eq_log_mulHeight₁,
    log_le_log_iff (mulHeight₁_pos β) (mulHeight₁_pos β')] at hle
  have h := mulHeight₁_rpow_le_of_approxClass_eq hwInf hwFin hN hκ hne hβ hβ' hclass hle
  rw [← log_le_log_iff (rpow_pos_of_pos (mulHeight₁_pos β) _) (by positivity),
    log_rpow (mulHeight₁_pos β), log_mul (by positivity) (mulHeight₁_pos β').ne', log_pow,
    ← logHeight₁_eq_log_mulHeight₁, ← logHeight₁_eq_log_mulHeight₁] at h
  rw [absLogHeight₁_eq_div, absLogHeight₁_eq_div, mul_div_assoc', sub_le_iff_le_add,
    div_add' _ _ _ hd.ne', div_le_div_iff_of_pos_right hd]
  linarith

end NumberField
