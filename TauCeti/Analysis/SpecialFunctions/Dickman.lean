/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Dickman function

The *Dickman function* `ρ : ℝ → ℝ` is the function that is `1` on `[0, 1]`, is continuous on
`[0, ∞)` and satisfies the delay differential equation `u ρ'(u) = -ρ(u - 1)` for `u > 1`. It is
extended by `0` to the negative reals. For fixed `u > 0`, `ρ(u)` is the limiting proportion of
the positive integers `n ≤ x` all of whose prime factors are at most `x ^ (1 / u)`.

The function is constructed here from the integral form of the equation,
`ρ(u) = 1 - ∫_1^u ρ(t - 1) / t dt` for `u ≥ 1`. The right-hand side at `u` only involves the
values of `ρ` on `[0, u - 1]`, so the equation determines `ρ` on `[0, n + 1]` from its values on
`[0, n]`. Accordingly `ρ` is obtained from a sequence of approximants, each the integral of the
one before, in which the `n`-th approximant already has the final values on `(-∞, n + 1]`.

## Main definitions

* `TauCeti.dickman`: the Dickman function `ρ`.

## Main results

* `TauCeti.dickman_of_neg`, `TauCeti.dickman_of_le_one`: `ρ` is `0` on the negative reals and `1`
  on `[0, 1]`.
* `TauCeti.dickman_eq_one_sub_integral`: `ρ(u) = 1 - ∫_1^u ρ(t - 1) / t dt` for `u ≥ 0`.
* `TauCeti.continuousOn_dickman`: `ρ` is continuous on `[0, ∞)`.
* `TauCeti.hasDerivAt_dickman`: `ρ'(u) = -ρ(u - 1) / u` for `u ≠ 0, 1`; the content is `u > 1`.
* `TauCeti.not_differentiableAt_dickman_one`: `ρ` is not differentiable at `1`.
* `TauCeti.eqOn_dickman`, `TauCeti.eq_dickman`, `TauCeti.existsUnique_dickman`: the values on
  `[0, 1]` and the delay differential equation for `u > 1` determine `ρ` on `[0, ∞)`.
* `TauCeti.mul_dickman_eq_integral`: `u ρ(u) = ∫_{u-1}^u ρ(v) dv` for every real `u`.
* `TauCeti.dickman_pos`: `ρ(u) > 0` for `u ≥ 0`.
* `TauCeti.antitoneOn_dickman`, `TauCeti.strictAntiOn_dickman`: `ρ` is nonincreasing on `[0, ∞)`
  and strictly decreasing on `[1, ∞)`.
* `TauCeti.dickman_two`: `ρ(2) = 1 - log 2`.

## References

* A. Hildebrand, G. Tenenbaum, *Integers without large prime factors*, J. Théor. Nombres
  Bordeaux 5 (1993), 411–484.
-/

public section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace TauCeti

/-- The function that is `1` on `[0, ∞)` and `0` on `(-∞, 0)`: the Dickman function on
`(-∞, 1]`. -/
private noncomputable def dickmanInit (u : ℝ) : ℝ := if 0 ≤ u then 1 else 0

private theorem dickmanInit_of_nonneg {u : ℝ} (hu : 0 ≤ u) : dickmanInit u = 1 := by
  simp [dickmanInit, hu]

private theorem dickmanInit_of_neg {u : ℝ} (hu : u < 0) : dickmanInit u = 0 := by
  simp [dickmanInit, hu]

/-- The approximants of the Dickman function: the `n`-th one agrees with the Dickman function on
`(-∞, n + 1]`. -/
private noncomputable def dickmanAux : ℕ → ℝ → ℝ
  | 0, u => dickmanInit u
  | n + 1, u => dickmanInit u - ∫ t in (1 : ℝ)..max u 1, dickmanAux n (t - 1) / t

private theorem dickmanAux_of_le_one (n : ℕ) {u : ℝ} (hu : u ≤ 1) :
    dickmanAux n u = dickmanInit u := by
  cases n with
  | zero => rfl
  | succ n => rw [dickmanAux, max_eq_right hu, integral_same, sub_zero]

private theorem dickmanAux_succ {n : ℕ} {u : ℝ} (hu : u ≤ n + 1) :
    dickmanAux (n + 1) u = dickmanAux n u := by
  induction n generalizing u with
  | zero =>
    have hu' : u ≤ 1 := by simpa using hu
    rw [dickmanAux_of_le_one _ hu', dickmanAux_of_le_one _ hu']
  | succ n ih =>
    rw [dickmanAux, dickmanAux]
    congr 1
    refine integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (le_max_right u 1)] at ht
    have : t - 1 ≤ n + 1 := by
      have := ht.2.trans (max_le hu (by norm_cast; omega))
      push_cast at this
      linarith
    simp only [ih this]

private theorem dickmanAux_of_le {n m : ℕ} (hnm : n ≤ m) {u : ℝ} (hu : u ≤ n + 1) :
    dickmanAux m u = dickmanAux n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [dickmanAux_succ (hu.trans (by norm_cast; omega)), ih]

/-- The Dickman function `ρ`: it is `0` on the negative reals, `1` on `[0, 1]`, continuous on
`[0, ∞)`, and satisfies `u ρ'(u) = -ρ(u - 1)` for `1 < u`. -/
noncomputable def dickman (u : ℝ) : ℝ := dickmanAux ⌊u⌋₊ u

private theorem dickman_eq_dickmanAux {n : ℕ} {u : ℝ} (hu : u ≤ n + 1) :
    dickman u = dickmanAux n u := by
  rw [dickman, ← dickmanAux_of_le (le_max_left ⌊u⌋₊ n) (Nat.lt_floor_add_one u).le,
    dickmanAux_of_le (le_max_right ⌊u⌋₊ n) hu]

/-- The Dickman function vanishes on the negative reals. -/
theorem dickman_of_neg {u : ℝ} (hu : u < 0) : dickman u = 0 := by
  rw [dickman_eq_dickmanAux (n := 0) (by linarith), dickmanAux, dickmanInit_of_neg hu]

/-- The Dickman function is `1` on `[0, 1]`. -/
theorem dickman_of_le_one {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u ≤ 1) : dickman u = 1 := by
  rw [dickman_eq_dickmanAux (n := 0) (by simpa using h₁), dickmanAux, dickmanInit_of_nonneg h₀]

/-- `ρ(0) = 1`. -/
@[simp]
theorem dickman_zero : dickman 0 = 1 := dickman_of_le_one le_rfl zero_le_one

/-- `ρ(1) = 1`. -/
@[simp]
theorem dickman_one : dickman 1 = 1 := dickman_of_le_one zero_le_one le_rfl

/-- For `0 ≤ u`, `ρ(u) = 1 - ∫_1^{max u 1} ρ(t - 1) / t dt`. -/
private theorem dickman_eq_one_sub_integral_max {u : ℝ} (hu : 0 ≤ u) :
    dickman u = 1 - ∫ t in (1 : ℝ)..max u 1, dickman (t - 1) / t := by
  have hn : u ≤ (⌊u⌋₊ + 1 : ℕ) + 1 := by
    push_cast
    linarith [(Nat.lt_floor_add_one u).le]
  rw [dickman_eq_dickmanAux hn, dickmanAux, dickmanInit_of_nonneg hu]
  congr 1
  refine integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le (le_max_right u 1)] at ht
  have : t - 1 ≤ ⌊u⌋₊ + 1 := by
    have := ht.2.trans (max_le (Nat.lt_floor_add_one u).le (by norm_cast; omega))
    linarith
  simp only [dickman_eq_dickmanAux this]

/-- The integral equation of the Dickman function: `ρ(u) = 1 - ∫_1^u ρ(t - 1) / t dt` for
`0 ≤ u`. For `u < 1` the integral vanishes, because `ρ` vanishes on the negative reals. -/
theorem dickman_eq_one_sub_integral {u : ℝ} (hu : 0 ≤ u) :
    dickman u = 1 - ∫ t in (1 : ℝ)..u, dickman (t - 1) / t := by
  rcases le_total 1 u with h | h
  · simpa [max_eq_left h] using dickman_eq_one_sub_integral_max hu
  · have h0 : ∫ t in (1 : ℝ)..u, dickman (t - 1) / t = 0 := by
      rw [integral_symm, integral_of_le h, integral_Ioc_eq_integral_Ioo,
        setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
          rw [dickman_of_neg (by linarith [ht.2]), zero_div], neg_zero]
    rw [h0, sub_zero, dickman_of_le_one hu h]

/-! ### Continuity and the delay differential equation -/

private theorem continuousOn_dickmanAux (n : ℕ) : ContinuousOn (dickmanAux n) (Ici 0) := by
  induction n with
  | zero => exact continuousOn_const.congr fun u hu ↦ dickmanInit_of_nonneg hu
  | succ n ih =>
    have hG : Continuous fun t : ℝ ↦ dickmanAux n (max t 1 - 1) / max t 1 :=
      (ih.comp_continuous (by fun_prop) fun t ↦ sub_nonneg.2 (le_max_right t 1)).div
        (by fun_prop) fun t ↦ (zero_lt_one.trans_le (le_max_right t 1)).ne'
    have hP : Continuous fun u : ℝ ↦
        1 - ∫ t in (1 : ℝ)..max u 1, dickmanAux n (max t 1 - 1) / max t 1 :=
      continuous_const.sub
        ((continuous_primitive (fun a b ↦ hG.intervalIntegrable a b) 1).comp (by fun_prop))
    refine hP.continuousOn.congr fun u hu ↦ ?_
    rw [dickmanAux, dickmanInit_of_nonneg hu]
    congr 1
    refine integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (le_max_right u 1)] at ht
    simp only [max_eq_left ht.1]

/-- The Dickman function is continuous on `[0, ∞)`. It is not continuous at `0` as a function on
the real line, since it vanishes on the negative reals. -/
theorem continuousOn_dickman : ContinuousOn dickman (Ici 0) := by
  intro u hu
  have hlt : u < (⌊u⌋₊ + 1 : ℕ) + 1 := by
    push_cast
    linarith [Nat.lt_floor_add_one u]
  refine ((continuousOn_dickmanAux (⌊u⌋₊ + 1)) u hu).congr_of_eventuallyEq ?_
    (dickman_eq_dickmanAux hlt.le)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with v hv
  exact dickman_eq_dickmanAux (le_of_lt hv)

/-- The integrand `ρ(t - 1) / t` of the integral equation, extended from `[1, ∞)` to a continuous
function on the real line by clamping `t` at `1`. -/
private theorem continuous_dickmanKernel :
    Continuous fun t : ℝ ↦ dickman (max t 1 - 1) / max t 1 :=
  (continuousOn_dickman.comp_continuous (by fun_prop) fun t ↦ sub_nonneg.2 (le_max_right t 1)).div
    (by fun_prop) fun t ↦ (zero_lt_one.trans_le (le_max_right t 1)).ne'

private theorem integral_dickmanKernel {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in a..b, dickman (max t 1 - 1) / max t 1 = ∫ t in a..b, dickman (t - 1) / t := by
  refine integral_congr fun t ht ↦ ?_
  simp only [max_eq_left ((le_min ha hb).trans ht.1)]

/-- The delay differential equation of the Dickman function: `ρ'(u) = -ρ(u - 1) / u`. The
content is the case `1 < u`; on `(-∞, 0)` and on `(0, 1)` the function is constant and
`ρ(u - 1) = 0`. At `0` the function is not continuous, and at `1` it is not differentiable. -/
theorem hasDerivAt_dickman {u : ℝ} (h₀ : u ≠ 0) (h₁ : u ≠ 1) :
    HasDerivAt dickman (-dickman (u - 1) / u) u := by
  rcases lt_or_gt_of_ne h₁ with hu | hu
  · rw [dickman_of_neg (by linarith), neg_zero, zero_div]
    rcases lt_or_gt_of_ne h₀ with hneg | hpos
    · refine (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hneg] with v hv using dickman_of_neg hv
    · refine (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hpos hu] with v hv using dickman_of_le_one hv.1.le hv.2.le
  · have h := ((continuous_dickmanKernel.integral_hasStrictDerivAt 1 u).hasDerivAt).const_sub 1
    rw [max_eq_left hu.le, ← neg_div] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [dickman_eq_one_sub_integral (zero_le_one.trans hv.le),
      integral_dickmanKernel le_rfl (le_of_lt hv)]

/-- The Dickman function is not differentiable at `1`: its left derivative there is `0` and its
right derivative is `-1`. -/
theorem not_differentiableAt_dickman_one : ¬DifferentiableAt ℝ dickman 1 := by
  intro h
  have hl : HasDerivWithinAt dickman 0 (Icc 0 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Icc 0 1) (1 : ℝ)).congr
      (fun v hv ↦ dickman_of_le_one hv.1 hv.2) dickman_one
  have hr : HasDerivWithinAt dickman (-1) (Icc 1 2) 1 := by
    have h' : HasDerivWithinAt
        (fun v ↦ 1 - ∫ t in (1 : ℝ)..v, dickman (max t 1 - 1) / max t 1) (-1) (Icc 1 2) 1 := by
      simpa using (((continuous_dickmanKernel.integral_hasStrictDerivAt 1 1).hasDerivAt).const_sub
        1).hasDerivWithinAt
    refine h'.congr (fun v hv ↦ ?_) (by simp)
    rw [dickman_eq_one_sub_integral (zero_le_one.trans hv.1),
      integral_dickmanKernel le_rfl hv.1]
  have hl' := (uniqueDiffOn_Icc zero_lt_one 1 ⟨zero_le_one, le_rfl⟩).eq_deriv _
    h.hasDerivAt.hasDerivWithinAt hl
  have hr' := (uniqueDiffOn_Icc one_lt_two 1 ⟨le_rfl, one_le_two⟩).eq_deriv _
    h.hasDerivAt.hasDerivWithinAt hr
  linarith

/-- `ρ(2) = 1 - log 2`. -/
theorem dickman_two : dickman 2 = 1 - Real.log 2 := by
  have h : ∫ t in (1 : ℝ)..2, dickman (t - 1) / t = ∫ t in (1 : ℝ)..2, t⁻¹ :=
    integral_congr fun t ht ↦ by
      rw [uIcc_of_le one_le_two] at ht
      simp only [dickman_of_le_one (sub_nonneg.2 ht.1) (by linarith [ht.2]), one_div]
  rw [dickman_eq_one_sub_integral zero_le_two, h, integral_inv_of_pos one_pos two_pos, div_one]

/-! ### Uniqueness -/

private theorem eqOn_dickman_of_integral_eq {f : ℝ → ℝ} (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, f u = 1)
    (hf : ∀ u, 1 ≤ u → f u = 1 - ∫ t in (1 : ℝ)..u, f (t - 1) / t) (n : ℕ) :
    EqOn f dickman (Icc 0 (n + 1)) := by
  induction n with
  | zero =>
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    rw [h₁ u hu', dickman_of_le_one hu'.1 hu'.2]
  | succ n ih =>
    intro u hu
    rcases le_total u 1 with hu1 | hu1
    · rw [h₁ u ⟨hu.1, hu1⟩, dickman_of_le_one hu.1 hu1]
    · rw [hf u hu1, dickman_eq_one_sub_integral hu.1]
      congr 1
      refine integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hu1] at ht
      have hmem : t - 1 ∈ Icc (0 : ℝ) (n + 1) := by
        have := hu.2
        push_cast at this
        exact ⟨sub_nonneg.2 ht.1, by linarith [ht.2]⟩
      simp only [ih hmem]


/-- A function that is `1` on `[0, 1]` and satisfies the delay differential equation for `1 < u`
is `1 - log u` on `(1, 2)`. On `(1, 2)` it is `C - log u` for a constant `C`, and comparing the
derivative at `2` with the limit of the derivative from the right gives `C = 1`. -/
private theorem eq_one_sub_log_of_delay {f : ℝ → ℝ} (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, f u = 1)
    (hd : ∀ u, 1 < u → HasDerivAt f (-f (u - 1) / u) u) {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    f u = 1 - Real.log u := by
  have hg : ∀ v ∈ Ioo (1 : ℝ) 2, HasDerivAt (fun v ↦ f v + Real.log v) 0 v := by
    intro v hv
    have hv0 : v ≠ 0 := (zero_lt_one.trans hv.1).ne'
    have h := (hd v hv.1).add (Real.hasDerivAt_log hv0)
    rw [h₁ (v - 1) ⟨by linarith [hv.1], by linarith [hv.2]⟩] at h
    convert h using 1
    field_simp
    ring
  have hconst : ∀ v ∈ Ioo (1 : ℝ) 2, f v + Real.log v = f (3 / 2) + Real.log (3 / 2) :=
    fun v hv ↦ isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun w hw ↦ (hg w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hg w hw).deriv) hv (by norm_num)
  set C := f (3 / 2) + Real.log (3 / 2)
  have hderiv : ∀ v ∈ Ioo (2 : ℝ) 3, deriv f v = -(C - Real.log (v - 1)) / v := fun v hv ↦ by
    rw [(hd v (by linarith [hv.1])).deriv,
      ← hconst (v - 1) ⟨by linarith [hv.1], by linarith [hv.2]⟩, add_sub_cancel_right]
  have htend : Tendsto (fun v ↦ deriv f v) (𝓝[>] (2 : ℝ)) (𝓝 (-C / 2)) := by
    have hcts : ContinuousAt (fun v : ℝ ↦ -(C - Real.log (v - 1)) / v) 2 :=
      ((continuousAt_const.sub ((Real.continuousAt_log (by norm_num)).comp
        (f := fun v : ℝ ↦ v - 1) (by fun_prop))).neg).div continuousAt_id two_ne_zero
    have h := hcts.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 2))
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (2 : ℝ) < 3 by norm_num)] with v hv
      using (hderiv v hv).symm
  have hr : HasDerivWithinAt f (-C / 2) (Ici 2) 2 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 1)
      (fun v hv ↦ (hd v hv).differentiableAt.differentiableWithinAt)
      (hd 2 one_lt_two).continuousAt.continuousWithinAt
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_lt_two)) htend
  have h2 := (uniqueDiffWithinAt_Ici (2 : ℝ)).eq_deriv _ hr (hd 2 one_lt_two).hasDerivWithinAt
  rw [show (2 : ℝ) - 1 = 1 by norm_num, h₁ 1 ⟨zero_le_one, le_rfl⟩] at h2
  have hC : C = 1 := by linarith
  have := hconst u hu
  rw [hC] at this
  linarith

/-- A function that is `1` on `[0, 1]` and satisfies the delay differential equation for `1 < u`
is continuous on `[0, ∞)`. Only continuity from the right at `1` needs an argument. -/
private theorem continuousOn_of_delay {f : ℝ → ℝ} (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, f u = 1)
    (hd : ∀ u, 1 < u → HasDerivAt f (-f (u - 1) / u) u) : ContinuousOn f (Ici 0) := by
  have hone : f 1 = 1 := h₁ 1 ⟨zero_le_one, le_rfl⟩
  intro v hv
  rcases lt_trichotomy v 1 with hv1 | rfl | hv1
  · refine (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ ↦ (1 : ℝ)) (Ici 0) v)
      |>.congr_of_eventuallyEq ?_ (h₁ v ⟨hv, hv1.le⟩)
    filter_upwards [inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds hv1)] with w hw
      using h₁ w ⟨hw.1, le_of_lt hw.2⟩
  · have hl : ContinuousWithinAt f (Icc 0 1) 1 :=
      (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ ↦ (1 : ℝ)) (Icc 0 1) 1).congr
        (fun w hw ↦ h₁ w hw) hone
    have hr : ContinuousWithinAt f (Ici 1) 1 := by
      have hlog : ContinuousWithinAt (fun w : ℝ ↦ 1 - Real.log w) (Ici 1) 1 :=
        (continuousAt_const.sub (Real.continuousAt_log one_ne_zero)).continuousWithinAt
      refine hlog.congr_of_eventuallyEq ?_ (by rw [hone, Real.log_one, sub_zero])
      filter_upwards [Icc_mem_nhdsGE (show (1 : ℝ) < 3 / 2 by norm_num)] with w hw
      rcases hw.1.eq_or_lt with rfl | h
      · rw [hone, Real.log_one, sub_zero]
      · exact eq_one_sub_log_of_delay h₁ hd ⟨h, by linarith [hw.2]⟩
    exact (hl.union hr).mono fun w hw ↦ (le_total w 1).elim (fun h ↦ Or.inl ⟨hw, h⟩) Or.inr
  · exact (hd v hv1).continuousAt.continuousWithinAt

/-- The Dickman function is determined on `[0, ∞)` by its values on `[0, 1]` and the delay
differential equation: a function that is `1` on `[0, 1]` and satisfies `u f'(u) = -f(u - 1)` for
`1 < u` agrees with it there. Continuity on `[0, ∞)` is not assumed: differentiability at `2`
forces continuity from the right at `1`. -/
theorem eqOn_dickman {f : ℝ → ℝ} (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, f u = 1)
    (hd : ∀ u, 1 < u → HasDerivAt f (-f (u - 1) / u) u) : EqOn f dickman (Ici 0) := by
  have hc := continuousOn_of_delay h₁ hd
  have hk : ContinuousOn (fun t : ℝ ↦ -f (t - 1) / t) (Ici 1) :=
    ((hc.comp (by fun_prop) fun t ht ↦ sub_nonneg.2 ht).neg).div continuousOn_id
      fun t ht ↦ (zero_lt_one.trans_le ht).ne'
  have hf : ∀ u, 1 ≤ u → f u = 1 - ∫ t in (1 : ℝ)..u, f (t - 1) / t := by
    intro u hu
    have h := integral_eq_sub_of_hasDerivAt_of_le hu
      (hc.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 zero_le_one)))
      (fun t ht ↦ hd t ht.1) ((hk.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hu)
    rw [h₁ 1 ⟨zero_le_one, le_rfl⟩] at h
    simp only [neg_div, intervalIntegral.integral_neg] at h
    linarith
  intro u hu
  exact eqOn_dickman_of_integral_eq h₁ hf ⌊u⌋₊ ⟨hu, (Nat.lt_floor_add_one u).le⟩

/-- The Dickman function is the unique function on the real line that vanishes on the negative
reals, is `1` on `[0, 1]` and satisfies `u f'(u) = -f(u - 1)` for `1 < u`. -/
theorem eq_dickman {f : ℝ → ℝ} (h₀ : ∀ u < 0, f u = 0) (h₁ : ∀ u ∈ Icc (0 : ℝ) 1, f u = 1)
    (hd : ∀ u, 1 < u → HasDerivAt f (-f (u - 1) / u) u) : f = dickman := by
  funext u
  rcases lt_or_ge u 0 with hu | hu
  · rw [h₀ u hu, dickman_of_neg hu]
  · exact eqOn_dickman h₁ hd hu

/-- There is exactly one function on the real line that vanishes on the negative reals, is `1` on
`[0, 1]`, is continuous on `[0, ∞)` and satisfies `u f'(u) = -f(u - 1)` for `1 < u`: the Dickman
function. -/
theorem existsUnique_dickman :
    ∃! f : ℝ → ℝ, (∀ u < 0, f u = 0) ∧ (∀ u ∈ Icc (0 : ℝ) 1, f u = 1) ∧
      ContinuousOn f (Ici 0) ∧ ∀ u, 1 < u → HasDerivAt f (-f (u - 1) / u) u :=
  ⟨dickman, ⟨fun _ hu ↦ dickman_of_neg hu, fun _ hu ↦ dickman_of_le_one hu.1 hu.2,
    continuousOn_dickman, fun _ hu ↦ hasDerivAt_dickman (zero_lt_one.trans hu).ne' hu.ne'⟩,
    fun _ hf ↦ eq_dickman hf.1 hf.2.1 hf.2.2.2⟩

/-! ### The integral identity -/

/-- The Dickman function is integrable on every bounded interval. -/
theorem intervalIntegrable_dickman (a b : ℝ) : IntervalIntegrable dickman volume a b := by
  have hG : Continuous fun u : ℝ ↦ dickman (max u 0) :=
    continuousOn_dickman.comp_continuous (by fun_prop) fun u ↦ le_max_right u 0
  have h : dickman = (Ici (0 : ℝ)).indicator fun u ↦ dickman (max u 0) := by
    funext u
    by_cases hu : 0 ≤ u
    · rw [indicator_of_mem (mem_Ici.2 hu), max_eq_left hu]
    · rw [indicator_of_notMem (by simpa using hu), dickman_of_neg (not_le.1 hu)]
  rw [h, intervalIntegrable_iff]
  exact (intervalIntegrable_iff.1 (hG.intervalIntegrable a b)).indicator measurableSet_Ici

private theorem integral_dickman_of_le_zero {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    ∫ v in a..b, dickman v = 0 := by
  rw [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_eq_zero_of_forall_eq_zero fun v hv ↦ dickman_of_neg (hv.2.trans_le hb)

private theorem integral_dickman_of_le_one {u : ℝ} (h₀ : 0 ≤ u) (h₁ : u ≤ 1) :
    ∫ v in (0 : ℝ)..u, dickman v = u := by
  have h : ∫ v in (0 : ℝ)..u, dickman v = ∫ _v in (0 : ℝ)..u, (1 : ℝ) :=
    integral_congr fun v hv ↦ by
      rw [uIcc_of_le h₀] at hv
      exact dickman_of_le_one hv.1 (hv.2.trans h₁)
  rw [h, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

private theorem mul_dickman_eq_integral_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    u * dickman u = ∫ v in (u - 1)..u, dickman v := by
  have hcont : ContinuousOn (fun t : ℝ ↦ t * dickman t) (Icc 1 u) :=
    (continuousOn_id.mul continuousOn_dickman).mono
      (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 zero_le_one))
  have hderiv : ∀ t ∈ Ioo 1 u,
      HasDerivAt (fun t : ℝ ↦ t * dickman t) (dickman t - dickman (t - 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht.1).ne'
    have h := (hasDerivAt_id' t).mul (hasDerivAt_dickman ht0 ht.1.ne')
    rw [show dickman t - dickman (t - 1) = 1 * dickman t + t * (-dickman (t - 1) / t) by
      field_simp
      ring]
    exact h
  have hi₁ : IntervalIntegrable dickman volume 1 u := intervalIntegrable_dickman 1 u
  have hi₂ : IntervalIntegrable (fun t ↦ dickman (t - 1)) volume 1 u :=
    (continuousOn_dickman.comp (f := fun t : ℝ ↦ t - 1) (s := Icc 1 u) (by fun_prop)
      fun t ht ↦ sub_nonneg.2 ht.1).intervalIntegrable_of_Icc hu
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le (f' := fun t ↦ dickman t - dickman (t - 1)) hu
    hcont hderiv (hi₁.sub hi₂)
  rw [integral_sub hi₁ hi₂, integral_comp_sub_right (fun t ↦ dickman t) 1, sub_self, dickman_one,
    mul_one] at hFTC
  have h₁ := integral_add_adjacent_intervals (intervalIntegrable_dickman 0 1)
    (intervalIntegrable_dickman 1 u)
  have h₂ := integral_add_adjacent_intervals (intervalIntegrable_dickman 0 (u - 1))
    (intervalIntegrable_dickman (u - 1) u)
  rw [integral_dickman_of_le_one zero_le_one le_rfl] at h₁
  linarith

/-- For every real `u`, `u ρ(u) = ∫_{u-1}^u ρ(v) dv`. For `u < 1` this uses that the Dickman
function vanishes on the negative reals. -/
theorem mul_dickman_eq_integral (u : ℝ) : u * dickman u = ∫ v in (u - 1)..u, dickman v := by
  rcases le_total 1 u with hu1 | hu1
  · exact mul_dickman_eq_integral_of_one_le hu1
  rcases le_total u 0 with hu0 | hu0
  · rw [integral_dickman_of_le_zero (by linarith) hu0]
    rcases hu0.eq_or_lt with rfl | h
    · rw [zero_mul]
    · rw [dickman_of_neg h, mul_zero]
  · rw [← integral_add_adjacent_intervals (intervalIntegrable_dickman (u - 1) 0)
      (intervalIntegrable_dickman 0 u), integral_dickman_of_le_zero (by linarith) le_rfl, zero_add,
      integral_dickman_of_le_one hu0 hu1, dickman_of_le_one hu0 hu1, mul_one]

/-! ### Positivity and monotonicity -/

/-- The Dickman function is positive on `[0, ∞)`. -/
theorem dickman_pos {u : ℝ} (hu : 0 ≤ u) : 0 < dickman u := by
  by_contra hneg
  have hS_closed : IsClosed (Ici (0 : ℝ) ∩ dickman ⁻¹' Iic 0) :=
    continuousOn_dickman.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  have hS_bdd : BddBelow (Ici (0 : ℝ) ∩ dickman ⁻¹' Iic 0) := ⟨0, fun v hv ↦ hv.1⟩
  obtain ⟨h₀, hle⟩ := hS_closed.csInf_mem ⟨u, hu, not_lt.1 hneg⟩ hS_bdd
  set u₀ := sInf (Ici (0 : ℝ) ∩ dickman ⁻¹' Iic 0)
  have hpos : ∀ v, 0 ≤ v → v < u₀ → 0 < dickman v := fun v hv hlt ↦ by
    by_contra h
    exact notMem_of_lt_csInf hlt hS_bdd ⟨hv, not_lt.1 h⟩
  have hle' : dickman u₀ ≤ 0 := hle
  have h1 : 1 < u₀ := by
    by_contra h
    rw [dickman_of_le_one h₀ (not_lt.1 h)] at hle'
    exact absurd hle' (by norm_num)
  have hint : 0 < ∫ v in (u₀ - 1)..u₀, dickman v :=
    intervalIntegral_pos_of_pos_on (intervalIntegrable_dickman _ _)
      (fun v hv ↦ hpos v (by linarith [hv.1]) hv.2) (by linarith)
  rw [← mul_dickman_eq_integral] at hint
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ u₀ by linarith) (neg_nonneg.2 hle')]

/-- The Dickman function is nonnegative. -/
theorem dickman_nonneg (u : ℝ) : 0 ≤ dickman u := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [dickman_of_neg hu]
  · exact (dickman_pos hu).le

/-- The Dickman function is nonincreasing on `[0, ∞)`. -/
theorem antitoneOn_dickman : AntitoneOn dickman (Ici 0) := by
  intro a ha b hb hab
  have hI (c d : ℝ) :
      IntervalIntegrable (fun t : ℝ ↦ dickman (max t 1 - 1) / max t 1) volume c d :=
    continuous_dickmanKernel.intervalIntegrable c d
  have hnn : 0 ≤ ∫ t in max a 1..max b 1, dickman (max t 1 - 1) / max t 1 :=
    integral_nonneg (max_le_max_right 1 hab) fun t _ ↦
      div_nonneg (dickman_nonneg _) (zero_le_one.trans (le_max_right t 1))
  have hadd := integral_add_adjacent_intervals (hI 1 (max a 1)) (hI (max a 1) (max b 1))
  rw [dickman_eq_one_sub_integral_max ha, dickman_eq_one_sub_integral_max hb,
    ← integral_dickmanKernel le_rfl (le_max_right a 1),
    ← integral_dickmanKernel le_rfl (le_max_right b 1)]
  linarith

/-- The Dickman function is strictly decreasing on `[1, ∞)`. -/
theorem strictAntiOn_dickman : StrictAntiOn dickman (Ici 1) := by
  intro a ha b hb hab
  have hI (c d : ℝ) :
      IntervalIntegrable (fun t : ℝ ↦ dickman (max t 1 - 1) / max t 1) volume c d :=
    continuous_dickmanKernel.intervalIntegrable c d
  have hpos : 0 < ∫ t in a..b, dickman (max t 1 - 1) / max t 1 :=
    intervalIntegral_pos_of_pos_on (hI a b) (fun t _ ↦
      div_pos (dickman_pos (sub_nonneg.2 (le_max_right t 1)))
        (zero_lt_one.trans_le (le_max_right t 1))) hab
  have hadd := integral_add_adjacent_intervals (hI 1 a) (hI a b)
  rw [dickman_eq_one_sub_integral (zero_le_one.trans ha),
    dickman_eq_one_sub_integral (zero_le_one.trans hb), ← integral_dickmanKernel le_rfl ha,
    ← integral_dickmanKernel le_rfl hb]
  linarith

/-- The Dickman function is at most `1`. -/
theorem dickman_le_one (u : ℝ) : dickman u ≤ 1 := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [dickman_of_neg hu]
    exact zero_le_one
  · simpa using antitoneOn_dickman (mem_Ici.2 le_rfl) hu hu

/-! ### Examples -/

example : dickman (-1) = 0 := dickman_of_neg (by norm_num)

end TauCeti
