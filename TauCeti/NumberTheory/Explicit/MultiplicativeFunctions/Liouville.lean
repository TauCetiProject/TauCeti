/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ZetaValues
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.ArithmeticFunction.Liouville

/-!
# The summatory function of the Liouville function

The Liouville summatory function `L_λ(x) = ∑_{n ≤ x} λ(n)` (`TauCeti.liouvilleSum`) is the sum of
`ArithmeticFunction.liouville` over `Finset.Icc 1 ⌊x⌋₊`, so it vanishes for `x < 1`, like the
Mertens function `M(x) = TauCeti.moebiusSum x`.

Summing the convolution identities `λ = μ * 1_□` and `μ = λ * μ_□` over `n ≤ x` and grouping the
terms by the square divisor `w²` relates the two summatory functions over the naturals
`1 ≤ w ≤ √x`:
`L_λ(x) = ∑_{w ≤ √x} M(x / w²)` and `M(x) = ∑_{w ≤ √x} μ(w) L_λ(x / w²)`.

These identities transfer bounds between `M` and `L_λ`. If `|M(y)| ≤ ε y` for every `y ≥ Y`, then
`|L_λ(x)| ≤ (π² / 6) ε x + 2 x^{3/4}` for every `x ≥ Y²`: the terms with `w ≤ x^{1/4}` have
`x / w² ≥ √x ≥ Y` and contribute at most `ε x ∑_{w ≥ 1} w⁻² = (π² / 6) ε x`, and the others are
bounded by the trivial `|M(y)| ≤ y` and the tail `∑_{w > x^{1/4}} w⁻² ≤ 2 x^{-1/4}`. The same
holds with `M` and `L_λ` exchanged. Letting `ε → 0`, `L_λ(x) = o(x)` if and only if `M(x) = o(x)`.

The summatory identity for `L_λ` and the deduction of `L_λ(x) = o(x)` from `M(x) = o(x)` are
adapted from `PrimeNumberTheoremAnd/Consequences.lean` (`sum_lambda_eq_sum_mu_div_sq`,
`sum_mu_div_sq_isLittleO`, `lambda_pnt`) in the PrimeNumberTheoremAnd project
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, revision `2e6b7fe`).

## Main declarations

* `TauCeti.liouvilleSum`: the Liouville summatory function `L_λ`.
* `TauCeti.liouvilleSum_natCast`, `TauCeti.liouvilleSum_natFloor`,
  `TauCeti.liouvilleSum_natCast_add_one`: agreement with the sum over `Finset.Icc 1 N`, constancy
  on `[N, N + 1)` and the jump `λ(N + 1)`.
* `TauCeti.abs_liouvilleSum_le`: the trivial bound `|L_λ(x)| ≤ x` for `x ≥ 0`.
* `TauCeti.liouvilleSum_eq_sum_moebiusSum`: `L_λ(x) = ∑_{w ≤ √x} M(x / w²)`.
* `TauCeti.moebiusSum_eq_sum_liouvilleSum`: `M(x) = ∑_{w ≤ √x} μ(w) L_λ(x / w²)`.
* `TauCeti.abs_liouvilleSum_le_sum`, `TauCeti.abs_moebiusSum_le_sum`: the bounds
  `|L_λ(x)| ≤ ∑_{w ≤ √x} |M(x / w²)|` and `|M(x)| ≤ ∑_{w ≤ √x} μ(w)² |L_λ(x / w²)|`.
* `TauCeti.sum_abs_apply_div_sq_le`: the transfer for a function `F` with `|F(y)| ≤ y`.
* `TauCeti.abs_liouvilleSum_le_of_abs_moebiusSum_le`,
  `TauCeti.abs_moebiusSum_le_of_abs_liouvilleSum_le`: the transfer of bounds.
* `TauCeti.liouvilleSum_isLittleO_iff`: `L_λ(x) = o(x)` if and only if `M(x) = o(x)`.
-/

public section

open Finset Filter Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

variable {x : ℝ}

/-! ### The summatory function -/

/-- The Liouville summatory function `L_λ(x) = ∑_{n ≤ x} λ(n)` at a real argument; the sum runs over
`Finset.Icc 1 ⌊x⌋₊`, so `L_λ(x) = 0` for `x < 1`. -/
noncomputable def liouvilleSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.liouville n : ℝ)

/-- The defining sum of `L_λ(x)`. -/
theorem liouvilleSum_def (x : ℝ) :
    liouvilleSum x = ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.liouville n : ℝ) := (rfl)

/-- `L_λ(x) = 0` for `x < 1`: the sum is empty. -/
theorem liouvilleSum_of_lt_one (hx : x < 1) : liouvilleSum x = 0 :=
  sum_Icc_one_natFloor_eq_zero _ hx

/-- At a natural number `N`, `L_λ(N)` is the sum of `λ` over `Finset.Icc 1 N`. -/
@[simp]
theorem liouvilleSum_natCast (N : ℕ) :
    liouvilleSum N = ∑ n ∈ Icc 1 N, (ArithmeticFunction.liouville n : ℝ) := by
  simp [liouvilleSum]

/-- `L_λ` is constant on each interval `[N, N + 1)`: `L_λ(x) = L_λ(⌊x⌋₊)`. -/
@[simp high]
theorem liouvilleSum_natFloor (x : ℝ) : liouvilleSum ⌊x⌋₊ = liouvilleSum x := by
  simp [liouvilleSum]

/-- `L_λ` jumps by `λ(N + 1)` at `N + 1`. -/
theorem liouvilleSum_natCast_add_one (N : ℕ) :
    liouvilleSum (N + 1) = liouvilleSum N + ArithmeticFunction.liouville (N + 1) := by
  rw [← Nat.cast_add_one, liouvilleSum_natCast, liouvilleSum_natCast,
    sum_Icc_succ_top (Nat.le_add_left 1 N)]

/-- `L_λ(1) = λ(1) = 1`. -/
@[simp]
theorem liouvilleSum_one : liouvilleSum 1 = 1 := by
  simpa [ArithmeticFunction.liouville_apply_one] using liouvilleSum_natCast 1

/-- The trivial bound `|L_λ(x)| ≤ x` for `x ≥ 0`, as `|λ(n)| ≤ 1`. -/
theorem abs_liouvilleSum_le (hx : 0 ≤ x) : |liouvilleSum x| ≤ x := by
  rw [liouvilleSum_def]
  refine abs_sum_Icc_one_natFloor_le (fun n ↦ ?_) hx
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [ArithmeticFunction.liouville_apply hn]

/-! ### The summatory identities -/

/-- `L_λ(x) = ∑_{w ≤ √x} M(x / w²)`, the sum running over the naturals `1 ≤ w ≤ √x`. -/
theorem liouvilleSum_eq_sum_moebiusSum (x : ℝ) :
    liouvilleSum x = ∑ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), moebiusSum (x / w ^ 2) := by
  have h := ArithmeticFunction.sum_Icc_natFloor_mul_dilateSq μ (ζ : ArithmeticFunction ℤ) x
  rw [← ArithmeticFunction.liouville_eq_moebius_mul_dilateSq] at h
  rw [liouvilleSum_def, h]
  refine sum_congr rfl fun w hw ↦ ?_
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
    (Nat.one_le_iff_ne_zero.1 (mem_Icc.1 hw).1),
    Nat.cast_one, Int.cast_one, one_mul, moebiusSum_def]

/-- `M(x) = ∑_{w ≤ √x} μ(w) L_λ(x / w²)`, the sum running over the naturals `1 ≤ w ≤ √x`. -/
theorem moebiusSum_eq_sum_liouvilleSum (x : ℝ) :
    moebiusSum x = ∑ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), (μ w : ℝ) * liouvilleSum (x / w ^ 2) := by
  have h := ArithmeticFunction.sum_Icc_natFloor_mul_dilateSq ArithmeticFunction.liouville μ x
  rw [ArithmeticFunction.liouville_mul_dilateSq_moebius] at h
  rw [moebiusSum_def, h]
  simp only [liouvilleSum_def]

/-- `|L_λ(x)| ≤ ∑_{w ≤ √x} |M(x / w²)|`. -/
theorem abs_liouvilleSum_le_sum (x : ℝ) :
    |liouvilleSum x| ≤ ∑ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), |moebiusSum (x / w ^ 2)| := by
  rw [liouvilleSum_eq_sum_moebiusSum]
  exact abs_sum_le_sum_abs _ _

/-- `|M(x)| ≤ ∑_{w ≤ √x} μ(w)² |L_λ(x / w²)|`. -/
theorem abs_moebiusSum_le_sum (x : ℝ) :
    |moebiusSum x| ≤ ∑ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), (μ w : ℝ) ^ 2 * |liouvilleSum (x / w ^ 2)| := by
  rw [moebiusSum_eq_sum_liouvilleSum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ ↦ ?_)
  rw [abs_mul]
  gcongr
  have h := Int.natAbs_le_self_sq (μ w)
  rw [Int.natCast_natAbs] at h
  exact_mod_cast h

/-! ### The transfer of bounds -/

/-- The terms `w ≤ x^{1/4}` of the transfer: there `x / w² ≥ Y`, and they contribute at most
`(π² / 6) ε x`. -/
private theorem sum_abs_div_sq_le_of_le_rpow {F : ℝ → ℝ} {ε Y : ℝ}
    (hε : ∀ y, Y ≤ y → |F y| ≤ ε * y) (hx : Y ^ 2 ≤ x) (s : Finset ℕ)
    (hs : ∀ w ∈ s, 1 ≤ w ∧ (w : ℝ) ≤ x ^ (1 / 4 : ℝ)) :
    ∑ w ∈ s, |F (x / w ^ 2)| ≤ π ^ 2 / 6 * ε * x := by
  have hx₀ : 0 ≤ x := (sq_nonneg Y).trans hx
  have hε₀ : 0 ≤ ε := by
    have h := (abs_nonneg _).trans (hε _ (le_max_left Y 1))
    exact nonneg_of_mul_nonneg_left h (lt_max_of_lt_right one_pos)
  have hq : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    rw [← rpow_natCast, ← rpow_mul hx₀]
    norm_num
  calc ∑ w ∈ s, |F (x / w ^ 2)| ≤ ∑ w ∈ s, ε * x * (1 / (w : ℝ) ^ 2) := by
        refine sum_le_sum fun w hw ↦ ?_
        obtain ⟨hw₁, hwq⟩ := hs w hw
        have hw₀ : (0 : ℝ) < (w : ℝ) ^ 2 := by positivity
        have hw4 : (w : ℝ) ^ 4 ≤ x := hq ▸ pow_le_pow_left₀ (by positivity) hwq 4
        have hYw : |Y| * (w : ℝ) ^ 2 ≤ x := by
          refine (pow_le_pow_iff_left₀ (by positivity) hx₀ two_ne_zero).1 ?_
          rw [mul_pow, sq_abs, ← pow_mul, sq x]
          exact mul_le_mul hx hw4 (by positivity) hx₀
        calc |F (x / w ^ 2)| ≤ ε * (x / w ^ 2) :=
              hε _ ((le_div_iff₀ hw₀).2 ((mul_le_mul_of_nonneg_right (le_abs_self Y)
                hw₀.le).trans hYw))
          _ = ε * x * (1 / (w : ℝ) ^ 2) := by ring
    _ = ε * x * ∑ w ∈ s, 1 / (w : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ ε * x * (π ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left (sum_le_hasSum s (fun _ _ ↦ by positivity) hasSum_zeta_two)
          (mul_nonneg hε₀ hx₀)
    _ = π ^ 2 / 6 * ε * x := by ring

/-- The terms `w > x^{1/4}` of the transfer: by the trivial bound they contribute at most
`2 x^{3/4}`. -/
private theorem sum_abs_div_sq_le_of_rpow_lt {F : ℝ → ℝ} (hF : ∀ y, 1 ≤ y → |F y| ≤ y)
    (hx : 0 ≤ x) (s : Finset ℕ)
    (hs : ∀ w ∈ s, ⌊x ^ (1 / 4 : ℝ)⌋₊ < w ∧ (w : ℝ) ^ 2 ≤ x) :
    ∑ w ∈ s, |F (x / w ^ 2)| ≤ 2 * x ^ (3 / 4 : ℝ) := by
  have hw₀ (w : ℕ) (hw : w ∈ s) : (0 : ℝ) < (w : ℝ) ^ 2 := by
    have : 0 < w := (Nat.zero_le _).trans_lt (hs w hw).1
    positivity
  rcases hx.eq_or_lt with rfl | hx
  · rw [eq_empty_of_forall_notMem fun w hw ↦ (hw₀ w hw).not_ge (hs w hw).2]
    simp
  set k := ⌊x ^ (1 / 4 : ℝ)⌋₊
  have hsub : s ⊆ Ioo k (s.sup id + 1) := fun w hw ↦
    mem_Ioo.2 ⟨(hs w hw).1, Nat.lt_succ_of_le (le_sup (f := id) hw)⟩
  calc ∑ w ∈ s, |F (x / w ^ 2)| ≤ ∑ w ∈ s, x * ((w : ℝ) ^ 2)⁻¹ := by
        refine sum_le_sum fun w hw ↦ ?_
        rw [← div_eq_mul_inv]
        exact hF _ ((one_le_div₀ (hw₀ w hw)).2 (hs w hw).2)
    _ = x * ∑ w ∈ s, ((w : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ x * (2 / (k + 1)) := by
        refine mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ ↦ by positivity).trans (sum_Ioo_inv_sq_le _ _)) hx.le
    _ ≤ x * (2 / x ^ (1 / 4 : ℝ)) := by
        gcongr
        exact (Nat.lt_floor_add_one _).le
    _ = 2 * x ^ (3 / 4 : ℝ) := by
        rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, rpow_sub hx, rpow_one]
        ring

/-- **The transfer of bounds.** If `|F(y)| ≤ y` for `y ≥ 1` and `|F(y)| ≤ ε y` for `y ≥ Y`, then
`∑_{w ≤ √x} |F(x / w²)| ≤ (π² / 6) ε x + 2 x^{3/4}` for every `x ≥ Y²`. -/
theorem sum_abs_apply_div_sq_le {F : ℝ → ℝ} {ε Y : ℝ} (hF : ∀ y, 1 ≤ y → |F y| ≤ y)
    (hε : ∀ y, Y ≤ y → |F y| ≤ ε * y) (hx : Y ^ 2 ≤ x) :
    ∑ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), |F (x / w ^ 2)| ≤ π ^ 2 / 6 * ε * x + 2 * x ^ (3 / 4 : ℝ) := by
  have hx₀ : 0 ≤ x := (sq_nonneg Y).trans hx
  have hsq : ∀ w ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), (w : ℝ) ^ 2 ≤ x := fun w hw ↦ by
    have hw₀ := Nat.one_le_iff_ne_zero.1 (mem_Icc.1 hw).1
    exact_mod_cast (Nat.le_floor_iff' (pow_ne_zero 2 hw₀)).1 (Nat.le_sqrt'.1 (mem_Icc.1 hw).2)
  rw [← sum_filter_add_sum_filter_not _ (· ≤ ⌊x ^ (1 / 4 : ℝ)⌋₊)]
  refine add_le_add (sum_abs_div_sq_le_of_le_rpow hε hx _ fun w hw ↦ ?_)
    (sum_abs_div_sq_le_of_rpow_lt hF hx₀ _ fun w hw ↦ ?_)
  · obtain ⟨hw, hwk⟩ := mem_filter.1 hw
    exact ⟨(mem_Icc.1 hw).1, (Nat.cast_le.2 hwk).trans (Nat.floor_le (by positivity))⟩
  · obtain ⟨hw, hwk⟩ := mem_filter.1 hw
    exact ⟨not_le.1 hwk, hsq w hw⟩

/-- **The transfer from `M` to `L_λ`.** If `|M(y)| ≤ ε y` for every `y ≥ Y`, then
`|L_λ(x)| ≤ (π² / 6) ε x + 2 x^{3/4}` for every `x ≥ Y²`. -/
theorem abs_liouvilleSum_le_of_abs_moebiusSum_le {ε Y : ℝ}
    (hM : ∀ y, Y ≤ y → |moebiusSum y| ≤ ε * y) (hx : Y ^ 2 ≤ x) :
    |liouvilleSum x| ≤ π ^ 2 / 6 * ε * x + 2 * x ^ (3 / 4 : ℝ) :=
  (abs_liouvilleSum_le_sum x).trans
    (sum_abs_apply_div_sq_le (fun _ hy ↦ abs_moebiusSum_le (zero_le_one.trans hy)) hM hx)

/-- **The transfer from `L_λ` to `M`.** If `|L_λ(y)| ≤ ε y` for every `y ≥ Y`, then
`|M(x)| ≤ (π² / 6) ε x + 2 x^{3/4}` for every `x ≥ Y²`. -/
theorem abs_moebiusSum_le_of_abs_liouvilleSum_le {ε Y : ℝ}
    (hL : ∀ y, Y ≤ y → |liouvilleSum y| ≤ ε * y) (hx : Y ^ 2 ≤ x) :
    |moebiusSum x| ≤ π ^ 2 / 6 * ε * x + 2 * x ^ (3 / 4 : ℝ) := by
  refine (abs_moebiusSum_le_sum x).trans ((sum_le_sum fun w _ ↦ ?_).trans
    (sum_abs_apply_div_sq_le (fun _ hy ↦ abs_liouvilleSum_le (zero_le_one.trans hy)) hL hx))
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [sq_le_one_iff_abs_le_one]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-! ### `L_λ(x) = o(x)` if and only if `M(x) = o(x)` -/

/-- A function that is `o(x)` is eventually at most `ε y` in absolute value, for every `ε > 0`. -/
private theorem exists_forall_abs_le_of_isLittleO {G : ℝ → ℝ}
    (hG : G =o[atTop] fun y ↦ y) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y, ∀ y, Y ≤ y → |G y| ≤ ε * y := by
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (hG.def hε)
  refine ⟨max Y 0, fun y hy ↦ ?_⟩
  have h := hY y (le_of_max_le_left hy)
  rwa [norm_eq_abs, norm_eq_abs, abs_of_nonneg (le_of_max_le_right hy)] at h

/-- A function bounded by the right side of the transfer for every `ε > 0` is `o(x)`. -/
private theorem isLittleO_of_forall_abs_le {F : ℝ → ℝ}
    (h : ∀ ε > 0, ∃ X, ∀ x, X ≤ x → |F x| ≤ π ^ 2 / 6 * ε * x + 2 * x ^ (3 / 4 : ℝ)) :
    F =o[atTop] fun x ↦ x := by
  refine Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_
  obtain ⟨X, hX⟩ := h (c / 4) (by positivity)
  have hrpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
    (eventually_le_nhds (by positivity : (0 : ℝ) < c / 4))
  filter_upwards [eventually_ge_atTop X, eventually_gt_atTop 0, hrpow] with x hxX hx₀ hxq
  rw [norm_eq_abs, norm_eq_abs, abs_of_pos hx₀]
  have hpi : π ^ 2 / 6 < 2 := by nlinarith [pi_lt_d2, pi_pos]
  have h34 : x ^ (3 / 4 : ℝ) = x * x ^ (-(1 / 4) : ℝ) := by
    rw [← rpow_one_add' hx₀.le (by norm_num)]
    norm_num
  calc |F x| ≤ π ^ 2 / 6 * (c / 4) * x + 2 * (x * x ^ (-(1 / 4) : ℝ)) := h34 ▸ hX x hxX
    _ ≤ 2 * (c / 4) * x + 2 * (x * (c / 4)) := by gcongr
    _ = c * x := by ring

/-- `L_λ(x) = o(x)` if and only if `M(x) = o(x)`. -/
theorem liouvilleSum_isLittleO_iff :
    (liouvilleSum =o[atTop] fun x ↦ x) ↔ moebiusSum =o[atTop] fun x ↦ x := by
  constructor
  · refine fun hL ↦ isLittleO_of_forall_abs_le fun ε hε ↦ ?_
    obtain ⟨Y, hY⟩ := exists_forall_abs_le_of_isLittleO hL hε
    exact ⟨Y ^ 2, fun x hx ↦ abs_moebiusSum_le_of_abs_liouvilleSum_le hY hx⟩
  · refine fun hM ↦ isLittleO_of_forall_abs_le fun ε hε ↦ ?_
    obtain ⟨Y, hY⟩ := exists_forall_abs_le_of_isLittleO hM hε
    exact ⟨Y ^ 2, fun x hx ↦ abs_liouvilleSum_le_of_abs_moebiusSum_le hY hx⟩

end TauCeti
