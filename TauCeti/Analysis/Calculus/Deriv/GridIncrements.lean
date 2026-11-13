/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform-grid increment bounds from one-sided Lipschitz oscillation

If a curve `f : ℝ → E` satisfies the right-sided pointwise Lipschitz bound
`(f · - f t) =O[𝓝[>] t] (· - t)` at `t ≥ 0` (in particular, if `f` is right-differentiable at `t`),
then for every window length `p : ℕ` and every sufficiently small mesh `h > 0`, the `p` consecutive
uniform-grid increments immediately to the right of `t` (starting at index `⌊t / h⌋₊ + 1`) all have
norm `O(h)`. A dual statement holds for left-sided oscillation `(f · - f t) =O[𝓝[<] t] (· - t)` at
`t > 0`, using the `p` consecutive grid increments immediately to the left of `t` (starting at
index `⌈t / h⌉₊ - (p + 1)`).

Contrapositively, if along dyadic meshes `h = 2⁻ⁿ` every block of `p` consecutive increments on
every bounded horizon `[0, N]` eventually contains an increment exceeding `M / 2ⁿ`, then `f` fails
the right-sided pointwise Lipschitz bound at every `t ≥ 0` and fails the left-sided pointwise
Lipschitz bound at every `t > 0`. In particular, `f` admits no right derivative on `[0, ∞)`, no
left derivative on `(0, ∞)`, and no two-sided derivative on `[0, ∞)`.

## Main statements

* `Asymptotics.IsBigO.exists_forall_norm_sub_mul_le_of_nhdsGT` — right-sided uniform-mesh window
  bound from `(f · - f t) =O[𝓝[>] t] (· - t)` at `t ≥ 0`.
* `Asymptotics.IsBigO.exists_forall_norm_sub_mul_le_of_nhdsLT` — left-sided uniform-mesh window
  bound from `(f · - f t) =O[𝓝[<] t] (· - t)` at `t > 0`.
* `TauCeti.not_isBigO_sub_nhdsGT_of_dyadic` and `TauCeti.not_isBigO_sub_nhdsLT_of_dyadic` —
  obstruction to one-sided pointwise Lipschitz oscillation from dyadic rough-path oscillation.
* `TauCeti.not_differentiableWithinAt_Ici_of_dyadic`,
  `TauCeti.not_differentiableWithinAt_Iic_of_dyadic`, and `TauCeti.not_differentiableAt_of_dyadic` —
  resulting non-existence of one-sided and two-sided derivatives.

## References

* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.30.
* A. Dvoretzky, P. Erdős, S. Kakutani, *Nonincrease everywhere of the Brownian motion process*,
  Proc. Fourth Berkeley Symp. Math. Statist. Probab., Vol. II (1961), 103–116.
-/

public section

open Filter Set
open scoped Topology

namespace Asymptotics.IsBigO

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {t : ℝ}

private theorem floor_add_one_add_mul_mem_Ioc {t h₀ : ℝ} (ht : 0 ≤ t) (hh₀ : 0 < h₀)
    {p k : ℕ} (hk : k ≤ p) :
    ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) * h₀ ∈ Ioc t (t + ((p + 1 : ℕ) : ℝ) * h₀) := by
  refine ⟨?_, ?_⟩
  · have hlt : t / h₀ < ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) := by
      calc
        t / h₀ < (⌊t / h₀⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) := by push_cast; linarith
    exact (div_lt_iff₀ hh₀).mp hlt
  · have hle : ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) ≤ t / h₀ + ((p + 1 : ℕ) : ℝ) := by
      have hfl : (⌊t / h₀⌋₊ : ℝ) ≤ t / h₀ := Nat.floor_le (div_nonneg ht hh₀.le)
      have hkp : (k : ℝ) ≤ p := Nat.cast_le.mpr hk
      push_cast
      linarith
    calc
      ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) * h₀
        ≤ (t / h₀ + ((p + 1 : ℕ) : ℝ)) * h₀ := mul_le_mul_of_nonneg_right hle hh₀.le
      _ = t + ((p + 1 : ℕ) : ℝ) * h₀ := by rw [add_mul, div_mul_cancel₀ _ hh₀.ne']

private theorem ceil_sub_add_mul_mem_Ico {t h₀ : ℝ} (hh₀ : 0 < h₀) {p k : ℕ}
    (hq : p + 1 < ⌈t / h₀⌉₊) (hk : k ≤ p) :
    ((⌈t / h₀⌉₊ - (p + 1) + k : ℕ) : ℝ) * h₀ ∈ Ico (t - ((p + 1 : ℕ) : ℝ) * h₀) t := by
  set m : ℕ := ⌈t / h₀⌉₊ - (p + 1)
  refine ⟨?_, ?_⟩
  · have hceil : t / h₀ ≤ ((m + (p + 1) : ℕ) : ℝ) := by
      have hm : m + (p + 1) = ⌈t / h₀⌉₊ := by omega
      rw [hm]
      exact Nat.le_ceil _
    have hle : t / h₀ - ((p + 1 : ℕ) : ℝ) ≤ ((m + k : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hceil ⊢
      linarith
    calc
      t - ((p + 1 : ℕ) : ℝ) * h₀ = (t / h₀ - ((p + 1 : ℕ) : ℝ)) * h₀ := by
        rw [sub_mul, div_mul_cancel₀ _ hh₀.ne']
      _ ≤ ((m + k : ℕ) : ℝ) * h₀ := mul_le_mul_of_nonneg_right hle hh₀.le
  · have hmk_lt : m + k < ⌈t / h₀⌉₊ := by omega
    exact (lt_div_iff₀ hh₀).mp (Nat.lt_ceil.mp hmk_lt)

/-- If `f` has bounded right-sided linear oscillation `(f · - f t) =O[𝓝[>] t] (· - t)` at `t ≥ 0`,
then for every window length `p : ℕ` there exist `K > 0` and `δ > 0` such that for every mesh
`0 < h` with `(p + 1) * h < δ`, all `p` consecutive grid increments immediately to the right of `t`
have norm at most `K * h`. -/
theorem exists_forall_norm_sub_mul_le_of_nhdsGT
    (h : (f · - f t) =O[𝓝[>] t] (· - t)) (ht : 0 ≤ t) (p : ℕ) :
    ∃ K > 0, ∃ δ > 0, ∀ {h₀ : ℝ}, 0 < h₀ → ((p + 1 : ℕ) : ℝ) * h₀ < δ →
      ∀ j < p,
        ‖f (((⌊t / h₀⌋₊ + 1 + j + 1 : ℕ) : ℝ) * h₀) -
            f (((⌊t / h₀⌋₊ + 1 + j : ℕ) : ℝ) * h₀)‖ ≤ K * h₀ := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨b, htb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound.bound
  refine ⟨2 * ((p + 1 : ℕ) : ℝ) * C, by positivity, b - t, sub_pos.mpr htb, ?_⟩
  intro h₀ hh₀ hmesh j hj
  have hpt (k : ℕ) (hk : k ≤ p) :
      ‖f (((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) * h₀) - f t‖ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by
    obtain ⟨hts, hsb⟩ := floor_add_one_add_mul_mem_Ioc ht hh₀ hk
    set s : ℝ := ((⌊t / h₀⌋₊ + 1 + k : ℕ) : ℝ) * h₀
    calc
      ‖f s - f t‖ ≤ C * ‖s - t‖ := hb ⟨hts, by linarith⟩
      _ = C * (s - t) := by rw [Real.norm_of_nonneg (sub_pos.mpr hts).le]
      _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by gcongr; linarith
  calc
    ‖f (((⌊t / h₀⌋₊ + 1 + j + 1 : ℕ) : ℝ) * h₀) - f (((⌊t / h₀⌋₊ + 1 + j : ℕ) : ℝ) * h₀)‖
      ≤ ‖f (((⌊t / h₀⌋₊ + 1 + (j + 1) : ℕ) : ℝ) * h₀) - f t‖ +
          ‖f t - f (((⌊t / h₀⌋₊ + 1 + j : ℕ) : ℝ) * h₀)‖ := by
        simpa only [Nat.add_assoc] using norm_sub_le_norm_sub_add_norm_sub _ (f t) _
    _ = ‖f (((⌊t / h₀⌋₊ + 1 + (j + 1) : ℕ) : ℝ) * h₀) - f t‖ +
          ‖f (((⌊t / h₀⌋₊ + 1 + j : ℕ) : ℝ) * h₀) - f t‖ := by
        rw [norm_sub_rev (f t)]
    _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) + C * (((p + 1 : ℕ) : ℝ) * h₀) :=
        add_le_add (hpt (j + 1) hj) (hpt j hj.le)
    _ = 2 * ((p + 1 : ℕ) : ℝ) * C * h₀ := by ring

/-- If `f` has bounded left-sided linear oscillation `(f · - f t) =O[𝓝[<] t] (· - t)` at `t > 0`,
then for every window length `p : ℕ` there exist `K > 0` and `δ > 0` such that for every mesh
`0 < h` with `(p + 1) * h < δ`, the index `m = ⌈t / h⌉₊ - (p + 1)` is positive and all `p`
consecutive grid increments from `m * h` to `(m + p) * h` (strictly to the left of `t`) have norm
at most `K * h`. -/
theorem exists_forall_norm_sub_mul_le_of_nhdsLT
    (h : (f · - f t) =O[𝓝[<] t] (· - t)) (ht : 0 < t) (p : ℕ) :
    ∃ K > 0, ∃ δ > 0, ∀ {h₀ : ℝ}, 0 < h₀ → ((p + 1 : ℕ) : ℝ) * h₀ < δ →
      p + 1 < ⌈t / h₀⌉₊ ∧
        ∀ j < p,
          ‖f (((⌈t / h₀⌉₊ - (p + 1) + j + 1 : ℕ) : ℝ) * h₀) -
              f (((⌈t / h₀⌉₊ - (p + 1) + j : ℕ) : ℝ) * h₀)‖ ≤ K * h₀ := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨a, hat, ha⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hbound.bound
  refine ⟨2 * ((p + 1 : ℕ) : ℝ) * C, by positivity, min t (t - a),
    lt_min ht (sub_pos.mpr hat), ?_⟩
  intro h₀ hh₀ hmesh
  have hmesh_t : ((p + 1 : ℕ) : ℝ) * h₀ < t := hmesh.trans_le (min_le_left _ _)
  have hmesh_a : ((p + 1 : ℕ) : ℝ) * h₀ < t - a := hmesh.trans_le (min_le_right _ _)
  have hq : p + 1 < ⌈t / h₀⌉₊ :=
    Nat.cast_lt.mp (((lt_div_iff₀ hh₀).mpr hmesh_t).trans_le (Nat.le_ceil _))
  refine ⟨hq, fun j hj ↦ ?_⟩
  have hpt (k : ℕ) (hk : k ≤ p) :
      ‖f (((⌈t / h₀⌉₊ - (p + 1) + k : ℕ) : ℝ) * h₀) - f t‖ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by
    obtain ⟨hts, hst⟩ := ceil_sub_add_mul_mem_Ico hh₀ hq hk
    set s : ℝ := ((⌈t / h₀⌉₊ - (p + 1) + k : ℕ) : ℝ) * h₀
    calc
      ‖f s - f t‖ ≤ C * ‖s - t‖ := ha ⟨by linarith, hst⟩
      _ = C * (t - s) := by rw [norm_sub_rev, Real.norm_of_nonneg (sub_pos.mpr hst).le]
      _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by gcongr; linarith
  calc
    ‖f (((⌈t / h₀⌉₊ - (p + 1) + j + 1 : ℕ) : ℝ) * h₀) -
        f (((⌈t / h₀⌉₊ - (p + 1) + j : ℕ) : ℝ) * h₀)‖
      ≤ ‖f (((⌈t / h₀⌉₊ - (p + 1) + (j + 1) : ℕ) : ℝ) * h₀) - f t‖ +
          ‖f t - f (((⌈t / h₀⌉₊ - (p + 1) + j : ℕ) : ℝ) * h₀)‖ := by
        simpa only [Nat.add_assoc] using norm_sub_le_norm_sub_add_norm_sub _ (f t) _
    _ = ‖f (((⌈t / h₀⌉₊ - (p + 1) + (j + 1) : ℕ) : ℝ) * h₀) - f t‖ +
          ‖f (((⌈t / h₀⌉₊ - (p + 1) + j : ℕ) : ℝ) * h₀) - f t‖ := by
        rw [norm_sub_rev (f t)]
    _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) + C * (((p + 1 : ℕ) : ℝ) * h₀) :=
        add_le_add (hpt (j + 1) hj) (hpt j hj.le)
    _ = 2 * ((p + 1 : ℕ) : ℝ) * C * h₀ := by ring

end Seminormed

end Asymptotics.IsBigO

namespace TauCeti

section Dyadic

variable {E : Type*}

private theorem eventually_div_two_pow_lt (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, c / (2 : ℝ) ^ n < δ := by
  have hlim : Tendsto (fun n : ℕ ↦ c * (2⁻¹ : ℝ) ^ n) atTop (𝓝 (c * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)).const_mul c
  rw [mul_zero] at hlim
  filter_upwards [(tendsto_order.mp hlim).2 δ hδ] with n hn
  simpa [div_eq_mul_inv, inv_pow] using hn

/-- If along dyadic grids `2⁻ⁿ` every window of `p` consecutive increments on `[0, N]` eventually
contains an increment exceeding `M / 2ⁿ`, then `f` fails the right-sided Lipschitz bound
`(f · - f t) =O[𝓝[>] t] (· - t)` at every `t ≥ 0`. -/
theorem not_isBigO_sub_nhdsGT_of_dyadic [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℕ}
    (hosc : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n,
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℕ) : ℝ) / 2 ^ n) - f (((m + j : ℕ) : ℝ) / 2 ^ n)‖)
    {t : ℝ} (ht : 0 ≤ t) :
    ¬ (f · - f t) =O[𝓝[>] t] (· - t) := by
  intro hO
  obtain ⟨K, _, δ, hδ, hwin⟩ := hO.exists_forall_norm_sub_mul_le_of_nhdsGT ht p
  set N : ℕ := ⌊t⌋₊ + 2
  set M : ℕ := ⌈K⌉₊
  obtain ⟨n, hn_osc, hn_mesh⟩ :=
    ((hosc N M).and (eventually_div_two_pow_lt ((p + 1 : ℕ) : ℝ) hδ)).exists
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hh₀ : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpow_pos
  have hmesh' : ((p + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ < δ := by
    simpa [div_eq_mul_inv] using hn_mesh
  set m : ℕ := ⌊t / ((2 : ℝ) ^ n)⁻¹⌋₊ + 1
  have hm : m < N * 2 ^ n := by
    have htN : t + 1 < (N : ℝ) := by
      have := Nat.lt_floor_add_one t
      push_cast [N]
      linarith
    have hpow_ge : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hm_real : (m : ℝ) < ((N * 2 ^ n : ℕ) : ℝ) := by
      have hfl : (⌊t / ((2 : ℝ) ^ n)⁻¹⌋₊ : ℝ) ≤ t * (2 : ℝ) ^ n := by
        simpa [div_inv_eq_mul] using Nat.floor_le (div_nonneg ht hh₀.le)
      calc
        (m : ℝ) = (⌊t / ((2 : ℝ) ^ n)⁻¹⌋₊ : ℝ) + 1 := by push_cast [m]; rfl
        _ ≤ t * (2 : ℝ) ^ n + (2 : ℝ) ^ n := by linarith
        _ = (t + 1) * (2 : ℝ) ^ n := by ring
        _ < (N : ℝ) * (2 : ℝ) ^ n := mul_lt_mul_of_pos_right htN hpow_pos
        _ = ((N * 2 ^ n : ℕ) : ℝ) := by push_cast; rfl
    exact Nat.cast_lt.mp hm_real
  obtain ⟨j, hj_gt⟩ := hn_osc m hm
  have hj_le : ‖f (((m + j + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) -
      f (((m + j : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)‖ ≤ K * ((2 : ℝ) ^ n)⁻¹ := hwin hh₀ hmesh' j j.isLt
  have hKM : K * ((2 : ℝ) ^ n)⁻¹ ≤ (M : ℝ) * ((2 : ℝ) ^ n)⁻¹ :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) hh₀.le
  simp only [div_eq_mul_inv] at hj_gt
  linarith

/-- If along dyadic grids `2⁻ⁿ` every window of `p` consecutive increments on `[0, N]` eventually
contains an increment exceeding `M / 2ⁿ`, then `f` fails the left-sided Lipschitz bound
`(f · - f t) =O[𝓝[<] t] (· - t)` at every `t > 0`. -/
theorem not_isBigO_sub_nhdsLT_of_dyadic [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℕ}
    (hosc : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n,
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℕ) : ℝ) / 2 ^ n) - f (((m + j : ℕ) : ℝ) / 2 ^ n)‖)
    {t : ℝ} (ht : 0 < t) :
    ¬ (f · - f t) =O[𝓝[<] t] (· - t) := by
  intro hO
  obtain ⟨K, _, δ, hδ, hwin⟩ := hO.exists_forall_norm_sub_mul_le_of_nhdsLT ht p
  set N : ℕ := ⌊t⌋₊ + 1
  set M : ℕ := ⌈K⌉₊
  obtain ⟨n, hn_osc, hn_mesh⟩ :=
    ((hosc N M).and (eventually_div_two_pow_lt ((p + 1 : ℕ) : ℝ) hδ)).exists
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hh₀ : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpow_pos
  have hmesh' : ((p + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ < δ := by
    simpa [div_eq_mul_inv] using hn_mesh
  obtain ⟨hq, hwin'⟩ := hwin hh₀ hmesh'
  set m : ℕ := ⌈t / ((2 : ℝ) ^ n)⁻¹⌉₊ - (p + 1)
  have hm : m < N * 2 ^ n := by
    have htN : t < (N : ℝ) := by
      simpa [N] using Nat.lt_floor_add_one t
    have hceil_le : ⌈t / ((2 : ℝ) ^ n)⁻¹⌉₊ ≤ N * 2 ^ n := by
      refine Nat.ceil_le.mpr ?_
      rw [div_inv_eq_mul]
      push_cast
      exact (mul_lt_mul_of_pos_right htN hpow_pos).le
    omega
  obtain ⟨j, hj_gt⟩ := hn_osc m hm
  have hj_le : ‖f (((m + j + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹) -
      f (((m + j : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹)‖ ≤ K * ((2 : ℝ) ^ n)⁻¹ := hwin' j j.isLt
  have hKM : K * ((2 : ℝ) ^ n)⁻¹ ≤ (M : ℝ) * ((2 : ℝ) ^ n)⁻¹ :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) hh₀.le
  simp only [div_eq_mul_inv] at hj_gt
  linarith

/-- Under the dyadic rough-path oscillation property on `[0, ∞)`, `f` has no right derivative at any
`t ≥ 0`. -/
theorem not_differentiableWithinAt_Ici_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ}
    (hosc : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n,
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℕ) : ℝ) / 2 ^ n) - f (((m + j : ℕ) : ℝ) / 2 ^ n)‖)
    {t : ℝ} (ht : 0 ≤ t) :
    ¬ DifferentiableWithinAt ℝ f (Ici t) t := fun hd ↦
  not_isBigO_sub_nhdsGT_of_dyadic hosc ht
    (hd.isBigO_sub.mono (nhdsWithin_mono _ Ioi_subset_Ici_self))

/-- Under the dyadic rough-path oscillation property on `[0, ∞)`, `f` has no left derivative at any
`t > 0`. -/
theorem not_differentiableWithinAt_Iic_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ}
    (hosc : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n,
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℕ) : ℝ) / 2 ^ n) - f (((m + j : ℕ) : ℝ) / 2 ^ n)‖)
    {t : ℝ} (ht : 0 < t) :
    ¬ DifferentiableWithinAt ℝ f (Iic t) t := fun hd ↦
  not_isBigO_sub_nhdsLT_of_dyadic hosc ht
    (hd.isBigO_sub.mono (nhdsWithin_mono _ Iio_subset_Iic_self))

/-- Under the dyadic rough-path oscillation property on `[0, ∞)`, `f` is not differentiable at any
`t ≥ 0`. -/
theorem not_differentiableAt_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ}
    (hosc : ∀ N M : ℕ, ∀ᶠ n in atTop, ∀ m < N * 2 ^ n,
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℕ) : ℝ) / 2 ^ n) - f (((m + j : ℕ) : ℝ) / 2 ^ n)‖)
    {t : ℝ} (ht : 0 ≤ t) :
    ¬ DifferentiableAt ℝ f t := fun hd ↦
  not_differentiableWithinAt_Ici_of_dyadic hosc ht hd.differentiableWithinAt

end Dyadic

end TauCeti
