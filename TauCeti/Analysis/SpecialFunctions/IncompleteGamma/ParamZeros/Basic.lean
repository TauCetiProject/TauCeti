/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Real
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.ParamZeros.TailIntegral

/-!
# Parameter zeros of Tricomi's incomplete Gamma function

This file classifies the real zeros of Tricomi's entire incomplete Gamma function
`a ↦ γ*(a, x)` for a fixed real argument `x` (DLMF §8.13(iii)).

For `x = 0`, `γ*(a, 0) = 1 / Γ(a + 1)` vanishes precisely at the negative integers `a = -n`
(`n ≥ 1`). For `x < 0`, the series `Γ(a) γ*(a, x) = ∑ (-x)^k / (k! (a + k))` is strictly
decreasing and changes sign on each unit band `(-(m + 1), -m)`, yielding a unique zero per unit
band and hence exactly two zeros in `(-2n, 2 - 2n)` for every `n ≥ 1`.

For `x > 0` and `n ≥ 1`, on the even band `(-2n, 1 - 2n)` we have
`x^a Re γ*(a, x) = 1 - I(a, x) / Γ(a)` where `I(a, x) = ∫_x^∞ t^{a - 1} e^{-t} dt`. Combining
the tail-integral curvature bound `(log I(·, x))''(a) < (a ^ 2)⁻¹` with the trigamma lower bound
`(log Γ)''(a) = ψ'(a) ≥ (a ^ 2)⁻¹` shows that the log-ratio `L(a, x) = log I(a, x) - log Γ(a)` is
strictly concave in `a` and tends to `-∞` at both endpoints. Thus `a ↦ L(a, x)` has a unique
maximum `M(x)` which decreases strictly and continuously from `+∞` to `-∞` on `(0, ∞)`, whose
unique root `x*_n > 0` separates two simple zeros, one double zero, and no zeros.

## Main results

* `Complex.tricomiIncompleteGamma_zero_right_eq_zero_iff` — DLMF §8.13(iii)(c): `γ*(a, 0) = 0` iff
  `a = -n` for some `n ≥ 1`.
* `Complex.existsUnique_tricomiIncompleteGamma_eq_zero_of_neg` — unique zero in each unit band
  `(-(m + 1), -m)` for `x < 0`.
* `Complex.tricomiIncompleteGamma_param_zeros_of_neg` — DLMF §8.13(iii)(a): exactly two zeros
  in `(-2n, 2 - 2n)` for `x < 0` and `n ≥ 1`.
* `Complex.tricomiIncompleteGamma_param_zeros` — DLMF §8.13(iii)(b): threshold `x*_n > 0`
  governing simple, double, and absent zeros in `(-2n, 1 - 2n)` for `x > 0` and `n ≥ 1`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*,
  Math. Z. 53 (1950), 136–148.
* K. S. Kölbig, *On the zeros of the incomplete gamma function*,
  Math. Comp. 26 (1972), 751–756.
-/

public section

noncomputable section

open Complex Filter Finset MeasureTheory Set
open scoped Nat Topology Interval

namespace Complex

/-! ### Zeros at `x = 0` (DLMF §8.13(iii)(c)) -/

/-- **DLMF §8.13(iii)(c)**: at `z = 0`, Tricomi's function `γ*(a, 0) = 1 / Γ(a + 1)` vanishes
precisely at the negative integers `a = -n` with `n ≥ 1`. -/
theorem tricomiIncompleteGamma_zero_right_eq_zero_iff (a : ℂ) :
    tricomiIncompleteGamma a 0 = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℂ) := by
  rw [tricomiIncompleteGamma_zero_right, inv_eq_zero, Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, Nat.succ_pos m, by push_cast; linear_combination hm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n - 1, by rw [Nat.cast_sub hn, Nat.cast_one]; ring⟩

/-! ### Reality of `γ*` at real arguments and band helpers -/

private theorem tricomiIncompleteGamma_ofReal_im (a x : ℝ) :
    (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).im = 0 := by
  have h := Complex.imCLM.hasSum (hasSum_tricomiIncompleteGamma (a : ℂ) (x : ℂ))
  have hzero : (fun k : ℕ =>
      Complex.imCLM (cexp (-(x : ℂ)) * (x : ℂ) ^ k / Gamma ((a : ℂ) + k + 1))) = 0 := by
    ext k
    simp only [Pi.zero_apply]
    have hterm : cexp (-(x : ℂ)) * (x : ℂ) ^ k / Gamma ((a : ℂ) + k + 1) =
        ((Real.exp (-x) * x ^ k / Real.Gamma (a + k + 1) : ℝ) : ℂ) := by
      rw [ofReal_div, ofReal_mul, ofReal_exp, ofReal_neg, ofReal_pow, ← Gamma_ofReal]
      push_cast; rfl
    rw [hterm, imCLM_apply, ofReal_im]
  rw [hzero] at h
  exact (hasSum_zero.unique h).symm

private theorem tricomiIncompleteGamma_ofReal_eq_zero_iff (a x : ℝ) :
    tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0 ↔
      (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re = 0 :=
  ⟨fun h => by simp [h], fun h => Complex.ext h (tricomiIncompleteGamma_ofReal_im a x)⟩

private theorem continuous_re_tricomiIncompleteGamma_left (x : ℝ) :
    Continuous fun a : ℝ => (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re :=
  Complex.continuous_re.comp
    ((differentiable_tricomiIncompleteGamma_left (x : ℂ)).continuous.comp continuous_ofReal)

private theorem ne_neg_natCast_of_mem_Ioo_neg_nat {m : ℕ} {a : ℝ}
    (ha : a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ))) : ∀ k : ℕ, a ≠ -(k : ℝ) := by
  intro k hk
  have : m < k := by exact_mod_cast (by linarith [ha.2] : (m : ℝ) < k)
  have : k < m + 1 := by exact_mod_cast (by linarith [ha.1] : (k : ℝ) < m + 1)
  omega

private theorem evenBand_lt_neg_one {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : a < -1 := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [ha.2]

private theorem evenBand_ne_neg_natCast {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : ∀ k : ℕ, a ≠ -(k : ℝ) :=
  ne_neg_natCast_of_mem_Ioo_neg_nat (m := 2 * n - 1) <| by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

private theorem hasSum_Gamma_mul_re_tricomiIncompleteGamma {a : ℝ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) (x : ℝ) :
    HasSum (fun k : ℕ => (-x) ^ k / ((k ! : ℝ) * (a + k)))
      (Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re) := by
  have haC : ∀ k : ℕ, (a : ℂ) ≠ -(k : ℂ) := fun k h => ha k (by exact_mod_cast h)
  have h := Complex.reCLM.hasSum
    ((hasSum_tricomiIncompleteGamma_of_ne_neg_natCast haC (x : ℂ)).mul_left (Gamma (a : ℂ)))
  have hval : Complex.reCLM (Gamma (a : ℂ) * tricomiIncompleteGamma (a : ℂ) (x : ℂ)) =
      Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re := by
    simp [Gamma_ofReal, mul_re]
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  have hterm : Gamma (a : ℂ) * ((Gamma (a : ℂ))⁻¹ * ((-(x : ℂ)) ^ k / (k ! * ((a : ℂ) + k)))) =
      (((-x) ^ k / ((k ! : ℝ) * (a + k)) : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_inv_cancel₀ (Gamma_ne_zero haC), one_mul]
    push_cast; rfl
  rw [reCLM_apply, hterm, ofReal_re]

/-! ### Parameter zeros for `x < 0` (DLMF §8.13(iii)(a)) -/

private theorem strictAntiOn_Gamma_mul_re_tricomi_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    StrictAntiOn (fun a : ℝ => Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re)
      (Ioo (-(m + 1 : ℝ)) (-(m : ℝ))) := by
  intro a₁ ha₁ a₂ ha₂ hlt
  dsimp only
  have hs₁ := hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_natCast_of_mem_Ioo_neg_nat ha₁) x
  have hs₂ := hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_natCast_of_mem_Ioo_neg_nat ha₂) x
  rw [← hs₁.tsum_eq, ← hs₂.tsum_eq]
  have hy : 0 < -x := by linarith
  have hterm : ∀ k : ℕ, (-x) ^ k / ((k ! : ℝ) * (a₂ + k)) <
      (-x) ^ k / ((k ! : ℝ) * (a₁ + k)) := fun k => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
    refine mul_lt_mul_of_pos_left
      (mul_lt_mul_of_pos_left ?_ (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k))))
      (pow_pos hy k)
    by_cases hk : k ≤ m
    · have : (k : ℝ) ≤ m := by exact_mod_cast hk
      have hneg := inv_strictAnti₀ (by linarith [ha₂.2] : 0 < -(a₂ + k))
        (by linarith : -(a₂ + k) < -(a₁ + k))
      simp only [inv_neg] at hneg; linarith
    · have : (m + 1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hk)
      exact inv_strictAnti₀ (by linarith [ha₁.1]) (by linarith)
  exact hs₂.summable.tsum_lt_tsum (i := 0) (fun k => (hterm k).le) (hterm 0) hs₁.summable

private theorem exists_pos_Gamma_mul_re_tricomi_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)),
      0 < Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re := by
  let y : ℝ := -x
  have hy : 0 < y := by dsimp [y]; linarith
  let ε : ℝ := min (1 / 4) (y ^ (m + 1) / (((m + 1)! : ℝ) * (4 * Real.exp y)))
  have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_q : ε ≤ 1 / 4 := min_le_left _ _
  have hε_b : ε ≤ y ^ (m + 1) / (((m + 1)! : ℝ) * (4 * Real.exp y)) := min_le_right _ _
  let a : ℝ := -(m + 1 : ℝ) + ε
  have ha : a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)) := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  refine ⟨a, ha, ?_⟩
  have hsplit := (hasSum_nat_add_iff' (m + 2)).mpr
    (hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_natCast_of_mem_Ioo_neg_nat ha) x)
  have htail_nonneg : 0 ≤ ∑' k : ℕ,
      y ^ (k + (m + 2)) / (((k + (m + 2))! : ℝ) * (a + ((k + (m + 2) : ℕ) : ℝ))) :=
    tsum_nonneg fun k => div_nonneg (by positivity)
      (mul_nonneg (by positivity) (by push_cast [a]; linarith))
  have hneg_part : -2 * Real.exp y ≤ ∑ k ∈ range (m + 1), y ^ k / ((k ! : ℝ) * (a + k)) := by
    have hle : ∑ k ∈ range (m + 1), (-2) * (y ^ k / (k ! : ℝ)) ≤
        ∑ k ∈ range (m + 1), y ^ k / ((k ! : ℝ) * (a + k)) := Finset.sum_le_sum fun k hk => by
      have hkm : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hinv : (-2 : ℝ) ≤ (a + k)⁻¹ := by
        have h : (-(a + k))⁻¹ ≤ 2 :=
          (inv_le_comm₀ (by dsimp [a]; linarith : 0 < -(a + k)) (by norm_num)).mpr
            (by dsimp [a]; linarith)
        have h' := neg_le_neg h
        rwa [inv_neg, neg_neg] at h'
      rw [div_eq_mul_inv (y ^ k) ((k ! : ℝ) * (a + k)), mul_inv, ← mul_assoc, ← div_eq_mul_inv,
        mul_comm (-2)]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    rw [← Finset.mul_sum] at hle
    linarith [Real.sum_le_exp_of_nonneg hy.le (m + 1)]
  have hmain : 4 * Real.exp y ≤ y ^ (m + 1) / (((m + 1)! : ℝ) * (a + ((m + 1 : ℕ) : ℝ))) := by
    have ha_eq : a + ((m + 1 : ℕ) : ℝ) = ε := by push_cast [a]; ring
    rw [ha_eq, le_div_iff₀ (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hε_pos)]
    linarith [(le_div_iff₀ (by positivity : (0 : ℝ) < ((m + 1)! : ℝ) * (4 * Real.exp y))).mp hε_b]
  have hval := hsplit.tsum_eq
  rw [Finset.sum_range_succ] at hval
  linarith [Real.exp_pos y]

private theorem exists_neg_Gamma_mul_re_tricomi_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃ a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)),
      Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re < 0 := by
  let y : ℝ := -x
  have hy : 0 < y := by dsimp [y]; linarith
  let ε : ℝ := min (1 / 4) (y ^ m / ((m ! : ℝ) * (4 * Real.exp y)))
  have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_q : ε ≤ 1 / 4 := min_le_left _ _
  have hε_b : ε ≤ y ^ m / ((m ! : ℝ) * (4 * Real.exp y)) := min_le_right _ _
  let a : ℝ := -(m : ℝ) - ε
  have ha : a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)) := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  refine ⟨a, ha, ?_⟩
  have hsplit := (hasSum_nat_add_iff' (m + 1)).mpr
    (hasSum_Gamma_mul_re_tricomiIncompleteGamma (ne_neg_natCast_of_mem_Ioo_neg_nat ha) x)
  have hhead_le : ∑ k ∈ range (m + 1), y ^ k / ((k ! : ℝ) * (a + k)) ≤ -(4 * Real.exp y) := by
    rw [Finset.sum_range_succ]
    have hprev : ∑ k ∈ range m, y ^ k / ((k ! : ℝ) * (a + k)) ≤ 0 := Finset.sum_nonpos fun k hk =>
      div_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (by
          have : (k : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hk
          dsimp [a]; linarith))
    have hm_term : y ^ m / ((m ! : ℝ) * (a + m)) ≤ -(4 * Real.exp y) := by
      have ha_eq : a + (m : ℝ) = -ε := by dsimp [a]; ring
      rw [ha_eq, mul_neg, div_neg, neg_le_neg_iff,
        le_div_iff₀ (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hε_pos)]
      linarith [(le_div_iff₀ (by positivity : (0 : ℝ) < (m ! : ℝ) * (4 * Real.exp y))).mp hε_b]
    linarith
  have htail_le :
      ∑' k : ℕ, y ^ (k + (m + 1)) / (((k + (m + 1))! : ℝ) * (a + ((k + (m + 1) : ℕ) : ℝ))) ≤
        2 * Real.exp y := by
    have hexp2 : HasSum (fun k : ℕ => 2 * (y ^ k / (k ! : ℝ))) (2 * Real.exp y) := by
      simpa [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp y).mul_left 2
    have hsh := (hasSum_nat_add_iff' (m + 1)).mpr hexp2
    have h1 := hsplit.summable.tsum_le_tsum (fun k => by
      have hinv : (a + ((k + (m + 1) : ℕ) : ℝ))⁻¹ ≤ 2 :=
        (inv_le_comm₀ (by push_cast [a]; linarith) (by norm_num)).mpr (by push_cast [a]; linarith)
      rw [div_eq_mul_inv (y ^ _), mul_inv, ← mul_assoc, ← div_eq_mul_inv, mul_comm 2]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)) hsh.summable
    have hpre : 0 ≤ ∑ k ∈ range (m + 1), 2 * (y ^ k / (k ! : ℝ)) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith [hsh.tsum_eq]
  linarith [hsplit.tsum_eq, Real.exp_pos y]

/-- For fixed `x < 0` and every `m : ℕ`, Tricomi's function `a ↦ γ*(a, x)` has a unique zero
in the open unit interval `(-(m + 1), -m)`. -/
theorem existsUnique_tricomiIncompleteGamma_eq_zero_of_neg {x : ℝ} (hx : x < 0) (m : ℕ) :
    ∃! a : ℝ, a ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)) ∧
      tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0 := by
  let g : ℝ → ℝ := fun a => Real.Gamma a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re
  have hanti := strictAntiOn_Gamma_mul_re_tricomi_of_neg hx m
  obtain ⟨a₁, ha₁, hpos⟩ := exists_pos_Gamma_mul_re_tricomi_of_neg hx m
  obtain ⟨a₂, ha₂, hneg⟩ := exists_neg_Gamma_mul_re_tricomi_of_neg hx m
  have ha₁₂ : a₁ < a₂ := by
    by_contra h; push Not at h
    rcases h.eq_or_lt with rfl | hgt
    · linarith
    · linarith [hanti ha₂ ha₁ hgt]
  have hcont : ContinuousOn g (Icc a₁ a₂) :=
    ContinuousOn.mul (fun a ha => (Real.differentiableAt_Gamma
      (ne_neg_natCast_of_mem_Ioo_neg_nat ⟨ha₁.1.trans_le ha.1, ha.2.trans_lt ha₂.2⟩)).continuousAt
      |>.continuousWithinAt) (continuous_re_tricomiIncompleteGamma_left x).continuousOn
  obtain ⟨a₀, ha₀_mem, ha₀_eq⟩ := intermediate_value_Icc' ha₁₂.le hcont ⟨hneg.le, hpos.le⟩
  have ha₀_Ioo : a₀ ∈ Ioo (-(m + 1 : ℝ)) (-(m : ℝ)) :=
    ⟨ha₁.1.trans_le ha₀_mem.1, ha₀_mem.2.trans_lt ha₂.2⟩
  refine ⟨a₀, ⟨ha₀_Ioo, ?_⟩, fun a ⟨ha_Ioo, ha_zero⟩ => ?_⟩
  · rw [tricomiIncompleteGamma_ofReal_eq_zero_iff]
    exact (mul_eq_zero.mp ha₀_eq).resolve_left
      (Real.Gamma_ne_zero (ne_neg_natCast_of_mem_Ioo_neg_nat ha₀_Ioo))
  · exact hanti.injOn ha_Ioo ha₀_Ioo
      ((by simp [g, (tricomiIncompleteGamma_ofReal_eq_zero_iff a x).mp ha_zero] : g a = 0).trans
        ha₀_eq.symm)

/-- **DLMF §8.13(iii)(a)**: for fixed `x < 0` and `n ≥ 1`, Tricomi's function `a ↦ γ*(a, x)` has
exactly two zeros in the open interval `(-2n, 2 - 2n)`, one in `(-2n, 1 - 2n)` and one in
`(1 - 2n, 2 - 2n)`. -/
theorem tricomiIncompleteGamma_param_zeros_of_neg {x : ℝ} (hx : x < 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (2 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = {a₁, a₂} := by
  have hm1 : -((2 * n - 1 : ℕ) + 1 : ℝ) = -2 * n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hm1' : -((2 * n - 1 : ℕ) : ℝ) = 1 - 2 * n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hm2 : -((2 * n - 2 : ℕ) + 1 : ℝ) = 1 - 2 * n := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]; push_cast; ring
  have hm2' : -((2 * n - 2 : ℕ) : ℝ) = 2 - 2 * n := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]; push_cast; ring
  obtain ⟨a₁, ⟨ha₁_mem, ha₁_zero⟩, ha₁_uniq⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 1)
  obtain ⟨a₂, ⟨ha₂_mem, ha₂_zero⟩, ha₂_uniq⟩ :=
    existsUnique_tricomiIncompleteGamma_eq_zero_of_neg hx (2 * n - 2)
  rw [hm1, hm1'] at ha₁_mem
  rw [hm2, hm2'] at ha₂_mem
  refine ⟨a₁, a₂, ha₁_mem.2.trans ha₂_mem.1, ?_⟩
  ext a
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨ha_mem, ha_zero⟩ => ?_, ?_⟩
  · rcases lt_trichotomy a (1 - 2 * (n : ℝ)) with hlt | heq | hgt
    · exact Or.inl (ha₁_uniq a ⟨by rw [hm1, hm1']; exact ⟨ha_mem.1, hlt⟩, ha_zero⟩)
    · exfalso
      have hcast : (a : ℂ) = -((2 * n - 1 : ℕ) : ℂ) := by
        rw [heq, Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
      rw [hcast, tricomiIncompleteGamma_neg_natCast] at ha_zero
      exact pow_ne_zero _ (ofReal_ne_zero.mpr hx.ne) ha_zero
    · exact Or.inr (ha₂_uniq a ⟨by rw [hm2, hm2']; exact ⟨hgt, ha_mem.2⟩, ha_zero⟩)
  · rintro (rfl | rfl)
    · exact ⟨⟨ha₁_mem.1, ha₁_mem.2.trans (by linarith)⟩, ha₁_zero⟩
    · exact ⟨⟨(by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ)).trans ha₂_mem.1, ha₂_mem.2⟩, ha₂_zero⟩

/-! ### Strict concavity of the log-ratio on even bands -/

private theorem evenBand_Gamma_pos {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) : 0 < Real.Gamma a := by
  have hm : a ∈ Ioo (-((2 * n - 1 : ℕ) + 1 : ℝ)) (-((2 * n - 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have h := Real.neg_one_pow_mul_Gamma_pos hm
  have hpow : (-1 : ℝ) ^ (2 * n - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n), pow_mul]
    norm_num
  rwa [hpow, one_mul] at h

private def logRatio (a x : ℝ) : ℝ :=
  Real.log (∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t)) - Real.log (Real.Gamma a)

private def logRatioDeriv (a x : ℝ) : ℝ :=
  deriv (fun b : ℝ => Real.log (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t))) a - Real.digamma a

private def logRatioDeriv2 (a x : ℝ) : ℝ :=
  deriv (deriv fun b : ℝ => Real.log (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t))) a -
    deriv Real.digamma a

private theorem hasDerivAt_logRatio {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => logRatio b x) (logRatioDeriv a x) a := by
  have ha_neg : a < 0 := (evenBand_lt_neg_one hn ha).trans (by norm_num)
  exact (TauCeti.differentiableAt_log_integral_rpow_sub_one_mul_exp_neg
    ha_neg hx).hasDerivAt.fun_sub
    (Real.hasDerivAt_log_Gamma (evenBand_ne_neg_natCast hn ha))

private theorem hasDerivAt_logRatioDeriv {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => logRatioDeriv b x) (logRatioDeriv2 a x) a := by
  have ha_neg : a < 0 := (evenBand_lt_neg_one hn ha).trans (by norm_num)
  exact (TauCeti.differentiableAt_deriv_log_integral_rpow_sub_one_mul_exp_neg
    ha_neg hx).hasDerivAt.fun_sub
    (Real.differentiableAt_digamma (evenBand_ne_neg_natCast hn ha)).hasDerivAt

private theorem logRatioDeriv2_neg {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    logRatioDeriv2 a x < 0 := by
  have ha_neg : a < 0 := (evenBand_lt_neg_one hn ha).trans (by norm_num)
  have hv := TauCeti.deriv_deriv_log_integral_rpow_sub_one_mul_exp_neg_lt ha_neg hx
  have hp := Real.inv_sq_le_deriv_digamma (evenBand_ne_neg_natCast hn ha)
  simp only [logRatioDeriv2]
  linarith

private theorem strictAntiOn_logRatioDeriv {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    StrictAntiOn (fun a : ℝ => logRatioDeriv a x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun a ha => (hasDerivAt_logRatioDeriv hn ha hx).continuousAt.continuousWithinAt) fun a ha => ?_
  rw [interior_Ioo] at ha
  rw [(hasDerivAt_logRatioDeriv hn ha hx).deriv]
  exact logRatioDeriv2_neg hn ha hx

private theorem log_tailGamma_le_of_evenBand {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ B : ℝ, ∀ a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      Real.log (∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t)) ≤ B := by
  let C : ℝ := max (x ^ (-2 * (n : ℝ))) (x ^ (1 - 2 * (n : ℝ)))
  refine ⟨Real.log C, fun a ha => ?_⟩
  have hpow_le : x ^ a ≤ C := by
    rcases le_total 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 ha.2.le).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 ha.1.le).trans (le_max_left _ _)
  exact Real.log_le_log (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a hx)
    ((TauCeti.integral_rpow_sub_one_mul_exp_neg_le_rpow
      (evenBand_lt_neg_one hn ha).le hx).trans hpow_le)

private theorem tendsto_logRatio_atBot_left {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ => logRatio a x) (𝓝[>] (-2 * (n : ℝ))) atBot := by
  obtain ⟨B, hB⟩ := log_tailGamma_le_of_evenBand hn hx
  have hG : Tendsto Real.Gamma (𝓝[>] (-2 * (n : ℝ))) atTop := by
    have h := Real.tendsto_neg_one_pow_mul_Gamma_nhdsGT_atTop (2 * n)
    have hpt : -((2 * n : ℕ) : ℝ) = -2 * (n : ℝ) := by push_cast; ring
    have hpow : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
    simpa [hpt, hpow] using h
  have hupper : Tendsto (fun a : ℝ => B - Real.log (Real.Gamma a)) (𝓝[>] (-2 * (n : ℝ))) atBot := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add_atBot
      (tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp hG))
  refine tendsto_atBot_mono' _ ?_ hupper
  filter_upwards [Ioo_mem_nhdsGT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))] with a ha
  simp only [logRatio]; linarith [hB a ha]

private theorem tendsto_logRatio_atBot_right {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ => logRatio a x) (𝓝[<] (1 - 2 * (n : ℝ))) atBot := by
  obtain ⟨B, hB⟩ := log_tailGamma_le_of_evenBand hn hx
  have hG : Tendsto Real.Gamma (𝓝[<] (1 - 2 * (n : ℝ))) atTop := by
    have h := Real.tendsto_neg_one_pow_mul_Gamma_nhdsLT_atTop (2 * n - 1)
    have hpt : -((2 * n - 1 : ℕ) : ℝ) = 1 - 2 * (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
    have hpow : (-1 : ℝ) ^ (2 * n - 1 + 1) = 1 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n), pow_mul]; norm_num
    simpa [hpt, hpow] using h
  have hupper : Tendsto (fun a : ℝ => B - Real.log (Real.Gamma a))
      (𝓝[<] (1 - 2 * (n : ℝ))) atBot := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add_atBot
      (tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp hG))
  refine tendsto_atBot_mono' _ ?_ hupper
  filter_upwards [Ioo_mem_nhdsLT (by linarith : -2 * (n : ℝ) < 1 - 2 * (n : ℝ))] with a ha
  simp only [logRatio]; linarith [hB a ha]

/-! ### Global maximum `M(x)`, threshold `x*_n`, and classification for `x > 0` -/

private def maxLogRatio (n : ℕ) (x : ℝ) : ℝ :=
  sSup ((fun a : ℝ => logRatio a x) '' Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))

private theorem exists_maximizer_logRatio {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)),
      logRatioDeriv a₀ x = 0 ∧
      StrictMonoOn (fun a : ℝ => logRatio a x) (Ioc (-2 * (n : ℝ)) a₀) ∧
      StrictAntiOn (fun a : ℝ => logRatio a x) (Ico a₀ (1 - 2 * (n : ℝ))) ∧
      maxLogRatio n x = logRatio a₀ x := by
  -- Cut off both poles where `logRatio → -∞`, maximize on `[l, r]`, then use strict concavity.
  let c : ℝ := -2 * (n : ℝ) + 1 / 2
  have hc : c ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  obtain ⟨l, hl_lt, hl_Ioo⟩ := (((tendsto_logRatio_atBot_left hn hx).eventually
    (eventually_lt_atBot (logRatio c x))).and (Ioo_mem_nhdsGT hc.1)).exists
  obtain ⟨r, hr_lt, hr_Ioo⟩ := (((tendsto_logRatio_atBot_right hn hx).eventually
    (eventually_lt_atBot (logRatio c x))).and (Ioo_mem_nhdsLT hc.2)).exists
  have hcont_Ioo : ContinuousOn (fun a : ℝ => logRatio a x)
      (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :=
    fun a ha => (hasDerivAt_logRatio hn ha hx).continuousAt.continuousWithinAt
  have hsub : Icc l r ⊆ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    fun a ha => ⟨hl_Ioo.1.trans_le ha.1, ha.2.trans_lt hr_Ioo.2⟩
  obtain ⟨a₀, ha₀_Icc, ha₀_max⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (hl_Ioo.2.trans hr_Ioo.1).le) (hcont_Ioo.mono hsub)
  have hle_a₀ : logRatio c x ≤ logRatio a₀ x := ha₀_max ⟨hl_Ioo.2.le, hr_Ioo.1.le⟩
  have ha₀_gt_l : l < a₀ := lt_of_le_of_ne ha₀_Icc.1 (fun h => by subst h; linarith)
  have ha₀_lt_r : a₀ < r := lt_of_le_of_ne ha₀_Icc.2 (fun h => by subst h; linarith)
  have ha₀_Ioo : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := hsub ha₀_Icc
  have hloc : IsLocalMax (fun a : ℝ => logRatio a x) a₀ := by
    filter_upwards [Icc_mem_nhds ha₀_gt_l ha₀_lt_r] with a ha; exact ha₀_max ha
  have hd0 : logRatioDeriv a₀ x = 0 := hloc.hasDerivAt_eq_zero (hasDerivAt_logRatio hn ha₀_Ioo hx)
  have hanti_d := strictAntiOn_logRatioDeriv hn hx
  have hmono_left : StrictMonoOn (fun a : ℝ => logRatio a x) (Ioc (-2 * (n : ℝ)) a₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc _ _)
      (hcont_Ioo.mono fun a ha => ⟨ha.1, ha.2.trans_lt ha₀_Ioo.2⟩) fun a ha => ?_
    rw [interior_Ioc] at ha
    have ha_Ioo : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := ⟨ha.1, ha.2.trans ha₀_Ioo.2⟩
    rw [(hasDerivAt_logRatio hn ha_Ioo hx).deriv, ← hd0]
    exact hanti_d ha_Ioo ha₀_Ioo ha.2
  have hanti_right : StrictAntiOn (fun a : ℝ => logRatio a x) (Ico a₀ (1 - 2 * (n : ℝ))) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico _ _)
      (hcont_Ioo.mono fun a ha => ⟨ha₀_Ioo.1.trans_le ha.1, ha.2⟩) fun a ha => ?_
    rw [interior_Ico] at ha
    have ha_Ioo : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) := ⟨ha₀_Ioo.1.trans ha.1, ha.2⟩
    rw [(hasDerivAt_logRatio hn ha_Ioo hx).deriv, ← hd0]
    exact hanti_d ha₀_Ioo ha_Ioo ha.1
  have hgreatest : IsGreatest ((fun a : ℝ => logRatio a x) '' Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)))
      (logRatio a₀ x) := by
    refine ⟨⟨a₀, ha₀_Ioo, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rcases le_total a a₀ with hle | hge
    · exact hmono_left.monotoneOn ⟨ha.1, hle⟩ ⟨ha₀_Ioo.1, le_rfl⟩ hle
    · exact hanti_right.antitoneOn ⟨le_rfl, ha₀_Ioo.2⟩ ⟨hge, ha.2⟩ hge
  exact ⟨a₀, ha₀_Ioo, hd0, hmono_left, hanti_right, hgreatest.csSup_eq⟩

private theorem logRatio_le_maxLogRatio {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    logRatio a x ≤ maxLogRatio n x := by
  obtain ⟨a₀, ha₀, _, hmono, hanti, hmax⟩ := exists_maximizer_logRatio hn hx
  rw [hmax]
  rcases le_total a a₀ with hle | hge
  · exact hmono.monotoneOn ⟨ha.1, hle⟩ ⟨ha₀.1, le_rfl⟩ hle
  · exact hanti.antitoneOn ⟨le_rfl, ha₀.2⟩ ⟨hge, ha.2⟩ hge

private theorem strictAntiOn_maxLogRatio {n : ℕ} (hn : 1 ≤ n) :
    StrictAntiOn (maxLogRatio n) (Ioi (0 : ℝ)) := by
  intro x₁ hx₁ x₂ hx₂ hlt
  obtain ⟨a₂, ha₂, _, _, _, hmax₂⟩ := exists_maximizer_logRatio hn hx₂
  have hadd := intervalIntegral.integral_interval_add_Ioi
    (TauCeti.integrableOn_rpow_sub_one_mul_exp_neg a₂ hx₁)
    (TauCeti.integrableOn_rpow_sub_one_mul_exp_neg a₂ hx₂)
  have hint_seg : IntervalIntegrable (fun t : ℝ => t ^ (a₂ - 1) * Real.exp (-t)) volume x₁ x₂ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).mpr
      ((TauCeti.integrableOn_rpow_sub_one_mul_exp_neg a₂ hx₁).mono_set Ioc_subset_Ioi_self)
  have hseg_pos : 0 < ∫ t in x₁..x₂, t ^ (a₂ - 1) * Real.exp (-t) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint_seg
      (fun t ht => mul_pos (Real.rpow_pos_of_pos (hx₁.trans ht.1) _) (Real.exp_pos _)) hlt
  have htail_lt : (∫ t in Ioi x₂, t ^ (a₂ - 1) * Real.exp (-t)) <
      ∫ t in Ioi x₁, t ^ (a₂ - 1) * Real.exp (-t) := by linarith
  have hlog_lt : logRatio a₂ x₂ < logRatio a₂ x₁ := by
    simp only [logRatio]
    linarith [Real.log_lt_log (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a₂ hx₂) htail_lt]
  exact hmax₂.trans_lt (hlog_lt.trans_le (logRatio_le_maxLogRatio hn ha₂ hx₁))

private theorem maxLogRatio_sub_le {n : ℕ} (hn : 1 ≤ n)
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) :
    maxLogRatio n x₁ - maxLogRatio n x₂ ≤ (x₂ - x₁) + (2 * (n : ℝ) + 1) * Real.log (x₂ / x₁) := by
  have hx₂ : 0 < x₂ := hx₁.trans_le hle
  obtain ⟨a₁, ha₁, _, _, _, hmax₁⟩ := exists_maximizer_logRatio hn hx₁
  have ha₁_le1 : a₁ ≤ 1 := (evenBand_lt_neg_one hn ha₁).le.trans (by norm_num)
  have hshift := TauCeti.mul_integral_rpow_sub_one_mul_exp_neg_le ha₁_le1 hx₁ hle
  have hpow : (x₂ / x₁) ^ (-(2 * (n : ℝ) + 1)) ≤ (x₂ / x₁) ^ (a₁ - 1) :=
    Real.rpow_le_rpow_of_exponent_le ((one_le_div hx₁).mpr hle) (by linarith [ha₁.1])
  have hscale_le : Real.exp (-(x₂ - x₁)) * (x₂ / x₁) ^ (-(2 * (n : ℝ) + 1)) *
      (∫ t in Ioi x₁, t ^ (a₁ - 1) * Real.exp (-t)) ≤
      ∫ t in Ioi x₂, t ^ (a₁ - 1) * Real.exp (-t) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
      (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a₁ hx₁).le).trans hshift
  have hlog := Real.log_le_log
    (mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (div_pos hx₂ hx₁) _))
      (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a₁ hx₁)) hscale_le
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (div_pos hx₂ hx₁) _)).ne'
      (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a₁ hx₁).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (div_pos hx₂ hx₁) _).ne',
    Real.log_exp, Real.log_rpow (div_pos hx₂ hx₁)] at hlog
  have hle_max₂ := logRatio_le_maxLogRatio hn ha₁ hx₂
  rw [hmax₁]; simp only [logRatio] at hle_max₂ ⊢; linarith

private theorem continuousOn_maxLogRatio {n : ℕ} (hn : 1 ≤ n) :
    ContinuousOn (maxLogRatio n) (Ioi (0 : ℝ)) := by
  intro x hx
  refine ContinuousAt.continuousWithinAt (Metric.continuousAt_iff'.mpr fun ε hε => ?_)
  have hlog_cont : ContinuousAt (fun y : ℝ => Real.log (y / x)) x :=
    (Real.continuousAt_log (div_pos hx hx).ne').comp
      (f := fun y : ℝ => y / x) (continuousAt_id.div_const x)
  have htend : Tendsto (fun y : ℝ => |y - x| + (2 * (n : ℝ) + 1) * |Real.log (y / x)|)
      (𝓝 x) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => |y - x| + (2 * (n : ℝ) + 1) * |Real.log (y / x)|) x :=
      (continuousAt_id.sub continuousAt_const).abs.add (hlog_cont.abs.const_mul _)
    simpa [div_self hx.ne'] using hcont.tendsto
  filter_upwards [htend.eventually (Iio_mem_nhds hε), isOpen_Ioi.mem_nhds hx] with y hy_lt hy_pos
  rw [Real.dist_eq]
  have habs_le : |maxLogRatio n y - maxLogRatio n x| ≤
      |y - x| + (2 * (n : ℝ) + 1) * |Real.log (y / x)| := by
    rcases le_total y x with hle | hge
    · have hsub := maxLogRatio_sub_le hn hy_pos hle
      have hlog_eq : Real.log (x / y) = |Real.log (y / x)| := by
        rw [abs_of_nonpos (Real.log_nonpos (div_pos hy_pos hx).le ((div_le_one hx).mpr hle)),
          ← Real.log_inv, inv_div]
      rw [hlog_eq] at hsub
      rw [abs_of_nonneg (sub_nonneg.mpr ((strictAntiOn_maxLogRatio hn).antitoneOn hy_pos hx hle)),
        abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
    · have hsub := maxLogRatio_sub_le hn hx hge
      have hlog_eq : Real.log (y / x) = |Real.log (y / x)| :=
        (abs_of_nonneg (Real.log_nonneg ((one_le_div hx).mpr hge))).symm
      rw [hlog_eq] at hsub
      rw [abs_of_nonpos (sub_nonpos.mpr ((strictAntiOn_maxLogRatio hn).antitoneOn hx hy_pos hge)),
        abs_of_nonneg (sub_nonneg.mpr hge)]
      linarith
  exact habs_le.trans_lt hy_lt

private theorem exists_pos_maxLogRatio {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ 0 < maxLogRatio n x := by
  -- Evaluate at the midpoint `c = -2n + 1/2` and lower-bound the tail integral on `[x, 2x]`.
  let c : ℝ := -2 * (n : ℝ) + 1 / 2
  have hc_Ioo : c ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hc_le : c ≤ -1 := (evenBand_lt_neg_one hn hc_Ioo).le
  have hGc : 0 < Real.Gamma c := evenBand_Gamma_pos hn hc_Ioo
  let K : ℝ := 2 ^ (c - 1) * Real.exp (-1)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.exp_pos _)
  let x : ℝ := min (1 / 2) (K / (2 * Real.Gamma c))
  have hx_pos : 0 < x := lt_min (by norm_num) (div_pos hK (by positivity))
  have hx_le_half : x ≤ 1 / 2 := min_le_left _ _
  have hx_le_K : x ≤ K / (2 * Real.Gamma c) := min_le_right _ _
  refine ⟨x, hx_pos, lt_of_lt_of_le ?_ (logRatio_le_maxLogRatio hn hc_Ioo hx_pos)⟩
  have htail_ge : 2 * Real.Gamma c ≤ ∫ t in Ioi x, t ^ (c - 1) * Real.exp (-t) := by
    have hsplit := intervalIntegral.integral_interval_add_Ioi
      (TauCeti.integrableOn_rpow_sub_one_mul_exp_neg c hx_pos)
      (TauCeti.integrableOn_rpow_sub_one_mul_exp_neg c (by linarith : 0 < 2 * x))
    have hrem : 0 ≤ ∫ t in Ioi (2 * x), t ^ (c - 1) * Real.exp (-t) :=
      (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos c (by linarith)).le
    have hseg : x * ((2 * x) ^ (c - 1) * Real.exp (-1)) ≤
        ∫ t in x..(2 * x), t ^ (c - 1) * Real.exp (-t) := by
      have hconst_int : x * ((2 * x) ^ (c - 1) * Real.exp (-1)) =
          ∫ _ in x..(2 * x), ((2 * x) ^ (c - 1) * Real.exp (-1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [hconst_int]
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
          ((TauCeti.integrableOn_rpow_sub_one_mul_exp_neg c hx_pos).mono_set Ioc_subset_Ioi_self))
        fun t ht =>
          mul_le_mul (Real.rpow_le_rpow_of_nonpos (hx_pos.trans_le ht.1) ht.2 (by linarith))
            (Real.exp_le_exp.mpr (by linarith [ht.2])) (Real.exp_pos _).le
            (Real.rpow_nonneg (hx_pos.trans_le ht.1).le _)
    have hK_pow : K * x⁻¹ ≤ x * ((2 * x) ^ (c - 1) * Real.exp (-1)) := by
      have hpow_eq : x * (2 * x) ^ (c - 1) = 2 ^ (c - 1) * x ^ c := by
        rw [Real.mul_rpow (by norm_num) hx_pos.le, mul_left_comm, mul_comm x,
          ← Real.rpow_add_one hx_pos.ne', sub_add_cancel]
      have hx_rpow : x⁻¹ ≤ x ^ c := by
        rw [← Real.rpow_neg_one x]
        exact Real.rpow_le_rpow_of_exponent_ge hx_pos (by linarith) hc_le
      calc K * x⁻¹ ≤ 2 ^ (c - 1) * Real.exp (-1) * x ^ c :=
            mul_le_mul_of_nonneg_left hx_rpow (by positivity)
        _ = (2 ^ (c - 1) * x ^ c) * Real.exp (-1) := by ring
        _ = x * ((2 * x) ^ (c - 1) * Real.exp (-1)) := by rw [← hpow_eq]; ring
    have h2G : 2 * Real.Gamma c ≤ K * x⁻¹ := by
      rw [le_mul_inv_iff₀ hx_pos]
      linarith [(le_div_iff₀ (by positivity : 0 < 2 * Real.Gamma c)).mp hx_le_K]
    linarith
  simp only [logRatio]
  linarith [Real.log_lt_log hGc
    (by linarith : Real.Gamma c < ∫ t in Ioi x, t ^ (c - 1) * Real.exp (-t))]

private theorem exists_neg_maxLogRatio {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : ℝ, 0 < x ∧ maxLogRatio n x < 0 := by
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le (-2 * (n : ℝ))
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hγ_pos : 0 < M⁻¹ := inv_pos.mpr hM
  let x : ℝ := max 1 (Real.log (2 / M⁻¹))
  have hx1 : 1 ≤ x := le_max_left _ _
  have hx_pos : 0 < x := zero_lt_one.trans_le hx1
  obtain ⟨a₀, ha₀, _, _, _, hmax⟩ := exists_maximizer_logRatio hn hx_pos
  have ha₀_le1 : a₀ ≤ 1 := (evenBand_lt_neg_one hn ha₀).le.trans (by norm_num)
  have hγ : M⁻¹ ≤ Real.Gamma a₀ := by
    refine (inv_le_comm₀ hM (evenBand_Gamma_pos hn ha₀)).mpr ?_
    have h1 := hC a₀ ha₀.1.le
    rw [abs_of_pos (inv_pos.mpr (evenBand_Gamma_pos hn ha₀))] at h1
    exact h1.trans (le_max_left C 1)
  have hexp_le : Real.exp (-x) ≤ M⁻¹ / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos x) (by positivity), inv_div,
      ← Real.exp_log (div_pos (by norm_num) hγ_pos)]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  have htail_lt : (∫ t in Ioi x, t ^ (a₀ - 1) * Real.exp (-t)) < Real.Gamma a₀ :=
    (TauCeti.integral_rpow_sub_one_mul_exp_neg_le_exp_neg ha₀_le1 hx1).trans_lt
      (hexp_le.trans_lt (by linarith))
  refine ⟨x, hx_pos, ?_⟩
  rw [hmax, logRatio]
  linarith [Real.log_lt_log (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a₀ hx_pos) htail_lt]

private theorem tricomiIncompleteGamma_eq_zero_iff_logRatio {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0 ↔ logRatio a x = 0 := by
  rw [tricomiIncompleteGamma_ofReal_eq_zero_iff]
  have hid := rpow_mul_re_tricomiIncompleteGamma_eq_one_sub_div_Gamma
    (evenBand_ne_neg_natCast hn ha) hx
  have hexpL : Real.exp (logRatio a x) =
      (∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t)) / Real.Gamma a := by
    rw [logRatio, Real.exp_sub, Real.exp_log (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a hx),
      Real.exp_log (evenBand_Gamma_pos hn ha)]
  rw [← hexpL] at hid
  refine ⟨fun h0 => ?_, fun hL0 => ?_⟩
  · rw [h0, mul_zero] at hid; exact Real.exp_injective (by rw [Real.exp_zero]; linarith)
  · rw [hL0, Real.exp_zero, sub_self] at hid
    exact (mul_eq_zero.mp hid).resolve_left (Real.rpow_pos_of_pos hx a).ne'

private theorem hasDerivAt_re_tricomi_evenBand {n : ℕ} (hn : 1 ≤ n)
    {a x : ℝ} (ha : a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re)
      (-(Real.log x * x ^ (-a) * (1 - Real.exp (logRatio a x))) -
        x ^ (-a) * Real.exp (logRatio a x) * logRatioDeriv a x) a := by
  have heq : (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) =ᶠ[𝓝 a]
      fun b : ℝ => x ^ (-b) * (1 - Real.exp (logRatio b x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    have hid := rpow_mul_re_tricomiIncompleteGamma_eq_one_sub_div_Gamma
      (evenBand_ne_neg_natCast hn hb) hx
    have hexpL : Real.exp (logRatio b x) =
        (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t)) / Real.Gamma b := by
      rw [logRatio, Real.exp_sub, Real.exp_log (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos b hx),
        Real.exp_log (evenBand_Gamma_pos hn hb)]
    have hmul : x ^ (-b) * (x ^ b * (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) =
        (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re := by
      rw [← mul_assoc, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero, one_mul]
    rw [← hexpL] at hid
    rw [← hmul, hid]
  have hd_pow : HasDerivAt (fun b : ℝ => x ^ (-b)) (-Real.log x * x ^ (-a)) a := by
    convert (hasDerivAt_neg a).const_rpow hx using 1; ring
  have hd := (hd_pow.fun_mul ((hasDerivAt_logRatio hn ha hx).exp.const_sub 1)).congr_of_eventuallyEq
    heq
  convert hd using 1; ring

private theorem deriv_deriv_re_tricomi_at_double_zero {n : ℕ} (hn : 1 ≤ n)
    {a₀ x : ℝ} (ha₀ : a₀ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) (hx : 0 < x)
    (hL0 : logRatio a₀ x = 0) (hL'0 : logRatioDeriv a₀ x = 0) :
    deriv (deriv fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₀ ≠ 0 := by
  have heq : deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) =ᶠ[𝓝 a₀]
      fun b : ℝ => -(Real.log x * x ^ (-b) * (1 - Real.exp (logRatio b x))) -
        x ^ (-b) * Real.exp (logRatio b x) * logRatioDeriv b x := by
    filter_upwards [isOpen_Ioo.mem_nhds ha₀] with b hb
    exact (hasDerivAt_re_tricomi_evenBand hn hb hx).deriv
  have hd_pow : HasDerivAt (fun b : ℝ => x ^ (-b)) (-Real.log x * x ^ (-a₀)) a₀ := by
    convert (hasDerivAt_neg a₀).const_rpow hx using 1; ring
  have hd_exp : HasDerivAt (fun b : ℝ => Real.exp (logRatio b x)) 0 a₀ := by
    simpa [hL0, hL'0] using (hasDerivAt_logRatio hn ha₀ hx).exp
  have hd_term1 : HasDerivAt
      (fun b : ℝ => -(Real.log x * x ^ (-b) * (1 - Real.exp (logRatio b x)))) 0 a₀ := by
    simpa [hL0] using ((hd_pow.const_mul (Real.log x)).fun_mul (hd_exp.const_sub 1)).fun_neg
  have hd_term2 : HasDerivAt
      (fun b : ℝ => x ^ (-b) * Real.exp (logRatio b x) * logRatioDeriv b x)
      (x ^ (-a₀) * logRatioDeriv2 a₀ x) a₀ := by
    simpa [hL0, hL'0] using (hd_pow.fun_mul hd_exp).fun_mul (hasDerivAt_logRatioDeriv hn ha₀ hx)
  rw [((hd_term1.fun_sub hd_term2).congr_of_eventuallyEq heq).deriv, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero (Real.rpow_pos_of_pos hx _).ne'
    (logRatioDeriv2_neg hn ha₀ hx).ne)

private theorem param_zeros_of_maxLogRatio_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hpos : 0 < maxLogRatio n x) :
    ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = {a₁, a₂} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₁ ≠ 0 ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₂ ≠ 0 := by
  obtain ⟨a₀, ha₀, hL'0, hmonoL, hantiL, hmaxL⟩ := exists_maximizer_logRatio hn hx
  have hpos_a₀ : 0 < logRatio a₀ x := hmaxL ▸ hpos
  have hcontL : ContinuousOn (fun a : ℝ => logRatio a x) (Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ))) :=
    fun a ha => (hasDerivAt_logRatio hn ha hx).continuousAt.continuousWithinAt
  obtain ⟨l, hl_neg, hl_Ioo⟩ := (((tendsto_logRatio_atBot_left hn hx).eventually
    (eventually_lt_atBot 0)).and (Ioo_mem_nhdsGT ha₀.1)).exists
  obtain ⟨r, hr_neg, hr_Ioo⟩ := (((tendsto_logRatio_atBot_right hn hx).eventually
    (eventually_lt_atBot 0)).and (Ioo_mem_nhdsLT ha₀.2)).exists
  obtain ⟨a₁, ha₁_Icc, ha₁_zero⟩ := intermediate_value_Icc hl_Ioo.2.le
    (hcontL.mono fun _ ha => ⟨hl_Ioo.1.trans_le ha.1, ha.2.trans_lt ha₀.2⟩) ⟨hl_neg.le, hpos_a₀.le⟩
  obtain ⟨a₂, ha₂_Icc, ha₂_zero⟩ := intermediate_value_Icc' hr_Ioo.1.le
    (hcontL.mono fun _ ha => ⟨ha₀.1.trans_le ha.1, ha.2.trans_lt hr_Ioo.2⟩) ⟨hr_neg.le, hpos_a₀.le⟩
  dsimp only at ha₁_zero ha₂_zero
  have ha₁_lt : a₁ < a₀ := lt_of_le_of_ne ha₁_Icc.2 (fun h => by subst h; linarith)
  have ha₀_lt : a₀ < a₂ := lt_of_le_of_ne ha₂_Icc.1 (fun h => by subst h; linarith)
  have ha₁_Ioo : a₁ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨hl_Ioo.1.trans_le ha₁_Icc.1, ha₁_lt.trans ha₀.2⟩
  have ha₂_Ioo : a₂ ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) :=
    ⟨ha₀.1.trans ha₀_lt, ha₂_Icc.2.trans_lt hr_Ioo.2⟩
  refine ⟨a₁, a₂, ha₁_lt.trans ha₀_lt, ?_, ?_, ?_⟩
  · ext a; simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨ha, h0⟩ => ?_, ?_⟩
    · have hLa := (tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha hx).mp h0
      rcases lt_trichotomy a a₀ with hlt₀ | rfl | hgt₀
      · exact Or.inl (hmonoL.injOn ⟨ha.1, hlt₀.le⟩ ⟨ha₁_Ioo.1, ha₁_lt.le⟩ (hLa.trans ha₁_zero.symm))
      · linarith
      · exact Or.inr (hantiL.injOn ⟨hgt₀.le, ha.2⟩ ⟨ha₀_lt.le, ha₂_Ioo.2⟩ (hLa.trans ha₂_zero.symm))
    · rintro (rfl | rfl)
      · exact ⟨ha₁_Ioo, (tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha₁_Ioo hx).mpr ha₁_zero⟩
      · exact ⟨ha₂_Ioo, (tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha₂_Ioo hx).mpr ha₂_zero⟩
  · have hd1 : 0 < logRatioDeriv a₁ x := hL'0 ▸ strictAntiOn_logRatioDeriv hn hx ha₁_Ioo ha₀ ha₁_lt
    rw [(hasDerivAt_re_tricomi_evenBand hn ha₁_Ioo hx).deriv, ha₁_zero, Real.exp_zero, sub_self,
      mul_zero, neg_zero, zero_sub, mul_one]
    exact neg_ne_zero.mpr (mul_pos (Real.rpow_pos_of_pos hx _) hd1).ne'
  · have hd2 : logRatioDeriv a₂ x < 0 := hL'0 ▸ strictAntiOn_logRatioDeriv hn hx ha₀ ha₂_Ioo ha₀_lt
    rw [(hasDerivAt_re_tricomi_evenBand hn ha₂_Ioo hx).deriv, ha₂_zero, Real.exp_zero, sub_self,
      mul_zero, neg_zero, zero_sub, mul_one]
    exact neg_ne_zero.mpr (mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' hd2.ne)

private theorem param_zeros_of_maxLogRatio_eq_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hzero : maxLogRatio n x = 0) :
    ∃ a₀ : ℝ,
      {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
        tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = {a₀} ∧
      deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₀ = 0 ∧
      deriv (deriv fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₀ ≠ 0 := by
  obtain ⟨a₀, ha₀, hL'0, hmonoL, hantiL, hmaxL⟩ := exists_maximizer_logRatio hn hx
  have hL0 : logRatio a₀ x = 0 := hmaxL ▸ hzero
  refine ⟨a₀, ?_, ?_, deriv_deriv_re_tricomi_at_double_zero hn ha₀ hx hL0 hL'0⟩
  · ext a; simp only [mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun ⟨ha, h0⟩ => ?_, fun h => h ▸ ⟨ha₀,
      (tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha₀ hx).mpr hL0⟩⟩
    have hLa := (tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha hx).mp h0
    rcases lt_trichotomy a a₀ with hlt₀ | rfl | hgt₀
    · linarith [hmonoL ⟨ha.1, hlt₀.le⟩ ⟨ha₀.1, le_rfl⟩ hlt₀]
    · rfl
    · linarith [hantiL ⟨le_rfl, ha₀.2⟩ ⟨hgt₀.le, ha.2⟩ hgt₀]
  · rw [(hasDerivAt_re_tricomi_evenBand hn ha₀ hx).deriv, hL0, hL'0]; simp

private theorem param_zeros_of_maxLogRatio_neg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hneg : maxLogRatio n x < 0) :
    {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
      tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = ∅ := by
  ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro ha h0
  linarith [(tricomiIncompleteGamma_eq_zero_iff_logRatio hn ha hx).mp h0,
    logRatio_le_maxLogRatio hn ha hx]

/-- **DLMF §8.13(iii)(b)**: for each `n ≥ 1`, there exists a threshold `xs > 0` such that for
fixed `x > 0`, the real zeros of `a ↦ γ*(a, x)` in `(-2n, 1 - 2n)` are two simple zeros when
`0 < x < xs`, one double zero when `x = xs`, and none when `x > xs`. -/
theorem tricomiIncompleteGamma_param_zeros {n : ℕ} (hn : 1 ≤ n) :
    ∃ xs : ℝ, 0 < xs ∧ ∀ x : ℝ, 0 < x →
      (x < xs → ∃ a₁ a₂ : ℝ, a₁ < a₂ ∧
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = {a₁, a₂} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₁ ≠ 0 ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₂ ≠ 0) ∧
      (x = xs → ∃ a₀ : ℝ,
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = {a₀} ∧
        deriv (fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₀ = 0 ∧
        deriv (deriv fun b : ℝ => (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re) a₀ ≠ 0) ∧
      (xs < x →
        {a : ℝ | a ∈ Ioo (-2 * (n : ℝ)) (1 - 2 * (n : ℝ)) ∧
          tricomiIncompleteGamma (a : ℂ) (x : ℂ) = 0} = ∅) := by
  obtain ⟨x₁, hx₁_pos, hx₁_posM⟩ := exists_pos_maxLogRatio hn
  obtain ⟨x₂, hx₂_pos, hx₂_negM⟩ := exists_neg_maxLogRatio hn
  have hantiM := strictAntiOn_maxLogRatio hn
  have hx₁₂ : x₁ < x₂ := by
    by_contra h; push Not at h
    rcases h.eq_or_lt with rfl | hgt
    · linarith
    · linarith [hantiM hx₂_pos hx₁_pos hgt]
  obtain ⟨xs, hxs_Icc, hxs_zero⟩ := intermediate_value_Icc' hx₁₂.le
    ((continuousOn_maxLogRatio hn).mono fun _ hy => hx₁_pos.trans_le hy.1)
    ⟨hx₂_negM.le, hx₁_posM.le⟩
  have hxs_pos : 0 < xs := hx₁_pos.trans_le hxs_Icc.1
  exact ⟨xs, hxs_pos, fun x hx =>
    ⟨fun hlt => param_zeros_of_maxLogRatio_pos hn hx (hxs_zero ▸ hantiM hx hxs_pos hlt),
     fun heq => param_zeros_of_maxLogRatio_eq_zero hn hx (heq ▸ hxs_zero),
     fun hgt => param_zeros_of_maxLogRatio_neg hn hx (hxs_zero ▸ hantiM hxs_pos hx hgt)⟩⟩

end Complex
