/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.EvalAt
import Mathlib.RingTheory.PowerSeries.Log
import TauCeti.Analysis.Normed.Algebra.Logarithm.Basic
import TauCeti.NumberTheory.Padics.Exp.Disc
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicValNat
import TauCeti.NumberTheory.Padics.PowerSeries

/-!
# Integral power series for the `p`-adic exponential and logarithm on deep discs

Reading Mathlib's `p`-adic logarithm `NormedSpace.log` on `1 + p^i ℤ_p` and exponential
`NormedSpace.exp` on `p^i ℤ_p` in the normalized disc coordinate `x ∈ ℤ_p` gives two formal power
series over `ℤ_p` without constant term,

```text
deepLogSeries hi = ∑_{n ≥ 1} (-1)^(n + 1) p^(i (n - 1)) / n · X^n,
deepExpSeries hi = ∑_{n ≥ 1} p^(i (n - 1)) / n! · X^n,
```

where `deepLogSeries` is defined and restricted at radius `1` for every `i ≠ 0`, while
`deepExpSeries` is defined and restricted at radius `1` in the deep convergence range
`1 < (p - 1) * i`. They evaluate at `x : ℤ_p` to `log (1 + p^i x) / p^i` and
`(exp (p^i x) - 1) / p^i` respectively, and for `1 < (p - 1) * i` they are mutually inverse both
formally under `PowerSeries.subst` and analytically under `PowerSeries.evalAt` on `ℤ_p`.

## Main definitions

* `TauCeti.deepLogSeries hi`: the restricted series `(p^i)⁻¹ log (1 + p^i X) ∈ ℤ_p⟦X⟧` (`i ≠ 0`).
* `TauCeti.deepExpSeries hi`: the restricted series `(p^i)⁻¹ (exp (p^i X) - 1) ∈ ℤ_p⟦X⟧`
  (`1 < (p - 1) * i`).

## Main results

* `TauCeti.isRestricted_deepLogSeries`, `TauCeti.coe_evalAt_deepLogSeries`,
  `TauCeti.pow_mul_coe_evalAt_deepLogSeries`: restrictedness at radius `1` and evaluation of
  `deepLogSeries` for `i ≠ 0`.
* `TauCeti.isRestricted_deepExpSeries`, `TauCeti.coe_evalAt_deepExpSeries`,
  `TauCeti.one_add_pow_mul_coe_evalAt_deepExpSeries`: restrictedness at radius `1` and evaluation
  of `deepExpSeries` for `1 < (p - 1) * i`.
* `TauCeti.evalAt_deepLogSeries_evalAt_deepExpSeries`,
  `TauCeti.evalAt_deepExpSeries_evalAt_deepLogSeries`,
  `TauCeti.subst_deepLogSeries_deepExpSeries`,
  `TauCeti.subst_deepExpSeries_deepLogSeries`: analytic and formal mutual-inverse identities.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open Filter Topology NormedSpace
open scoped PowerSeries

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {i : ℕ}

private theorem pow_prime_ne_zero (i : ℕ) : (p : ℚ_[p]) ^ i ≠ 0 :=
  pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)

private theorem norm_pow_mul_coe_le (i : ℕ) (x : ℤ_[p]) :
    ‖(p : ℚ_[p]) ^ i * x‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
  rw [norm_mul, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
    (PadicInt.norm_le_one x)

private theorem pow_mul_sub_one_mul {n : ℕ} (hn : n ≠ 0) :
    (p : ℚ_[p]) ^ (i * n) = (p : ℚ_[p]) ^ (i * (n - 1)) * (p : ℚ_[p]) ^ i := by
  rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]

private theorem norm_deepLogTerm_le_one (hi : i ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ‖(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p])‖ ≤ 1 := by
  rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  refine Padic.norm_pow_div_natCast_le_one hn ?_
  rw [Nat.padicValNat_def]
  have hlt : multiplicity p n < n := Nat.lt_two_pow_self.trans_le <|
    (Nat.pow_le_pow_left hp.out.two_le _).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (pow_multiplicity_dvd p n))
  exact (Nat.le_sub_one_of_lt hlt).trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hi))

private theorem norm_deepExpTerm_le_one (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ‖(p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p])‖ ≤ 1 := by
  have hi0 : 1 ≤ i := by
    rcases eq_or_ne i 0 with rfl | hi0
    · simp at hi
    · exact Nat.pos_of_ne_zero hi0
  have hleg := sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hn
  rw [← Nat.padicValNat_def] at hleg
  have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have hv : padicValNat p n.factorial ≤ i * (n - 1) :=
    (Nat.le_mul_of_pos_left _ hp1).trans ((by omega : _ ≤ n - 1).trans
      (Nat.le_mul_of_pos_left _ hi0))
  exact Padic.norm_pow_div_natCast_le_one n.factorial_ne_zero hv

/-- The `p`-adic integer power series
`(p^i)⁻¹ log (1 + p^i X) = ∑_{n ≥ 1} (-1)^(n+1) p^(i(n-1))/n X^n` at any nonzero depth `i ≠ 0`. -/
noncomputable def deepLogSeries (hi : i ≠ 0) : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ if hn : n = 0 then 0 else
    ⟨(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]),
      norm_deepLogTerm_le_one hi hn⟩

@[simp] theorem constantCoeff_deepLogSeries (hi : i ≠ 0) :
    PowerSeries.constantCoeff (deepLogSeries (p := p) hi) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deepLogSeries, PowerSeries.coeff_mk]; simp

@[simp] theorem coeff_one_deepLogSeries (hi : i ≠ 0) :
    PowerSeries.coeff 1 (deepLogSeries (p := p) hi) = 1 := by ext; simp [deepLogSeries]

theorem coe_coeff_deepLogSeries_of_ne_zero (hi : i ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ((PowerSeries.coeff n (deepLogSeries (p := p) hi) : ℤ_[p]) : ℚ_[p]) =
      (-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]) := by
  simp [deepLogSeries, hn]

/-- In `ℚ_[p]`, the series `deepLogSeries hi` evaluated termwise at `x : ℤ_[p]` sums to
`log (1 + p^i x) / p^i`. -/
theorem hasSum_coeff_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PowerSeries.coeff n (deepLogSeries hi) : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      (log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i) := by
  have hxlt : ‖1 + (p : ℚ_[p]) ^ i * x - 1‖ < 1 := by
    rw [add_sub_cancel_left]
    exact (norm_pow_mul_coe_le i x).trans_lt <|
      zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt) (by simpa using Nat.pos_of_ne_zero hi)
  refine ((NormedSpace.hasSum_log_of_norm_sub_one_lt_one ℚ_[p] hxlt).div_const
    ((p : ℚ_[p]) ^ i)).congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [constantCoeff_deepLogSeries]
  · rw [coe_coeff_deepLogSeries_of_ne_zero hi hn]
    simp only [smul_eq_mul, add_sub_cancel_left, mul_pow, ← pow_mul, pow_mul_sub_one_mul hn]
    field_simp [pow_prime_ne_zero (p := p) i]

/-- **Restrictedness of the normalized deep logarithm series.** At any nonzero depth `i ≠ 0`,
`deepLogSeries hi` is restricted at radius `1`. -/
theorem isRestricted_deepLogSeries (hi : i ≠ 0) : (deepLogSeries (p := p) hi).IsRestricted 1 := by
  simpa only [norm_one] using
    ((deepLogSeries (p := p) hi).isRestricted_norm_iff_summable_coe_coeff_mul_pow 1).mpr
      (hasSum_coeff_deepLogSeries (p := p) hi 1).summable

/-- **Evaluation of `deepLogSeries`.** For `i ≠ 0` and `x : ℤ_p`,
`((deepLogSeries hi).evalAt x : ℚ_p) = log (1 + p^i x) / p^i`. -/
@[simp] theorem coe_evalAt_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    (((deepLogSeries (p := p) hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i :=
  ((isRestricted_deepLogSeries hi).hasSum_coe_evalAt (PadicInt.norm_le_one x)).unique
    (hasSum_coeff_deepLogSeries hi x)

/-- Evaluated at `x : ℤ_p`, `p^i · (deepLogSeries hi)(x) = log (1 + p^i x)`. -/
theorem pow_mul_coe_evalAt_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    (p : ℚ_[p]) ^ i * ((deepLogSeries (p := p) hi).evalAt x : ℤ_[p]) =
      log (1 + (p : ℚ_[p]) ^ i * x) := by
  rw [coe_evalAt_deepLogSeries hi x, mul_div_cancel₀ _ (pow_prime_ne_zero i)]

/-- The `p`-adic integer power series `(p^i)⁻¹ (exp (p^i X) - 1) = ∑_{n ≥ 1} p^(i(n-1))/n! X^n`
at a depth `i` in the convergence range `1 < (p - 1) * i`. -/
noncomputable def deepExpSeries (hi : 1 < (p - 1) * i) : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦ if hn : n = 0 then 0 else
    ⟨(p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p]), norm_deepExpTerm_le_one hi hn⟩

@[simp] theorem constantCoeff_deepExpSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.constantCoeff (deepExpSeries (p := p) hi) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deepExpSeries, PowerSeries.coeff_mk]; simp

@[simp] theorem coeff_one_deepExpSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.coeff 1 (deepExpSeries (p := p) hi) = 1 := by ext; simp [deepExpSeries]

theorem coe_coeff_deepExpSeries_of_ne_zero (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ((PowerSeries.coeff n (deepExpSeries (p := p) hi) : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p]) := by
  simp [deepExpSeries, hn]

/-- In `ℚ_[p]`, the series `deepExpSeries hi` evaluated termwise at `x : ℤ_[p]` sums to
`(exp (p^i x) - 1) / p^i`. -/
theorem hasSum_coeff_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PowerSeries.coeff n (deepExpSeries hi) : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      ((exp ((p : ℚ_[p]) ^ i * x) - 1) / (p : ℚ_[p]) ^ i) := by
  have hexp := (expSeries_hasSum_exp_of_norm_lt
    ((norm_pow_mul_coe_le i x).trans_lt (zpow_neg_lt_amiceRadius_zero hi))).update 0 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, zero_sub,
    neg_add_eq_sub] at hexp
  refine (hexp.div_const ((p : ℚ_[p]) ^ i)).congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [constantCoeff_deepExpSeries]
  · rw [Function.update_of_ne hn, coe_coeff_deepExpSeries_of_ne_zero hi hn, smul_eq_mul,
      mul_pow, ← pow_mul, pow_mul_sub_one_mul hn]
    field_simp [pow_prime_ne_zero (p := p) i]

/-- **Restrictedness of the normalized deep exponential series.** At a depth `i` with
`1 < (p - 1) * i`, `deepExpSeries hi` is restricted at radius `1`. -/
theorem isRestricted_deepExpSeries (hi : 1 < (p - 1) * i) :
    (deepExpSeries (p := p) hi).IsRestricted 1 := by
  simpa only [norm_one] using
    ((deepExpSeries (p := p) hi).isRestricted_norm_iff_summable_coe_coeff_mul_pow 1).mpr
      (hasSum_coeff_deepExpSeries (p := p) hi 1).summable

/-- **Evaluation of `deepExpSeries`.** For `1 < (p - 1) * i` and `x : ℤ_p`,
`((deepExpSeries hi).evalAt x : ℚ_p) = (exp (p^i x) - 1) / p^i`. -/
@[simp] theorem coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    (((deepExpSeries hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      (exp ((p : ℚ_[p]) ^ i * x) - 1) / (p : ℚ_[p]) ^ i :=
  ((isRestricted_deepExpSeries hi).hasSum_coe_evalAt (PadicInt.norm_le_one x)).unique
    (hasSum_coeff_deepExpSeries hi x)

/-- Evaluated at `x : ℤ_p`, `1 + p^i · (deepExpSeries hi)(x) = exp (p^i x)`. -/
theorem one_add_pow_mul_coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    1 + (p : ℚ_[p]) ^ i * ((deepExpSeries hi).evalAt x : ℤ_[p]) = exp ((p : ℚ_[p]) ^ i * x) := by
  rw [coe_evalAt_deepExpSeries hi x, mul_div_cancel₀ _ (pow_prime_ne_zero i), add_sub_cancel]

/-- **Analytic left inverse.** In the deep convergence range `1 < (p - 1) * i`, `deepLogSeries`
inverts `deepExpSeries` under evaluation on `ℤ_p`. -/
@[simp] theorem evalAt_deepLogSeries_evalAt_deepExpSeries (hi' : i ≠ 0) (hi : 1 < (p - 1) * i)
    (x : ℤ_[p]) : (deepLogSeries (p := p) hi').evalAt ((deepExpSeries hi).evalAt x) = x := by
  apply PadicInt.ext
  rw [coe_evalAt_deepLogSeries, one_add_pow_mul_coe_evalAt_deepExpSeries,
    log_exp_of_norm_lt ((norm_pow_mul_coe_le i x).trans_lt (zpow_neg_lt_amiceRadius_zero hi)),
    mul_div_cancel_left₀ _ (pow_prime_ne_zero i)]

/-- **Analytic right inverse.** In the deep convergence range `1 < (p - 1) * i`, `deepExpSeries`
inverts `deepLogSeries` under evaluation on `ℤ_p`. -/
@[simp] theorem evalAt_deepExpSeries_evalAt_deepLogSeries (hi : 1 < (p - 1) * i) (hi' : i ≠ 0)
    (x : ℤ_[p]) : (deepExpSeries hi).evalAt ((deepLogSeries (p := p) hi').evalAt x) = x := by
  apply PadicInt.ext
  have hu : ‖1 + (p : ℚ_[p]) ^ i * x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [add_sub_cancel_left]; exact norm_pow_mul_coe_le i x
  rw [coe_evalAt_deepExpSeries, pow_mul_coe_evalAt_deepLogSeries,
    exp_log_of_norm_sub_one_lt (hu.trans_lt (zpow_neg_lt_amiceRadius_zero hi)),
    add_sub_cancel_left, mul_div_cancel_left₀ _ (pow_prime_ne_zero i)]

/-- **Formal left inverse.** In `ℤ_p⟦X⟧`, substituting `deepExpSeries hi` into `deepLogSeries hi'`
gives `X`. -/
@[simp] theorem subst_deepLogSeries_deepExpSeries (hi' : i ≠ 0) (hi : 1 < (p - 1) * i) :
    (deepLogSeries (p := p) hi').subst (deepExpSeries hi) = PowerSeries.X := by
  let c : ℚ_[p] := (p : ℚ_[p]) ^ i
  have hexp_pow {n : ℕ} (hn : n ≠ 0) : c * (p : ℚ_[p]) ^ (i * (n - 1)) = c ^ n := by
    dsimp only [c]; rw [← pow_mul, mul_comm c, ← pow_mul_sub_one_mul hn]
  have hL : c • PowerSeries.map PadicInt.Coe.ringHom (deepLogSeries (p := p) hi') =
      PowerSeries.rescale c (PowerSeries.log ℚ_[p]) := by
    ext n
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_rescale,
      PowerSeries.coeff_log, PadicInt.Coe.ringHom_apply, smul_eq_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [constantCoeff_deepLogSeries]
    · simp only [hn, ↓reduceIte, coe_coeff_deepLogSeries_of_ne_zero hi' hn, map_div₀, map_pow,
        map_neg, map_one, map_natCast]
      rw [← mul_div_assoc, ← mul_assoc, mul_comm c, mul_assoc, hexp_pow hn]; ring
  have hE : c • MvPowerSeries.map PadicInt.Coe.ringHom (deepExpSeries hi) =
      PowerSeries.rescale c (PowerSeries.exp ℚ_[p] - 1) := by
    change c • PowerSeries.map PadicInt.Coe.ringHom (deepExpSeries hi) = _
    ext n
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_rescale,
      map_sub, PowerSeries.coeff_exp, PadicInt.Coe.ringHom_apply, smul_eq_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [constantCoeff_deepExpSeries]
    · simp only [hn, coe_coeff_deepExpSeries_of_ne_zero hi hn, PowerSeries.coeff_one, ↓reduceIte,
        sub_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast, one_div, Rat.cast_inv,
        Rat.cast_natCast]
      rw [← mul_div_assoc, hexp_pow hn, div_eq_mul_inv]
  have hsub_E : PowerSeries.HasSubst (deepExpSeries hi) :=
    .of_constantCoeff_zero' (constantCoeff_deepExpSeries hi)
  have hsub_EQ :
      PowerSeries.HasSubst (MvPowerSeries.map PadicInt.Coe.ringHom (deepExpSeries hi)) :=
    .of_constantCoeff_zero' <| by
      change PowerSeries.constantCoeff (PowerSeries.map PadicInt.Coe.ringHom _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_deepExpSeries, map_zero]
  have hsub_cX : PowerSeries.HasSubst (c • PowerSeries.X : ℚ_[p]⟦X⟧) :=
    .of_constantCoeff_zero' (by simp)
  have hc_sub : c • PowerSeries.map PadicInt.Coe.ringHom
      ((deepLogSeries (p := p) hi').subst (deepExpSeries hi)) = c • PowerSeries.X := by
    change c • MvPowerSeries.map PadicInt.Coe.ringHom _ = c • PowerSeries.X
    rw [PowerSeries.map_subst hsub_E, ← PowerSeries.subst_smul hsub_EQ, hL,
      PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hsub_cX hsub_EQ,
      PowerSeries.subst_smul hsub_EQ, PowerSeries.subst_X hsub_EQ, hE,
      PowerSeries.rescale_eq_subst,
      ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.exp_sub_one hsub_cX,
      PowerSeries.subst_log_exp_sub_one, PowerSeries.subst_X hsub_cX]
  ext n
  have hn := congrArg (PowerSeries.coeff n) hc_sub
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_map, PadicInt.Coe.ringHom_apply,
    smul_eq_mul] at hn
  by_cases hn1 : n = 1 <;>
    simpa [PowerSeries.coeff_X, hn1] using mul_left_cancel₀ (pow_prime_ne_zero (p := p) i) hn

/-- **Formal right inverse.** In `ℤ_p⟦X⟧`, substituting `deepLogSeries hi'` into `deepExpSeries hi`
gives `X`. -/
@[simp] theorem subst_deepExpSeries_deepLogSeries (hi : 1 < (p - 1) * i) (hi' : i ≠ 0) :
    (deepExpSeries hi).subst (deepLogSeries (p := p) hi') = PowerSeries.X :=
  PowerSeries.subst_eq_X_of_subst_eq_X (deepLogSeries (p := p) hi')
    (constantCoeff_deepLogSeries hi') (by simp [coeff_one_deepLogSeries])
    (.of_constantCoeff_zero' (constantCoeff_deepExpSeries hi))
    (subst_deepLogSeries_deepExpSeries hi' hi)

end TauCeti
