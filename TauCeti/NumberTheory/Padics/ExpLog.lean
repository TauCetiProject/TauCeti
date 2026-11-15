/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
import TauCeti.NumberTheory.LocalField.Exponential
import TauCeti.NumberTheory.LocalField.Logarithm
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.PadicValNat

/-!
# The `p`-adic exponential and logarithm in terms of the norm

Mathlib's `NormedSpace.exp` and `NormedSpace.log` on `ℚ_[p]` are mutually inverse between the
closed disc `‖x‖ ≤ p ^ (-i)` and the closed disc `‖u - 1‖ ≤ p ^ (-i)` about `1`, whenever the
depth `i` satisfies `1 < (p - 1) * i`, that is, `i ≥ 1` for odd `p` and `i ≥ 2` for `p = 2`. On
these discs both maps preserve the distance to the centre, and the logarithm turns products into
sums.

These are the results of `TauCeti.NumberTheory.LocalField.ExpLog` and
`TauCeti.NumberTheory.LocalField.DeepUnits.Basic` for the local field `ℚ_[p]`, whose absolute
ramification index is one, restated with Mathlib's `p`-adic norm instead of the valuation of the
valuative relation and the unit filtration. They are the analytic input for the logarithm on the
principal units `1 + qℤ_p`, with `q = p` for odd `p` and `q = 4` for `p = 2`, in
`TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm`.

Reading the two maps in the normalized disc coordinate `x ∈ ℤ_p` on `p^i ℤ_p` and `1 + p^i ℤ_p`
gives two formal power series over `ℤ_p` without constant term,

```text
deepLogSeries hi = ∑_{n ≥ 1} (-1)^(n + 1) p^(i (n - 1)) / n · X^n,
deepExpSeries hi = ∑_{n ≥ 1} p^(i (n - 1)) / n! · X^n,
```

both restricted at the radius `1`, evaluating at `x : ℤ_p` to `log (1 + p^i x) / p^i` and
`(exp (p^i x) - 1) / p^i` respectively. They express the change of coordinate between the
normalized disc coordinate on `1 + p^i ℤ_p` and its logarithmic coordinate in `ℤ_p`.

## Main definitions

* `PadicInt.deepLogSeries hi`: the restricted series `(p^i)⁻¹ log (1 + p^i X) ∈ ℤ_p⟦X⟧`.
* `PadicInt.deepExpSeries hi`: the restricted series `(p^i)⁻¹ (exp (p^i X) - 1) ∈ ℤ_p⟦X⟧`.

## Main results

* `Padic.mem_unitFiltration_iff_norm_sub_one_le`: the unit filtration `U(ℚ_p,i)` is the disc
  `‖x - 1‖ ≤ p ^ (-i)`.
* `Padic.norm_exp_sub_one`: `‖exp x - 1‖ = ‖x‖`.
* `Padic.norm_log`: `‖log u‖ = ‖u - 1‖`.
* `Padic.log_exp`, `Padic.exp_log`: the exponential and the logarithm are inverse.
* `Padic.log_mul`: `log (u * w) = log u + log w`.
* `PadicInt.isRestricted_deepLogSeries`, `PadicInt.coe_evalAt_deepLogSeries`: restrictedness at
  radius `1` and evaluation of `deepLogSeries`.
* `PadicInt.isRestricted_deepExpSeries`, `PadicInt.coe_evalAt_deepExpSeries`,
  `PadicInt.one_add_pow_mul_coe_evalAt_deepExpSeries`: restrictedness at radius `1` and evaluation
  of `deepExpSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open Filter Topology ValuativeRel NormedSpace

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

private theorem absoluteRamificationIndex_lt {i : ℕ} (hi : 1 < (p - 1) * i) :
    TauCeti.absoluteRamificationIndex ℚ_[p] p < (p - 1) * i := by
  rwa [TauCeti.absoluteRamificationIndex_padic]

omit hp in
private theorem ne_zero_of_one_lt_mul {i : ℕ} (hi : 1 < (p - 1) * i) : i ≠ 0 := by
  rintro rfl
  simp at hi

/-- An element of `ℚ_[p]` of norm at most `p ^ (-i)`, as an element of the ideal `𝓂 ^ i` of the
ring of integers. -/
private noncomputable def toMaximalIdealPow {i : ℕ} {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : (𝓂[ℚ_[p]] ^ i : Ideal 𝒪[ℚ_[p]]) :=
  ⟨⟨x, by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation ℚ_[p]),
      valuation_le_valuation_iff_norm_le, norm_one]
    exact hx.trans (zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le) (by simp))⟩,
    TauCeti.Padic.mem_maximalIdeal_pow_iff_norm_le.mpr hx⟩

/-- A unit of `ℚ_[p]` lies in the unit filtration `U(ℚ_p,i)`, `i ≥ 1`, exactly when
`‖x - 1‖ ≤ p ^ (-i)`. -/
theorem mem_unitFiltration_iff_norm_sub_one_le {i : ℕ} (hi : i ≠ 0) {x : ℚ_[p]ˣ} :
    x ∈ TauCeti.unitFiltration ℚ_[p] i ↔ ‖(x : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
  rw [TauCeti.mem_unitFiltration_iff_valuation_sub_one_le hi
    (TauCeti.Padic.irreducible_natCast_self p), valuation_le_valuation_natCast_pow_iff]

private theorem ne_zero_of_norm_sub_one_le {i : ℕ} (hi : i ≠ 0) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : x ≠ 0 := by
  rintro rfl
  have h1 : (p : ℝ) ^ (-(i : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by exact_mod_cast hp.out.one_lt) (by simpa using Nat.pos_of_ne_zero hi)
  rw [zero_sub, norm_neg, norm_one] at hx
  linarith

/-- An element `x` with `‖x - 1‖ ≤ p ^ (-i)` is a unit lying in the unit filtration `U(ℚ_p,i)`. -/
private theorem mk0_mem_unitFiltration {i : ℕ} (hi : 1 < (p - 1) * i) {x : ℚ_[p]}
    (hx : ‖x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) :
    Units.mk0 x (ne_zero_of_norm_sub_one_le (ne_zero_of_one_lt_mul hi) hx) ∈
      TauCeti.unitFiltration ℚ_[p] i :=
  (mem_unitFiltration_iff_norm_sub_one_le (ne_zero_of_one_lt_mul hi)).mpr hx

/-- **The exponential preserves the norm on deep discs.** For `1 < (p - 1) * i` and
`‖x‖ ≤ p ^ (-i)`, `‖exp x - 1‖ = ‖x‖`. -/
theorem norm_exp_sub_one {i : ℕ} (hi : 1 < (p - 1) * i) {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : ‖exp x - 1‖ = ‖x‖ :=
  valuation_eq_valuation_iff_norm_eq.mp
    (TauCeti.valuation_exp_sub_one (absoluteRamificationIndex_lt hi) (toMaximalIdealPow hx))

/-- **The logarithm preserves the norm on deep discs.** For `1 < (p - 1) * i` and
`‖u - 1‖ ≤ p ^ (-i)`, `‖log u‖ = ‖u - 1‖`. -/
theorem norm_log {i : ℕ} (hi : 1 < (p - 1) * i) {u : ℚ_[p]}
    (hu : ‖u - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : ‖log u‖ = ‖u - 1‖ :=
  valuation_eq_valuation_iff_norm_eq.mp
    (TauCeti.valuation_log (absoluteRamificationIndex_lt hi) (mk0_mem_unitFiltration hi hu))

/-- **The logarithm inverts the exponential on deep discs.** For `1 < (p - 1) * i` and
`‖x‖ ≤ p ^ (-i)`, `log (exp x) = x`. -/
theorem log_exp {i : ℕ} (hi : 1 < (p - 1) * i) {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : log (exp x) = x :=
  TauCeti.log_exp_of_mem_maximalIdeal_pow (absoluteRamificationIndex_lt hi) (toMaximalIdealPow hx)

/-- **The exponential inverts the logarithm on deep discs.** For `1 < (p - 1) * i` and
`‖u - 1‖ ≤ p ^ (-i)`, `exp (log u) = u`. -/
theorem exp_log {i : ℕ} (hi : 1 < (p - 1) * i) {u : ℚ_[p]}
    (hu : ‖u - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) : exp (log u) = u :=
  TauCeti.exp_log_of_mem_unitFiltration (absoluteRamificationIndex_lt hi)
    (mk0_mem_unitFiltration hi hu)

/-- **The logarithm is a homomorphism on deep discs.** For `1 < (p - 1) * i`,
`‖u - 1‖ ≤ p ^ (-i)` and `‖w - 1‖ ≤ p ^ (-i)`, `log (u * w) = log u + log w`. -/
theorem log_mul {i : ℕ} (hi : 1 < (p - 1) * i) {u w : ℚ_[p]}
    (hu : ‖u - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) (hw : ‖w - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ))) :
    log (u * w) = log u + log w :=
  TauCeti.log_mul_of_mem_unitFiltration (absoluteRamificationIndex_lt hi)
    (mk0_mem_unitFiltration hi hu) (mk0_mem_unitFiltration hi hw)

end Padic

/-! ### Integral power-series expansions on deep discs -/

namespace PadicInt

open scoped PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {i : ℕ}

private theorem norm_pow_div_natCast_le_one {a m : ℕ} (hm : m ≠ 0) (hle : padicValNat p m ≤ a) :
    ‖(p : ℚ_[p]) ^ a / (m : ℚ_[p])‖ ≤ 1 := by
  rw [norm_div, Padic.norm_p_pow, Padic.norm_natCast_eq_zpow hm,
    div_le_one (zpow_pos (by exact_mod_cast hp.out.pos) _)]
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)

private theorem norm_deepLogTerm_le_one (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ‖(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p])‖ ≤ 1 := by
  rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · have hv : padicValNat p n ≤ i * (n - 1) := by
      simpa using (TauCeti.mul_padicValNat_lt_mul_sub_one (e := 1) hi (by omega)).le
    exact norm_pow_div_natCast_le_one hn hv

private theorem norm_deepExpTerm_le_one (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ‖(p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p])‖ ≤ 1 := by
  have hi0 : 1 ≤ i := Nat.pos_of_ne_zero (Padic.ne_zero_of_one_lt_mul hi)
  have hleg := sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hn
  rw [← Nat.padicValNat_def] at hleg
  have hv : padicValNat p n.factorial ≤ i * (n - 1) := by
    have hp1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
    calc padicValNat p n.factorial
        ≤ (p - 1) * padicValNat p n.factorial := Nat.le_mul_of_pos_left _ hp1
      _ ≤ n - 1 := by omega
      _ ≤ i * (n - 1) := Nat.le_mul_of_pos_left _ hi0
  exact norm_pow_div_natCast_le_one n.factorial_ne_zero hv

/-- The `p`-adic integer power series
`(p^i)⁻¹ log (1 + p^i X) = ∑_{n ≥ 1} (-1)^(n+1) p^(i(n-1))/n X^n` at a depth `i` in the
convergence range `1 < (p - 1) * i`. -/
noncomputable def deepLogSeries (hi : 1 < (p - 1) * i) : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦
    if hn : n = 0 then 0
    else ⟨(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]),
      norm_deepLogTerm_le_one hi hn⟩

@[simp]
theorem constantCoeff_deepLogSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.constantCoeff (deepLogSeries (p := p) hi) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deepLogSeries, PowerSeries.coeff_mk]
  simp

@[simp]
theorem coeff_one_deepLogSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.coeff 1 (deepLogSeries (p := p) hi) = 1 := by
  ext
  simp [deepLogSeries]

theorem coe_coeff_deepLogSeries_of_ne_zero (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ((PowerSeries.coeff n (deepLogSeries (p := p) hi) : ℤ_[p]) : ℚ_[p]) =
      (-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]) := by
  simp [deepLogSeries, hn]

/-- In `ℚ_[p]`, the series `deepLogSeries hi` evaluated termwise at `x : ℤ_[p]` sums to
`log (1 + p^i x) / p^i`. -/
theorem hasSum_coeff_deepLogSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PowerSeries.coeff n (deepLogSeries hi) : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      (log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i) := by
  have hi0 := Padic.ne_zero_of_one_lt_mul hi
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hx1 : ‖1 + (p : ℚ_[p]) ^ i * x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [add_sub_cancel_left, norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
      (PadicInt.norm_le_one x)
  have hu1 : Units.mk0 (1 + (p : ℚ_[p]) ^ i * x) (Padic.ne_zero_of_norm_sub_one_le hi0 hx1) ∈
      TauCeti.unitFiltration ℚ_[p] 1 :=
    (Padic.mem_unitFiltration_iff_norm_sub_one_le one_ne_zero).mpr <| hx1.trans <|
      zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega)
  refine ((TauCeti.hasSum_log_of_mem_unitFiltration_one p hu1).div_const
    ((p : ℚ_[p]) ^ i)).congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [constantCoeff_deepLogSeries]
  · rw [coe_coeff_deepLogSeries_of_ne_zero hi hn]
    simp only [Units.val_mk0, add_sub_cancel_left, mul_pow, ← pow_mul]
    have hexp : (p : ℚ_[p]) ^ (i * n) = (p : ℚ_[p]) ^ (i * (n - 1)) * (p : ℚ_[p]) ^ i := by
      rw [← pow_add]
      congr 1
      have : i * (n - 1) + i = i * (n - 1 + 1) := by ring
      rw [this, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
    rw [hexp]
    field_simp [hpi]

/-- **Restrictedness of the normalized deep logarithm series.** At a depth `i` with
`1 < (p - 1) * i`, `deepLogSeries hi` is restricted at radius `1`. -/
theorem isRestricted_deepLogSeries (hi : 1 < (p - 1) * i) :
    (deepLogSeries (p := p) hi).IsRestricted 1 := by
  have h := (hasSum_coeff_deepLogSeries (p := p) hi 1).summable.tendsto_atTop_zero
  rw [PowerSeries.isRestricted_iff']
  simpa only [PadicInt.coe_one, one_pow, mul_one, ← PadicInt.norm_def, Function.comp_def] using
    tendsto_norm_zero.comp h

/-- **Evaluation of `deepLogSeries`.** For `1 < (p - 1) * i` and `x : ℤ_p`,
`((deepLogSeries hi).evalAt x : ℚ_p) = log (1 + p^i x) / p^i`. -/
theorem coe_evalAt_deepLogSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    (((deepLogSeries hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i := by
  have hs := ((isRestricted_deepLogSeries hi).hasSum_evalAt (PadicInt.norm_le_one x)).map
    PadicInt.Coe.ringHom (continuous_subtype_val : Continuous ((↑) : ℤ_[p] → ℚ_[p]))
  exact hs.unique <| (hasSum_coeff_deepLogSeries hi x).congr_fun fun n ↦ by simp

/-- The `p`-adic integer power series `(p^i)⁻¹ (exp (p^i X) - 1) = ∑_{n ≥ 1} p^(i(n-1))/n! X^n`
at a depth `i` in the convergence range `1 < (p - 1) * i`. -/
noncomputable def deepExpSeries (hi : 1 < (p - 1) * i) : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦
    if hn : n = 0 then 0
    else ⟨(p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p]),
      norm_deepExpTerm_le_one hi hn⟩

@[simp]
theorem constantCoeff_deepExpSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.constantCoeff (deepExpSeries (p := p) hi) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deepExpSeries, PowerSeries.coeff_mk]
  simp

@[simp]
theorem coeff_one_deepExpSeries (hi : 1 < (p - 1) * i) :
    PowerSeries.coeff 1 (deepExpSeries (p := p) hi) = 1 := by
  ext
  simp [deepExpSeries]

theorem coe_coeff_deepExpSeries_of_ne_zero (hi : 1 < (p - 1) * i) {n : ℕ} (hn : n ≠ 0) :
    ((PowerSeries.coeff n (deepExpSeries (p := p) hi) : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (i * (n - 1)) / (n.factorial : ℚ_[p]) := by
  simp [deepExpSeries, hn]

/-- In `ℚ_[p]`, the series `deepExpSeries hi` evaluated termwise at `x : ℤ_[p]` sums to
`(exp (p^i x) - 1) / p^i`. -/
theorem hasSum_coeff_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PowerSeries.coeff n (deepExpSeries hi) : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      ((exp ((p : ℚ_[p]) ^ i * x) - 1) / (p : ℚ_[p]) ^ i) := by
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hx : ‖(p : ℚ_[p]) ^ i * x‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
      (PadicInt.norm_le_one x)
  have hexp := (TauCeti.hasSum_exp_of_mem_maximalIdeal_pow (Padic.toMaximalIdealPow hx)
    (Padic.absoluteRamificationIndex_lt hi)).update 0 0
  simp only [Padic.toMaximalIdealPow, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    zero_sub, neg_add_eq_sub] at hexp
  refine (hexp.div_const ((p : ℚ_[p]) ^ i)).congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [constantCoeff_deepExpSeries]
  · rw [Function.update_of_ne hn, coe_coeff_deepExpSeries_of_ne_zero hi hn, mul_pow, ← pow_mul]
    have hexp_pow : (p : ℚ_[p]) ^ (i * n) = (p : ℚ_[p]) ^ (i * (n - 1)) * (p : ℚ_[p]) ^ i := by
      rw [← pow_add]
      congr 1
      have : i * (n - 1) + i = i * (n - 1 + 1) := by ring
      rw [this, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
    rw [hexp_pow]
    field_simp [hpi]

/-- **Restrictedness of the normalized deep exponential series.** At a depth `i` with
`1 < (p - 1) * i`, `deepExpSeries hi` is restricted at radius `1`. -/
theorem isRestricted_deepExpSeries (hi : 1 < (p - 1) * i) :
    (deepExpSeries (p := p) hi).IsRestricted 1 := by
  have h := (hasSum_coeff_deepExpSeries (p := p) hi 1).summable.tendsto_atTop_zero
  rw [PowerSeries.isRestricted_iff']
  simpa only [PadicInt.coe_one, one_pow, mul_one, ← PadicInt.norm_def, Function.comp_def] using
    tendsto_norm_zero.comp h

/-- **Evaluation of `deepExpSeries`.** For `1 < (p - 1) * i` and `x : ℤ_p`,
`((deepExpSeries hi).evalAt x : ℚ_p) = (exp (p^i x) - 1) / p^i`. -/
theorem coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    (((deepExpSeries hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      (exp ((p : ℚ_[p]) ^ i * x) - 1) / (p : ℚ_[p]) ^ i := by
  have hs := ((isRestricted_deepExpSeries hi).hasSum_evalAt (PadicInt.norm_le_one x)).map
    PadicInt.Coe.ringHom (continuous_subtype_val : Continuous ((↑) : ℤ_[p] → ℚ_[p]))
  exact hs.unique <| (hasSum_coeff_deepExpSeries hi x).congr_fun fun n ↦ by simp

/-- Evaluated at `x : ℤ_p`, `1 + p^i · (deepExpSeries hi)(x) = exp (p^i x)`. -/
theorem one_add_pow_mul_coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    1 + (p : ℚ_[p]) ^ i * ((deepExpSeries hi).evalAt x : ℤ_[p]) = exp ((p : ℚ_[p]) ^ i * x) := by
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [coe_evalAt_deepExpSeries hi x, mul_div_cancel₀ _ hpi, add_sub_cancel]

end PadicInt
