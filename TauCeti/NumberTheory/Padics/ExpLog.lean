/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
import Mathlib.RingTheory.PowerSeries.Log
import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
import TauCeti.NumberTheory.LocalField.Exponential
import TauCeti.NumberTheory.LocalField.Logarithm
import TauCeti.NumberTheory.Padics.Basic
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

* `Padic.mem_unitFiltration_iff_norm_sub_one_le`: the unit filtration `U(ℚ_p,i)` is the disc
  `‖x - 1‖ ≤ p ^ (-i)`.
* `Padic.norm_exp_sub_one`: `‖exp x - 1‖ = ‖x‖`.
* `Padic.norm_log`: `‖log u‖ = ‖u - 1‖`.
* `Padic.log_exp`, `Padic.exp_log`: the exponential and the logarithm are inverse.
* `Padic.log_mul`: `log (u * w) = log u + log w`.
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

namespace TauCeti

open scoped PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {i : ℕ}

private theorem isRestricted_of_hasSum_coe {f : ℤ_[p]⟦X⟧} {s : ℚ_[p]}
    (hf : HasSum (fun n ↦ ((PowerSeries.coeff n f : ℤ_[p]) : ℚ_[p]) * (1 : ℚ_[p]) ^ n) s) :
    f.IsRestricted 1 := by
  rw [PowerSeries.isRestricted_iff']
  simpa only [one_pow, mul_one, ← PadicInt.norm_def, Function.comp_def] using
    tendsto_norm_zero.comp hf.summable.tendsto_atTop_zero

private theorem coe_evalAt_of_hasSum_coe {f : ℤ_[p]⟦X⟧} (hf : f.IsRestricted 1) (x : ℤ_[p])
    {s : ℚ_[p]}
    (hs : HasSum (fun n ↦ ((PowerSeries.coeff n f : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n) s) :
    ((f.evalAt x : ℤ_[p]) : ℚ_[p]) = s := by
  rw [← PadicInt.Coe.ringHom_apply]
  exact ((hf.hasSum_evalAt (PadicInt.norm_le_one x)).map PadicInt.Coe.ringHom
    PadicInt.isEmbedding_coe_ringHom.continuous).unique <|
      hs.congr_fun fun n ↦ by simp

private theorem norm_deepLogTerm_le_one (hi : i ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ‖(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p])‖ ≤ 1 := by
  rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hv : padicValNat p n ≤ i * (n - 1) := by
    rw [Nat.padicValNat_def]
    have hlt : multiplicity p n < n :=
      Nat.lt_two_pow_self.trans_le <|
        (Nat.pow_le_pow_left hp.out.two_le _).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (pow_multiplicity_dvd p n))
    exact (Nat.le_sub_one_of_lt hlt).trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hi))
  exact Padic.norm_pow_div_natCast_le_one hn hv

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
  exact Padic.norm_pow_div_natCast_le_one n.factorial_ne_zero hv

/-- The `p`-adic integer power series
`(p^i)⁻¹ log (1 + p^i X) = ∑_{n ≥ 1} (-1)^(n+1) p^(i(n-1))/n X^n` at any nonzero depth `i ≠ 0`. -/
noncomputable def deepLogSeries (hi : i ≠ 0) : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun n ↦
    if hn : n = 0 then 0
    else ⟨(-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]),
      norm_deepLogTerm_le_one hi hn⟩

@[simp]
theorem constantCoeff_deepLogSeries (hi : i ≠ 0) :
    PowerSeries.constantCoeff (deepLogSeries (p := p) hi) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deepLogSeries, PowerSeries.coeff_mk]
  simp

@[simp]
theorem coeff_one_deepLogSeries (hi : i ≠ 0) :
    PowerSeries.coeff 1 (deepLogSeries (p := p) hi) = 1 := by
  ext
  simp [deepLogSeries]

theorem coe_coeff_deepLogSeries_of_ne_zero (hi : i ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ((PowerSeries.coeff n (deepLogSeries (p := p) hi) : ℤ_[p]) : ℚ_[p]) =
      (-1 : ℚ_[p]) ^ (n + 1) * (p : ℚ_[p]) ^ (i * (n - 1)) / (n : ℚ_[p]) := by
  simp [deepLogSeries, hn]

/-- In `ℚ_[p]`, the series `deepLogSeries hi` evaluated termwise at `x : ℤ_[p]` sums to
`log (1 + p^i x) / p^i`. -/
theorem hasSum_coeff_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PowerSeries.coeff n (deepLogSeries hi) : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      (log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i) := by
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hx1 : ‖1 + (p : ℚ_[p]) ^ i * x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [add_sub_cancel_left, norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
      (PadicInt.norm_le_one x)
  have hu1 : Units.mk0 (1 + (p : ℚ_[p]) ^ i * x) (Padic.ne_zero_of_norm_sub_one_le hi hx1) ∈
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

/-- **Restrictedness of the normalized deep logarithm series.** At any nonzero depth `i ≠ 0`,
`deepLogSeries hi` is restricted at radius `1`. -/
theorem isRestricted_deepLogSeries (hi : i ≠ 0) :
    (deepLogSeries (p := p) hi).IsRestricted 1 :=
  isRestricted_of_hasSum_coe (hasSum_coeff_deepLogSeries (p := p) hi 1)

/-- **Evaluation of `deepLogSeries`.** For `i ≠ 0` and `x : ℤ_p`,
`((deepLogSeries hi).evalAt x : ℚ_p) = log (1 + p^i x) / p^i`. -/
@[simp]
theorem coe_evalAt_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    (((deepLogSeries (p := p) hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      log (1 + (p : ℚ_[p]) ^ i * x) / (p : ℚ_[p]) ^ i :=
  coe_evalAt_of_hasSum_coe (isRestricted_deepLogSeries hi) x (hasSum_coeff_deepLogSeries hi x)

/-- Evaluated at `x : ℤ_p`, `p^i · (deepLogSeries hi)(x) = log (1 + p^i x)`. -/
theorem pow_mul_coe_evalAt_deepLogSeries (hi : i ≠ 0) (x : ℤ_[p]) :
    (p : ℚ_[p]) ^ i * ((deepLogSeries (p := p) hi).evalAt x : ℤ_[p]) =
      log (1 + (p : ℚ_[p]) ^ i * x) := by
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [coe_evalAt_deepLogSeries hi x, mul_div_cancel₀ _ hpi]

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
    (deepExpSeries (p := p) hi).IsRestricted 1 :=
  isRestricted_of_hasSum_coe (hasSum_coeff_deepExpSeries (p := p) hi 1)

/-- **Evaluation of `deepExpSeries`.** For `1 < (p - 1) * i` and `x : ℤ_p`,
`((deepExpSeries hi).evalAt x : ℚ_p) = (exp (p^i x) - 1) / p^i`. -/
@[simp]
theorem coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    (((deepExpSeries hi).evalAt x : ℤ_[p]) : ℚ_[p]) =
      (exp ((p : ℚ_[p]) ^ i * x) - 1) / (p : ℚ_[p]) ^ i :=
  coe_evalAt_of_hasSum_coe (isRestricted_deepExpSeries hi) x (hasSum_coeff_deepExpSeries hi x)

/-- Evaluated at `x : ℤ_p`, `1 + p^i · (deepExpSeries hi)(x) = exp (p^i x)`. -/
theorem one_add_pow_mul_coe_evalAt_deepExpSeries (hi : 1 < (p - 1) * i) (x : ℤ_[p]) :
    1 + (p : ℚ_[p]) ^ i * ((deepExpSeries hi).evalAt x : ℤ_[p]) = exp ((p : ℚ_[p]) ^ i * x) := by
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [coe_evalAt_deepExpSeries hi x, mul_div_cancel₀ _ hpi, add_sub_cancel]

/-- **Analytic left inverse.** In the deep convergence range `1 < (p - 1) * i`, `deepLogSeries`
inverts `deepExpSeries` under evaluation on `ℤ_p`. -/
@[simp]
theorem evalAt_deepLogSeries_evalAt_deepExpSeries (hi' : i ≠ 0) (hi : 1 < (p - 1) * i)
    (x : ℤ_[p]) :
    (deepLogSeries (p := p) hi').evalAt ((deepExpSeries hi).evalAt x) = x := by
  apply PadicInt.ext
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hx : ‖(p : ℚ_[p]) ^ i * x‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
      (PadicInt.norm_le_one x)
  rw [coe_evalAt_deepLogSeries, one_add_pow_mul_coe_evalAt_deepExpSeries,
    Padic.log_exp hi hx, mul_div_cancel_left₀ _ hpi]

/-- **Analytic right inverse.** In the deep convergence range `1 < (p - 1) * i`, `deepExpSeries`
inverts `deepLogSeries` under evaluation on `ℤ_p`. -/
@[simp]
theorem evalAt_deepExpSeries_evalAt_deepLogSeries (hi : 1 < (p - 1) * i) (hi' : i ≠ 0)
    (x : ℤ_[p]) :
    (deepExpSeries hi).evalAt ((deepLogSeries (p := p) hi').evalAt x) = x := by
  apply PadicInt.ext
  have hpi : (p : ℚ_[p]) ^ i ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hu : ‖1 + (p : ℚ_[p]) ^ i * x - 1‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [add_sub_cancel_left, norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (zpow_pos (by exact_mod_cast hp.out.pos) _).le
      (PadicInt.norm_le_one x)
  rw [coe_evalAt_deepExpSeries, pow_mul_coe_evalAt_deepLogSeries,
    Padic.exp_log hi hu, add_sub_cancel_left, mul_div_cancel_left₀ _ hpi]

/-- **Formal left inverse.** In `ℤ_p⟦X⟧`, substituting `deepExpSeries hi` into `deepLogSeries hi'`
gives `X`. -/
@[simp]
theorem subst_deepLogSeries_deepExpSeries (hi' : i ≠ 0) (hi : 1 < (p - 1) * i) :
    (deepLogSeries (p := p) hi').subst (deepExpSeries hi) = PowerSeries.X := by
  let c : ℚ_[p] := (p : ℚ_[p]) ^ i
  have hc : c ≠ 0 := pow_ne_zero i (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hexp_pow {n : ℕ} (hn : n ≠ 0) : c * (p : ℚ_[p]) ^ (i * (n - 1)) = c ^ n := by
    dsimp only [c]
    rw [← pow_mul, ← pow_add]
    congr 1
    have : i + i * (n - 1) = i * (n - 1 + 1) := by ring
    rw [this, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  have hL : c • PowerSeries.map PadicInt.Coe.ringHom (deepLogSeries (p := p) hi') =
      PowerSeries.rescale c (PowerSeries.log ℚ_[p]) := by
    ext n
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_rescale,
      PowerSeries.coeff_log, PadicInt.Coe.ringHom_apply, smul_eq_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [constantCoeff_deepLogSeries]
    · simp only [hn, ↓reduceIte, coe_coeff_deepLogSeries_of_ne_zero hi' hn, map_div₀, map_pow,
        map_neg, map_one, map_natCast]
      rw [← mul_div_assoc, ← mul_assoc, mul_comm c, mul_assoc, hexp_pow hn]
      ring
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
      change PowerSeries.constantCoeff
        (PowerSeries.map PadicInt.Coe.ringHom (deepExpSeries hi)) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_deepExpSeries, map_zero]
  have hsub_cX : PowerSeries.HasSubst (c • PowerSeries.X : ℚ_[p]⟦X⟧) :=
    .of_constantCoeff_zero' (by simp)
  have hc_sub : c • PowerSeries.map PadicInt.Coe.ringHom
      ((deepLogSeries (p := p) hi').subst (deepExpSeries hi)) = c • PowerSeries.X := by
    change c • MvPowerSeries.map PadicInt.Coe.ringHom
      ((deepLogSeries (p := p) hi').subst (deepExpSeries hi)) = c • PowerSeries.X
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
  rcases eq_or_ne n 1 with rfl | hn1
  · simpa [PowerSeries.coeff_one_X] using mul_left_cancel₀ hc hn
  · simpa [PowerSeries.coeff_X, hn1] using mul_left_cancel₀ hc hn

/-- **Formal right inverse.** In `ℤ_p⟦X⟧`, substituting `deepLogSeries hi'` into `deepExpSeries hi`
gives `X`. -/
@[simp]
theorem subst_deepExpSeries_deepLogSeries (hi : 1 < (p - 1) * i) (hi' : i ≠ 0) :
    (deepExpSeries hi).subst (deepLogSeries (p := p) hi') = PowerSeries.X :=
  PowerSeries.subst_eq_X_of_subst_eq_X (deepLogSeries (p := p) hi')
    (constantCoeff_deepLogSeries hi') (by simp [coeff_one_deepLogSeries])
    (.of_constantCoeff_zero' (constantCoeff_deepExpSeries hi))
    (subst_deepLogSeries_deepExpSeries hi' hi)

end TauCeti
