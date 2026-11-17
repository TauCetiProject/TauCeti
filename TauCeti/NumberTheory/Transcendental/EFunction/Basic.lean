/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.Height.House
public import TauCeti.RingTheory.PowerSeries.DFinite.Basic
public import TauCeti.RingTheory.PowerSeries.ExponentialSeries.Analytic

import TauCeti.RingTheory.PowerSeries.DFinite.Borel
import TauCeti.RingTheory.PowerSeries.DFinite.NumberField

/-!
# Siegel's E-functions and G-functions

In the geometric growth normalization of Shidlovskii, André, Beukers, and Fischler–Rivoal, a complex
sequence `a : ℕ → ℂ` defines an **E-function** (`∑ₙ aₙ zⁿ / n!`) or **G-function** (`∑ₙ aₙ zⁿ`)
when: (1) every `a n` is algebraic over `ℚ`; (2) `ePowerSeries a` (resp. `PowerSeries.mk a`) is
D-finite over `algebraicClosure ℚ ℂ`; (3) all conjugates satisfy `|σ(a n)| ≤ C ^ (n + 1)`; and
(4) common integer denominators clearing `a 0, …, a n` satisfy `1 ≤ d n ≤ D ^ (n + 1)`.

The general formal Borel transform (`TauCeti.RingTheory.PowerSeries.DFinite.Borel`) gives
`IsGFunction a ↔ IsEFunction a`, and `TauCeti.RingTheory.PowerSeries.DFinite.NumberField` yields
containment of all coefficients in a single number field. Analytically, `eFun a` is entire and
`PowerSeries.mk a` has positive radius of convergence.

## Main definitions

* `TauCeti.IsEFunction`: Siegel's E-functions in geometric normalization.
* `TauCeti.IsGFunction`: Siegel's G-functions in geometric normalization.

## Main results

* `TauCeti.isGFunction_iff_isEFunction`: formal Borel transform equivalence.
* `TauCeti.IsEFunction.exists_numberField`, `TauCeti.IsGFunction.exists_numberField`: all
  coefficients lie in a single number field.
* `TauCeti.IsEFunction.isEntire_ePowerSeries`, `TauCeti.IsEFunction.differentiable_eFun`,
  `TauCeti.IsEFunction.hasSum_eFun`: `eFun a` is entire and represented everywhere by its series.
* `TauCeti.IsGFunction.radius_pos`, `TauCeti.IsGFunction.exists_pos_summable`: a G-function has
  positive radius of convergence.

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.
  Phys.-Math. Kl. **1929**, no. 1.
* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. **163** (2006).
* F. Beukers, *E-functions and G-functions*, Arizona Winter School, 2008, §3.1, §4.1.
* S. Fischler and T. Rivoal, *Arithmetic theory of E-operators*, J. Éc. polytech. Math. **3**
  (2016), 31–65, §1.
-/

public section

open Polynomial PowerSeries
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Definitions of E-functions and G-functions -/

/-- Siegel's *E-functions* (in the geometric normalization of Shidlovskii, André, and Beukers):
sequences `a : ℕ → ℂ` of algebraic numbers whose factorial-divided formal series `ePowerSeries a`
is D-finite over `algebraicClosure ℚ ℂ` and whose conjugates and common denominators grow at most
geometrically. -/
structure IsEFunction (a : ℕ → ℂ) : Prop where
  /-- Every coefficient `a n` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The factorial-divided series `∑ₙ (aₙ / n!) Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a)
  /-- All complex conjugates of `a n` are bounded in modulus by `C ^ (n + 1)`. -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Common positive integer denominators `d n` clearing `a 0, …, a n` into algebraic integers
  satisfy `d n ≤ D ^ (n + 1)`. -/
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
    ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

/-- Siegel's *G-functions*: sequences `a : ℕ → ℂ` of algebraic numbers whose ordinary generating
series `PowerSeries.mk a = ∑ₙ aₙ Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`, with the same
geometric conjugate and common-denominator bounds as `IsEFunction`. -/
structure IsGFunction (a : ℕ → ℂ) : Prop where
  /-- Every coefficient `a n` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The ordinary power series `∑ₙ aₙ Xⁿ` is D-finite over `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a)
  /-- All complex conjugates of `a n` are bounded in modulus by `C ^ (n + 1)`. -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Common positive integer denominators `d n` clearing `a 0, …, a n` into algebraic integers
  satisfy `d n ≤ D ^ (n + 1)`. -/
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
    ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

/-- Construct an `IsEFunction` from a geometric bound on `TauCeti.house`. -/
theorem IsEFunction.of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (ePowerSeries a))
    (hsize : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
      ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) : IsEFunction a where
  isAlgebraic := halg
  isDFinite := hdf
  size_le := by
    obtain ⟨C, hC, hh⟩ := hsize
    exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mp (hh n)⟩
  den_le := hden

/-- Construct an `IsGFunction` from a geometric bound on `TauCeti.house`. -/
theorem IsGFunction.of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a))
    (hsize : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ, ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧
      ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) : IsGFunction a where
  isAlgebraic := halg
  isDFinite := hdf
  size_le := by
    obtain ⟨C, hC, hh⟩ := hsize
    exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mp (hh n)⟩
  den_le := hden

/-! ### Borel transform equivalence and number-field containment -/

/-- **Borel transform equivalence.** A complex sequence `a` defines a G-function iff it defines an
E-function. -/
theorem isGFunction_iff_isEFunction {a : ℕ → ℂ} : IsGFunction a ↔ IsEFunction a :=
  ⟨fun h ↦ ⟨h.isAlgebraic, isDFinite_mk_iff_isDFinite_ePowerSeries.mp h.isDFinite,
      h.size_le, h.den_le⟩,
    fun h ↦ ⟨h.isAlgebraic, isDFinite_mk_iff_isDFinite_ePowerSeries.mpr h.isDFinite,
      h.size_le, h.den_le⟩⟩

/-- All coefficients of a G-function lie in a single number field inside `ℂ`. -/
theorem IsGFunction.exists_numberField {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K :=
  exists_numberField_of_isDFinite_mk ha.isAlgebraic ha.isDFinite

/-- All coefficients of an E-function lie in a single number field inside `ℂ`. -/
theorem IsEFunction.exists_numberField {a : ℕ → ℂ} (ha : IsEFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K :=
  (isGFunction_iff_isEFunction.mpr ha).exists_numberField

/-! ### Analytic consequences for E-functions and G-functions -/

namespace IsEFunction

variable {a : ℕ → ℂ}

/-- The houses of the coefficients of an E-function grow at most geometrically. -/
theorem exists_house_le (ha : IsEFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hsize⟩ := ha.size_le
  exact ⟨C, hC, fun n ↦ (house_le_iff_forall_mem_aroots (by positivity)).mpr (hsize n)⟩

/-- The moduli `‖a n‖` of an E-function grow at most geometrically. -/
theorem exists_norm_le (ha : IsEFunction a) : ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hh⟩ := ha.exists_house_le
  exact ⟨C, hC, fun n ↦ (norm_le_house (ha.isAlgebraic n)).trans (hh n)⟩

/-- The formal factorial-divided series `ePowerSeries a` of an E-function is entire. -/
theorem isEntire_ePowerSeries (ha : IsEFunction a) : (ePowerSeries a).IsEntire := by
  obtain ⟨_, _, hnorm⟩ := ha.exists_norm_le; exact isEntire_ePowerSeries_of_norm_le hnorm

/-- The formal radius of `ePowerSeries a` for an E-function is `⊤`. -/
theorem radius_ePowerSeries (ha : IsEFunction a) : (ePowerSeries a).radius = ⊤ :=
  radius_eq_top_iff.mpr ha.isEntire_ePowerSeries

/-- For an E-function `a` and every `z : ℂ`, `∑ₙ aₙ zⁿ / n!` converges to `eFun a z`. -/
theorem hasSum_eFun (ha : IsEFunction a) (z : ℂ) :
    HasSum (fun n ↦ a n * z ^ n / n.factorial) (eFun a z) :=
  TauCeti.hasSum_eFun ha.isEntire_ePowerSeries z

/-- For an E-function `a` and every `z : ℂ`, `fun n ↦ a n * z ^ n / n!` is summable. -/
theorem summable_eFun (ha : IsEFunction a) (z : ℂ) :
    Summable fun n ↦ a n * z ^ n / n.factorial := TauCeti.summable_eFun ha.isEntire_ePowerSeries z

/-- `eFun a` has formal power series `∑ₙ (aₙ / n!) zⁿ` of infinite radius at `0`. -/
theorem hasFPowerSeriesOnBall_eFun (ha : IsEFunction a) :
    HasFPowerSeriesOnBall (eFun a)
      (FormalMultilinearSeries.ofScalars ℂ fun k ↦ a k / k.factorial) 0 ⊤ :=
  TauCeti.hasFPowerSeriesOnBall_eFun ha.isEntire_ePowerSeries

/-- For an E-function `a`, `eFun a` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_eFun (ha : IsEFunction a) : AnalyticOnNhd ℂ (eFun a) Set.univ :=
  TauCeti.analyticOnNhd_eFun ha.isEntire_ePowerSeries

/-- For an E-function `a`, `eFun a` is an entire (everywhere complex-differentiable) function. -/
theorem differentiable_eFun (ha : IsEFunction a) : Differentiable ℂ (eFun a) :=
  TauCeti.differentiable_eFun ha.isEntire_ePowerSeries

/-- Shifting the coefficients of an E-function differentiates `eFun a`. -/
theorem deriv_eFun (ha : IsEFunction a) : deriv (eFun a) = eFun fun n ↦ a (n + 1) :=
  TauCeti.deriv_eFun ha.isEntire_ePowerSeries

/-- Iterated derivatives of `eFun a` for an E-function shift the coefficients by `k`. -/
theorem iteratedDeriv_eFun (ha : IsEFunction a) (k : ℕ) :
    iteratedDeriv k (eFun a) = eFun fun n ↦ a (n + k) :=
  TauCeti.iteratedDeriv_eFun ha.isEntire_ePowerSeries k

/-- The `k`-th derivative of `eFun a` at `0` is `a k`. -/
theorem iteratedDeriv_eFun_zero (ha : IsEFunction a) (k : ℕ) :
    iteratedDeriv k (eFun a) 0 = a k := TauCeti.iteratedDeriv_eFun_zero ha.isEntire_ePowerSeries k

end IsEFunction

namespace IsGFunction

variable {a : ℕ → ℂ}

/-- The houses of the coefficients of a G-function grow at most geometrically. -/
theorem exists_house_le (ha : IsGFunction a) : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) :=
  (isGFunction_iff_isEFunction.mp ha).exists_house_le

/-- The moduli `‖a n‖` of a G-function grow at most geometrically. -/
theorem exists_norm_le (ha : IsGFunction a) : ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) :=
  (isGFunction_iff_isEFunction.mp ha).exists_norm_le

/-- **Positive radius of convergence of a G-function.** For every G-function `a`, the ordinary
series `PowerSeries.mk a` has positive radius of convergence. -/
theorem radius_pos (ha : IsGFunction a) : 0 < (PowerSeries.mk a).radius := by
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  set r : ℝ≥0 := Real.toNNReal C⁻¹
  have hrc : (r : ℝ) = C⁻¹ := Real.coe_toNNReal C⁻¹ (inv_nonneg.mpr hC.le)
  have hr : (0 : ℝ≥0∞) < r := ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr (inv_pos.mpr hC))
  refine hr.trans_le (PowerSeries.le_radius_of_bound C (r := r) fun n ↦ ?_)
  rw [coeff_mk, hrc]
  calc ‖a n‖ * (C⁻¹) ^ n ≤ C ^ (n + 1) * (C⁻¹) ^ n := by gcongr; exact hnorm n
    _ = C * (C * C⁻¹) ^ n := by rw [pow_succ', mul_pow, mul_assoc]
    _ = C := by rw [mul_inv_cancel₀ hC.ne', one_pow, mul_one]

/-- A G-function converges absolutely on an open disc of positive radius around `0`. -/
theorem exists_pos_summable (ha : IsGFunction a) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → Summable fun n ↦ a n * z ^ n := by
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  refine ⟨C⁻¹, inv_pos.mpr hC, fun z hz ↦ Summable.of_norm ?_⟩
  have hlt : C * ‖z‖ < 1 :=
    (mul_lt_mul_of_pos_left hz hC).trans_eq (mul_inv_cancel₀ hC.ne')
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (by positivity) hlt).mul_left C)
  rw [norm_mul, norm_pow]
  calc ‖a n‖ * ‖z‖ ^ n ≤ C ^ (n + 1) * ‖z‖ ^ n := by gcongr; exact hnorm n
    _ = C * (C * ‖z‖) ^ n := by rw [pow_succ', mul_pow, mul_assoc]

/-- `PowerSeries.mk a` defines an analytic function on the open ball of radius
`(PowerSeries.mk a).radius` around `0`. -/
theorem hasFPowerSeriesOnBall (ha : IsGFunction a) :
    HasFPowerSeriesOnBall (fun z ↦ ∑' n, a n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 (PowerSeries.mk a).radius := by
  have hrad : (PowerSeries.mk a).radius = (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    simpa only [coeff_mk] using PowerSeries.radius_eq_radius_ofScalars ℂ (PowerSeries.mk a)
  rw [hrad]
  have hp := (FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall (hrad ▸ ha.radius_pos)
  convert hp using 1; ext z
  simp [FormalMultilinearSeries.sum, smul_eq_mul, mul_comm]

end IsGFunction

end TauCeti
