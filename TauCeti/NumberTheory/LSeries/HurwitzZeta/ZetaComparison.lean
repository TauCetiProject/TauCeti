/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Continuation
import TauCeti.NumberTheory.LSeries.ComplexHurwitzSeries

/-!
# Comparisons of the continued complex Hurwitz zeta function with Mathlib zeta functions

Extends the half-plane series comparisons in `TauCeti.NumberTheory.LSeries.ComplexHurwitzSeries`
to all `s ≠ 1` via `TauCeti.eq_complexHurwitzZeta_of_eqOn_re_gt`:
- along `(0, 1]`, `TauCeti.complexHurwitzZeta s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`;
- at `c = 1`, `TauCeti.complexHurwitzZeta s 1 = riemannZeta s`;
- at `c = 1 / 2`, `TauCeti.complexHurwitzZeta s (1 / 2) = (2 ^ s - 1) * riemannZeta s`.

## Main results

* `TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta`: agreement with `HurwitzZeta.hurwitzZeta` for
  `x ∈ (0, 1]` and `s ≠ 1`.
* `TauCeti.complexHurwitzZeta_one_right`, `TauCeti.complexHurwitzZeta_one_half_right`:
  specializations at `c = 1` and `c = 1 / 2` for `s ≠ 1`.
-/

public section

open Complex Set

namespace TauCeti

/-- For real `x ∈ (0, 1]` and `s ≠ 1`, `complexHurwitzZeta s x` agrees with Mathlib's
`HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzZeta_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : s ≠ 1)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzZeta s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have hx_re : 0 < (x : ℂ).re := by simp [hx.1]
  have hdg : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta (x : UnitAddCircle))
      ({1}ᶜ : Set ℂ) :=
    fun _ hz => (HurwitzZeta.differentiableAt_hurwitzZeta _ hz).differentiableWithinAt
  exact (eq_complexHurwitzZeta_of_eqOn_re_gt hx_re (b := 1) hdg (fun z hz => by
    have hz1 : 1 < z.re := by simpa using hz
    exact (complexHurwitzSeries_ofReal hx.1 hx.2 hz1).symm) hs).symm

/-- At `c = 1` and `s ≠ 1`, `complexHurwitzZeta s 1 = riemannZeta s`. -/
theorem complexHurwitzZeta_one_right {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s 1 = riemannZeta s := by
  have h := complexHurwitzZeta_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `c = 1 / 2` and `s ≠ 1`, `complexHurwitzZeta s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzZeta_one_half_right {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hhalf_re : 0 < (1 / 2 : ℂ).re := by norm_num
  have hdg : DifferentiableOn ℂ (fun z => ((2 : ℂ) ^ z - 1) * riemannZeta z) ({1}ᶜ) :=
    fun _ hz => (((differentiableAt_id.const_cpow (Or.inl two_ne_zero)).sub
      (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hz)).differentiableWithinAt
  exact (eq_complexHurwitzZeta_of_eqOn_re_gt hhalf_re (b := 1) hdg (fun z hz => by
    have hz1 : 1 < z.re := by simpa using hz
    exact (complexHurwitzSeries_one_half hz1).symm) hs).symm

end TauCeti

end
