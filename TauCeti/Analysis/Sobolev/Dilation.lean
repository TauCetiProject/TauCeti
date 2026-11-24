/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.MeasureTheory.Function.Lp.Dilation` is imported publicly:
-- `MeasureTheory.Measure.eLpNorm_comp_inv_smul` is the companion of the statement below, and
-- supplies the `eLpNorm` and Haar measure API appearing in its signature.
public import TauCeti.MeasureTheory.Function.Lp.Dilation
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
-- `Mathlib.Analysis.Calculus.FDeriv.Equiv` is imported privately: its `fderiv_comp_smul` is used
-- only inside the proof, so downstream importers do not pay for the equivalence machinery.
import Mathlib.Analysis.Calculus.FDeriv.Equiv
-- `Mathlib.Analysis.Calculus.ContDiff.Operations` is imported privately for the same reason: it
-- supplies `iteratedFDeriv_comp_const_smul`, used only inside a proof.
import Mathlib.Analysis.Calculus.ContDiff.Operations
-- `Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm` is imported privately: its `toReal_eLpNorm`
-- is used only inside a proof.
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Dilation scaling of the Sobolev seminorms

Fix a finite-dimensional real normed space `E` of dimension `n` carrying an additive Haar
measure `μ`, and dilate the variable of a function by `r ≠ 0`, i.e. replace `u` by
`x ↦ u (r⁻¹ • x)`. This file records how that operation rescales the `Lᵖ` seminorm of the
derivative, the second of the two quantities a first-order Sobolev estimate compares; the first,
the `Lᵖ` seminorm of the function itself, is `MeasureTheory.Measure.eLpNorm_comp_inv_smul`. It
also records the scaling of the `Lᵖ` seminorm of the derivative of every order `k`.

For every exponent `p` the two scaling laws are

`‖u (r⁻¹ • ·)‖_p = |r| ^ (n / p) * ‖u‖_p` and `‖D(u (r⁻¹ • ·))‖_p = |r| ^ (n / p - 1) * ‖Du‖_p`,

the extra `|r|⁻¹` in the second coming from the chain rule, in the shape of Mathlib's
`fderiv_comp_smul`. Here `n / p` stands for `n / p.toReal`, which is `0` at `p = 0` and `p = ∞`
by Lean's conventions `ENNReal.toReal ∞ = 0` and `x / 0 = 0`; at those two exponents the factors
are therefore `1` and `|r|⁻¹`. The mismatch of the two exponents is the scaling obstruction behind
`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`: a
Poincaré-type inequality cannot hold with one constant for all compactly supported functions on
the whole space.

## Main declarations

* `MeasureTheory.Measure.eLpNorm_fderiv_comp_inv_smul`:
  `‖D(u (r⁻¹ • ·))‖_p = |r| ^ (n / p - 1) * ‖Du‖_p`.
* `MeasureTheory.Measure.eLpNorm_iteratedFDeriv_comp_inv_smul`:
  `‖Dᵏ(u (r⁻¹ • ·))‖_p = |r| ^ (n / p - k) * ‖Dᵏ u‖_p` for `u` of class `Cᵏ`.
* `MeasureTheory.Measure.eLpNorm_iteratedFDeriv_comp_smul`: with the dilation written as
  `u (r • ·)`, `‖Dᵏ(u (r • ·))‖_p = |r| ^ (k - n / p) * ‖Dᵏ u‖_p`.
* `MeasureTheory.Measure.lpNorm_iteratedFDeriv_comp_smul`: the same law in the real-valued
  seminorm.
* `MeasureTheory.MemLp.iteratedFDeriv_comp_smul`: dilation preserves `Lᵖ` integrability of the
  `k`-th derivative.
-/

public section

namespace MeasureTheory.Measure

open Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Dilation scaling of the `Lᵖ` seminorm of the derivative:**
`‖D(u (r⁻¹ • ·))‖_p = |r| ^ (n / p - 1) * ‖Du‖_p` for `r ≠ 0`. The exponent drops by one relative
to `MeasureTheory.Measure.eLpNorm_comp_inv_smul` because the chain rule contributes a factor `r⁻¹`.
The exponent `n / p` is `n / p.toReal`, which is `0` at `p = 0` and `p = ∞`, where the factor is
thus `|r|⁻¹`. -/
theorem eLpNorm_fderiv_comp_inv_smul (u : E → F) {r : ℝ} (hr : r ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ fun y => u (r⁻¹ • y)) p μ =
      ENNReal.ofReal (|r| ^ ((finrank ℝ E : ℝ) / p.toReal - 1)) * eLpNorm (fderiv ℝ u) p μ := by
  have hfderiv : (fderiv ℝ fun y => u (r⁻¹ • y)) = r⁻¹ • fun x => fderiv ℝ u (r⁻¹ • x) :=
    funext fun x => fderiv_comp_smul (f := u) (x := x) r⁻¹
  rw [hfderiv, eLpNorm_const_smul r⁻¹ (fun x => fderiv ℝ u (r⁻¹ • x)) p μ,
    eLpNorm_comp_inv_smul μ (fderiv ℝ u) hr p, ← mul_assoc]
  congr 1
  rw [Real.eNorm_eq_ofReal_abs, abs_inv, ← ENNReal.ofReal_mul (by positivity),
    Real.rpow_sub (abs_pos.2 hr), Real.rpow_one, ← div_eq_inv_mul]

/-- **Dilation scaling of the `Lᵖ` seminorm of the `k`-th derivative:**
`‖Dᵏ(u (r⁻¹ • ·))‖_p = |r| ^ (n / p - k) * ‖Dᵏ u‖_p` for `r ≠ 0` and `u` of class `Cᵏ`. Each of
the `k` differentiations contributes a factor `r⁻¹` by the chain rule, in the shape of Mathlib's
`iteratedFDeriv_comp_const_smul`. The exponent `n / p` is `n / p.toReal`, which is `0` at `p = 0`
and `p = ∞`. -/
theorem eLpNorm_iteratedFDeriv_comp_inv_smul {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u) {r : ℝ}
    (hr : r ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ k fun y => u (r⁻¹ • y)) p μ =
      ENNReal.ofReal (|r| ^ ((finrank ℝ E : ℝ) / p.toReal - k)) *
        eLpNorm (iteratedFDeriv ℝ k u) p μ := by
  have hiter : (iteratedFDeriv ℝ k fun y => u (r⁻¹ • y)) =
      r⁻¹ ^ k • fun x => iteratedFDeriv ℝ k u (r⁻¹ • x) := by
    rw [iteratedFDeriv_comp_const_smul r⁻¹ hu, Pi.smul_def]
  rw [hiter, eLpNorm_const_smul (r⁻¹ ^ k) (fun x => iteratedFDeriv ℝ k u (r⁻¹ • x)) p μ,
    eLpNorm_comp_inv_smul μ (iteratedFDeriv ℝ k u) hr p, ← mul_assoc]
  congr 1
  rw [Real.eNorm_eq_ofReal_abs, abs_pow, abs_inv, ← ENNReal.ofReal_mul (by positivity),
    Real.rpow_sub (abs_pos.2 hr), Real.rpow_natCast, inv_pow, ← div_eq_inv_mul]

/-- **Dilation scaling of the `Lᵖ` seminorm of the `k`-th derivative, for `u (r • ·)`:**
`‖Dᵏ(u (r • ·))‖_p = |r| ^ (k - n / p) * ‖Dᵏ u‖_p` for `r ≠ 0` and `u` of class `Cᵏ`. This is
`MeasureTheory.Measure.eLpNorm_iteratedFDeriv_comp_inv_smul` for the dilation by `r⁻¹`. -/
theorem eLpNorm_iteratedFDeriv_comp_smul {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u) {r : ℝ}
    (hr : r ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ k fun y => u (r • y)) p μ =
      ENNReal.ofReal (|r| ^ ((k : ℝ) - finrank ℝ E / p.toReal)) *
        eLpNorm (iteratedFDeriv ℝ k u) p μ := by
  simpa [abs_inv, Real.inv_rpow, ← Real.rpow_neg] using
    eLpNorm_iteratedFDeriv_comp_inv_smul μ hu (inv_ne_zero hr) p

/-- **Dilation scaling of the real `Lᵖ` seminorm of the `k`-th derivative:**
`‖Dᵏ(u (r • ·))‖_p = |r| ^ (k - n / p) * ‖Dᵏ u‖_p` for `r ≠ 0` and `u` of class `Cᵏ`. This is
`MeasureTheory.Measure.eLpNorm_iteratedFDeriv_comp_smul` read in `lpNorm`. -/
theorem lpNorm_iteratedFDeriv_comp_smul {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u) {r : ℝ}
    (hr : r ≠ 0) (p : ℝ≥0∞) :
    lpNorm (iteratedFDeriv ℝ k fun y => u (r • y)) p μ =
      |r| ^ ((k : ℝ) - finrank ℝ E / p.toReal) * lpNorm (iteratedFDeriv ℝ k u) p μ := by
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_iteratedFDeriv_comp_smul μ hu hr p,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end MeasureTheory.Measure

namespace MeasureTheory.MemLp

open Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Dilation preserves `Lᵖ` integrability of the `k`-th derivative.** If `u` is of class `Cᵏ`
and `Dᵏ u ∈ Lᵖ`, then `Dᵏ(u (r • ·)) ∈ Lᵖ` for every `r ≠ 0`. -/
theorem iteratedFDeriv_comp_smul {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u) {r : ℝ} (hr : r ≠ 0)
    {p : ℝ≥0∞} (hm : MemLp (iteratedFDeriv ℝ k u) p μ) :
    MemLp (iteratedFDeriv ℝ k fun y => u (r • y)) p μ := by
  rw [memLp_iff, Measure.eLpNorm_iteratedFDeriv_comp_smul μ hu hr p]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.1 hm)

end MeasureTheory.MemLp
