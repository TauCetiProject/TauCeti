/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Meromorphic.Complex
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Residues of the complex Gamma function and Gamma weights

At each nonpositive integer `-n`, the complex Gamma function has a simple pole with limit
`(s + n) Γ(s) → (-1)^n / n!` (`Complex.tendsto_add_natCast_mul_Gamma`). This file records the
corresponding values of `TauCeti.Contour.residue`, together with the residue formulas for products
against an analytic weight `g`, both unshifted (`s ↦ g s * Γ(s)` at `-n` and `0`) and shifted
(`s ↦ g s * Γ(s - z₀)` at `z₀ - n` and `z₀`), derived from the general simple-pole product rule
`TauCeti.Contour.residue_mul_of_analyticAt`.

## Main results

* `TauCeti.Contour.residue_Gamma_neg_nat`: `Res_{-n} Γ = (-1)^n / n!`.
* `TauCeti.Contour.residue_Gamma_zero`: `Res_0 Γ = 1`.
* `TauCeti.Contour.residue_mul_Gamma_neg_nat`: `Res_{-n} (g(s) Γ(s)) = g(-n) (-1)^n / n!` when `g`
  is analytic at `-n`.
* `TauCeti.Contour.residue_mul_Gamma_zero`: `Res_0 (g(s) Γ(s)) = g(0)` when `g` is analytic at `0`.
* `TauCeti.Contour.residue_mul_Gamma_sub_sub_nat`: `Res_{z₀ - n} (g(s) Γ(s - z₀)) =
  g(z₀ - n) (-1)^n / n!` when `g` is analytic at `z₀ - n`.
* `TauCeti.Contour.residue_mul_Gamma_sub`: `Res_{z₀} (g(s) Γ(s - z₀)) = g(z₀)` when `g` is
  analytic at `z₀`.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §12.1.
-/

public section

open Filter Topology

namespace TauCeti.Contour

/-- At each nonpositive integer `-n`, `Γ` has residue `(-1)^n / n!`. -/
-- Deliberately not `@[simp]`: `simp` rewrites `residue Complex.Gamma (-(n : ℂ))` to
-- `meromorphicTrailingCoeffAt Complex.Gamma (-(n : ℂ))` via
-- `Complex.meromorphicOrderAt_Gamma_neg_nat` and
-- `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one`, so `simpNF` rejects `@[simp]`.
theorem residue_Gamma_neg_nat (n : ℕ) :
    residue Complex.Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) :=
  residue_eq_of_tendsto_sub_mul (Meromorphic.Gamma _)
    ((Complex.tendsto_add_natCast_mul_Gamma n).congr fun s ↦ by ring)

/-- At `0`, `Γ` has residue `1`. -/
@[simp]
theorem residue_Gamma_zero : residue Complex.Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

/-- Multiplying an analytic weight `g` by `Γ` produces residue `g(-n) (-1)^n / n!` at the pole
`-n`. -/
theorem residue_mul_Gamma_neg_nat {g : ℂ → ℂ} (n : ℕ) (hg : AnalyticAt ℂ g (-(n : ℂ))) :
    residue (fun s ↦ g s * Complex.Gamma s) (-(n : ℂ)) =
      g (-(n : ℂ)) * ((-1) ^ n / (n.factorial : ℂ)) := by
  rw [residue_mul_of_analyticAt hg (by rw [Complex.meromorphicOrderAt_Gamma_neg_nat]),
    residue_Gamma_neg_nat]

/-- Multiplying an analytic weight `g` by `Γ` produces residue `g 0` at `s = 0`. -/
theorem residue_mul_Gamma_zero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    residue (fun s ↦ g s * Complex.Gamma s) 0 = g 0 := by
  simpa using residue_mul_Gamma_neg_nat 0 (by simpa using hg)

/-- Multiplying an analytic weight `g` by the shifted Gamma factor `Γ(s - z₀)` produces residue
`g(z₀ - n) (-1)^n / n!` at the pole `z₀ - n`. -/
theorem residue_mul_Gamma_sub_sub_nat {g : ℂ → ℂ} {z₀ : ℂ} (n : ℕ)
    (hg : AnalyticAt ℂ g (z₀ - n)) :
    residue (fun s ↦ g s * Complex.Gamma (s - z₀)) (z₀ - n) =
      g (z₀ - n) * ((-1) ^ n / (n.factorial : ℂ)) := by
  have hg' : AnalyticAt ℂ (fun w ↦ g (w + z₀)) (-(n : ℂ)) :=
    hg.comp_of_eq (analyticAt_id.add analyticAt_const) (by ring)
  have hshift := residue_comp_add_const (fun w ↦ g (w + z₀) * Complex.Gamma w) (-z₀) (z₀ - n)
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at hshift
  rw [show z₀ + (-(n : ℂ) + -z₀) = -(n : ℂ) by ring] at hshift
  simpa only [sub_eq_add_neg, show -(n : ℂ) + z₀ = z₀ + -(n : ℂ) by ring] using
    hshift.trans (residue_mul_Gamma_neg_nat n hg')

/-- Multiplying an analytic weight `g` by `Γ(s - z₀)` produces residue `g z₀` at `s = z₀`. -/
theorem residue_mul_Gamma_sub {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    residue (fun s ↦ g s * Complex.Gamma (s - z₀)) z₀ = g z₀ := by
  simpa using residue_mul_Gamma_sub_sub_nat 0 (by simpa using hg)

end TauCeti.Contour
