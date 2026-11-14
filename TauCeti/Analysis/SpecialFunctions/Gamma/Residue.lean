/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Residues of the complex Gamma function and shifted Gamma weights

At each nonpositive integer `-n`, the complex Gamma function has a simple pole with limit
`(s + n) Γ(s) → (-1)^n / n!` (`Complex.tendsto_add_natCast_mul_Gamma`). This file records the
corresponding values of `TauCeti.Contour.residue`, together with the residue formulas for products
`s ↦ g s * Γ(s - z₀)` against an analytic weight `g`: at `s = z₀ - n` the residue is
`g (z₀ - n) * (-1)^n / n!`, and in particular at `s = z₀` it is `g z₀`.

## Main results

* `Complex.meromorphicAt_Gamma`: `Γ` is meromorphic at every complex point.
* `Complex.residue_Gamma_neg_nat`: `Res_{-n} Γ = (-1)^n / n!`.
* `Complex.residue_Gamma_zero`: `Res_0 Γ = 1`.
* `TauCeti.Contour.residue_mul_Gamma_sub_neg_nat`: `Res_{z₀ - n} (g(s) Γ(s - z₀)) =
  g(z₀ - n) (-1)^n / n!` when `g` is analytic at `z₀ - n`.
* `TauCeti.Contour.residue_mul_Gamma_sub`: `Res_{z₀} (g(s) Γ(s - z₀)) = g(z₀)` when `g` is
  analytic at `z₀`.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §12.1.
-/

public section

open Filter Topology

namespace Complex

/-- The complex Gamma function is meromorphic at every point of `ℂ`, being the reciprocal of the
entire function `s ↦ (Γ(s))⁻¹`. -/
@[fun_prop]
theorem meromorphicAt_Gamma (s : ℂ) : MeromorphicAt Gamma s :=
  ((differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv).congr
    (Eventually.of_forall fun z ↦ by simp)

/-- At each nonpositive integer `-n`, `Γ` has residue `(-1)^n / n!`. -/
theorem residue_Gamma_neg_nat (n : ℕ) :
    TauCeti.Contour.residue Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) :=
  TauCeti.Contour.residue_eq_of_tendsto_sub_mul (meromorphicAt_Gamma _)
    ((tendsto_add_natCast_mul_Gamma n).congr fun s ↦ by ring)

/-- At `0`, `Γ` has residue `1`. -/
@[simp]
theorem residue_Gamma_zero : TauCeti.Contour.residue Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

end Complex

namespace TauCeti.Contour

/-- Multiplying an analytic weight `g` by the shifted Gamma factor `Γ(s - z₀)` produces residue
`g(z₀ - n) (-1)^n / n!` at the pole `z₀ - n`. -/
theorem residue_mul_Gamma_sub_neg_nat {g : ℂ → ℂ} {z₀ : ℂ} (n : ℕ)
    (hg : AnalyticAt ℂ g (z₀ - n)) :
    residue (fun s ↦ g s * Complex.Gamma (s - z₀)) (z₀ - n) =
      g (z₀ - n) * ((-1) ^ n / (n.factorial : ℂ)) := by
  have hg' : AnalyticAt ℂ (fun w ↦ g (w + z₀)) (-(n : ℂ)) :=
    hg.comp_of_eq (analyticAt_id.add analyticAt_const) (by ring)
  have hmero : MeromorphicAt (fun w ↦ g (w + z₀) * Complex.Gamma w) (-(n : ℂ)) :=
    hg'.meromorphicAt.mul (Complex.meromorphicAt_Gamma _)
  have hg_lim : Tendsto (fun w ↦ g (w + z₀)) (𝓝[≠] (-(n : ℂ))) (𝓝 (g (z₀ - n))) := by
    simpa [show -(n : ℂ) + z₀ = z₀ - n by ring] using
      hg'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun w ↦ (w - -(n : ℂ)) * (g (w + z₀) * Complex.Gamma w))
      (𝓝[≠] (-(n : ℂ))) (𝓝 (g (z₀ - n) * ((-1) ^ n / (n.factorial : ℂ)))) :=
    (hg_lim.mul (Complex.tendsto_add_natCast_mul_Gamma n)).congr fun w ↦ by ring
  have hshift := residue_comp_add_const (fun w ↦ g (w + z₀) * Complex.Gamma w) (-z₀) (z₀ - n)
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at hshift
  rw [show z₀ + (-(n : ℂ) + -z₀) = -(n : ℂ) by ring] at hshift
  simpa only [sub_eq_add_neg] using hshift.trans (residue_eq_of_tendsto_sub_mul hmero hlim)

/-- Multiplying an analytic weight `g` by `Γ(s - z₀)` produces residue `g z₀` at `s = z₀`. -/
theorem residue_mul_Gamma_sub {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    residue (fun s ↦ g s * Complex.Gamma (s - z₀)) z₀ = g z₀ := by
  simpa using residue_mul_Gamma_sub_neg_nat 0 (by simpa using hg)

end TauCeti.Contour
