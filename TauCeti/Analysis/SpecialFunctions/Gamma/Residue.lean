/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Residues of the complex Gamma function

The complex Gamma function has simple poles at the nonpositive integers `-n` with residues
`(-1)^n / n!`, as follows from `Complex.tendsto_add_natCast_mul_Gamma` and the simple-pole limit
formula `TauCeti.Contour.residue_eq_of_tendsto_sub_mul`. Multiplying by a weight `w` analytic at
`-n` scales the residue by `w (-n)`.

## Main results

* `Complex.residue_Gamma_mul_neg_nat`: `residue (fun s ↦ Γ(s) w(s)) (-n) = ((-1)^n / n!) w(-n)`
  for `w` analytic at `-n`.
* `Complex.residue_Gamma_mul_zero`: `residue (fun s ↦ Γ(s) w(s)) 0 = w(0)` for `w` analytic at `0`.
* `Complex.residue_Gamma_neg_nat`, `Complex.meromorphicTrailingCoeffAt_Gamma_neg_nat`:
  `residue Γ (-n) = meromorphicTrailingCoeffAt Γ (-n) = (-1)^n / n!`.
* `Complex.residue_Gamma_zero`, `Complex.meromorphicTrailingCoeffAt_Gamma_zero`:
  `residue Γ 0 = meromorphicTrailingCoeffAt Γ 0 = 1`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §4.41.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1.
-/

public section

open Filter
open scoped Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- Multiplying `Complex.Gamma` by a function `w` analytic at `-n` scales the residue at `-n` by
`w (-n)`. -/
theorem residue_Gamma_mul_neg_nat (n : ℕ) {w : ℂ → ℂ} (hw : AnalyticAt ℂ w (-(n : ℂ))) :
    TauCeti.Contour.residue (fun s ↦ Gamma s * w s) (-(n : ℂ)) =
      (-1) ^ n / (n.factorial : ℂ) * w (-(n : ℂ)) := by
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul ((Meromorphic.Gamma _).mul hw.meromorphicAt)
    ?_
  have hlim := (tendsto_add_natCast_mul_Gamma n).mul
    (hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine hlim.congr fun s ↦ ?_
  ring

/-- Multiplying `Complex.Gamma` by a function `w` analytic at `0` gives residue `w 0` at `0`. -/
theorem residue_Gamma_mul_zero {w : ℂ → ℂ} (hw : AnalyticAt ℂ w 0) :
    TauCeti.Contour.residue (fun s ↦ Gamma s * w s) 0 = w 0 := by
  simpa using residue_Gamma_mul_neg_nat 0 (by simpa using hw)

/-- The residue of `Complex.Gamma` at the nonpositive integer `-n` is `(-1)^n / n!`. -/
-- Deliberately not `@[simp]`: `simp` rewrites the LHS to `meromorphicTrailingCoeffAt Gamma (-n)`
-- via `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` and
-- `meromorphicOrderAt_Gamma_neg_nat`, then closes via `meromorphicTrailingCoeffAt_Gamma_neg_nat`.
theorem residue_Gamma_neg_nat (n : ℕ) :
    TauCeti.Contour.residue Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) := by
  simpa only [mul_one] using residue_Gamma_mul_neg_nat n (analyticAt_const (v := 1))

/-- The leading Laurent coefficient of `Complex.Gamma` at `-n` is `(-1)^n / n!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Gamma (-(n : ℂ)) = (-1) ^ n / (n.factorial : ℂ) := by
  rw [← TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one
    (meromorphicOrderAt_Gamma_neg_nat n), residue_Gamma_neg_nat]

/-- The residue of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem residue_Gamma_zero : TauCeti.Contour.residue Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

/-- The leading Laurent coefficient of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gamma_zero : meromorphicTrailingCoeffAt Gamma 0 = 1 := by
  simpa using meromorphicTrailingCoeffAt_Gamma_neg_nat 0

end Complex
