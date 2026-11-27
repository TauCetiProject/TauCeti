/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Residues of the complex Gamma and digamma functions

The complex Gamma function has simple poles at the nonpositive integers `-n` with residues
`(-1)^n / n!`, as follows from `Complex.tendsto_add_natCast_mul_Gamma` and the simple-pole limit
formula `TauCeti.Contour.residue_eq_of_tendsto_sub_mul`. Multiplying by a weight `w` analytic at
`-n` scales the residue by `w (-n)`.

The digamma function `ψ = Γ′/Γ` (`Complex.digamma`) also has simple poles at the nonpositive
integers, but with residue `-1` at every one of them, independent of `n`: the residue of a
logarithmic derivative is the order of the function
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`), and `Γ` has order `-1` at `-n`.
Equivalently `(z + n) ψ(z) → -1` as `z → -n`.

## Main results

* `Complex.residue_Gamma_mul_neg_nat`: `residue (fun s ↦ Γ(s) w(s)) (-n) = ((-1)^n / n!) w(-n)`
  for `w` analytic at `-n`.
* `Complex.residue_Gamma_mul_zero`: `residue (fun s ↦ Γ(s) w(s)) 0 = w(0)` for `w` analytic at `0`.
* `Complex.residue_Gamma_neg_nat`: `residue Γ (-n) = (-1)^n / n!`.
* `Complex.residue_Gamma_zero`: `residue Γ 0 = 1`.
* `Complex.meromorphicOrderAt_digamma_neg_nat`: `ψ` has a simple pole at `-n`.
* `Complex.residue_digamma_neg_nat`, `Complex.tendsto_add_natCast_mul_digamma`: the residue of `ψ`
  at `-n` is `-1`, that is, `(z + n) ψ(z) → -1` as `z → -n`.
* `Complex.residue_digamma_mul_neg_nat`: `residue (fun s ↦ ψ(s) w(s)) (-n) = -w(-n)` for `w`
  analytic at `-n`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §4.41.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.1.
* F. W. J. Olver, *Asymptotics and Special Functions*, Ch. 2, §2.1 (the poles of `ψ`).
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

/-- The residue of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem residue_Gamma_zero : TauCeti.Contour.residue Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

/-! ### The poles of digamma -/

/-- The digamma function has a simple pole at each nonpositive integer. -/
@[simp]
theorem meromorphicOrderAt_digamma_neg_nat (n : ℕ) :
    meromorphicOrderAt digamma (-(n : ℂ)) = -1 := by
  rw [digamma_def]
  exact meromorphicOrderAt_logDeriv_eq_neg_one (by simp) (by simp)

/-- The residue of `Complex.digamma` at the nonpositive integer `-n` is `-1`, for every `n`. -/
-- Deliberately not `@[simp]`: `simp` proves it through
-- `residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one`,
-- `meromorphicOrderAt_digamma_neg_nat` and `meromorphicTrailingCoeffAt_digamma_neg_nat`.
theorem residue_digamma_neg_nat (n : ℕ) :
    TauCeti.Contour.residue digamma (-(n : ℂ)) = -1 := by
  rw [digamma_def, TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt (Meromorphic.Gamma _)
    (n := -1) (by simp)]
  simp

/-- **The residue of `ψ` at `-n`**: `(z + n) ψ(z) → -1` as `z → -n`. Unlike the residue
`(-1)^n / n!` of `Γ` (`Complex.tendsto_add_natCast_mul_Gamma`), it does not depend on `n`. -/
theorem tendsto_add_natCast_mul_digamma (n : ℕ) :
    Tendsto (fun z : ℂ ↦ (z + n) * digamma z) (𝓝[≠] (-(n : ℂ))) (𝓝 (-1)) := by
  simpa only [residue_digamma_neg_nat, sub_neg_eq_add] using
    TauCeti.Contour.tendsto_sub_mul_nhds_residue_of_order_eq_neg_one
      (meromorphicOrderAt_digamma_neg_nat n)

/-- The leading Laurent coefficient of `Complex.digamma` at `-n` is `-1`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_digamma_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt digamma (-(n : ℂ)) = -1 := by
  rw [← TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one
    (meromorphicOrderAt_digamma_neg_nat n), residue_digamma_neg_nat]

/-- The leading Laurent coefficient of `Complex.digamma` at `0` is `-1`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_digamma_zero : meromorphicTrailingCoeffAt digamma 0 = -1 := by
  simpa using meromorphicTrailingCoeffAt_digamma_neg_nat 0

/-- Multiplying `Complex.digamma` by a function `w` analytic at `-n` gives residue `-w (-n)` at
`-n`. -/
theorem residue_digamma_mul_neg_nat (n : ℕ) {w : ℂ → ℂ} (hw : AnalyticAt ℂ w (-(n : ℂ))) :
    TauCeti.Contour.residue (fun s ↦ digamma s * w s) (-(n : ℂ)) = -w (-(n : ℂ)) := by
  rw [TauCeti.Contour.residue_mul_of_neg_one_le (meromorphic_digamma _)
    (meromorphicOrderAt_digamma_neg_nat n).ge hw, residue_digamma_neg_nat, neg_one_mul]

/-- Multiplying `Complex.digamma` by a function `w` analytic at `0` gives residue `-w 0` at `0`. -/
theorem residue_digamma_mul_zero {w : ℂ → ℂ} (hw : AnalyticAt ℂ w 0) :
    TauCeti.Contour.residue (fun s ↦ digamma s * w s) 0 = -w 0 := by
  simpa using residue_digamma_mul_neg_nat 0 (by simpa using hw)

/-- The residue of `Complex.digamma` at `0` is `-1`. -/
@[simp]
theorem residue_digamma_zero : TauCeti.Contour.residue digamma 0 = -1 := by
  simpa using residue_digamma_neg_nat 0

end Complex
