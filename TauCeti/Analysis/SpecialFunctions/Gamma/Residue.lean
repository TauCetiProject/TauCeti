/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Residues of the complex Gamma function

The complex Gamma function has simple poles at the nonpositive integers `-n` with residues
`(-1)^n / n!`, as follows from `Complex.tendsto_add_natCast_mul_Gamma` and the simple-pole limit
formula `TauCeti.Contour.residue_eq_of_tendsto_sub_mul`. Multiplying by a weight `w` analytic at
`-n` scales the residue by `w (-n)`. The numerator `(z + n) Γ(z)`, extended by the residue at
`-n`, is analytic there, and the affine change of variable `s = A - 2t` gives the residue
`(-1)^(n+1) / (2 n!)` of `Γ(A - 2t)` at its pole `t = (A + n) / 2`.

## Main results

* `Complex.residue_Gamma_mul_neg_nat`: `residue (fun s ↦ Γ(s) w(s)) (-n) = ((-1)^n / n!) w(-n)`
  for `w` analytic at `-n`.
* `Complex.residue_Gamma_mul_zero`: `residue (fun s ↦ Γ(s) w(s)) 0 = w(0)` for `w` analytic at `0`.
* `Complex.residue_Gamma_neg_nat`: `residue Γ (-n) = (-1)^n / n!`.
* `Complex.residue_Gamma_zero`: `residue Γ 0 = 1`.
* `Complex.analyticAt_update_add_natCast_mul_Gamma`: `(z + n) Γ(z)`, extended by `(-1)^n / n!` at
  `-n`, is analytic at `-n`.
* `Complex.tendsto_sub_mul_Gamma_sub_two_mul`: `(t - (A + n) / 2) Γ(A - 2t) → (-1)^(n+1) / (2 n!)`
  as `t → (A + n) / 2`.

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

/-- The residue of `Complex.Gamma` at `0` is `1`. -/
@[simp]
theorem residue_Gamma_zero : TauCeti.Contour.residue Gamma 0 = 1 := by
  simpa using residue_Gamma_neg_nat 0

/-- The numerator `(z + n) Γ(z)` of the pole of `Γ` at `-n`, extended by its limit `(-1)^n / n!` at
`-n`, is analytic there. Near `-n` this writes `Γ(z) = φ(z) / (z + n)` with `φ` analytic. -/
theorem analyticAt_update_add_natCast_mul_Gamma (n : ℕ) :
    AnalyticAt ℂ (Function.update (fun z : ℂ ↦ (z + n) * Gamma z) (-(n : ℂ))
      ((-1) ^ n / (n.factorial : ℂ))) (-(n : ℂ)) := by
  refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    (continuousAt_update_same.mpr (tendsto_add_natCast_mul_Gamma n))
  filter_upwards [(Meromorphic.Gamma (-(n : ℂ))).eventually_analyticAt, eventually_mem_nhdsWithin]
    with z hz hzn
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ (z + n) * Gamma z) z := by fun_prop
  refine ha.differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hzn] with w hw
  exact Function.update_of_ne hw _ _

/-- **The residue of `Γ(A - 2t)` at `t = (A + n) / 2`**:
`(t - (A + n) / 2) Γ(A - 2t) → (-1)^(n+1) / (2 n!)`. -/
-- The factor `-1/2` relative to `Complex.tendsto_add_natCast_mul_Gamma` comes from the affine
-- change of variable `s = A - 2t`.
theorem tendsto_sub_mul_Gamma_sub_two_mul (A : ℂ) (n : ℕ) :
    Tendsto (fun t : ℂ ↦ (t - (A + n) / 2) * Gamma (A - 2 * t))
      (𝓝[≠] ((A + n) / 2)) (𝓝 ((-1 : ℂ) ^ (n + 1) / (2 * n.factorial))) := by
  have hs : Tendsto (fun t : ℂ ↦ A - 2 * t) (𝓝[≠] ((A + n) / 2)) (𝓝[≠] (-(n : ℂ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun t : ℂ ↦ A - 2 * t) (𝓝 ((A + n) / 2)) (𝓝 (A - 2 * ((A + n) / 2))) :=
        (continuous_const.sub (continuous_const.mul continuous_id)).tendsto _
      have hpole : A - 2 * ((A + n) / 2) = -(n : ℂ) := by ring
      rw [hpole] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht h
      exact ht (Set.mem_singleton_iff.mpr
        (by linear_combination (-1 / 2 : ℂ) * Set.mem_singleton_iff.mp h))
  have h := ((tendsto_add_natCast_mul_Gamma n).comp hs).const_mul (-1 / 2 : ℂ)
  have hres : (-1 / 2 : ℂ) * ((-1) ^ n / (n.factorial : ℂ)) =
      (-1 : ℂ) ^ (n + 1) / (2 * n.factorial) := by
    rw [pow_succ]
    ring
  rw [hres] at h
  refine h.congr fun t ↦ ?_
  simp only [Function.comp_apply]
  ring

end Complex
