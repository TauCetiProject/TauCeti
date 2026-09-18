/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
import TauCeti.Analysis.Calculus.Taylor

/-!
# A Bernstein function divided by its parameter is completely monotone

If `f` is a Bernstein function, then `t ↦ f(t) / t` is completely monotone on `(0, ∞)`. This is
one of the standard correspondences between Bernstein and completely monotone functions, next to
`t ↦ e^{-x f(t)}` (`TauCeti.IsBernsteinFunction.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul`)
and the primitive of a completely monotone function
(`TauCeti.IsCompletelyMonotoneOnIoi.isBernsteinFunction_integral`). For a *complete* Bernstein
function the quotient is even a Stieltjes function
(`TauCeti.IsCompleteBernsteinFunction.isStieltjesFunction_div`); for a general Bernstein function
complete monotonicity is the most one can say.

The open half-line is essential: the quotient has a singularity `f(0) / t` at the origin whenever
`f(0) > 0`. Continuity of `f` at `0` is not needed, only its nonnegativity and smoothness on
`(0, ∞)` and the complete monotonicity of `f'` there, so the theorem is stated under exactly
those hypotheses and specialized to Bernstein functions afterwards.

The sign of `dⁿ/dtⁿ (f(t) / t)` is that of `(-1)ⁿ T(0)`, where `T` is the Taylor polynomial of
order `n` of `f` expanded at `t` (`TauCeti.iteratedDeriv_div_id`). Since `(-1)ⁿ f⁽ⁿ⁺¹⁾ ≥ 0`,
the Taylor remainder has a sign on every `[ε, t]` with `ε > 0`, giving `T(ε) ≥ f(ε) ≥ 0`
(`TauCeti.le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg`), and `T(0) ≥ 0`
follows by letting `ε → 0`.

## Main declarations

* `TauCeti.isCompletelyMonotoneOnIoi_div_of_isCompletelyMonotoneOnIoi_deriv`: if `f` is smooth
  and nonnegative on `(0, ∞)` with completely monotone derivative there, then `t ↦ f(t) / t` is
  completely monotone on `(0, ∞)`.
* `TauCeti.IsBernsteinFunction.isCompletelyMonotoneOnIoi_div`: a Bernstein function divided by
  its parameter is completely monotone on `(0, ∞)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 3.
-/

public section

open Set Filter
open scoped ContDiff Topology Nat

namespace TauCeti

variable {f : ℝ → ℝ}

/-- If `f` is smooth and nonnegative on `(0, ∞)` and its derivative is completely monotone there,
then `t ↦ f(t) / t` is completely monotone on `(0, ∞)`. -/
theorem isCompletelyMonotoneOnIoi_div_of_isCompletelyMonotoneOnIoi_deriv
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (hnonneg : ∀ t, 0 < t → 0 ≤ f t)
    (hf' : IsCompletelyMonotoneOnIoi (deriv f)) :
    IsCompletelyMonotoneOnIoi (fun t => f t / t) := by
  refine ⟨hf.div contDiffOn_id fun t ht => ht.ne', fun n t ht => ?_⟩
  -- The Taylor polynomial of order `n` of `f` at `t`, evaluated at `ε ∈ (0, t)`, dominates `f ε`.
  have hle : ∀ ε ∈ Ioo 0 t, f ε ≤ taylorWithinEval f n (Ioi 0) t ε := fun ε hε =>
    le_taylorWithinEval_of_neg_one_pow_mul_iteratedDerivWithin_nonneg isOpen_Ioi hε.2.le
      (fun z hz => lt_of_lt_of_le hε.1 hz.1) (hf.of_le (by exact_mod_cast le_top))
      fun z hz => by
        have hz0 : 0 < z := lt_of_lt_of_le hε.1 hz.1
        rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hz0, iteratedDeriv_succ']
        exact hf'.neg_one_pow_mul_iteratedDeriv_nonneg n hz0
  -- Letting `ε → 0`, the Taylor polynomial at `0` is nonnegative.
  have hcont : Continuous fun x => taylorWithinEval f n (Ioi 0) t x := by
    simp only [taylor_within_apply]
    fun_prop
  have htaylor : 0 ≤ taylorWithinEval f n (Ioi 0) t 0 :=
    ge_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_of_mem (Ioo_mem_nhdsGT ht) fun ε hε => (hnonneg ε hε.1).trans (hle ε hε))
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [iteratedDeriv_div_id isOpen_Ioi ht ht.ne' (hf.of_le (by exact_mod_cast le_top)),
    ← mul_assoc, ← mul_assoc, ← mul_assoc, hsq, one_mul]
  positivity

/-- **A Bernstein function divided by its parameter is completely monotone** on `(0, ∞)`. -/
theorem IsBernsteinFunction.isCompletelyMonotoneOnIoi_div (hf : IsBernsteinFunction f) :
    IsCompletelyMonotoneOnIoi (fun t => f t / t) :=
  isCompletelyMonotoneOnIoi_div_of_isCompletelyMonotoneOnIoi_deriv hf.contDiffOn
    (fun _ ht => hf.nonneg ht.le) hf.deriv_isCompletelyMonotoneOnIoi

end TauCeti
