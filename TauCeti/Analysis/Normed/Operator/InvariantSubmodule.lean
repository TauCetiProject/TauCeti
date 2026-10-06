/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Invariant submodules of operator exponentials

This file characterizes the closed submodules preserved by every operator in the one-parameter
family `exp (t A)`. Over a characteristic-zero nontrivially normed field, a closed submodule is
preserved by this entire family exactly when it is preserved by its infinitesimal generator `A`.

This equivalence lets consumers replace preservation by the full exponential family with the single
infinitesimal condition that `A` preserves the submodule.

## Main results

* `ContinuousLinearMap.forall_exp_smul_mem_invtSubmodule_iff`: a closed submodule is invariant
  under every `exp (t A)` if and only if it is invariant under `A`.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [ContinuousSMul ℚ 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- A closed submodule is invariant under every exponential `exp (t A)` if and only if it is
invariant under the bounded operator `A`. -/
theorem forall_exp_smul_mem_invtSubmodule_iff (A : X →L[𝕜] X)
    {S : Submodule 𝕜 X} (hS : IsClosed (S : Set X)) :
    (∀ t : 𝕜, S ∈ Module.End.invtSubmodule (exp (t • A)).toLinearMap) ↔
      S ∈ Module.End.invtSubmodule A.toLinearMap := by
  constructor
  · intro hExp x hx
    have hball : (0 : 𝕜) • A ∈
        Metric.eball (0 : X →L[𝕜] X) (expSeries 𝕜 (X →L[𝕜] X)).radius := by
      rw [expSeries_radius_eq_top]
      exact edist_lt_top _ _
    have hderiv : HasDerivAt (fun t : 𝕜 ↦ exp (t • A) x) (A x) 0 := by
      simpa [mul_apply_eq_comp] using
        (hasDerivAt_exp_smul_const_of_mem_ball A (0 : 𝕜) hball).clm_apply
          (hasDerivAt_const 0 x)
    simpa using hderiv.hasFDerivAt.apply_mem_of_eventually_sub_mem hS
      (.of_forall fun t ↦ S.sub_mem (hExp t hx) (by simpa using hx)) 1
  · intro hA t x hx
    have htA : S ∈ Module.End.invtSubmodule (t • A).toLinearMap :=
      fun y hy ↦ S.smul_mem t (hA hy)
    have hpow : ∀ n : ℕ, ((t • A) ^ n) x ∈ S := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n hn =>
          rw [pow_succ', mul_apply_eq_comp]
          exact htA hn
    have hsum := (exp_series_hasSum_exp' (𝔸 := X →L[𝕜] X) (𝕂 := 𝕜) (t • A)).mapL
      (ContinuousLinearMap.apply 𝕜 X x)
    exact hS.mem_of_tendsto hsum (.of_forall fun s ↦
      S.sum_mem fun n _ ↦ S.smul_mem _ (hpow n))

end ContinuousLinearMap

end
