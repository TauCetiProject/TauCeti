/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass

/-!
# Diagonal operators in the trace-class and Hilbert–Schmidt ideals

On `ℓ²(ℕ, 𝕜)`, the diagonal operator with decreasing nonnegative coefficients `cₙ` has
approximation numbers `cₙ` (`lp.singularValue_diagonalCLM_ofAntitone`). It is therefore trace
class exactly when `∑ cₙ < ∞`. More generally, a diagonal operator on `ℓ²(ι, 𝕜)` with bounded
coefficients `dᵢ` is Hilbert–Schmidt exactly when `∑ ‖dᵢ‖² < ∞`, with no ordering needed: its
Hilbert–Schmidt energy in the coordinate basis is `∑ ‖dᵢ‖²`.

## Main results

* `lp.diagonalCLM_ofAntitone_mem_traceClass_iff`: a decreasing diagonal operator on `ℓ²` is
  trace class iff its coefficients are summable.
* `lp.diagonalCLM_mem_hilbertSchmidt_iff`: a bounded diagonal operator on `ℓ²` is Hilbert–Schmidt
  iff the squared norms of its coefficients are summable.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
-/

public section

open InnerProductSpace TauCeti TauCeti.OperatorIdealFamily
open scoped InnerProductSpace ENNReal NNReal lp

universe u

namespace lp

variable {𝕜 : Type u} [RCLike 𝕜]

/-- A diagonal operator on `ℓ²(ℕ, 𝕜)` with decreasing nonnegative coefficients `cₙ` is trace class
exactly when `∑ cₙ < ∞`. -/
theorem diagonalCLM_ofAntitone_mem_traceClass_iff {c : ℕ → ℝ≥0} (hc : Antitone c) :
    diagonalCLM (p := 2) (ofAntitone 𝕜 hc) ∈
        ((traceClass.{u, u, u} 𝕜).operatorGauge ℓ²(ℕ, 𝕜) ℓ²(ℕ, 𝕜)).finiteSubmodule ↔
      Summable c := by
  rw [mem_finiteSubmodule_traceClass_iff,
    show (diagonalCLM (p := 2) (ofAntitone 𝕜 hc)).singularValue = c from
      funext (singularValue_diagonalCLM_ofAntitone hc)]

/-- A diagonal operator on `ℓ²(ι, 𝕜)` with bounded coefficients `dᵢ` is Hilbert–Schmidt exactly
when `∑ ‖dᵢ‖² < ∞`: its Hilbert–Schmidt energy in the coordinate basis is `∑ ‖dᵢ‖²`. -/
theorem diagonalCLM_mem_hilbertSchmidt_iff {ι : Type*} (d : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := 2) d ∈
        ((hilbertSchmidt 𝕜).operatorGauge ℓ²(ι, 𝕜) ℓ²(ι, 𝕜)).finiteSubmodule ↔
      Summable fun i ↦ ‖d i‖ ^ 2 := by
  classical
  have h (i : ι) :
      ‖diagonalCLM (p := 2) d ((default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) i)‖ₑ ^ 2 = ‖d i ^ 2‖ₑ := by
    simp [HilbertBasis.default_apply, diagonalCLM_single, ← ofReal_norm, lp.norm_single two_pos,
      ENNReal.ofReal_pow]
  rw [mem_finiteSubmodule_hilbertSchmidt_iff _ (default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)),
    ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_congr h,
    tsum_eNorm_ne_top_iff_summable_norm]
  simp

end lp
