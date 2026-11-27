/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Projection
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass.Trace

import Mathlib.Analysis.PSeries

/-!
# Diagonal operators and finite-rank projections in the trace class

Two basic examples of the trace-class and Hilbert–Schmidt ideals.

**Diagonal operators.** On `ℓ²(ℕ, 𝕜)`, the diagonal operator with decreasing nonnegative
coefficients `cₙ` has approximation numbers `cₙ` (`lp.singularValue_diagonalCLM_ofAntitone`). It
is therefore trace class exactly when `∑ cₙ < ∞`. More generally, a diagonal operator with
bounded coefficients `dᵢ` is Hilbert–Schmidt exactly when `∑ ‖dᵢ‖² < ∞`, with no ordering needed.
For `cₙ = 1 / (n + 1)` the second series converges and the first does not, so this diagonal
operator is Hilbert–Schmidt but not trace class: the Hilbert–Schmidt ideal is not contained in
the trace-class ideal.

**Orthogonal projections.** The orthogonal projection onto a subspace of finite dimension `r` has
approximation numbers `1` below `r` and `0` from `r` on, so its trace norm is `r`. It is the sum
`∑ₖ ⟪eₖ, ·⟫ eₖ` over an orthonormal basis `(eₖ)` of the subspace, so its trace is
`∑ₖ ⟪eₖ, eₖ⟫ = r`.

## Main results

* `lp.diagonalCLM_ofAntitone_mem_traceClass_iff`: a decreasing diagonal operator on `ℓ²` is
  trace class iff its coefficients are summable.
* `lp.diagonalCLM_mem_hilbertSchmidt_iff`: a bounded diagonal operator on `ℓ²` is Hilbert–Schmidt
  iff the squared norms of its coefficients are summable.
* `lp.diagonalCLM_one_div_add_one_mem_hilbertSchmidt` and
  `lp.diagonalCLM_one_div_add_one_notMem_traceClass`: the diagonal operator with coefficients
  `1 / (n + 1)` is Hilbert–Schmidt and not trace class.
* `Submodule.nuclearENorm_starProjection` and `ContinuousLinearMap.trace_starProjection`: the
  orthogonal projection onto a subspace of dimension `r` has trace norm `r` and trace `r`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99, AMS,
  2009, Section 6.3.
-/

public section

open InnerProductSpace TauCeti TauCeti.OperatorIdealFamily
open scoped InnerProductSpace ENNReal NNReal lp

universe u

namespace lp

variable {𝕜 : Type u} [RCLike 𝕜] {c : ℕ → ℝ≥0} (hc : Antitone c)

/-- A diagonal operator on `ℓ²(ℕ, 𝕜)` with decreasing nonnegative coefficients `cₙ` is trace class
exactly when `∑ cₙ < ∞`. -/
theorem diagonalCLM_ofAntitone_mem_traceClass_iff :
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

/-- **The diagonal operator `diag(1 / (n + 1))` is Hilbert–Schmidt**, since `∑ 1 / (n + 1)² < ∞`. -/
theorem diagonalCLM_one_div_add_one_mem_hilbertSchmidt :
    diagonalCLM (p := 2) (ofAntitone 𝕜 antitone_one_div_add_one) ∈
      ((hilbertSchmidt.{u, u, u} 𝕜).operatorGauge ℓ²(ℕ, 𝕜) ℓ²(ℕ, 𝕜)).finiteSubmodule := by
  rw [diagonalCLM_mem_hilbertSchmidt_iff]
  simp_rw [norm_ofAntitone_apply]
  push_cast
  simpa [inv_pow] using (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)

/-- **The diagonal operator `diag(1 / (n + 1))` is not trace class**, since
`∑ 1 / (n + 1) = ∞`. -/
theorem diagonalCLM_one_div_add_one_notMem_traceClass :
    diagonalCLM (p := 2) (ofAntitone 𝕜 antitone_one_div_add_one) ∉
      ((traceClass.{u, u, u} 𝕜).operatorGauge ℓ²(ℕ, 𝕜) ℓ²(ℕ, 𝕜)).finiteSubmodule := by
  rw [diagonalCLM_ofAntitone_mem_traceClass_iff, ← NNReal.summable_coe]
  push_cast
  exact fun h ↦ Real.not_summable_natCast_inv ((summable_nat_add_iff 1).1 (by simpa using h))

end lp

namespace Submodule

variable {𝕜 : Type*} {E : Type u} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U]

/-- **Trace norm of a finite-rank projection.** The orthogonal projection onto a subspace of
finite dimension `r` has nuclear gauge `r`. -/
@[simp]
theorem nuclearENorm_starProjection : U.starProjection.nuclearENorm = Module.finrank 𝕜 U := by
  have h (n : ℕ) : (U.starProjection.singularValue n : ℝ≥0∞) =
      if n ∈ Finset.range (Module.finrank 𝕜 U) then 1 else 0 := by
    simp only [singularValue_starProjection, ← Module.finrank_eq_rank, Nat.cast_lt,
      Finset.mem_range]
    split_ifs <;> simp
  simp_rw [ContinuousLinearMap.nuclearENorm_def, h]
  rw [tsum_eq_sum (s := Finset.range (Module.finrank 𝕜 U)) fun n hn ↦ by simp_all,
    Finset.sum_ite_of_true fun _ hn ↦ hn, Finset.sum_const, Finset.card_range, nsmul_one]

variable [CompleteSpace E]

/-- The orthogonal projection onto a finite-dimensional subspace is trace class. -/
theorem starProjection_mem_traceClass :
    U.starProjection ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
  rw [mem_finiteSubmodule_traceClass_iff_nuclearENorm_ne_top, nuclearENorm_starProjection]
  exact ENNReal.natCast_ne_top _

end Submodule

namespace ContinuousLinearMap

variable {𝕜 : Type*} {E : Type u} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U]

/-- **Trace of a finite-rank projection.** The orthogonal projection onto a subspace of finite
dimension `r` has trace `r`. -/
@[simp]
theorem trace_starProjection : U.starProjection.trace = Module.finrank 𝕜 U := by
  set e := stdOrthonormalBasis 𝕜 U
  have hsum : HasSum (fun i ↦ rankOne 𝕜 (e i : E) (e i : E)) U.starProjection := by
    rw [e.starProjection_eq_sum_rankOne]
    exact hasSum_fintype _
  rw [trace_eq_tsum_of_hasSum_rankOne .of_finite hsum, tsum_fintype]
  have he (i) : ‖(e i : E)‖ = 1 := e.norm_eq_one i
  simp [inner_self_eq_norm_sq_to_K, he]

end ContinuousLinearMap
