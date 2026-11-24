/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Polynomial kernel chains for continuous linear endomorphisms

For a continuous linear endomorphism `K : E →L[𝕜] E` and a sequence of scalars `μ : ℕ → 𝕜`, the
evaluated polynomials `P n = Polynomial.aeval K (∏ i ∈ Finset.range n, (X - C (μ i)))` are
continuous linear endomorphisms whose kernels form an increasing chain of submodules stepped down
by `K - μ n • 1`. In a `T1Space`, each kernel is closed by `ContinuousLinearMap.isClosed_ker`
with no completeness hypothesis on `𝕜` or `E`. Over an integral domain acting without zero
divisors, whenever `μ n` is an eigenvalue of `K` distinct from `μ 0, …, μ (n - 1)`, the inclusion
`ker (P n) < ker (P (n + 1))` is strict.

## Main results

* `ContinuousLinearMap.ker_aeval_prod_range_le_succ`: the polynomial kernels increase with `n`.
* `ContinuousLinearMap.mem_ker_aeval_prod_range_succ_iff`: `x` lies in the `(n + 1)`-st kernel
  iff `K x - μ n • x` lies in the `n`-th kernel.
* `ContinuousLinearMap.ker_aeval_prod_range_lt_succ`: an eigenvalue `μ n` distinct from all
  earlier `μ i` (`i < n`) makes the inclusion from step `n` to step `n + 1` strict.
-/

public section

open Polynomial

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

private theorem aeval_prod_range_succ (K : E →L[𝕜] E) (μ : ℕ → 𝕜) (n : ℕ) :
    aeval K (∏ i ∈ Finset.range (n + 1), (X - C (μ i))) =
      aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) * (K - μ n • 1) := by
  simp only [Finset.prod_range_succ, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one]

private theorem aeval_prod_range_succ_comm (K : E →L[𝕜] E) (μ : ℕ → 𝕜) (n : ℕ) :
    aeval K (∏ i ∈ Finset.range (n + 1), (X - C (μ i))) =
      (K - μ n • 1) * aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) := by
  simp only [Finset.prod_range_succ_comm, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one]

/-- The kernels of `aeval K (∏ i < n, (X - C (μ i)))` form an increasing chain of submodules.
In a `T1Space`, each kernel is closed by `ContinuousLinearMap.isClosed_ker`. -/
theorem ker_aeval_prod_range_le_succ (K : E →L[𝕜] E) (μ : ℕ → 𝕜) (n : ℕ) :
    LinearMap.ker (aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) : E →ₗ[𝕜] E) ≤
      LinearMap.ker (aeval K (∏ i ∈ Finset.range (n + 1), (X - C (μ i))) : E →ₗ[𝕜] E) := by
  simpa only [aeval_prod_range_succ_comm, toLinearMap_mul, Module.End.mul_eq_comp] using
    LinearMap.ker_le_ker_comp
      (aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) : E →ₗ[𝕜] E)
      ((K - μ n • 1 : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- A vector `x` lies in the kernel of `aeval K (∏ i < n + 1, (X - C (μ i)))` iff
`K x - μ n • x` lies in the kernel of `aeval K (∏ i < n, (X - C (μ i)))`. -/
theorem mem_ker_aeval_prod_range_succ_iff (K : E →L[𝕜] E) (μ : ℕ → 𝕜) (n : ℕ) {x : E} :
    x ∈ LinearMap.ker (aeval K (∏ i ∈ Finset.range (n + 1), (X - C (μ i))) : E →ₗ[𝕜] E) ↔
      K x - μ n • x ∈
        LinearMap.ker (aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) : E →ₗ[𝕜] E) := by
  simp only [LinearMap.mem_ker, coe_coe, aeval_prod_range_succ, _root_.mul_apply_eq_comp,
    _root_.sub_apply, _root_.smul_apply, one_apply_eq_self]

/-- Over an integral domain acting without zero divisors, if `μ n` is an eigenvalue of a
continuous linear endomorphism `K` distinct from `μ i` for every `i < n`, then the kernel of
`aeval K (∏ i < n, (X - C (μ i)))` is strictly contained in that of
`aeval K (∏ i < n + 1, (X - C (μ i)))`. -/
theorem ker_aeval_prod_range_lt_succ [IsDomain 𝕜] [NoZeroSMulDivisors 𝕜 E]
    (K : E →L[𝕜] E) {μ : ℕ → 𝕜} {n : ℕ} (hμ : ∀ i < n, μ n ≠ μ i)
    (hval : Module.End.HasEigenvalue (K : Module.End 𝕜 E) (μ n)) :
    LinearMap.ker (aeval K (∏ i ∈ Finset.range n, (X - C (μ i))) : E →ₗ[𝕜] E) <
      LinearMap.ker (aeval K (∏ i ∈ Finset.range (n + 1), (X - C (μ i))) : E →ₗ[𝕜] E) := by
  obtain ⟨v, hv⟩ := hval.exists_hasEigenvector
  have hPv (m : ℕ) :
      aeval K (∏ i ∈ Finset.range m, (X - C (μ i))) v =
        (∏ i ∈ Finset.range m, (μ n - μ i)) • v := by
    rw [← coe_coe, toLinearMap_aeval, Module.End.aeval_apply_of_hasEigenvector hv, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  refine IsConcreteLE.lt_iff_le_and_exists.2
    ⟨K.ker_aeval_prod_range_le_succ μ n, v, ?_, ?_⟩
  · rw [LinearMap.mem_ker, coe_coe, hPv,
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _), zero_smul]
  · rw [LinearMap.mem_ker, coe_coe, hPv]
    exact smul_ne_zero
      (Finset.prod_ne_zero_iff.2 fun i hi ↦ sub_ne_zero.2 (hμ i (Finset.mem_range.1 hi)))
      (Module.End.hasEigenvector_iff.1 hv).2

end ContinuousLinearMap
