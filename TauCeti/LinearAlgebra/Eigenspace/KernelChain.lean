/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic

import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Polynomial kernel chains for linear endomorphisms

For a linear endomorphism `f : Module.End 𝕜 E` and a sequence of scalars `μ : ℕ → 𝕜`, the
evaluated polynomials `P n = Polynomial.aeval f (∏ i ∈ Finset.range n, (X - C (μ i)))` have
kernels forming an increasing chain of submodules stepped down by `f - μ n • 1`. Over an integral
domain acting on a torsion-free module, whenever `μ n` is an eigenvalue of `f` distinct from
`μ 0, …, μ (n - 1)`, the inclusion `ker (P n) < ker (P (n + 1))` is strict.

## Main results

* `Module.End.ker_aeval_prod_range_le_succ`: the polynomial kernels increase with `n`.
* `Module.End.mem_ker_aeval_prod_range_succ_iff`: `x` lies in the `(n + 1)`-st kernel
  iff `f x - μ n • x` lies in the `n`-th kernel.
* `Module.End.ker_aeval_prod_range_lt_succ`: an eigenvalue `μ n` distinct from all earlier
  `μ i` (`i < n`) makes the inclusion from step `n` to step `n + 1` strict.
-/

public section

open Polynomial

namespace Module.End

variable {𝕜 E : Type*} [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The kernels of `aeval f (∏ i < n, (X - C (μ i)))` form an increasing chain of submodules. -/
theorem ker_aeval_prod_range_le_succ (f : Module.End 𝕜 E) (μ : ℕ → 𝕜) (n : ℕ) :
    LinearMap.ker (aeval f (∏ i ∈ Finset.range n, (X - C (μ i)))) ≤
      LinearMap.ker (aeval f (∏ i ∈ Finset.range (n + 1), (X - C (μ i)))) := by
  simpa only [Finset.prod_range_succ_comm, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, mul_eq_comp] using
    LinearMap.ker_le_ker_comp
      (aeval f (∏ i ∈ Finset.range n, (X - C (μ i)))) (f - μ n • 1)

/-- A vector `x` lies in the kernel of `aeval f (∏ i < n + 1, (X - C (μ i)))` iff
`f x - μ n • x` lies in the kernel of `aeval f (∏ i < n, (X - C (μ i)))`. -/
@[simp high]
theorem mem_ker_aeval_prod_range_succ_iff (f : Module.End 𝕜 E) (μ : ℕ → 𝕜) (n : ℕ) {x : E} :
    x ∈ LinearMap.ker (aeval f (∏ i ∈ Finset.range (n + 1), (X - C (μ i)))) ↔
      f x - μ n • x ∈
        LinearMap.ker (aeval f (∏ i ∈ Finset.range n, (X - C (μ i)))) := by
  simp only [LinearMap.mem_ker, Finset.prod_range_succ, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, _root_.mul_apply_eq_comp, LinearMap.sub_apply,
    LinearMap.smul_apply, one_apply_eq_self]

/-- Over an integral domain acting on a torsion-free module, if `μ n` is an eigenvalue of a linear
endomorphism `f` distinct from `μ i` for every `i < n`, then the kernel of
`aeval f (∏ i < n, (X - C (μ i)))` is strictly contained in that of
`aeval f (∏ i < n + 1, (X - C (μ i)))`. -/
theorem ker_aeval_prod_range_lt_succ [IsDomain 𝕜] [Module.IsTorsionFree 𝕜 E]
    (f : Module.End 𝕜 E) {μ : ℕ → 𝕜} {n : ℕ} (hμ : ∀ i < n, μ n ≠ μ i)
    (hval : f.HasEigenvalue (μ n)) :
    LinearMap.ker (aeval f (∏ i ∈ Finset.range n, (X - C (μ i)))) <
      LinearMap.ker (aeval f (∏ i ∈ Finset.range (n + 1), (X - C (μ i)))) := by
  obtain ⟨v, hv⟩ := hval.exists_hasEigenvector
  have hPv (m : ℕ) :
      aeval f (∏ i ∈ Finset.range m, (X - C (μ i))) v =
        (∏ i ∈ Finset.range m, (μ n - μ i)) • v := by
    rw [aeval_apply_of_hasEigenvector hv, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  refine IsConcreteLE.lt_iff_le_and_exists.2
    ⟨f.ker_aeval_prod_range_le_succ μ n, v, ?_, ?_⟩
  · rw [LinearMap.mem_ker, hPv,
      Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _), zero_smul]
  · rw [LinearMap.mem_ker, hPv]
    exact smul_ne_zero
      (Finset.prod_ne_zero_iff.2 fun i hi ↦ sub_ne_zero.2 (hμ i (Finset.mem_range.1 hi)))
      (hasEigenvector_iff.1 hv).2

end Module.End
