/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Decomposition
public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.LinearAlgebra.End.RangePow

/-!
# Nilpotent and invertible parts of a compact operator

At every nonzero scalar `μ`, a compact operator `K` on a real or complex Banach space
splits into a finite-dimensional generalized eigenspace and a closed complementary range.
On the first summand `K - μ • 1` is nilpotent, and on the second it has a bounded inverse.
The restrictions use the inherited subspace norms. In particular, invertibility here is in
the algebra of continuous linear maps, not merely algebraic bijectivity.

The stable subspaces and bounded coordinate projections are constructed in
`Compact.Decomposition`. This file supplies the restrictions needed to use that splitting
as an operator decomposition, including when `μ` is in the resolvent or the space is zero.

## References

* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsRCLikeNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {K : X →L[𝕜] X}

/-- **The nilpotent/invertible Riesz decomposition.** For a compact operator and a nonzero
scalar, the stable kernel and range of the shifted operator are topological complements.
The kernel is finite dimensional and the shifted restriction to it is nilpotent; the
restriction to the range is invertible as a bounded operator. The stable exponent also
annihilates the kernel restriction. Neither a nonzero-space nor an eigenvalue hypothesis
is required. -/
theorem exists_stable_ker_range_restrictions_sub_smul (hK : IsCompactOperator K)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ p : ℕ,
      let A := K - μ • (1 : X →L[𝕜] X)
      let f : X →ₗ[𝕜] X := A
      let M := LinearMap.ker (f ^ p)
      let N := LinearMap.range (f ^ p)
      (∀ n, p ≤ n → LinearMap.ker (f ^ n) = M ∧ LinearMap.range (f ^ n) = N) ∧
      FiniteDimensional 𝕜 M ∧ M.IsTopCompl N ∧
      ∃ (hM : ∀ x ∈ M, A x ∈ M) (hN : ∀ x ∈ N, A x ∈ N),
        (A.restrict hM : M →L[𝕜] M) ^ p = 0 ∧
        IsUnit (A.restrict hN : N →L[𝕜] N) := by
  obtain ⟨p, hp, hc⟩ := hK.exists_stable_ker_range_pow_sub_smul hμ
  let A := K - μ • (1 : X →L[𝕜] X)
  let f : X →ₗ[𝕜] X := A
  let M := LinearMap.ker (f ^ p)
  let N := LinearMap.range (f ^ p)
  have hcomm (x : X) : (f ^ p) (A x) = A ((f ^ p) x) :=
    LinearMap.congr_fun (Commute.self_pow f p).eq.symm x
  have hM : ∀ x ∈ M, A x ∈ M := by
    intro x hx
    exact LinearMap.mem_ker.mpr (by rw [hcomm, LinearMap.mem_ker.mp hx, map_zero])
  have hN : ∀ x ∈ N, A x ∈ N := by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, hcomm y⟩
  have hfin : FiniteDimensional 𝕜 M := by
    have heq : M = Module.End.genEigenspace (K : X →ₗ[𝕜] X) μ p := by
      rw [Module.End.genEigenspace_nat]
      rfl
    rw [heq]
    exact hK.finiteDimensional_genEigenspace_nat hμ p
  refine ⟨p, hp, hfin, hc, hM, hN, ?_, ?_⟩
  · have hs : Function.Semiconj (fun x : M ↦ (x : X)) (A.restrict hM) f :=
      fun x ↦ ContinuousLinearMap.coe_restrict_apply hM x
    ext x
    have hi := hs.iterate_right p x
    rw [← pow_apply_eq_iterate, ← pow_apply_eq_iterate] at hi
    exact hi.trans (LinearMap.mem_ker.mp x.property)
  · have : CompleteSpace N := hc.isClosed'.completeSpace_coe
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    exact LinearMap.bijective_restrict_range_pow_of_stable f p
      (hp (p + 1) (Nat.le_succ p)).1 (hp (p + 1) (Nat.le_succ p)).2 hN

end IsCompactOperator
