/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite-dimensional eigenspaces of compact operators

This file develops Riesz--Schauder input used for compact perturbations of Fredholm operators. A
compact operator on a Hausdorff topological vector space over a complete nontrivially normed field
has a finite-dimensional eigenspace at every nonzero scalar. More generally, every finite stage of
the corresponding generalized eigenspace is finite dimensional.

The eigenspace proof restricts the compact operator to its eigenspace, where it is a nonzero
scalar multiple of the identity. Compactness of that identity forces finite dimensionality. The
generalized statement then uses the filtration by kernels of `(T - μ)^n`: the difference operator
maps stage `n + 1` into stage `n`, and its kernel embeds into the ordinary eigenspace.

Mathlib proves the eigenspace result as
`ContinuousLinearMap.finite_dimensional_eigenspace` in the setting of complete inner-product
spaces over `RCLike` fields. The argument used there needs neither a norm nor completeness of the
ambient space; the declarations below record it for Hausdorff topological vector spaces over
arbitrary complete nontrivially normed fields, which covers the Banach spaces of Fredholm theory.

## Main declarations

* `IsCompactOperator.finiteDimensional_eigenspace`: the eigenspace of a compact operator at a
  nonzero scalar is finite dimensional.
* `IsCompactOperator.finiteDimensional_genEigenspace_nat`: every finite-order generalized
  eigenspace at a nonzero scalar is finite dimensional.

The mathematical argument is the finite-dimensional eigenspace step in the Riesz--Schauder
theory; see, for example, Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

open Module End

namespace IsCompactOperator

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {T : E →L[𝕜] E} {μ : 𝕜}

/-- The eigenspace of a compact operator on a Hausdorff topological vector space at a nonzero
scalar is finite dimensional.

Unlike Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`, this needs no inner product
or norm on the space and works over any complete nontrivially normed field. -/
theorem finiteDimensional_eigenspace (hT : IsCompactOperator T)
    (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  have hT' := hT.restrict
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (eigenspace_mem_invtSubmodule T.toLinearMap μ))
    (ContinuousLinearMap.isClosed_eigenspace T μ)
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT'
  exact FiniteDimensional.of_isCompactOperator_id hT'

/-- Every finite stage of the generalized eigenspace of a compact operator at a nonzero scalar is
finite dimensional. In particular, compact operators have no infinite-dimensional finite-order
Jordan block at a nonzero eigenvalue. -/
theorem finiteDimensional_genEigenspace_nat (hT : IsCompactOperator T)
    (hμ : μ ≠ 0) (n : ℕ) :
    FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ n) := by
  have := hT.finiteDimensional_eigenspace hμ
  induction n with
  | zero =>
    rw [Nat.cast_zero, genEigenspace_zero]
    infer_instance
  | succ n ih =>
    rw [← Submodule.fg_iff_finiteDimensional]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (T.toLinearMap - μ • 1) ?_ ?_
    · refine (Submodule.fg_iff_finiteDimensional _).mpr (Submodule.finiteDimensional_of_le
        (S₂ := genEigenspace T.toLinearMap μ n) ?_)
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_genEigenspace_nat, LinearMap.mem_ker, pow_succ,
        mul_apply_eq_comp] at hx
      exact mem_genEigenspace_nat.mpr hx
    · exact (Submodule.fg_iff_finiteDimensional _).mpr (Submodule.finiteDimensional_of_le
        (S₂ := eigenspace T.toLinearMap μ) (inf_le_right.trans_eq eigenspace_def.symm))

end IsCompactOperator

end
