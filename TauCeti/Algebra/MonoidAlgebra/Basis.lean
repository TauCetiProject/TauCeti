/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The coordinates of the standard basis of a monoid algebra

Mathlib defines the standard basis `MonoidAlgebra.basis X k` of `k[X]` by
`repr := MonoidAlgebra.coeffLinearEquiv _` but records no lemma for the resulting `repr`. This
file is that missing bridge: the coordinates in the standard basis are the coefficients.

It is all that is needed for the generic basis API -- `Module.Basis.coe_sumCoords`,
`Module.Basis.sumCoords_self_apply`, `LinearMap.toMatrix_apply` -- to compute in terms of
`MonoidAlgebra.coeff`.

## Main statements

* `TauCeti.MonoidAlgebra.basis_repr`: the coordinates of `k[X]` in the standard basis are the
  coefficients.
* `TauCeti.MonoidAlgebra.sumCoords_basis_surjective`: the coefficient sum is surjective when the
  index type is nonempty.
* `TauCeti.MonoidAlgebra.ker_sumCoords_basis_eq_span`: its kernel is spanned by differences of
  basis vectors from a fixed one.
-/

public section

namespace TauCeti

/-- The coordinates of `k[X]` in the standard basis are the coefficients. -/
@[simp]
theorem MonoidAlgebra.basis_repr {k : Type*} [Semiring k] {X : Type*} (v : MonoidAlgebra k X) :
    (MonoidAlgebra.basis X k).repr v = v.coeff :=
  rfl

/-! ### The sum of the coefficients -/

section Augmentation

variable {k : Type*} [Semiring k] {X : Type*}

/-- The sum of the coefficients is surjective when the index type is nonempty. -/
theorem MonoidAlgebra.sumCoords_basis_surjective [Nonempty X] :
    Function.Surjective (MonoidAlgebra.basis X k).sumCoords := fun a =>
  ⟨MonoidAlgebra.single (Classical.arbitrary X) a, by simp⟩

end Augmentation

section Span

variable (k : Type*) [Ring k] (X : Type*)

/-- The kernel of the coefficient sum is spanned by the differences of the standard basis vectors
from a fixed one. -/
theorem MonoidAlgebra.ker_sumCoords_basis_eq_span (x₀ : X) :
    LinearMap.ker (MonoidAlgebra.basis X k).sumCoords =
      Submodule.span k (Set.range fun x : X =>
        (MonoidAlgebra.single x 1 - MonoidAlgebra.single x₀ 1 : MonoidAlgebra k X)) := by
  classical
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · simp only [LinearMap.mem_ker, Module.Basis.coe_sumCoords, MonoidAlgebra.basis_repr,
      Finsupp.sum, id_eq] at hv
    have hbasis : ∑ x ∈ v.coeff.support, MonoidAlgebra.single x (v.coeff x) = v :=
      MonoidAlgebra.sum_coeff_single v
    have key : ∑ x ∈ v.coeff.support, v.coeff x •
        (MonoidAlgebra.single x 1 - MonoidAlgebra.single x₀ 1 : MonoidAlgebra k X) = v := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hv, zero_smul, sub_zero]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans hbasis
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [← key]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
    simp

end Span

end TauCeti
