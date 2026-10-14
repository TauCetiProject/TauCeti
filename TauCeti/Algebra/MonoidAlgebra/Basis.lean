/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The coordinates of the standard basis of a monoid algebra

Mathlib defines the standard basis `MonoidAlgebra.basis X k` of `k[X]` by
`repr := MonoidAlgebra.coeffLinearEquiv _` but records no lemma for the resulting `repr`. This
file is that missing bridge: the coordinates in the standard basis are the coefficients.

It is all that is needed for the generic basis API -- `Module.Basis.coe_sumCoords`,
`Module.Basis.sumCoords_self_apply`, `LinearMap.toMatrix_apply` -- to compute in terms of
`MonoidAlgebra.coeff`.

## Main statements

* `MonoidAlgebra.basis_repr`: the coordinates of `k[X]` in the standard basis are the
  coefficients.
* `Module.Dual.coeff_basis_toDualEquiv_symm_apply`: the coefficients under the
  standard-basis dual equivalence are evaluations on basis vectors.
* `MonoidAlgebra.sumCoords_basis_surjective`: the coefficient sum is surjective when the
  index type is nonempty.
* `MonoidAlgebra.exists_coeff_ne_of_ne_zero_of_sumCoords_eq_zero`: a nonzero vector whose
  coefficients sum to zero has two distinct coefficients if the cardinality is nonzero in the
  scalars and the scalars have no zero divisors.
* `MonoidAlgebra.ker_sumCoords_basis_eq_span`: its kernel is spanned by differences of
  basis vectors from a fixed one.
-/

public section

/-- The coordinates of `k[X]` in the standard basis are the coefficients. -/
@[simp]
theorem MonoidAlgebra.basis_repr {k : Type*} [Semiring k] {X : Type*} (v : MonoidAlgebra k X) :
    (MonoidAlgebra.basis X k).repr v = v.coeff :=
  rfl

open scoped Classical in
/-- The coefficients of the vector corresponding to a functional under the standard-basis
identification `k[X] ≃ Hom_k(k[X], k)` are the values of the functional on the basis. -/
@[simp]
theorem Module.Dual.coeff_basis_toDualEquiv_symm_apply {k : Type*} [CommSemiring k]
    {X : Type*} [Finite X] (f : Module.Dual k (MonoidAlgebra k X)) (x : X) :
    ((MonoidAlgebra.basis X k).toDualEquiv.symm f).coeff x =
      f (MonoidAlgebra.single x 1) :=
  -- The standard basis has `repr = coeffLinearEquiv`, so its coordinates are the coefficients.
  (by simpa using (MonoidAlgebra.basis X k).coord_toDualEquiv_symm_apply x f :
    (MonoidAlgebra.basis X k).repr _ x = _)

/-! ### The sum of the coefficients -/

section Augmentation

variable {k : Type*} [Semiring k] {X : Type*}

/-- The sum of the coefficients is surjective when the index type is nonempty. -/
theorem MonoidAlgebra.sumCoords_basis_surjective [Nonempty X] :
    Function.Surjective (MonoidAlgebra.basis X k).sumCoords := fun a =>
  ⟨MonoidAlgebra.single (Classical.arbitrary X) a, by simp⟩

end Augmentation

/-- A nonzero vector in the kernel of `sumCoords` has two different coefficients, provided
`(Fintype.card α : k) ≠ 0`.

Nonemptiness of `α` is not assumed — it follows from `(Fintype.card α : k) ≠ 0`. -/
theorem _root_.MonoidAlgebra.exists_coeff_ne_of_ne_zero_of_sumCoords_eq_zero
    {k : Type*} [Semiring k] [NoZeroDivisors k] {α : Type*} [Fintype α]
    (v : MonoidAlgebra k α) (hchar : (Fintype.card α : k) ≠ 0) (hv0 : v ≠ 0)
    (hvker : (MonoidAlgebra.basis α k).sumCoords v = 0) :
    ∃ x y : α, x ≠ y ∧ v.coeff x ≠ v.coeff y := by
  classical
  by_contra! hcon
  apply hv0
  apply MonoidAlgebra.coeff_eq_zero.mp
  ext x
  -- Constant coefficients have sum `Fintype.card α` times their common value.
  have hall : ∀ z : α, v.coeff z = v.coeff x := fun z =>
    (eq_or_ne z x).elim (fun h => by rw [h]) fun h => hcon z x h
  have hsum : (MonoidAlgebra.basis α k).sumCoords v = ∑ z : α, v.coeff z := by simp
  have hmul : (Fintype.card α : k) * v.coeff x = 0 := by
    rw [← hvker, hsum, Finset.sum_congr rfl fun z _ => hall z]
    simp
  exact (mul_eq_zero.mp hmul).resolve_left hchar

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
