/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Restricting the unknowns of a matrix equation

For a matrix `A` over an algebra `L` of `K`, `A.restrictScalars b` expands each equation
in a `K`-basis `b` of `L`. Its unknowns remain in `K`: it has one row for each pair of an
original equation and a basis coordinate. Its kernel is exactly the set of `K`-valued
solutions of the original equations.

For a finite separable field extension, the span of these coordinate rows after extending
scalars to a field splitting all the minimal polynomials equals the span of all conjugates
of the original rows. Thus the latter span descends to `K`. This comparison allows height
estimates on conjugate rows to bound a system whose unknowns lie in the smaller field.

The comparison uses Dedekind independence of field embeddings and the native basis
construction of linear maps. The splitting field need not be algebraically closed.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), proof of Theorem 2.9.19.
-/

public section

noncomputable section

namespace Matrix

open Module Finset

variable {K L : Type*} {m n ι : Type*}

section Semiring

variable [CommSemiring K] [Semiring L] [Algebra K L]

/-- Expand the coefficients of every row in a basis of `L` over `K`. This matrix describes
the original equations with unknowns restricted to `K`. -/
def restrictScalars (A : Matrix m n L) (b : Basis ι K L) : Matrix (m × ι) n K :=
  fun p j ↦ b.repr (A p.1 j) p.2

/-- An entry of the matrix obtained by restricting the unknowns to `K`. -/
@[simp]
theorem restrictScalars_apply (A : Matrix m n L) (b : Basis ι K L) (i : m) (k : ι) (j : n) :
    A.restrictScalars b (i, k) j = b.repr (A i j) k :=
  (rfl)

variable [Fintype n]

/-- Each equation of the restricted system is a basis coordinate of the original equation. -/
@[simp]
theorem restrictScalars_mulVec (A : Matrix m n L) (b : Basis ι K L) (x : n → K)
    (i : m) (k : ι) :
    (A.restrictScalars b *ᵥ x) (i, k) = b.repr ((A *ᵥ (algebraMap K L ∘ x)) i) k := by
  simp only [mulVec, dotProduct, restrictScalars_apply, Function.comp_apply]
  simp only [← Algebra.smul_def, ← Algebra.commutes, map_sum, map_smul]
  simp [mul_comm]

/-- Restricting the unknowns to `K` preserves exactly the solutions with coordinates in `K`. -/
@[simp]
theorem restrictScalars_mulVec_eq_zero_iff (A : Matrix m n L) (b : Basis ι K L) (x : n → K) :
    A.restrictScalars b *ᵥ x = 0 ↔ A *ᵥ (algebraMap K L ∘ x) = 0 := by
  constructor
  · intro h
    ext i
    apply b.repr.injective
    ext k
    simpa only [Pi.zero_apply, map_zero, Finsupp.zero_apply, ← restrictScalars_mulVec] using
      congr_fun h (i, k)
  · intro h
    ext ⟨i, k⟩
    simp only [restrictScalars_mulVec, congr_fun h i, Pi.zero_apply, map_zero, Finsupp.zero_apply]

end Semiring

section SemiringMap

variable [CommSemiring K] [Semiring L] [Algebra K L]

/-- The image of a row under an algebra homomorphism is a linear combination of its mapped
coordinate rows. -/
theorem map_row_eq_sum_restrictScalars [Fintype ι]
    {E : Type*} [Semiring E] [Algebra K E] (A : Matrix m n L) (b : Basis ι K L)
    (σ : L →ₐ[K] E) (i : m) :
    (A.map σ).row i =
      ∑ k, σ (b k) • ((A.restrictScalars b).map (algebraMap K E)).row (i, k) := by
  ext j
  have h := congrArg σ (b.sum_repr (A i j))
  simpa only [row_apply, map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    restrictScalars_apply, map_sum, map_smul, Algebra.smul_def, map_mul,
    AlgHom.commutes, ← Algebra.commutes] using h.symm

end SemiringMap

section Fields

variable [Field K] [Field L] [Algebra K L] [Finite ι]
variable {E : Type*} [Field E] [Algebra K E]

variable [Algebra.IsSeparable K L]

/-- In a field splitting the minimal polynomials of `L/K`, the span of all conjugate rows
is the extension of the span of the coordinate equations over `K`. -/
theorem span_conjugate_rows_eq_span_restrictScalars (A : Matrix m n L) (b : Basis ι K L)
    (hsplit : ∀ x : L, ((minpoly K x).map (algebraMap K E)).Splits) :
    Submodule.span E (Set.range (fun p : m × (L →ₐ[K] E) ↦ (A.map p.2).row p.1)) =
      Submodule.span E (Set.range ((A.restrictScalars b).map (algebraMap K E)).row) := by
  let := Fintype.ofFinite ι
  let := b.finiteDimensional_of_finite
  classical
  -- Embeddings, evaluated on a basis, span the full coordinate space.
  have heval : ((b.constr E).symm.toLinearMap ∘ AlgHom.toLinearMap) =
      (fun σ : L →ₐ[K] E ↦ fun k ↦ σ (b k)) := by
    ext σ k
    simp only [Function.comp_apply, LinearEquiv.coe_coe, Basis.constr_symm_apply,
      AlgHom.toLinearMap_apply]
  have hli : LinearIndependent E (fun σ : L →ₐ[K] E ↦ fun k ↦ σ (b k)) := by
    rw [← heval]
    exact (linearIndependent_algHom_toLinearMap K L E).map'
      (b.constr E).symm.toLinearMap (LinearMap.ker_eq_bot.mpr (b.constr E).symm.injective)
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by
    rw [AlgHom.card_of_splits K L E hsplit, Module.finrank_fintype_fun_eq_card,
      Module.finrank_eq_card_basis b])
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, σ⟩, rfl⟩
    dsimp only
    rw [map_row_eq_sum_restrictScalars A b σ i]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(i, k), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    let f := Fintype.linearCombination E
      (fun l ↦ ((A.restrictScalars b).map (algebraMap K E)).row (i, l))
    have hmap : (Submodule.span E
        (Set.range (fun σ : L →ₐ[K] E ↦ fun l ↦ σ (b l)))).map f ≤
        Submodule.span E (Set.range (fun p : m × (L →ₐ[K] E) ↦ (A.map p.2).row p.1)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      simp only [f, Function.comp_apply, Fintype.linearCombination_apply]
      rw [← map_row_eq_sum_restrictScalars A b σ i]
      exact Submodule.subset_span ⟨(i, σ), rfl⟩
    have hmem := hmap (Submodule.mem_map.mpr
      ⟨Pi.single k 1, hspan.symm ▸ Submodule.mem_top, rfl⟩)
    simpa only [f, Fintype.linearCombination_apply_single, one_smul, SetLike.mem_coe] using hmem

end Fields

end Matrix
