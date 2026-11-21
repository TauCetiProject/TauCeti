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

For a matrix `A` over a `K`-module `L`, `A.basisCoord b` expands each equation in the
coordinates of a `K`-basis `b` of `L`. Its unknowns remain in `K`: it has one row for each
pair of an original equation and a basis coordinate. When `L` is a `K`-algebra, its kernel is
exactly the set of `K`-valued solutions of the original equations.

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

variable {K L : Type*} {m n ι ι' : Type*}

section Module

variable [Semiring K] [AddCommMonoid L] [Module K L]

/-- Expand the coefficients of every row in the coordinates of a basis of `L` over `K`. This
matrix describes the original equations with unknowns restricted to `K`. -/
def basisCoord (A : Matrix m n L) (b : Basis ι K L) : Matrix (m × ι) n K :=
  fun p j ↦ b.repr (A p.1 j) p.2

/-- An entry of the coordinate matrix is a basis coordinate of an entry of the original
matrix. -/
@[simp, grind =]
theorem basisCoord_apply (A : Matrix m n L) (b : Basis ι K L) (p : m × ι) (j : n) :
    A.basisCoord b p j = b.repr (A p.1 j) p.2 :=
  (rfl)

@[simp, grind =]
theorem basisCoord_zero (b : Basis ι K L) : (0 : Matrix m n L).basisCoord b = 0 := by
  ext
  simp

@[simp, grind =]
theorem basisCoord_add (A B : Matrix m n L) (b : Basis ι K L) :
    (A + B).basisCoord b = A.basisCoord b + B.basisCoord b := by
  ext
  simp

@[simp, grind =]
theorem basisCoord_smul (c : K) (A : Matrix m n L) (b : Basis ι K L) :
    (c • A).basisCoord b = c • A.basisCoord b := by
  ext
  simp

/-- A matrix is determined by its coordinates in a basis. -/
theorem basisCoord_injective (b : Basis ι K L) :
    Function.Injective fun A : Matrix m n L ↦ A.basisCoord b := by
  intro A B h
  ext i j
  apply b.repr.injective
  ext k
  exact congr_fun (congr_fun h (i, k)) j

@[simp]
theorem basisCoord_inj {A B : Matrix m n L} (b : Basis ι K L) :
    A.basisCoord b = B.basisCoord b ↔ A = B :=
  (basisCoord_injective b).eq_iff

@[simp]
theorem basisCoord_eq_zero_iff {A : Matrix m n L} (b : Basis ι K L) :
    A.basisCoord b = 0 ↔ A = 0 := by
  rw [← basisCoord_zero b, basisCoord_inj]

end Module

section CommSemiring

variable [CommSemiring K] [AddCommMonoid L] [Module K L]

/-- With a finite second basis, each coordinate row for the first basis is a `K`-linear
combination of the coordinate rows for the second basis. -/
theorem span_row_basisCoord_le [Finite ι'] (A : Matrix m n L) (b : Basis ι K L)
    (b' : Basis ι' K L) :
    Submodule.span K (Set.range (A.basisCoord b).row) ≤
      Submodule.span K (Set.range (A.basisCoord b').row) := by
  let := Fintype.ofFinite ι'
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, k⟩, rfl⟩
  have hrow : (A.basisCoord b).row (i, k) =
      ∑ l, b.repr (b' l) k • (A.basisCoord b').row (i, l) := by
    ext j
    have h := congrArg (fun x ↦ b.repr x k) (b'.sum_repr (A i j))
    simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finset.sum_apply, Finsupp.smul_apply,
      Pi.smul_apply, smul_eq_mul, row_apply, basisCoord_apply, mul_comm] using h.symm
  rw [hrow]
  exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)

/-- For finite bases, the `K`-span of the coordinate rows does not depend on the basis. -/
theorem span_row_basisCoord_eq [Finite ι] [Finite ι'] (A : Matrix m n L) (b : Basis ι K L)
    (b' : Basis ι' K L) :
    Submodule.span K (Set.range (A.basisCoord b).row) =
      Submodule.span K (Set.range (A.basisCoord b').row) :=
  le_antisymm (span_row_basisCoord_le A b b') (span_row_basisCoord_le A b' b)

/-- The image of a row under a `K`-linear map is a linear combination of its mapped
coordinate rows for a finite basis `b`, with coefficients the images of the basis vectors. -/
theorem row_map_eq_sum_basisCoord [Fintype ι] {E F : Type*} [Semiring E] [Algebra K E]
    [FunLike F L E] [LinearMapClass F K L E] (A : Matrix m n L) (b : Basis ι K L) (σ : F)
    (i : m) :
    (A.map σ).row i = ∑ k, σ (b k) • ((A.basisCoord b).map (algebraMap K E)).row (i, k) := by
  ext j
  have h := congrArg σ (b.sum_repr (A i j))
  simpa only [row_apply, map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisCoord_apply, map_sum, map_smul, Algebra.smul_def, ← Algebra.commutes] using h.symm

end CommSemiring

section Ring

variable [Ring K] [AddCommGroup L] [Module K L]

@[simp, grind =]
theorem basisCoord_neg (A : Matrix m n L) (b : Basis ι K L) :
    (-A).basisCoord b = -A.basisCoord b := by
  ext
  simp

@[simp, grind =]
theorem basisCoord_sub (A B : Matrix m n L) (b : Basis ι K L) :
    (A - B).basisCoord b = A.basisCoord b - B.basisCoord b := by
  ext
  simp

end Ring

section Algebra

variable [CommSemiring K] [Semiring L] [Algebra K L] [Fintype n]

/-- Each equation of the coordinate system is a basis coordinate of the original equation. -/
@[simp, grind =]
theorem basisCoord_mulVec_apply (A : Matrix m n L) (b : Basis ι K L) (x : n → K)
    (p : m × ι) :
    (A.basisCoord b *ᵥ x) p = b.repr ((A *ᵥ (algebraMap K L ∘ x)) p.1) p.2 := by
  simp only [mulVec, dotProduct, basisCoord_apply, Function.comp_apply]
  simp only [← Algebra.smul_def, ← Algebra.commutes, map_sum, map_smul]
  simp [mul_comm]

/-- Expanding in basis coordinates preserves exactly the solutions with coordinates
in `K`. -/
@[simp, grind =]
theorem basisCoord_mulVec_eq_zero_iff (A : Matrix m n L) (b : Basis ι K L) (x : n → K) :
    A.basisCoord b *ᵥ x = 0 ↔ A *ᵥ (algebraMap K L ∘ x) = 0 := by
  constructor
  · intro h
    ext i
    apply b.repr.injective
    ext k
    simpa only [Pi.zero_apply, map_zero, Finsupp.zero_apply, basisCoord_mulVec_apply] using
      congr_fun h (i, k)
  · intro h
    ext p
    simp only [basisCoord_mulVec_apply, congr_fun h p.1, Pi.zero_apply, map_zero,
      Finsupp.zero_apply]

end Algebra

section Fields

variable [Field K] [Field L] [Algebra K L] [Finite ι]
variable {E : Type*} [Field E] [Algebra K E]

variable [Algebra.IsSeparable K L]

/-- Let `L/K` be a finite separable extension with finite basis `b`, and let `E` be a field
splitting the minimal polynomials of `L/K`. Then the `E`-span of all conjugate rows of `A`,
the images of its rows under the `K`-algebra embeddings `L →ₐ[K] E`, equals the `E`-span of
the coordinate rows `A.basisCoord b` mapped to `E`. -/
theorem span_row_map_algHom_eq_span_row_map_basisCoord (A : Matrix m n L) (b : Basis ι K L)
    (hsplit : ∀ x : L, ((minpoly K x).map (algebraMap K E)).Splits) :
    Submodule.span E (Set.range (fun p : m × (L →ₐ[K] E) ↦ (A.map p.2).row p.1)) =
      Submodule.span E (Set.range ((A.basisCoord b).map (algebraMap K E)).row) := by
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
    rw [row_map_eq_sum_basisCoord A b σ i]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(i, k), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, k⟩, rfl⟩
    let f := Fintype.linearCombination E
      (fun l ↦ ((A.basisCoord b).map (algebraMap K E)).row (i, l))
    have hmap : (Submodule.span E
        (Set.range (fun σ : L →ₐ[K] E ↦ fun l ↦ σ (b l)))).map f ≤
        Submodule.span E (Set.range (fun p : m × (L →ₐ[K] E) ↦ (A.map p.2).row p.1)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      simp only [f, Function.comp_apply, Fintype.linearCombination_apply]
      rw [← row_map_eq_sum_basisCoord A b σ i]
      exact Submodule.subset_span ⟨(i, σ), rfl⟩
    have hmem := hmap (Submodule.mem_map.mpr
      ⟨Pi.single k 1, hspan.symm ▸ Submodule.mem_top, rfl⟩)
    simpa only [f, Fintype.linearCombination_apply_single, one_smul, SetLike.mem_coe] using hmem

end Fields

end Matrix
