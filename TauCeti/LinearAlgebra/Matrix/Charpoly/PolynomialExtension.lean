/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Amitsur
public import TauCeti.RingTheory.MatrixPolynomialAlgebra

/-!
# Amitsur's theorem for polynomial extensions

`AlgHom.charpoly_polynomialExtension_coeff_mem_range` shows that characteristic coefficients
in the image of the scalar ring remain so after extending a matrix-valued algebra homomorphism
to polynomials. This allows Amitsur's theorem to be used over a polynomial base ring, as needed
for polynomial matrix relations in Ribet's argument.
-/

public section

open Polynomial Matrix

namespace AlgHom

variable {R L Λ σ : Type*} [CommRing R] [CommRing L] [Algebra R L] [Fintype σ] [DecidableEq σ]
  [Semiring Λ] [Algebra R Λ]

attribute [local instance] Polynomial.algebra

/-- If every `ρ w` has characteristic polynomial over `R`, then every value of the polynomial
extension of `ρ` has characteristic polynomial over `R[X]`. -/
theorem charpoly_polynomialExtension_coeff_mem_range (ρ : Λ →ₐ[R] Matrix σ σ L)
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range) (p : Λ[X])
    (k : ℕ) : (polynomialExtension ρ p).charpoly.coeff k ∈ (algebraMap R[X] L[X]).range := by
  have hS : Submodule.span R[X] (Set.range (C : Λ → Λ[X])) = ⊤ := by
    refine eq_top_iff.2 fun q _ ↦ ?_
    rw [q.as_sum_range_C_mul_X_pow]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have h : C (q.coeff i) * X ^ i = (X ^ i : R[X]) • C (q.coeff i) := by
      rw [Algebra.smul_def, Polynomial.algebraMap_def, coe_mapRingHom, Polynomial.map_pow,
        map_X, (commute_X_pow _ i).eq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine charpoly_coeff_mem_range_of_span _ hS ?_ p k
  rintro _ ⟨w, rfl⟩ k
  obtain ⟨r, hr⟩ := hρ w k
  have hC : polynomialExtension ρ (C w) = (ρ w).map C := by
    ext s t i
    simp [coeff_polynomialExtension_apply, coeff_C, apply_ite (ρ · s t)]
  exact ⟨C r, by rw [hC, charpoly_map, coeff_map, ← hr]; simp⟩

end AlgHom
