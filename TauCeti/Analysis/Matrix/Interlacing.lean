/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import TauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Cauchy interlacing for principal submatrices

Let `A` be a Hermitian matrix indexed by a finite type `n`, and let `B = A.submatrix f f` be the
principal submatrix selected by an embedding `f : m ↪ n`. With the decreasing enumeration
`Matrix.IsHermitian.eigenvalues₀` of the eigenvalues, repeated by multiplicity, Cauchy's
interlacing theorem states
`λ_{i + (|n| - |m|)}(A) ≤ λᵢ(B) ≤ λᵢ(A)`
for every `i < |m|`.

The proof extends vectors by zero along `f`. This identifies the Rayleigh form of `B` with that
of `A` restricted to the range of the extension. The two inequalities then follow from the two
directions of the Courant–Fischer theorem in
`TauCeti.Analysis.InnerProductSpace.CourantFischer`: the upper bound by transporting a
subspace of the smaller space into the larger one, and the lower bound by pulling a subspace of
the larger space back, with a dimension count.

## Main results

* `Matrix.IsHermitian.eigenvalues₀_submatrix_le`: `λᵢ(B) ≤ λᵢ(A)`.
* `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_submatrix`:
  `λ_{i + (|n| - |m|)}(A) ≤ λᵢ(B)`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 4.3.28 (Cauchy interlacing theorem).
* R. Bhatia, *Matrix Analysis*, Springer (1997), Corollary III.1.5.
-/

public section

namespace TauCeti

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- Extension by zero along an embedding, as a linear isometry. -/
local notation "𝓔" => LinearIsometry.piLpExtendByZero 2 𝕜 𝕜

namespace Interlacing


/-- The Rayleigh form of `A` on a vector extended by zero is the Rayleigh form of the principal
submatrix on the original vector. -/
theorem inner_toEuclideanLin_piLpExtendByZero [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix n n 𝕜) (f : m ↪ n) (x : EuclideanSpace 𝕜 m) :
    ⟪Matrix.toEuclideanLin A (𝓔 f x),
        𝓔 f x⟫_𝕜 =
      ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 := by
  have key : ∀ h : n → 𝕜,
      ∑ b, h b * 𝓔 f x b = ∑ a, h (f a) * x a := fun h => by
    rw [← Finset.sum_extend_zero_of_injective (t := Finset.univ) (fun a ↦ h (f a) * x a)
      f.injective fun _ => Finset.mem_univ _]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hb
      simp [f.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ (by simpa using hb),
        LinearIsometry.piLpExtendByZero_apply_eq_zero hb]
  have hmul : ∀ b, (A.mulVec (𝓔 f x).ofLp) b =
      ∑ c, A b (f c) * x c := fun b => by
    simpa [Matrix.mulVec, dotProduct] using key (A b)
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, RCLike.inner_apply]
  conv_lhs => enter [2, b]; rw [mul_comm]
  rw [key (fun b => (starRingEnd 𝕜)
    (A.mulVec (𝓔 f x).ofLp b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, hmul (f a)]
  simp [Matrix.mulVec, dotProduct]

end Interlacing

/-- **Cauchy interlacing, upper bound.** Each sorted eigenvalue of a principal submatrix of a
Hermitian matrix is at most the sorted eigenvalue of the same index of the full matrix. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_submatrix_le [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : m ↪ n)
    (i : Fin (Fintype.card m)) :
    (hA.submatrix f).eigenvalues₀ i ≤
      hA.eigenvalues₀ (Fin.castLE (Fintype.card_le_of_embedding f) i) := by
  have hAs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hBs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.submatrix f)
  simp only [Matrix.IsHermitian.eigenvalues₀]
  obtain ⟨V, hVdim, hVlow⟩ :=
    hBs.exists_submodule_forall_unit_eigenvalue_le_re_inner finrank_euclideanSpace i
  obtain ⟨y, hyV, hy1, hyle⟩ := hAs.exists_unit_vector_re_inner_le_eigenvalue
    finrank_euclideanSpace (Fin.castLE (Fintype.card_le_of_embedding f) i)
    (V.map (𝓔 f).toLinearMap)
    (by rw [← (Submodule.equivMapOfInjective _ ((𝓔 f).injective) V).finrank_eq,
      hVdim]; simp)
  obtain ⟨x, hxV, rfl⟩ := Submodule.mem_map.mp hyV
  calc _ ≤ RCLike.re ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 :=
        hVlow x hxV (by simpa using hy1)
    _ = RCLike.re
          ⟪Matrix.toEuclideanLin A (𝓔 f x), 𝓔 f x⟫_𝕜 := by
        rw [Interlacing.inner_toEuclideanLin_piLpExtendByZero]
    _ ≤ _ := hyle

/-- **Cauchy interlacing, lower bound.** The sorted eigenvalue of index `i + (|n| - |m|)` of a
Hermitian matrix is at most the `i`-th sorted eigenvalue of any principal submatrix of size
`|m|`. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_submatrix [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : m ↪ n)
    (i : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card m), by
        have := Fintype.card_le_of_embedding f
        have := i.2
        omega⟩ ≤ (hA.submatrix f).eigenvalues₀ i := by
  have hAs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hBs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.submatrix f)
  simp only [Matrix.IsHermitian.eigenvalues₀]
  obtain ⟨V, hVdim, hVlow⟩ := hAs.exists_submodule_forall_unit_eigenvalue_le_re_inner
    finrank_euclideanSpace ⟨i + (Fintype.card n - Fintype.card m), by
      have := Fintype.card_le_of_embedding f
      have := i.2
      omega⟩
  have hU : (i : ℕ) + 1 ≤ finrank 𝕜 (V.comap (𝓔 f).toLinearMap) := by
    have := Submodule.finrank_add_finrank_le_finrank_comap_add_finrank
      ((𝓔 f).toLinearMap) V
    have hle := Fintype.card_le_of_embedding f
    simp only [finrank_euclideanSpace, hVdim] at this
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hU
  have hv' := hv.map' (V.comap (𝓔 f).toLinearMap).subtype
    (Submodule.ker_subtype _)
  obtain ⟨x, hxW, hx1, hxle⟩ := hBs.exists_unit_vector_re_inner_le_eigenvalue
    finrank_euclideanSpace i
    (Submodule.span 𝕜 (Set.range ((V.comap (𝓔 f).toLinearMap).subtype ∘ v)))
    (by rw [finrank_span_eq_card hv']; simp)
  have hxV : 𝓔 f x ∈ V := by
    refine (Submodule.span_le.mpr ?_ : Submodule.span 𝕜 _ ≤ V.comap (𝓔 f).toLinearMap) hxW
    rintro _ ⟨j, rfl⟩
    exact (v j).2
  calc _ ≤ RCLike.re
          ⟪Matrix.toEuclideanLin A (𝓔 f x), 𝓔 f x⟫_𝕜 :=
        hVlow _ hxV (by simpa using hx1)
    _ = RCLike.re ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 := by
        rw [Interlacing.inner_toEuclideanLin_piLpExtendByZero]
    _ ≤ _ := hxle

end TauCeti
