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

namespace Interlacing

/-- Extension by zero from `EuclideanSpace 𝕜 m` to `EuclideanSpace 𝕜 n` along `f`. -/
noncomputable def extend (f : m ↪ n) : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n :=
  (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).symm.toLinearMap ∘ₗ
    Function.ExtendByZero.linearMap 𝕜 𝕜 f ∘ₗ (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap

/-- Extension by zero agrees with the original vector on the range of `f`. -/
theorem extend_apply_apply (f : m ↪ n) (x : EuclideanSpace 𝕜 m) (a : m) :
    extend f x (f a) = x a := by
  simp [extend, f.injective.extend_apply]

/-- Extension by zero vanishes outside the range of `f`. -/
theorem extend_apply_of_notMem (f : m ↪ n) (x : EuclideanSpace 𝕜 m) {b : n}
    (hb : b ∉ Set.range f) : extend f x b = 0 := by
  simp [extend, Function.extend_apply' _ _ _ (by simpa using hb)]

/-- Sums against an extended-by-zero vector reduce to sums over the range of `f`. -/
theorem sum_extend [Fintype m] [Fintype n] (f : m ↪ n) (x : EuclideanSpace 𝕜 m) (h : n → 𝕜) :
    ∑ b, h b * extend f x b = ∑ a, h (f a) * x a := by
  have hsub : ∑ b ∈ Finset.univ.map f, h b * extend f x b = ∑ b, h b * extend f x b :=
    Finset.sum_subset (Finset.subset_univ _) fun b _ hb => by
      rw [extend_apply_of_notMem f x (by simpa using hb), mul_zero]
  rw [← hsub, Finset.sum_map]
  simp [extend_apply_apply]

/-- The Rayleigh form of `A` on a vector extended by zero is the Rayleigh form of the principal
submatrix on the original vector. -/
theorem inner_toEuclideanLin_extend [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix n n 𝕜) (f : m ↪ n) (x : EuclideanSpace 𝕜 m) :
    ⟪Matrix.toEuclideanLin A (extend f x), extend f x⟫_𝕜 =
      ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 := by
  have hmul : ∀ b, (A.mulVec (extend f x).ofLp) b = ∑ c, A b (f c) * x c := fun b => by
    simpa [Matrix.mulVec, dotProduct] using sum_extend f x (A b)
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, RCLike.inner_apply]
  conv_lhs => enter [2, b]; rw [mul_comm]
  rw [sum_extend f x (fun b => (starRingEnd 𝕜) (A.mulVec (extend f x).ofLp b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, hmul (f a)]
  simp [Matrix.mulVec, dotProduct]

/-- Extension by zero along an embedding is injective. -/
theorem extend_injective (f : m ↪ n) :
    Function.Injective (extend (𝕜 := 𝕜) f) := fun x y h =>
  PiLp.ext fun a => by rw [← extend_apply_apply f x a, h, extend_apply_apply]

/-- Extension by zero is an isometry. -/
theorem norm_extend [Fintype m] [Fintype n] (f : m ↪ n)
    (x : EuclideanSpace 𝕜 m) : ‖extend f x‖ = ‖x‖ := by
  classical
  have h := inner_toEuclideanLin_extend (1 : Matrix n n 𝕜) f x
  rw [Matrix.submatrix_one f f.injective] at h
  have h' : (((‖extend f x‖ ^ 2 : ℝ)) : 𝕜) = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by simpa using h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast h')

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
    (V.map (Interlacing.extend f))
    (by rw [← (Submodule.equivMapOfInjective _ (Interlacing.extend_injective f) V).finrank_eq,
      hVdim]; simp)
  obtain ⟨x, hxV, rfl⟩ := Submodule.mem_map.mp hyV
  calc _ ≤ RCLike.re ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 :=
        hVlow x hxV (by rwa [Interlacing.norm_extend] at hy1)
    _ = RCLike.re
          ⟪Matrix.toEuclideanLin A (Interlacing.extend f x), Interlacing.extend f x⟫_𝕜 := by
        rw [Interlacing.inner_toEuclideanLin_extend]
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
  have hU : (i : ℕ) + 1 ≤ finrank 𝕜 (V.comap (Interlacing.extend f)) := by
    have := Submodule.finrank_add_finrank_le_finrank_comap_add_finrank
      (Interlacing.extend (𝕜 := 𝕜) f) V
    have hle := Fintype.card_le_of_embedding f
    simp only [finrank_euclideanSpace, hVdim] at this
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hU
  have hv' := hv.map' (V.comap (Interlacing.extend f)).subtype
    (Submodule.ker_subtype _)
  obtain ⟨x, hxW, hx1, hxle⟩ := hBs.exists_unit_vector_re_inner_le_eigenvalue
    finrank_euclideanSpace i
    (Submodule.span 𝕜 (Set.range ((V.comap (Interlacing.extend f)).subtype ∘ v)))
    (by rw [finrank_span_eq_card hv']; simp)
  have hxV : Interlacing.extend f x ∈ V := by
    refine (Submodule.span_le.mpr ?_ : Submodule.span 𝕜 _ ≤ V.comap (Interlacing.extend f)) hxW
    rintro _ ⟨j, rfl⟩
    exact (v j).2
  calc _ ≤ RCLike.re
          ⟪Matrix.toEuclideanLin A (Interlacing.extend f x), Interlacing.extend f x⟫_𝕜 :=
        hVlow _ hxV (by rwa [Interlacing.norm_extend])
    _ = RCLike.re ⟪Matrix.toEuclideanLin (A.submatrix f f) x, x⟫_𝕜 := by
        rw [Interlacing.inner_toEuclideanLin_extend]
    _ ≤ _ := hxle

end TauCeti
