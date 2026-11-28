/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormalOperator
public import TauCeti.Analysis.InnerProductSpace.SchurHorn

import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Basic

/-!
# The Hoffman–Wielandt inequality for normal operators

Let `T` and `S` be operators on a finite-dimensional inner product space with orthonormal
eigenbases `(uᵢ)` and `(vⱼ)` and eigenvalues `αᵢ` and `βⱼ`. In every orthonormal basis `(bₖ)`
the squared Frobenius distance of `T` and `S` is the weighted sum of the squared eigenvalue gaps
against the Schur weights `‖⟪uᵢ, vⱼ⟫‖²` of the two eigenbases:

`∑ₖ ‖(T - S) bₖ‖² = ∑ᵢ ∑ⱼ ‖⟪uᵢ, vⱼ⟫‖² |αᵢ - βⱼ|²`.

The Schur weight matrix is doubly stochastic, and a linear function on the Birkhoff polytope takes
its smallest and its largest value at permutation matrices. So some matching `σ` of the
eigenvalues has `∑ᵢ |αᵢ - β_{σ i}|²` at most, and some matching has it at least, the squared
Frobenius distance. This is the **Hoffman–Wielandt inequality**.

By the spectral theorem every normal operator on a finite-dimensional complex inner product space
has an orthonormal eigenbasis, which may be chosen to realize any listing of the roots of its
characteristic polynomial. This gives the inequality for normal operators with eigenvalues listed
in any order. For symmetric operators with sorted eigenvalues the optimal matching is the sorted
one (`LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le_sum_sq_norm_apply`). The second half fails
for operators that are not normal: the nilpotent `[[0, 1], [0, 0]]` and `0` have only the
eigenvalue `0`, while their squared Frobenius distance is `1`.

## Main results

* `TauCeti.sum_norm_sub_apply_sq_eq_sum_schurWeight_mul`: the squared Frobenius distance of two
  operators as the Schur-weighted sum of their squared eigenvalue gaps.
* `TauCeti.exists_perm_sum_sq_le_and_le_of_apply_eq_smul`: the Hoffman–Wielandt inequality, both
  halves, for operators with given orthonormal eigenbases over `ℝ` or `ℂ`.
* `TauCeti.exists_perm_sum_sq_le_and_le`: **the Hoffman–Wielandt inequality for normal
  operators**, with the eigenvalues listed in any order as the roots of the characteristic
  polynomial.

## Attribution

The first half in supplied orthonormal eigenbases, and the computation of the Frobenius distance
through the doubly stochastic matrix of squared overlaps, are adapted from `CKMA.hoffman_wielandt`
and its helper lemmas in `CKMA/Analysis/InnerProductSpace/MatrixInequalities.lean` of the
lean-CKMA project, with AI assistance; the second half, the use of Tau Ceti's Schur weights and
the passage to normal operators are new here.

## References

* A. J. Hoffman, H. W. Wielandt, *The variation of the spectrum of a normal matrix*, Duke Math. J.
  **20** (1953), 37–39.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Theorem VI.4.1,
  p. 165.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section RCLike

variable {𝕜 E ι ι' κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [Fintype ι'] [Fintype κ]

/-- **The Frobenius distance of two operators in their eigenbases.** If `T (u i) = α i • u i` and
`S (v j) = β j • v j` for orthonormal bases `u` and `v`, then in every orthonormal basis `b` the
squared Frobenius distance `∑ₖ ‖(T - S) (b k)‖²` is `∑ᵢ ∑ⱼ ‖⟪u i, v j⟫‖² ‖α i - β j‖²`, the
weighted sum of the squared eigenvalue gaps against the Schur weights of `u` and `v`. -/
theorem sum_norm_sub_apply_sq_eq_sum_schurWeight_mul {T S : E →ₗ[𝕜] E}
    {u : OrthonormalBasis ι 𝕜 E} {v : OrthonormalBasis ι' 𝕜 E} {α : ι → 𝕜} {β : ι' → 𝕜}
    (hT : ∀ i, T (u i) = α i • u i) (hS : ∀ j, S (v j) = β j • v j)
    (b : OrthonormalBasis κ 𝕜 E) :
    ∑ k, ‖(T - S) (b k)‖ ^ 2 = ∑ i, ∑ j, u.schurWeight v i j * ‖α i - β j‖ ^ 2 := by
  rw [(T - S).sum_norm_apply_sq_eq_sum_norm_apply_sq b u]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← v.sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- In the eigenbasis `v`, the `j`-th coordinate of `S (u i)` is `β j` times that of `u i`.
  have hSu : ⟪v j, S (u i)⟫_𝕜 = β j * ⟪v j, u i⟫_𝕜 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using v.repr_apply_of_eigenbasis S hS (u i) j
  rw [LinearMap.sub_apply, inner_sub_right, hSu, hT,
    inner_smul_right, ← sub_mul, norm_mul, mul_pow,
    OrthonormalBasis.schurWeight_apply, norm_inner_symm, mul_comm]

/-- **The Hoffman–Wielandt inequality in given eigenbases.** If `T (u i) = α i • u i` and
`S (v i) = β i • v i` for orthonormal bases `u` and `v` with a common index type, then for every
orthonormal basis `b` some matching `σ` of the eigenvalues has `∑ᵢ ‖α i - β (σ i)‖²` at most the
squared Frobenius distance `∑ₖ ‖(T - S) (b k)‖²`, and some matching has it at least that
distance. -/
theorem exists_perm_sum_sq_le_and_le_of_apply_eq_smul {T S : E →ₗ[𝕜] E}
    {u v : OrthonormalBasis ι 𝕜 E} {α β : ι → 𝕜} (hT : ∀ i, T (u i) = α i • u i)
    (hS : ∀ i, S (v i) = β i • v i) (b : OrthonormalBasis κ 𝕜 E) :
    (∃ σ : Equiv.Perm ι, ∑ i, ‖α i - β (σ i)‖ ^ 2 ≤ ∑ k, ‖(T - S) (b k)‖ ^ 2) ∧
      ∃ σ : Equiv.Perm ι, ∑ k, ‖(T - S) (b k)‖ ^ 2 ≤ ∑ i, ‖α i - β (σ i)‖ ^ 2 := by
  classical
  have hM := u.schurWeight_mem_doublyStochastic v
  rw [sum_norm_sub_apply_sq_eq_sum_schurWeight_mul hT hS b]
  exact ⟨Matrix.exists_perm_sum_le_sum_mul_of_mem_doublyStochastic hM fun i j ↦ ‖α i - β j‖ ^ 2,
    Matrix.exists_perm_sum_mul_le_sum_of_mem_doublyStochastic hM fun i j ↦ ‖α i - β j‖ ^ 2⟩

end RCLike

section Normal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The Hoffman–Wielandt inequality for normal operators.** Let `T` and `S` be normal operators
on a finite-dimensional complex inner product space, with the roots of their characteristic
polynomials listed, with multiplicity and in any order, as `α` and `β`. For every orthonormal
basis `b`, some matching `σ` of the eigenvalues has `∑ᵢ ‖α i - β (σ i)‖²` at most the squared
Frobenius distance `∑ₖ ‖(T - S) (b k)‖²`, and some matching has it at least that distance. -/
theorem exists_perm_sum_sq_le_and_le {T S : E →ₗ[ℂ] E} [IsStarNormal T] [IsStarNormal S]
    {n : ℕ} {α β : Fin n → ℂ} (hα : Multiset.map α Finset.univ.val = T.charpoly.roots)
    (hβ : Multiset.map β Finset.univ.val = S.charpoly.roots) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) :
    (∃ σ : Equiv.Perm (Fin n), ∑ i, ‖α i - β (σ i)‖ ^ 2 ≤ ∑ k, ‖(T - S) (b k)‖ ^ 2) ∧
      ∃ σ : Equiv.Perm (Fin n), ∑ k, ‖(T - S) (b k)‖ ^ 2 ≤ ∑ i, ‖α i - β (σ i)‖ ^ 2 := by
  obtain ⟨u, hu⟩ := T.exists_orthonormalBasis_apply_eq_smul_of_map_eq_roots hα
  obtain ⟨v, hv⟩ := S.exists_orthonormalBasis_apply_eq_smul_of_map_eq_roots hβ
  exact exists_perm_sum_sq_le_and_le_of_apply_eq_smul hu hv b

end Normal

end TauCeti
