/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Attainment of finite-dimensional approximation numbers

For a bounded map `T` between finite-dimensional inner product spaces, the span of its first
`n` right singular vectors minimizes the orthogonal-tail min–max formula. Restricting `T` to
the orthogonal complement has norm exactly `T.singularValue n`. Composing `T` with the
projection onto that span therefore gives a best rank-at-most-`n` approximation, including
when `n` is at or beyond the source dimension. Best approximations also exist when only the
source is finite-dimensional: corestricting to the range supplies a finite-dimensional target.
For a supplied diagonal basis ordered by decreasing diagonal magnitudes, its first `n`
vectors give a minimizing span in the original diagonal coordinates.

The right singular basis is supplied by `LinearMap.rightSingularBasis`, with its Gram
relation `LinearMap.adjoint_comp_self_rightSingularBasis`. The tail estimate is
`ContinuousLinearMap.norm_comp_orthogonal_spanIndices_le_of_adjoint_comp_self_eigenbasis`;
`ContinuousLinearMap.singularValue_eq_linearMap_singularValues` supplies Eckart–Young.
Both the right-singular and diagonal minimizer formulas follow from
`ContinuousLinearMap.nnnorm_comp_orthogonal_spanIndices_of_adjoint_comp_self_eigenbasis`.
The explicit projection error is
`ContinuousLinearMap.nnnorm_sub_comp_rightSingularBasis_starProjection`; its rank bound follows
from `ContinuousLinearMap.rank_comp_starProjection_le` and
`OrthonormalBasis.rank_spanIndices_val_lt_le`.

## References

* C. Eckart and G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open Module
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Any sorted orthonormal eigenbasis of `T† T` gives a minimizing span of its first `n`
vectors in the orthogonal-tail min–max formula, including indices beyond the dimension. -/
theorem nnnorm_comp_orthogonal_spanIndices_of_adjoint_comp_self_eigenbasis
    (T : E →L[𝕜] F) {m : ℕ} (e : OrthonormalBasis (Fin m) 𝕜 E) {μ : Fin m → ℝ}
    (hμ : Antitone μ)
    (he : ∀ i, (LinearMap.adjoint (T : E →ₗ[𝕜] F) ∘ₗ (T : E →ₗ[𝕜] F)) (e i) =
      (μ i : 𝕜) • e i) (n : ℕ) :
    ‖T ∘L (e.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m)))ᗮ.subtypeL‖₊ =
      T.singularValue n := by
  refine le_antisymm ?_
    (T.singularValue_le_nnnorm_comp_orthogonal (e.rank_spanIndices_val_lt_le n))
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, T.singularValue_eq_linearMap_singularValues]
  exact T.norm_comp_orthogonal_spanIndices_le_of_adjoint_comp_self_eigenbasis e hμ he n

/-- The span of the first `n` right singular vectors attains the orthogonal-tail min–max
formula: the norm on its orthogonal complement is the `n`-th approximation number. -/
@[simp]
theorem nnnorm_comp_orthogonal_rightSingularBasis_spanIndices (T : E →L[𝕜] F) (n : ℕ) :
    let V := (T : E →ₗ[𝕜] F).rightSingularBasis.spanIndices
      ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
    ‖T ∘L Vᗮ.subtypeL‖₊ = T.singularValue n := by
  exact T.nnnorm_comp_orthogonal_spanIndices_of_adjoint_comp_self_eigenbasis
    (T : E →ₗ[𝕜] F).rightSingularBasis
    ((T : E →ₗ[𝕜] F).sq_singularValues_antitone.comp_monotone
      (Fin.valOrderEmb _).monotone)
    (T : E →ₗ[𝕜] F).adjoint_comp_self_rightSingularBasis n

/-- Composing with the projection onto the first `n` right singular vectors gives an
approximation whose error is exactly the `n`-th approximation number, including the zero tail
at and beyond the source dimension. Its rank is at most `n` by `rank_comp_starProjection_le`
and `OrthonormalBasis.rank_spanIndices_val_lt_le`. -/
@[simp]
theorem nnnorm_sub_comp_rightSingularBasis_starProjection (T : E →L[𝕜] F) (n : ℕ) :
    let V := (T : E →ₗ[𝕜] F).rightSingularBasis.spanIndices
      {i | (i : ℕ) < n}
    ‖T - T ∘L V.starProjection‖₊ = T.singularValue n := by
  let v := (T : E →ₗ[𝕜] F).rightSingularBasis
  let V := v.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
  suffices ‖T - T ∘L V.starProjection‖₊ = T.singularValue n by
    simpa only [V, v, Finset.coe_filter, Finset.mem_univ, true_and] using this
  have hR := T.rank_comp_starProjection_le (v.rank_spanIndices_val_lt_le n)
  refine le_antisymm ?_ (T.singularValue_le_nnnorm_sub hR)
  exact (T.nnnorm_sub_comp_starProjection_le V).trans_eq
    (T.nnnorm_comp_orthogonal_rightSingularBasis_spanIndices n)

omit [FiniteDimensional 𝕜 F] in
/-- For a finite-dimensional source, every approximation number is attained by a bounded map of rank
at most its index. In particular, the infimum defining it is a minimum. -/
theorem exists_rank_le_nnnorm_sub_eq_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖T - R‖₊ = T.singularValue n := by
  let W := LinearMap.range (T : E →ₗ[𝕜] F)
  let T' : E →L[𝕜] W := T.codRestrict W fun x ↦ LinearMap.mem_range_self _ x
  have hT : W.subtypeL ∘L T' = T :=
    T.subtypeL_comp_codRestrict W _
  have hproj : W.orthogonalProjectionOnto ∘L T = T' := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [ContinuousLinearMap.comp_apply, T', coe_codRestrict_apply] using
      W.orthogonalProjectionOnto_mem_subspace_eq_self (T' x)
  have hle : T'.singularValue n ≤ T.singularValue n := by
    rw [← hproj]
    exact (singularValue_comp_le_left _ _ _).trans
      (mul_le_of_le_one_left' (by exact_mod_cast W.orthogonalProjectionOnto_norm_le))
  let v := (T' : E →ₗ[𝕜] W).rightSingularBasis
  let V := v.spanIndices {i | (i : ℕ) < n}
  have hR : (T ∘L V.starProjection).rank ≤ n := by
    simpa only [Finset.coe_filter, Finset.mem_univ, true_and] using
      T.rank_comp_starProjection_le (v.rank_spanIndices_val_lt_le n)
  refine ⟨T ∘L V.starProjection, hR, le_antisymm ?_
    (T.singularValue_le_nnnorm_sub hR)⟩
  have hnorm : ‖T - T ∘L V.starProjection‖₊ = ‖T' - T' ∘L V.starProjection‖₊ := by
    apply NNReal.coe_injective
    simp only [coe_nnnorm]
    rw [← hT, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_sub,
      ← Submodule.subtypeₗᵢ_toContinuousLinearMap]
    exact W.subtypeₗᵢ.norm_toContinuousLinearMap_comp
  rw [hnorm, T'.nnnorm_sub_comp_rightSingularBasis_starProjection n]
  exact hle

end ContinuousLinearMap

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- For a diagonal map, an ordering `π` by nonincreasing diagonal magnitudes gives a minimizing
span of the first `n` reordered basis vectors in the orthogonal-tail min–max formula.
This includes the zero tail at and beyond the dimension. -/
@[simp]
theorem nnnorm_toLin_diagonal_comp_orthogonal_spanIndices
    (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜) (π : Fin m ≃ ι)
    (hπ : Antitone fun i ↦ ‖d (π i)‖) (n : ℕ) :
    let := Module.Finite.of_basis e.toBasis
    let D := LinearMap.toContinuousLinearMap
      (Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d))
    let V := (e.reindex π.symm).spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m))
    ‖D ∘L Vᗮ.subtypeL‖₊ = D.singularValue n := by
  let := Module.Finite.of_basis e.toBasis
  exact ContinuousLinearMap.nnnorm_comp_orthogonal_spanIndices_of_adjoint_comp_self_eigenbasis
    _ (e.reindex π.symm)
    (fun i j hij ↦ pow_le_pow_left₀ (norm_nonneg _) (hπ hij) 2)
    (e.adjoint_comp_self_toLin_diagonal_reindex_apply d π) n

end OrthonormalBasis
