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

The right singular basis and its tail estimate are supplied by
`LinearMap.rightSingularBasis` and `LinearMap.norm_apply_le_singularValues_mul_norm`;
`ContinuousLinearMap.singularValue_eq_linearMap_singularValues` supplies Eckart–Young.

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

/-- The span of the first `n` right singular vectors attains the orthogonal-tail min–max
formula: the norm on its orthogonal complement is the `n`-th approximation number. -/
@[simp]
theorem nnnorm_comp_orthogonal_rightSingularBasis_spanIndices (T : E →L[𝕜] F) (n : ℕ) :
    let V := (T : E →ₗ[𝕜] F).rightSingularBasis.spanIndices
      ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
    ‖T ∘L Vᗮ.subtypeL‖₊ = T.singularValue n := by
  let A : E →ₗ[𝕜] F := T
  let v := A.rightSingularBasis
  let V := v.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
  have hV : Module.rank 𝕜 V ≤ n := by
    rw [← finrank_eq_rank, v.finrank_spanIndices, Fin.card_filter_val_lt]
    exact_mod_cast min_le_right (finrank 𝕜 E) n
  refine le_antisymm ?_ (T.singularValue_le_nnnorm_comp_orthogonal hV)
  refine opNNNorm_le_bound _ _ fun x ↦ ?_
  have hx : (x : E) ∈ v.spanIndices {i | n ≤ (i : ℕ)} := by
    refine v.spanIndices_mono (fun i hi ↦ ?_) ((v.orthogonal_spanIndices _).le x.2)
    simpa using hi
  have h := A.norm_apply_le_singularValues_mul_norm hx
  rw [← T.singularValue_eq_linearMap_singularValues n] at h
  exact_mod_cast h

omit [FiniteDimensional 𝕜 F] in
/-- For a finite-dimensional source, every approximation number is attained by a bounded map of rank
at most its index. In particular, the infimum defining it is a minimum. -/
theorem exists_rank_le_nnnorm_sub_eq_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    ∃ R : E →L[𝕜] F, R.rank ≤ n ∧ ‖T - R‖₊ = T.singularValue n := by
  let W := LinearMap.range (T : E →ₗ[𝕜] F)
  let T' : E →L[𝕜] W := T.codRestrict W fun x ↦ LinearMap.mem_range_self _ x
  have hproj : W.orthogonalProjectionOnto ∘L T = T' := by
    apply ContinuousLinearMap.ext
    intro x
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨T x, LinearMap.mem_range_self _ x⟩
  have hle : T'.singularValue n ≤ T.singularValue n := by
    rw [← hproj]
    exact (singularValue_comp_le_left _ _ _).trans
      (mul_le_of_le_one_left' (by exact_mod_cast W.orthogonalProjectionOnto_norm_le))
  let v := (T' : E →ₗ[𝕜] W).rightSingularBasis
  let V := v.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
  have hV : Module.rank 𝕜 V ≤ n := by
    rw [← finrank_eq_rank, v.finrank_spanIndices, Fin.card_filter_val_lt]
    exact_mod_cast min_le_right (finrank 𝕜 E) n
  have hR : (T ∘L V.starProjection).rank ≤ n := by
    have hP : (V.starProjection : E →ₗ[𝕜] E).rank ≤ n := by
      rwa [LinearMap.rank, Submodule.range_starProjection]
    have hle := (LinearMap.lift_rank_comp_le_right (V.starProjection : E →ₗ[𝕜] E)
      (T : E →ₗ[𝕜] F)).trans (Cardinal.lift_le.mpr hP)
    rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at hle
  refine ⟨T ∘L V.starProjection, hR, le_antisymm ?_
    (T.singularValue_le_nnnorm_sub hR)⟩
  refine le_trans ?_ hle
  rw [← T'.nnnorm_comp_orthogonal_rightSingularBasis_spanIndices n]
  refine opNNNorm_le_bound _ _ fun x ↦ ?_
  have hx := V.sub_starProjection_mem_orthogonal x
  calc
    ‖(T - T ∘L V.starProjection) x‖₊ =
        ‖(T' ∘L Vᗮ.subtypeL) ⟨x - V.starProjection x, hx⟩‖₊ := by
          apply NNReal.coe_injective
          simp only [coe_nnnorm]
          rw [← Submodule.norm_coe]
          simp [T']
    _ ≤ ‖T' ∘L Vᗮ.subtypeL‖₊ * ‖x - V.starProjection x‖₊ :=
      (T' ∘L Vᗮ.subtypeL).le_opNNNorm ⟨_, hx⟩
    _ ≤ ‖T' ∘L Vᗮ.subtypeL‖₊ * ‖x‖₊ := by
      gcongr
      rw [← Submodule.starProjection_orthogonal_val]
      exact_mod_cast Vᗮ.norm_starProjection_apply_le x

end ContinuousLinearMap

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {m : ℕ}

/-- For a diagonal map whose diagonal magnitudes are nonincreasing, the span of the first
`n` basis vectors is a minimizing subspace in the orthogonal-tail min–max formula. This
includes the zero tail at and beyond the dimension. -/
@[simp]
theorem nnnorm_toLin_diagonal_comp_orthogonal_spanIndices
    (e : OrthonormalBasis (Fin m) 𝕜 E) (d : Fin m → 𝕜)
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    let := Module.Finite.of_basis e.toBasis
    let D := LinearMap.toContinuousLinearMap
      (Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d))
    let V := e.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m))
    ‖D ∘L Vᗮ.subtypeL‖₊ = D.singularValue n := by
  let := Module.Finite.of_basis e.toBasis
  set A := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
  set D := LinearMap.toContinuousLinearMap A
  set V := e.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin m))
  have hV : Module.rank 𝕜 V ≤ n := by
    rw [← finrank_eq_rank, e.finrank_spanIndices, Fin.card_filter_val_lt]
    exact_mod_cast min_le_right m n
  refine le_antisymm ?_ (D.singularValue_le_nnnorm_comp_orthogonal hV)
  by_cases hn : n < m
  · have hvalue : (D.singularValue n : ℝ) = ‖d ⟨n, hn⟩‖ := by
      rw [D.singularValue_eq_linearMap_singularValues]
      exact Matrix.singularValues_toLin_diagonal e d (Equiv.refl _) hd ⟨n, hn⟩
    have hAdj : LinearMap.adjoint A =
        Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal (star d)) := by
      rw [← Matrix.toLin_conjTranspose, Matrix.diagonal_conjTranspose]
    have hGram (i : Fin m) : (LinearMap.adjoint A ∘ₗ A) (e i) =
        ((‖d i‖ ^ 2 : ℝ) : 𝕜) • e i := by
      simp [A, hAdj, smul_smul, RCLike.mul_conj]
    refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x ↦ ?_
    have hx : (x : E) ∈ e.spanIndices {i | n ≤ (i : ℕ)} := by
      refine e.spanIndices_mono (fun i hi ↦ ?_) ((e.orthogonal_spanIndices _).le x.2)
      simpa using hi
    have h := A.isSymmetric_adjoint_comp_self.re_inner_le_of_eigenbasis e hGram
      (c := ‖d ⟨n, hn⟩‖ ^ 2)
      (fun i hi ↦ pow_le_pow_left₀ (norm_nonneg _) (hd hi) 2) hx
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq,
      ← mul_pow] at h
    have hnorm := (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp h
    rw [← hvalue] at hnorm
    exact_mod_cast hnorm
  · have htop : V = ⊤ := by
      apply top_unique
      dsimp only [V]
      rw [← e.toBasis.span_eq, e.spanIndices_eq_span]
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i, by simpa using (i.2.trans_le (le_of_not_gt hn)), rfl⟩
    rw [htop, Submodule.top_orthogonal_eq_bot]
    have hzero : D ∘L (⊥ : Submodule 𝕜 E).subtypeL = 0 := by
      ext x
      have hx : (x : E) = 0 := (Submodule.mem_bot 𝕜).mp x.2
      simp [hx]
    rw [hzero, nnnorm_zero]
    exact bot_le

end OrthonormalBasis
