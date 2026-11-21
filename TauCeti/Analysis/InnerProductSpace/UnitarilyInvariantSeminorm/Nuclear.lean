/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Nuclear-norm trace duality, orthogonal additivity, and low-rank decomposition

For linear maps `A, B : E →ₗ[𝕜] F` between finite-dimensional inner product spaces over `𝕜 = ℝ` or
`ℂ`, the Hilbert–Schmidt trace pairing `tr (A† B)` places the operator norm `‖·‖` and the nuclear
seminorm `‖·‖₁` in exact duality:

* **Trace duality**: `‖tr (A† B)‖ ≤ ‖A‖ ‖B‖₁` and `‖tr (A† B)‖ ≤ ‖A‖₁ ‖B‖`.
* **Variational characterizations**: the dual-norm bounds are attained, giving
  `‖B‖₁ = ⨆_{‖U‖ ≤ 1} ‖tr (U† B)‖` (attained by a contraction `U` whose range and adjoint
  range lie inside those of `B`) and `‖A‖ = ⨆_{‖B‖₁ ≤ 1} ‖tr (A† B)‖` (attained by some `B`
  with `‖B‖₁ ≤ 1`).
* **Orthogonal additivity**: when `A† B = 0` and `A B† = 0` (orthogonal column and row spaces),
  the polar partial isometries `U_A`, `U_B` inherit the same two-sided orthogonality, so
  `‖U_A + U_B‖ = max ‖U_A‖ ‖U_B‖ ≤ 1` by
  `TauCeti.UnitarilyInvariantSeminorm.opNorm_add_eq_max_of_orthogonal` and trace duality yields
  `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁`.
* **Low-rank tangent–normal decomposition**: for any subspaces `W ≤ F` and `K ≤ E`, decomposing
  `Δ = Δ₁ + Δ₂` with normal part `Δ₂ = P_W Δ P_K` and tangent part `Δ₁ = Δ - Δ₂` gives
  `rank Δ₁ ≤ dim Wᗮ + dim Kᗮ`, trace orthogonality `tr (Δ₁† Δ₂) = 0`, and therefore
  `‖Δ₁‖_F ≤ ‖Δ‖_F` and `‖Δ₁‖₁ ≤ √(dim Wᗮ + dim Kᗮ) ‖Δ‖_F`. Taking `W = (range Θ)ᗮ` and `K = ker Θ`
  makes `Θ` and `Δ₂` two-sided orthogonal, yielding Wainwright's nuclear-norm decomposability
  inequality `‖Θ‖₁ + ‖Δ₂‖₁ - ‖Δ₁‖₁ ≤ ‖Θ + Δ‖₁` together with `rank Δ₁ ≤ 2 rank Θ` and
  `‖Δ₁‖₁ ≤ √(2 rank Θ) ‖Δ‖_F`.

## Main declarations

* `LinearMap.trace_adjoint_comp_eq_sum_singularValues`:
  `tr (A† B) = ∑ᵢ σᵢ(B) ⟪A vᵢ, uᵢ⟫`.
* `TauCeti.UnitarilyInvariantSeminorm.norm_trace_adjoint_comp_le_opNorm_mul_nuclear`,
  `TauCeti.UnitarilyInvariantSeminorm.norm_trace_adjoint_comp_le_nuclear_mul_opNorm`:
  trace duality `‖tr (A† B)‖ ≤ ‖A‖ ‖B‖₁` and its symmetric form `‖tr (A† B)‖ ≤ ‖A‖₁ ‖B‖`.
* `TauCeti.UnitarilyInvariantSeminorm.exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_eq_iSup_norm_trace_adjoint_comp`:
  attainment and variational formula for the nuclear seminorm.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_rankOne`: `‖u ⊗ v‖₁ = ‖u‖ ‖v‖`.
* `TauCeti.UnitarilyInvariantSeminorm.exists_nuclear_le_one_trace_adjoint_comp_eq_opNorm`,
  `TauCeti.UnitarilyInvariantSeminorm.opNorm_eq_iSup_norm_trace_adjoint_comp`:
  attainment and variational formula for the operator norm.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_of_orthogonal`:
  `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁` whenever `A† B = 0` and `A B† = 0`.
* `LinearMap.trace_adjoint_sub_starProjection_comp_eq_zero`:
  trace orthogonality of the tangent–normal projection split
  `Δ = (Δ - P_W Δ P_K) + P_W Δ P_K`.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_sub_le_nuclear_add_of_orthogonal`,
  `TauCeti.UnitarilyInvariantSeminorm.frobenius_sub_starProjection_comp_le`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_sub_starProjection_comp_le`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_sub_orthogonal_range_ker_le`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_starProjection_comp_sub_le_nuclear_add`:
  explicit decomposability and tangent-part Frobenius and nuclear bounds.
* `TauCeti.UnitarilyInvariantSeminorm.exists_lowRank_decomposition`:
  Wainwright's low-rank decomposition for maps of rank at most `r`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.4.
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, Section 10.2.1.
-/

public section

open Module
open scoped ComplexConjugate InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Hilbert–Schmidt trace pairing `tr (A† B)` expanded in the singular system of `B`:
`tr (A† B) = ∑ᵢ σᵢ(B) ⟪A vᵢ, uᵢ⟫`. -/
theorem trace_adjoint_comp_eq_sum_singularValues (A B : E →ₗ[𝕜] F) :
    trace 𝕜 E (adjoint A ∘ₗ B) =
      ∑ i : Fin (finrank 𝕜 E), ((B.singularValues i : ℝ) : 𝕜) *
        ⟪A (B.rightSingularBasis i), B.leftSingularVector i⟫_𝕜 := by
  rw [trace_eq_sum_inner _ B.rightSingularBasis]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [comp_apply, adjoint_inner_right, B.apply_rightSingularBasis i, inner_smul_right]

/-- The tangent part `Δ - P_W Δ P_K` and the normal part `P_W Δ P_K` are orthogonal for the
Hilbert–Schmidt trace pairing: `tr ((Δ - P_W Δ P_K)† (P_W Δ P_K)) = 0`. -/
theorem trace_adjoint_sub_starProjection_comp_eq_zero (Δ : E →ₗ[𝕜] F) (W : Submodule 𝕜 F)
    (K : Submodule 𝕜 E) :
    trace 𝕜 E
      (adjoint (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) ∘ₗ
        (W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap)) = 0 := by
  set PW : F →ₗ[𝕜] F := W.starProjection.toLinearMap
  set PK : E →ₗ[𝕜] E := K.starProjection.toLinearMap
  have hPW_adj : adjoint PW = PW := W.starProjection_isSymmetric.adjoint_eq
  have hPK_adj : adjoint PK = PK := K.starProjection_isSymmetric.adjoint_eq
  have hPW_idem : PW ∘ₗ PW = PW :=
    LinearMap.ext fun y ↦ congrArg (fun f : F →L[𝕜] F ↦ f y) W.isIdempotentElem_starProjection
  have hPK_idem : PK ∘ₗ PK = PK :=
    LinearMap.ext fun x ↦ congrArg (fun f : E →L[𝕜] E ↦ f x) K.isIdempotentElem_starProjection
  have hΔ₂ : adjoint (PW ∘ₗ Δ ∘ₗ PK) ∘ₗ (PW ∘ₗ Δ ∘ₗ PK) = PK ∘ₗ adjoint Δ ∘ₗ PW ∘ₗ Δ ∘ₗ PK := by
    calc adjoint (PW ∘ₗ Δ ∘ₗ PK) ∘ₗ (PW ∘ₗ Δ ∘ₗ PK)
        = PK ∘ₗ adjoint Δ ∘ₗ (PW ∘ₗ PW) ∘ₗ Δ ∘ₗ PK := by
          simp only [adjoint_comp, hPW_adj, hPK_adj, comp_assoc]
      _ = PK ∘ₗ adjoint Δ ∘ₗ PW ∘ₗ Δ ∘ₗ PK := by rw [hPW_idem]
  have htr : trace 𝕜 E (adjoint Δ ∘ₗ (PW ∘ₗ Δ ∘ₗ PK)) =
      trace 𝕜 E (adjoint (PW ∘ₗ Δ ∘ₗ PK) ∘ₗ (PW ∘ₗ Δ ∘ₗ PK)) := by
    calc trace 𝕜 E (adjoint Δ ∘ₗ (PW ∘ₗ Δ ∘ₗ PK))
        = trace 𝕜 E ((adjoint Δ ∘ₗ PW ∘ₗ Δ) ∘ₗ PK) := by simp only [comp_assoc]
      _ = trace 𝕜 E (PK ∘ₗ (adjoint Δ ∘ₗ PW ∘ₗ Δ)) := trace_comp_comm' _ _
      _ = trace 𝕜 E ((PK ∘ₗ PK) ∘ₗ (adjoint Δ ∘ₗ PW ∘ₗ Δ)) := by rw [hPK_idem]
      _ = trace 𝕜 E (PK ∘ₗ (PK ∘ₗ adjoint Δ ∘ₗ PW ∘ₗ Δ)) := by simp only [comp_assoc]
      _ = trace 𝕜 E ((PK ∘ₗ adjoint Δ ∘ₗ PW ∘ₗ Δ) ∘ₗ PK) := trace_comp_comm' _ _
      _ = trace 𝕜 E (adjoint (PW ∘ₗ Δ ∘ₗ PK) ∘ₗ (PW ∘ₗ Δ ∘ₗ PK)) := by
          rw [hΔ₂]; simp only [comp_assoc]
  rw [map_sub, sub_comp, map_sub, htr, sub_self]

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### Trace duality between the operator norm and the nuclear seminorm -/

/-- **Trace duality**: `‖tr (A† B)‖ ≤ ‖A‖ ‖B‖₁`. -/
theorem norm_trace_adjoint_comp_le_opNorm_mul_nuclear (A B : E →ₗ[𝕜] F) :
    ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)‖ ≤ opNorm 𝕜 E F A * nuclear 𝕜 E F B := by
  rw [LinearMap.trace_adjoint_comp_eq_sum_singularValues A B, nuclear_apply,
    ← B.sum_fin_singularValues (fun s ↦ s) rfl, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  have hσ : 0 ≤ B.singularValues i := B.singularValues_nonneg _
  calc ‖((B.singularValues i : ℝ) : 𝕜) *
          ⟪A (B.rightSingularBasis i), B.leftSingularVector i⟫_𝕜‖
      = B.singularValues i * ‖⟪A (B.rightSingularBasis i), B.leftSingularVector i⟫_𝕜‖ := by
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg hσ]
    _ ≤ B.singularValues i * (‖A (B.rightSingularBasis i)‖ * ‖B.leftSingularVector i‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hσ
    _ ≤ B.singularValues i * (opNorm 𝕜 E F A * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (B.norm_leftSingularVector_le_one i)
          (norm_nonneg _) (apply_nonneg _ _)) hσ
        simpa [opNorm_apply, B.rightSingularBasis.norm_eq_one i] using
          (LinearMap.toContinuousLinearMap A).le_opNorm (B.rightSingularBasis i)
    _ = opNorm 𝕜 E F A * B.singularValues i := by ring

/-- **Trace duality (symmetric form)**: `‖tr (A† B)‖ ≤ ‖A‖₁ ‖B‖`. -/
theorem norm_trace_adjoint_comp_le_nuclear_mul_opNorm (A B : E →ₗ[𝕜] F) :
    ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)‖ ≤ nuclear 𝕜 E F A * opNorm 𝕜 E F B := by
  have hconj : LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B) =
      conj (LinearMap.trace 𝕜 E (LinearMap.adjoint B ∘ₗ A)) := by
    rw [← LinearMap.trace_adjoint, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rw [hconj, RCLike.norm_conj, mul_comm]
  exact norm_trace_adjoint_comp_le_opNorm_mul_nuclear B A

/-- **Attainment of trace duality for the nuclear seminorm**: every map `B` admits a contraction
`U` (`‖U‖ ≤ 1`) with `range U ≤ range B`, `range U† ≤ range B†`, and `tr (U† B) = ‖B‖₁`. -/
theorem exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear (B : E →ₗ[𝕜] F) :
    ∃ U : E →ₗ[𝕜] F,
      opNorm 𝕜 E F U ≤ 1 ∧
      LinearMap.range U ≤ LinearMap.range B ∧
      LinearMap.range (LinearMap.adjoint U) ≤ LinearMap.range (LinearMap.adjoint B) ∧
      LinearMap.trace 𝕜 E (LinearMap.adjoint U ∘ₗ B) = (nuclear 𝕜 E F B : 𝕜) := by
  -- Build the polar partial isometry `U = ∑ᵢ uᵢ ⊗ vᵢ` sending `vᵢ ↦ uᵢ`.
  let U : E →ₗ[𝕜] F := ∑ i : Fin (finrank 𝕜 E),
    (InnerProductSpace.rankOne 𝕜 (B.leftSingularVector i) (B.rightSingularBasis i)).toLinearMap
  have hU_apply (x : E) :
      U x = ∑ i : Fin (finrank 𝕜 E),
        ⟪B.rightSingularBasis i, x⟫_𝕜 • B.leftSingularVector i := by
    simp [U]
  have hU_basis (j : Fin (finrank 𝕜 E)) :
      U (B.rightSingularBasis j) = B.leftSingularVector j := by
    rw [hU_apply, Finset.sum_eq_single j]
    · simp [B.rightSingularBasis.orthonormal.1 j]
    · intro i _ hij
      simp [orthonormal_iff_ite.mp B.rightSingularBasis.orthonormal i j, hij]
    · simp
  -- Bound `‖U† y‖ ≤ ‖y‖` by Bessel's inequality for the left singular vectors, then pass to `U`.
  have hU_adj_norm (y : F) : ‖LinearMap.adjoint U y‖ ≤ 1 * ‖y‖ := by
    have hsq : ‖LinearMap.adjoint U y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← B.rightSingularBasis.sum_sq_norm_inner_right (LinearMap.adjoint U y)]
      simp_rw [LinearMap.adjoint_inner_right, hU_basis]
      exact B.sum_norm_inner_leftSingularVector_sq_le y
    simpa using le_of_sq_le_sq hsq (norm_nonneg y)
  have hU_norm : opNorm 𝕜 E F U ≤ 1 := by
    rw [opNorm_apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    simpa using LinearMap.norm_adjoint_apply_le zero_le_one hU_adj_norm x
  -- Both ranges sit inside those of `B` and `B†`.
  have hU_rng : LinearMap.range U ≤ LinearMap.range B := by
    rintro _ ⟨x, rfl⟩
    rw [hU_apply]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    rw [B.leftSingularVector_def]
    exact Submodule.smul_mem _ _ ⟨B.rightSingularBasis i, rfl⟩
  have hU_adj_rng :
      LinearMap.range (LinearMap.adjoint U) ≤ LinearMap.range (LinearMap.adjoint B) := by
    rintro _ ⟨y, rfl⟩
    rw [← B.rightSingularBasis.sum_repr' (LinearMap.adjoint U y)]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [LinearMap.adjoint_inner_right, hU_basis]
    by_cases hσ : B.singularValues i = 0
    · simp [(B.leftSingularVector_eq_zero_iff).mpr hσ]
    · refine Submodule.smul_mem _ _ ⟨((B.singularValues i : ℝ) : 𝕜)⁻¹ • B.leftSingularVector i, ?_⟩
      rw [map_smul, B.adjoint_leftSingularVector i, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hσ), one_smul]
  have hU_tr : LinearMap.trace 𝕜 E (LinearMap.adjoint U ∘ₗ B) = (nuclear 𝕜 E F B : 𝕜) := by
    rw [LinearMap.trace_adjoint_comp_eq_sum_singularValues U B, nuclear_apply,
      ← B.sum_fin_singularValues (fun s ↦ s) rfl, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hU_basis, B.inner_leftSingularVector]
    by_cases hσ : B.singularValues i = 0 <;> simp [hσ]
  exact ⟨U, hU_norm, hU_rng, hU_adj_rng, hU_tr⟩

/-- **Variational characterization of the nuclear seminorm**:
`‖B‖₁ = ⨆_{‖U‖ ≤ 1} ‖tr (U† B)‖`. -/
theorem nuclear_eq_iSup_norm_trace_adjoint_comp (B : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F B =
      ⨆ U : {U : E →ₗ[𝕜] F // opNorm 𝕜 E F U ≤ 1},
        ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U.val ∘ₗ B)‖ := by
  have : Nonempty {U : E →ₗ[𝕜] F // opNorm 𝕜 E F U ≤ 1} := ⟨⟨0, by simp⟩⟩
  have hle (U : {U : E →ₗ[𝕜] F // opNorm 𝕜 E F U ≤ 1}) :
      ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U.val ∘ₗ B)‖ ≤ nuclear 𝕜 E F B := by
    calc ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U.val ∘ₗ B)‖
        ≤ opNorm 𝕜 E F U.val * nuclear 𝕜 E F B :=
          norm_trace_adjoint_comp_le_opNorm_mul_nuclear U.val B
      _ ≤ 1 * nuclear 𝕜 E F B := mul_le_mul_of_nonneg_right U.property (apply_nonneg _ _)
      _ = nuclear 𝕜 E F B := one_mul _
  refine le_antisymm ?_ (ciSup_le hle)
  obtain ⟨U, hU_norm, _, _, hU_tr⟩ := exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear B
  have hbdd : BddAbove (Set.range fun U : {U : E →ₗ[𝕜] F // opNorm 𝕜 E F U ≤ 1} ↦
      ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U.val ∘ₗ B)‖) :=
    ⟨nuclear 𝕜 E F B, by rintro _ ⟨V, rfl⟩; exact hle V⟩
  calc nuclear 𝕜 E F B
      = ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U ∘ₗ B)‖ := by
        rw [hU_tr, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg _ _)]
    _ ≤ ⨆ U : {U : E →ₗ[𝕜] F // opNorm 𝕜 E F U ≤ 1},
          ‖LinearMap.trace 𝕜 E (LinearMap.adjoint U.val ∘ₗ B)‖ :=
        le_ciSup hbdd ⟨U, hU_norm⟩

/-- The nuclear seminorm of a rank-one map `x ↦ ⟪v, x⟫ u` is `‖u‖ * ‖v‖`. -/
theorem nuclear_rankOne (u : F) (v : E) :
    nuclear 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap = ‖u‖ * ‖v‖ := by
  refine le_antisymm ?_ ?_
  · have hrng : LinearMap.range (InnerProductSpace.rankOne 𝕜 u v).toLinearMap ≤
        Submodule.span 𝕜 {u} := by
      rintro _ ⟨x, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hrank : finrank 𝕜 (LinearMap.range (InnerProductSpace.rankOne 𝕜 u v).toLinearMap) ≤ 1 :=
      (Submodule.finrank_mono hrng).trans ((finrank_span_le_card ({u} : Set F)).trans (by simp))
    calc nuclear 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap
        ≤ √(finrank 𝕜 (LinearMap.range (InnerProductSpace.rankOne 𝕜 u v).toLinearMap)) *
            frobenius 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap :=
          nuclear_apply_le_sqrt_finrank_range_mul_frobenius_apply _
      _ ≤ √1 * (‖u‖ * ‖v‖) := by
          rw [frobenius_rankOne]
          exact mul_le_mul_of_nonneg_right
            (Real.sqrt_le_sqrt (by exact_mod_cast hrank)) (by positivity)
      _ = ‖u‖ * ‖v‖ := by simp
  · have hclm :
        LinearMap.toContinuousLinearMap (InnerProductSpace.rankOne 𝕜 u v).toLinearMap =
          InnerProductSpace.rankOne 𝕜 u v :=
      ContinuousLinearMap.ext fun _ ↦ rfl
    calc ‖u‖ * ‖v‖
        = opNorm 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap := by
          rw [opNorm_apply, hclm, InnerProductSpace.norm_rankOne]
      _ ≤ nuclear 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap := by
          simpa using opNorm_apply_le_schatten_apply 1 (InnerProductSpace.rankOne 𝕜 u v).toLinearMap

/-- **Attainment of trace duality for the operator norm**: every map `A` admits a map `B` with
`‖B‖₁ ≤ 1` and `tr (A† B) = ‖A‖`. -/
theorem exists_nuclear_le_one_trace_adjoint_comp_eq_opNorm (A : E →ₗ[𝕜] F) :
    ∃ B : E →ₗ[𝕜] F, nuclear 𝕜 E F B ≤ 1 ∧
      LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B) = (opNorm 𝕜 E F A : 𝕜) := by
  rcases (finrank 𝕜 E).eq_zero_or_pos with h0 | hpos
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    refine ⟨0, by simp, ?_⟩
    rw [Subsingleton.elim A 0]
    simp
  · let i₀ : Fin (finrank 𝕜 E) := ⟨0, hpos⟩
    let B : E →ₗ[𝕜] F :=
      (InnerProductSpace.rankOne 𝕜 (A.leftSingularVector i₀) (A.rightSingularBasis i₀)).toLinearMap
    refine ⟨B, ?_, ?_⟩
    · rw [nuclear_rankOne, A.rightSingularBasis.norm_eq_one i₀, mul_one]
      exact A.norm_leftSingularVector_le_one i₀
    · have hcomp : LinearMap.adjoint A ∘ₗ B =
          (InnerProductSpace.rankOne 𝕜
            (LinearMap.adjoint A (A.leftSingularVector i₀))
            (A.rightSingularBasis i₀)).toLinearMap := by
        ext x
        simp only [LinearMap.comp_apply, B, ContinuousLinearMap.coe_coe,
          InnerProductSpace.rankOne_apply, map_smul]
      simp only [hcomp, InnerProductSpace.trace_rankOne, A.adjoint_leftSingularVector i₀,
        inner_smul_right, orthonormal_iff_ite.mp A.rightSingularBasis.orthonormal i₀ i₀, ↓reduceIte,
        mul_one, opNorm_apply, A.norm_toContinuousLinearMap_eq_singularValues_zero, i₀]

/-- **Variational characterization of the operator norm**:
`‖A‖ = ⨆_{‖B‖₁ ≤ 1} ‖tr (A† B)‖`. -/
theorem opNorm_eq_iSup_norm_trace_adjoint_comp (A : E →ₗ[𝕜] F) :
    opNorm 𝕜 E F A =
      ⨆ B : {B : E →ₗ[𝕜] F // nuclear 𝕜 E F B ≤ 1},
        ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B.val)‖ := by
  have : Nonempty {B : E →ₗ[𝕜] F // nuclear 𝕜 E F B ≤ 1} := ⟨⟨0, by simp⟩⟩
  have hle (B : {B : E →ₗ[𝕜] F // nuclear 𝕜 E F B ≤ 1}) :
      ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B.val)‖ ≤ opNorm 𝕜 E F A := by
    calc ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B.val)‖
        ≤ opNorm 𝕜 E F A * nuclear 𝕜 E F B.val :=
          norm_trace_adjoint_comp_le_opNorm_mul_nuclear A B.val
      _ ≤ opNorm 𝕜 E F A * 1 := mul_le_mul_of_nonneg_left B.property (apply_nonneg _ _)
      _ = opNorm 𝕜 E F A := mul_one _
  refine le_antisymm ?_ (ciSup_le hle)
  obtain ⟨B, hB_norm, hB_tr⟩ := exists_nuclear_le_one_trace_adjoint_comp_eq_opNorm A
  have hbdd : BddAbove (Set.range fun B : {B : E →ₗ[𝕜] F // nuclear 𝕜 E F B ≤ 1} ↦
      ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B.val)‖) :=
    ⟨opNorm 𝕜 E F A, by rintro _ ⟨C, rfl⟩; exact hle C⟩
  calc opNorm 𝕜 E F A
      = ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)‖ := by
        rw [hB_tr, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg _ _)]
    _ ≤ ⨆ B : {B : E →ₗ[𝕜] F // nuclear 𝕜 E F B ≤ 1},
          ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B.val)‖ :=
        le_ciSup hbdd ⟨B, hB_norm⟩

/-! ### Orthogonal additivity of the nuclear seminorm -/

/-- **Orthogonal additivity (pinching) of the nuclear seminorm**: if `A† B = 0` and `A B† = 0`,
then `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁`. -/
theorem nuclear_add_of_orthogonal {A B : E →ₗ[𝕜] F}
    (h₁ : LinearMap.adjoint A ∘ₗ B = 0) (h₂ : A ∘ₗ LinearMap.adjoint B = 0) :
    nuclear 𝕜 E F (A + B) = nuclear 𝕜 E F A + nuclear 𝕜 E F B := by
  refine le_antisymm (map_add_le_add _ A B) ?_
  obtain ⟨U, hU_norm, hU_rng, hU_adj_rng, hU_tr⟩ :=
    exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear A
  obtain ⟨V, hV_norm, hV_rng, hV_adj_rng, hV_tr⟩ :=
    exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear B
  have hUV₁ : LinearMap.adjoint U ∘ₗ V = 0 :=
    LinearMap.adjoint_comp_eq_zero_of_range_le h₁ hU_rng hV_rng
  have hUV₂ : U ∘ₗ LinearMap.adjoint V = 0 := by
    have h₂' : LinearMap.adjoint (LinearMap.adjoint A) ∘ₗ LinearMap.adjoint B = 0 := by
      simpa only [LinearMap.adjoint_adjoint] using h₂
    simpa only [LinearMap.adjoint_adjoint] using
      LinearMap.adjoint_comp_eq_zero_of_range_le h₂' hU_adj_rng hV_adj_rng
  have hUB : LinearMap.adjoint U ∘ₗ B = 0 :=
    LinearMap.adjoint_comp_eq_zero_of_range_le h₁ hU_rng le_rfl
  have hVA : LinearMap.adjoint V ∘ₗ A = 0 := by
    have h₁' : LinearMap.adjoint B ∘ₗ A = 0 := by
      simpa [LinearMap.adjoint_comp] using congrArg LinearMap.adjoint h₁
    exact LinearMap.adjoint_comp_eq_zero_of_range_le h₁' hV_rng le_rfl
  have hUV_norm : opNorm 𝕜 E F (U + V) ≤ 1 := by
    rw [opNorm_add_eq_max_of_orthogonal hUV₁ hUV₂]
    exact max_le hU_norm hV_norm
  have htr : LinearMap.trace 𝕜 E (LinearMap.adjoint (U + V) ∘ₗ (A + B)) =
      ((nuclear 𝕜 E F A + nuclear 𝕜 E F B : ℝ) : 𝕜) := by
    rw [map_add, LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add,
      map_add, map_add, map_add, hU_tr, hUB, hVA, hV_tr, map_zero, add_zero, zero_add,
      RCLike.ofReal_add]
  have hnonneg : 0 ≤ nuclear 𝕜 E F A + nuclear 𝕜 E F B :=
    add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  calc nuclear 𝕜 E F A + nuclear 𝕜 E F B
      = ‖LinearMap.trace 𝕜 E (LinearMap.adjoint (U + V) ∘ₗ (A + B))‖ := by
        rw [htr, RCLike.norm_ofReal, abs_of_nonneg hnonneg]
    _ ≤ opNorm 𝕜 E F (U + V) * nuclear 𝕜 E F (A + B) :=
        norm_trace_adjoint_comp_le_opNorm_mul_nuclear (U + V) (A + B)
    _ ≤ 1 * nuclear 𝕜 E F (A + B) := mul_le_mul_of_nonneg_right hUV_norm (apply_nonneg _ _)
    _ = nuclear 𝕜 E F (A + B) := one_mul _

/-! ### Low-rank tangent–normal decomposition and decomposability -/

/-- **Nuclear-norm decomposability inequality**: whenever `Θ` and `Δ₂` are two-sided orthogonal
(`Θ† Δ₂ = 0` and `Θ Δ₂† = 0`), any split `Δ = Δ₁ + Δ₂` satisfies
`‖Θ‖₁ + ‖Δ₂‖₁ - ‖Δ₁‖₁ ≤ ‖Θ + (Δ₁ + Δ₂)‖₁`. -/
theorem nuclear_add_sub_le_nuclear_add_of_orthogonal {Θ Δ₁ Δ₂ : E →ₗ[𝕜] F}
    (h₁ : LinearMap.adjoint Θ ∘ₗ Δ₂ = 0) (h₂ : Θ ∘ₗ LinearMap.adjoint Δ₂ = 0) :
    nuclear 𝕜 E F Θ + nuclear 𝕜 E F Δ₂ - nuclear 𝕜 E F Δ₁ ≤
      nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) := by
  have htri : nuclear 𝕜 E F (Θ + Δ₂) ≤ nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) + nuclear 𝕜 E F Δ₁ := by
    have hEq : Θ + Δ₂ = (Θ + (Δ₁ + Δ₂)) + (-Δ₁) := by abel
    calc nuclear 𝕜 E F (Θ + Δ₂)
        = nuclear 𝕜 E F ((Θ + (Δ₁ + Δ₂)) + (-Δ₁)) := by rw [hEq]
      _ ≤ nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) + nuclear 𝕜 E F (-Δ₁) := map_add_le_add _ _ _
      _ = nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) + nuclear 𝕜 E F Δ₁ := by rw [map_neg_eq_map]
  linarith [nuclear_add_of_orthogonal h₁ h₂]

/-- The tangent part `Δ - P_W Δ P_K` has Frobenius seminorm at most `‖Δ‖_F`. -/
theorem frobenius_sub_starProjection_comp_le (W : Submodule 𝕜 F) (K : Submodule 𝕜 E)
    (Δ : E →ₗ[𝕜] F) :
    frobenius 𝕜 E F (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) ≤
      frobenius 𝕜 E F Δ := by
  set Δ₂ := W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap
  have hpyth := sq_frobenius_add_of_re_trace_adjoint_comp_eq_zero (A := Δ - Δ₂) (B := Δ₂) (by
    rw [Δ.trace_adjoint_sub_starProjection_comp_eq_zero W K, map_zero])
  rw [sub_add_cancel] at hpyth
  have hsq : frobenius 𝕜 E F (Δ - Δ₂) ^ 2 ≤ frobenius 𝕜 E F Δ ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact le_of_sq_le_sq hsq (apply_nonneg _ _)

/-- The nuclear seminorm of the tangent part `Δ - P_W Δ P_K` is bounded by
`√(dim Wᗮ + dim Kᗮ) ‖Δ‖_F`. -/
theorem nuclear_sub_starProjection_comp_le (W : Submodule 𝕜 F) (K : Submodule 𝕜 E)
    (Δ : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) ≤
      √((finrank 𝕜 Wᗮ + finrank 𝕜 Kᗮ : ℕ) : ℝ) * frobenius 𝕜 E F Δ := by
  have hrank := Δ.finrank_range_sub_starProjection_comp_le W K
  calc nuclear 𝕜 E F (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap)
      ≤ √(finrank 𝕜 (LinearMap.range
            (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap))) *
          frobenius 𝕜 E F
            (Δ - W.starProjection.toLinearMap ∘ₗ Δ ∘ₗ K.starProjection.toLinearMap) :=
        nuclear_apply_le_sqrt_finrank_range_mul_frobenius_apply _
    _ ≤ √((finrank 𝕜 Wᗮ + finrank 𝕜 Kᗮ : ℕ) : ℝ) * frobenius 𝕜 E F Δ :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hrank))
          (frobenius_sub_starProjection_comp_le W K Δ) (apply_nonneg _ _) (Real.sqrt_nonneg _)

/-- For a target map `Θ`, the canonical tangent part `Δ - P_{(range Θ)ᗮ} Δ P_{ker Θ}` satisfies
`‖Δ - P_{(range Θ)ᗮ} Δ P_{ker Θ}‖₁ ≤ √(2 rank Θ) ‖Δ‖_F`. -/
theorem nuclear_sub_orthogonal_range_ker_le (Θ Δ : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F
        (Δ - (LinearMap.range Θ)ᗮ.starProjection.toLinearMap ∘ₗ Δ ∘ₗ
          (LinearMap.ker Θ).starProjection.toLinearMap) ≤
      √(2 * (finrank 𝕜 (LinearMap.range Θ) : ℝ)) * frobenius 𝕜 E F Δ := by
  have h := nuclear_sub_starProjection_comp_le (LinearMap.range Θ)ᗮ (LinearMap.ker Θ) Δ
  rwa [Submodule.orthogonal_orthogonal, LinearMap.orthogonal_ker,
    LinearMap.finrank_range_adjoint, ← two_mul, Nat.cast_mul, Nat.cast_ofNat] at h

/-- **Explicit nuclear-norm decomposability** for the canonical tangent–normal split around `Θ`:
`‖Θ‖₁ + ‖P_{(range Θ)ᗮ} Δ P_{ker Θ}‖₁ - ‖Δ - P_{(range Θ)ᗮ} Δ P_{ker Θ}‖₁ ≤ ‖Θ + Δ‖₁`. -/
theorem nuclear_add_starProjection_comp_sub_le_nuclear_add (Θ Δ : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F Θ +
        nuclear 𝕜 E F ((LinearMap.range Θ)ᗮ.starProjection.toLinearMap ∘ₗ Δ ∘ₗ
          (LinearMap.ker Θ).starProjection.toLinearMap) -
        nuclear 𝕜 E F (Δ - (LinearMap.range Θ)ᗮ.starProjection.toLinearMap ∘ₗ Δ ∘ₗ
          (LinearMap.ker Θ).starProjection.toLinearMap) ≤
      nuclear 𝕜 E F (Θ + Δ) := by
  simpa only [sub_add_cancel] using
    nuclear_add_sub_le_nuclear_add_of_orthogonal
      (Δ₁ := Δ - (LinearMap.range Θ)ᗮ.starProjection.toLinearMap ∘ₗ Δ ∘ₗ
        (LinearMap.ker Θ).starProjection.toLinearMap)
      (LinearMap.adjoint_comp_orthogonal_range_starProjection_comp_ker Θ Δ)
      (LinearMap.comp_adjoint_orthogonal_range_starProjection_comp_ker Θ Δ)

/-- **Wainwright's low-rank tangent–normal decomposition**: if `rank Θ ≤ r`, then every
perturbation `Δ` splits as `Δ = Δ₁ + Δ₂` where `Δ₁` has rank at most `2 r`, `Δ₂` is two-sided
orthogonal to `Θ` (`Θ† Δ₂ = 0` and `Θ Δ₂† = 0`), `Δ₁` and `Δ₂` are trace-orthogonal
(`tr (Δ₁† Δ₂) = 0`), the nuclear seminorm is decomposable
(`‖Θ‖₁ + ‖Δ₂‖₁ - ‖Δ₁‖₁ ≤ ‖Θ + Δ‖₁`), and `‖Δ₁‖₁ ≤ √(2 r) ‖Δ‖_F`. -/
theorem exists_lowRank_decomposition {r : ℕ} {Θ : E →ₗ[𝕜] F}
    (hΘ : finrank 𝕜 (LinearMap.range Θ) ≤ r) (Δ : E →ₗ[𝕜] F) :
    ∃ Δ₁ Δ₂ : E →ₗ[𝕜] F,
      Δ₁ + Δ₂ = Δ ∧
      finrank 𝕜 (LinearMap.range Δ₁) ≤ 2 * r ∧
      LinearMap.adjoint Θ ∘ₗ Δ₂ = 0 ∧
      Θ ∘ₗ LinearMap.adjoint Δ₂ = 0 ∧
      LinearMap.trace 𝕜 E (LinearMap.adjoint Δ₁ ∘ₗ Δ₂) = 0 ∧
      nuclear 𝕜 E F Θ + nuclear 𝕜 E F Δ₂ - nuclear 𝕜 E F Δ₁ ≤ nuclear 𝕜 E F (Θ + Δ) ∧
      nuclear 𝕜 E F Δ₁ ≤ √(2 * (r : ℝ)) * frobenius 𝕜 E F Δ := by
  let Δ₂ : E →ₗ[𝕜] F :=
    (LinearMap.range Θ)ᗮ.starProjection.toLinearMap ∘ₗ Δ ∘ₗ
      (LinearMap.ker Θ).starProjection.toLinearMap
  let Δ₁ : E →ₗ[𝕜] F := Δ - Δ₂
  have hnuc : nuclear 𝕜 E F Δ₁ ≤ √(2 * (r : ℝ)) * frobenius 𝕜 E F Δ := by
    refine (nuclear_sub_orthogonal_range_ker_le Θ Δ).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (apply_nonneg _ _)
    gcongr
  exact ⟨Δ₁, Δ₂, sub_add_cancel Δ Δ₂,
    (Θ.finrank_range_sub_orthogonal_range_starProjection_comp_ker_le Δ).trans
      (Nat.mul_le_mul_left 2 hΘ),
    LinearMap.adjoint_comp_orthogonal_range_starProjection_comp_ker Θ Δ,
    LinearMap.comp_adjoint_orthogonal_range_starProjection_comp_ker Θ Δ,
    Δ.trace_adjoint_sub_starProjection_comp_eq_zero (LinearMap.range Θ)ᗮ (LinearMap.ker Θ),
    nuclear_add_starProjection_comp_sub_le_nuclear_add Θ Δ, hnuc⟩

end TauCeti.UnitarilyInvariantSeminorm
