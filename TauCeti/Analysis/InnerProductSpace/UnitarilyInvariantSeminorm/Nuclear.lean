/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm

import TauCeti.Analysis.InnerProductSpace.Polar.Finite
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
  `TauCeti.UnitarilyInvariantSeminorm.opNorm_add_eq_max_of_twoSidedOrthogonal` and trace duality
  yields `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁`.
* **Low-rank tangent–normal decomposition**: for any subspaces `W ≤ F` and `K ≤ E`, decomposing
  `Δ = Δ₁ + Δ₂` with normal part `Δ₂ = P_W Δ P_K` and tangent part `Δ₁ = Δ - Δ₂` gives
  `rank Δ₁ ≤ dim Wᗮ + dim Kᗮ`, trace orthogonality `tr (Δ₁† Δ₂) = 0`, and therefore
  `‖Δ₁‖_F ≤ ‖Δ‖_F` and `‖Δ₁‖₁ ≤ √(dim Wᗮ + dim Kᗮ) ‖Δ‖_F`. Taking `W = (range Θ)ᗮ` and `K = ker Θ`
  gives `Δ₂ = Θ.normalPart Δ`, which is two-sided orthogonal to `Θ`, yielding Wainwright's
  nuclear-norm decomposability inequality `‖Θ‖₁ + ‖Δ₂‖₁ - ‖Δ₁‖₁ ≤ ‖Θ + Δ‖₁` together with
  `rank Δ₁ ≤ 2 rank Θ` and `‖Δ₁‖₁ ≤ √(2 rank Θ) ‖Δ‖_F`.

## Main declarations

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
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_of_twoSidedOrthogonal`:
  `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁` whenever `A† B = 0` and `A B† = 0`.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_sub_le_nuclear_add_of_twoSidedOrthogonal`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_sub_starProjection_comp_le`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_sub_normalPart_le`,
  `TauCeti.UnitarilyInvariantSeminorm.nuclear_add_normalPart_sub_le_nuclear_add`:
  explicit decomposability and tangent-part nuclear bounds.
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

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### Trace duality between the operator norm and the nuclear seminorm -/

/-- **Trace duality**: `‖tr (A† B)‖ ≤ ‖A‖ ‖B‖₁`. -/
theorem norm_trace_adjoint_comp_le_opNorm_mul_nuclear (A B : E →ₗ[𝕜] F) :
    ‖LinearMap.trace 𝕜 E (LinearMap.adjoint A ∘ₗ B)‖ ≤ opNorm 𝕜 E F A * nuclear 𝕜 E F B := by
  rw [LinearMap.trace_adjoint_comp_eq_sum_singularValues_mul_inner A B, nuclear_apply,
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
  refine ⟨B.polarFactor, ?_, B.range_polarFactor.le, B.range_adjoint_polarFactor.le, ?_⟩
  · let := FiniteDimensional.completeSpace 𝕜 E
    let := FiniteDimensional.completeSpace 𝕜 F
    rw [opNorm_apply, B.toContinuousLinearMap_polarFactor]
    exact ContinuousLinearMap.norm_factorThru_le zero_le_one fun x ↦ by simp
  · rw [B.adjoint_polarFactor_comp, LinearMap.trace_eq_sum_inner _ B.rightSingularBasis,
      nuclear_apply, ← B.sum_fin_singularValues (fun s ↦ s) rfl, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.operatorAbs_rightSingularBasis, inner_smul_right,
      orthonormal_iff_ite.mp B.rightSingularBasis.orthonormal i i]
    simp

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
  symm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt hle fun w hw ↦ ?_
  obtain ⟨U, hU_norm, _, _, hU_tr⟩ := exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear B
  refine ⟨⟨U, hU_norm⟩, ?_⟩
  rwa [hU_tr, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg _ _)]

/-- The nuclear seminorm of a rank-one map `x ↦ ⟪v, x⟫ u` is `‖u‖ * ‖v‖`. -/
@[simp]
theorem nuclear_rankOne (u : F) (v : E) :
    nuclear 𝕜 E F (InnerProductSpace.rankOne 𝕜 u v).toLinearMap = ‖u‖ * ‖v‖ := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hrank : finrank 𝕜 (LinearMap.range (InnerProductSpace.rankOne 𝕜 u v).toLinearMap) ≤ 1 :=
    (Module.rank_eq_one_iff_finrank_eq_one.mp (InnerProductSpace.rank_rankOne hu hv)).le
  have hclm :
      LinearMap.toContinuousLinearMap (InnerProductSpace.rankOne 𝕜 u v).toLinearMap =
        InnerProductSpace.rankOne 𝕜 u v := by
    rw [← LinearMap.coe_toContinuousLinearMap_symm, LinearEquiv.apply_symm_apply]
  rw [← LinearMap.kyFanSum_eq_nuclear _ hrank, LinearMap.kyFanSum_def, Finset.sum_range_one,
    ← LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero, hclm,
    InnerProductSpace.norm_rankOne]

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
        nth_rw 1 [← LinearMap.coe_toContinuousLinearMap (LinearMap.adjoint A)]
        rw [← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.comp_rankOne,
          LinearMap.coe_toContinuousLinearMap']
      rw [hcomp]
      simp only [InnerProductSpace.trace_rankOne, A.adjoint_leftSingularVector i₀,
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
  symm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt hle fun w hw ↦ ?_
  obtain ⟨B, hB_norm, hB_tr⟩ := exists_nuclear_le_one_trace_adjoint_comp_eq_opNorm A
  refine ⟨⟨B, hB_norm⟩, ?_⟩
  rwa [hB_tr, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg _ _)]

/-! ### Orthogonal additivity of the nuclear seminorm -/

/-- **Orthogonal additivity of the nuclear seminorm**: if `A† B = 0` and `A B† = 0`,
then `‖A + B‖₁ = ‖A‖₁ + ‖B‖₁`. -/
theorem nuclear_add_of_twoSidedOrthogonal {A B : E →ₗ[𝕜] F}
    (h₁ : LinearMap.adjoint A ∘ₗ B = 0) (h₂ : A ∘ₗ LinearMap.adjoint B = 0) :
    nuclear 𝕜 E F (A + B) = nuclear 𝕜 E F A + nuclear 𝕜 E F B := by
  refine le_antisymm (map_add_le_add _ A B) ?_
  obtain ⟨U, hU_norm, hU_rng, hU_adj_rng, hU_tr⟩ :=
    exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear A
  obtain ⟨V, hV_norm, hV_rng, hV_adj_rng, hV_tr⟩ :=
    exists_opNorm_le_one_trace_adjoint_comp_eq_nuclear B
  have hUV₁ : LinearMap.adjoint U ∘ₗ V = 0 :=
    LinearMap.adjoint_comp_eq_zero_of_range_le h₁ hU_rng hV_rng
  have hUV₂ : U ∘ₗ LinearMap.adjoint V = 0 :=
    LinearMap.comp_adjoint_eq_zero_of_range_adjoint_le h₂ hU_adj_rng hV_adj_rng
  have hUB : LinearMap.adjoint U ∘ₗ B = 0 :=
    LinearMap.adjoint_comp_eq_zero_of_range_le h₁ hU_rng le_rfl
  have hVA : LinearMap.adjoint V ∘ₗ A = 0 :=
    LinearMap.adjoint_comp_eq_zero_of_range_le
      (LinearMap.adjoint_comp_eq_zero_comm.mp h₁) hV_rng le_rfl
  have hUV_norm : opNorm 𝕜 E F (U + V) ≤ 1 := by
    rw [opNorm_add_eq_max_of_twoSidedOrthogonal hUV₁ hUV₂]
    exact max_le hU_norm hV_norm
  have htr : LinearMap.trace 𝕜 E (LinearMap.adjoint (U + V) ∘ₗ (A + B)) =
      ((nuclear 𝕜 E F A + nuclear 𝕜 E F B : ℝ) : 𝕜) := by
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, hU_tr, hUB, hVA, hV_tr, add_zero,
      zero_add]
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
theorem nuclear_add_sub_le_nuclear_add_of_twoSidedOrthogonal {Θ Δ₁ Δ₂ : E →ₗ[𝕜] F}
    (h₁ : LinearMap.adjoint Θ ∘ₗ Δ₂ = 0) (h₂ : Θ ∘ₗ LinearMap.adjoint Δ₂ = 0) :
    nuclear 𝕜 E F Θ + nuclear 𝕜 E F Δ₂ - nuclear 𝕜 E F Δ₁ ≤
      nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) := by
  have htri : nuclear 𝕜 E F (Θ + Δ₂) ≤ nuclear 𝕜 E F (Θ + (Δ₁ + Δ₂)) + nuclear 𝕜 E F Δ₁ := by
    have h := le_map_add_map_sub (nuclear 𝕜 E F) (Θ + Δ₂) (Θ + (Δ₁ + Δ₂))
    have hdiff : Θ + Δ₂ - (Θ + (Δ₁ + Δ₂)) = -Δ₁ := by abel
    rwa [hdiff, map_neg_eq_map] at h
  linarith [nuclear_add_of_twoSidedOrthogonal h₁ h₂]

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

/-- For a target map `Θ`, the canonical tangent part `Δ - Θ.normalPart Δ` satisfies
`‖Δ - Θ.normalPart Δ‖₁ ≤ √(2 rank Θ) ‖Δ‖_F`. -/
theorem nuclear_sub_normalPart_le (Θ Δ : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F (Δ - Θ.normalPart Δ) ≤
      √(2 * (finrank 𝕜 (LinearMap.range Θ) : ℝ)) * frobenius 𝕜 E F Δ := by
  calc nuclear 𝕜 E F (Δ - Θ.normalPart Δ)
      ≤ √(finrank 𝕜 (LinearMap.range (Δ - Θ.normalPart Δ))) *
          frobenius 𝕜 E F (Δ - Θ.normalPart Δ) :=
        nuclear_apply_le_sqrt_finrank_range_mul_frobenius_apply _
    _ ≤ √(2 * (finrank 𝕜 (LinearMap.range Θ) : ℝ)) * frobenius 𝕜 E F Δ :=
        mul_le_mul
          (Real.sqrt_le_sqrt (by exact_mod_cast Θ.finrank_range_sub_normalPart_le Δ))
          (frobenius_sub_normalPart_le Θ Δ) (apply_nonneg _ _) (Real.sqrt_nonneg _)

/-- **Explicit nuclear-norm decomposability** for the canonical tangent–normal split around `Θ`:
`‖Θ‖₁ + ‖Θ.normalPart Δ‖₁ - ‖Δ - Θ.normalPart Δ‖₁ ≤ ‖Θ + Δ‖₁`. -/
theorem nuclear_add_normalPart_sub_le_nuclear_add (Θ Δ : E →ₗ[𝕜] F) :
    nuclear 𝕜 E F Θ + nuclear 𝕜 E F (Θ.normalPart Δ) - nuclear 𝕜 E F (Δ - Θ.normalPart Δ) ≤
      nuclear 𝕜 E F (Θ + Δ) := by
  simpa only [sub_add_cancel] using
    nuclear_add_sub_le_nuclear_add_of_twoSidedOrthogonal
      (Δ₁ := Δ - Θ.normalPart Δ)
      (LinearMap.adjoint_comp_normalPart_eq_zero Θ Δ)
      (LinearMap.comp_adjoint_normalPart_eq_zero Θ Δ)

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
  let Δ₂ : E →ₗ[𝕜] F := Θ.normalPart Δ
  let Δ₁ : E →ₗ[𝕜] F := Δ - Δ₂
  have hnuc : nuclear 𝕜 E F Δ₁ ≤ √(2 * (r : ℝ)) * frobenius 𝕜 E F Δ := by
    refine (nuclear_sub_normalPart_le Θ Δ).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (apply_nonneg _ _)
    gcongr
  exact ⟨Δ₁, Δ₂, sub_add_cancel Δ Δ₂,
    (Θ.finrank_range_sub_normalPart_le Δ).trans (Nat.mul_le_mul_left 2 hΘ),
    LinearMap.adjoint_comp_normalPart_eq_zero Θ Δ,
    LinearMap.comp_adjoint_normalPart_eq_zero Θ Δ,
    Θ.trace_adjoint_sub_normalPart_comp_normalPart_eq_zero Δ,
    nuclear_add_normalPart_sub_le_nuclear_add Θ Δ, hnuc⟩

end TauCeti.UnitarilyInvariantSeminorm
