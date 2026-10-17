/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Continuity, adjoints, and orthogonal extensions of the Jacobian `normDet`

For finite-dimensional real inner product spaces `U` and `V`, the `m`-dimensional Jacobian
`LinearMap.normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends continuously on the map.
This follows from `normDet² = det (A† A)` (`ContinuousLinearMap.normDet_sq`). Consequently, near an
injective linear map the Jacobian is controlled up to any factor `τ > 1`, uniformly with the
antilipschitz constant.

Extending a linear map `T : U → V` to the Euclidean product `ℝ × U` by sending the new direction
to a unit vector orthogonal to the range of `T` does not change the Jacobian. This is the linear
algebra behind cones: for `t > 0`, the Jacobian of `(t, u) ↦ t • ψ u` for a parametrization `ψ`
of a piece of the unit sphere is `tᵐ` times the Jacobian of `ψ`.

## Main declarations

* `ContinuousLinearMap.continuous_normDet`: the Jacobian `normDet` is continuous.
* `ContinuousLinearMap.exists_ball_antilipschitzWith_normDet_le`: around an injective linear map
  there is a ball with a uniform antilipschitz constant on which `normDet` varies by a factor at
  most `τ`.
* `TauCeti.LinearMap.normDet_adjoint_of_finrank_eq`: a map between spaces of equal dimension
  and its adjoint have the same norm determinant.
* `LinearMap.normDet_toSpanSingleton_coprod`: an orthogonal unit extension of a linear map has the
  same Jacobian.
* `TauCeti.ContinuousLinearMap.orthogonalKerEquivOfSurjective`: a surjective map restricted to
  the orthogonal complement of its kernel, as a continuous linear equivalence.
* `TauCeti.ContinuousLinearMap.normDet_orthogonalKerEquivOfSurjective`: the norm determinant of
  this restriction equals that of the adjoint.
-/

public section

open Function Metric Set
open scoped NNReal Topology

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `m`-dimensional Jacobian `normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends
continuously on the map. -/
theorem ContinuousLinearMap.continuous_normDet :
    Continuous fun A : U →L[ℝ] V => A.normDet := by
  have h (A : U →L[ℝ] V) : A.normDet = √((ContinuousLinearMap.adjoint A ∘L A).det) := by
    rw [← A.normDet_sq, RCLike.ofReal_real_eq_id, id, Real.sqrt_sq A.normDet_nonneg]
  simp_rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id)).sqrt

namespace ContinuousLinearMap

/-- Around an injective linear map `B` there is a ball on which the antilipschitz constant is
uniform and the Jacobian varies by a factor at most `τ`: every `C` within distance `ρ` of `B` is
`K`-antilipschitz, and `C.normDet` and `B.normDet` agree up to the factor `τ`. -/
theorem exists_ball_antilipschitzWith_normDet_le (B : U →L[ℝ] V)
    (hB : Injective B) {τ : ℝ} (hτ : 1 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ≥0, ∀ C : U →L[ℝ] V, dist C B < ρ →
      AntilipschitzWith K C ∧ C.normDet ≤ τ * B.normDet ∧ B.normDet ≤ τ * C.normDet := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := (B : U →ₗ[ℝ] V).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hB)
  have hJ : 0 < B.normDet := lt_of_le_of_ne B.normDet_nonneg
    (Ne.symm fun h => (LinearMap.normDet_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hB))
  -- Continuity of the Jacobian at `B`.
  have hev : ∀ᶠ C in 𝓝 B, C.normDet ∈ Ioo (B.normDet / τ) (τ * B.normDet) :=
    (continuous_normDet.tendsto B).eventually
      (Ioo_mem_nhds (div_lt_self hJ hτ) (lt_mul_of_one_lt_left hJ hτ))
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff.1 hev
  have hK₀' : (0 : ℝ) < K₀ := hK₀pos
  refine ⟨min ε (1 / (2 * K₀)), lt_min hε (by positivity), 2 * K₀, fun C hC => ⟨?_, ?_, ?_⟩⟩
  · -- `‖x‖ ≤ K₀ ‖B x‖ ≤ K₀ (‖C x‖ + ‖x‖ / (2 K₀))`.
    refine antilipschitz_of_bound C fun x => ?_
    have h1 : ‖x‖ ≤ K₀ * ‖B x‖ := by simpa using hK₀.le_mul_dist x 0
    have h2 : ‖B - C‖ ≤ 1 / (2 * K₀) := by
      rw [← dist_eq_norm, dist_comm]
      exact hC.le.trans (min_le_right _ _)
    have h3 : ‖B x‖ ≤ ‖C x‖ + 1 / (2 * K₀) * ‖x‖ := by
      calc ‖B x‖ = ‖C x + (B - C) x‖ := by simp
        _ ≤ ‖C x‖ + ‖(B - C) x‖ := norm_add_le _ _
        _ ≤ ‖C x‖ + 1 / (2 * K₀) * ‖x‖ := by
            gcongr
            exact ((B - C).le_opNorm x).trans (by gcongr)
    have h4 : K₀ * (1 / (2 * K₀) * ‖x‖) = ‖x‖ / 2 := by field_simp
    push_cast
    nlinarith
  · exact (hεJ (hC.trans_le (min_le_left _ _))).2.le
  · have h := (hεJ (hC.trans_le (min_le_left _ _))).1
    rw [div_lt_iff₀ (zero_lt_one.trans hτ)] at h
    linarith

end ContinuousLinearMap

namespace LinearMap

open scoped RealInnerProductSpace

/-- Extending `T : U →ₗ[ℝ] V` to the Euclidean product `WithLp 2 (ℝ × U)` by a unit vector `e`
orthogonal to the range of `T`, `(a, u) ↦ a • e + T u`, does not change the Jacobian `normDet`. -/
theorem normDet_toSpanSingleton_coprod {e : V} (he : ‖e‖ = 1) {T : U →ₗ[ℝ] V}
    (hT : ∀ u, ⟪e, T u⟫ = 0) :
    ((toSpanSingleton ℝ V e).coprod T ∘ₗ (WithLp.linearEquiv 2 ℝ (ℝ × U)).toLinearMap).normDet =
      T.normDet := by
  set P := WithLp.linearEquiv 2 ℝ (ℝ × U)
  set L := (toSpanSingleton ℝ V e).coprod T ∘ₗ P.toLinearMap
  -- The Gram operator of `L` is block diagonal: `1` on `ℝ` and `T† T` on `U`.
  have hL : L.adjoint ∘ₗ L = P.symm.conj ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap (T.adjoint ∘ₗ T)) := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp [L, P, LinearEquiv.conj_apply, WithLp.prod_inner_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hT, he, LinearMap.adjoint_inner_left, real_inner_comm e]
  have h₁ := L.normDet_sq
  have h₂ := T.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h₁ h₂
  refine (sq_eq_sq₀ L.normDet_nonneg T.normDet_nonneg).1 ?_
  rw [h₁, h₂, hL, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj,
    LinearMap.det_prodMap, LinearMap.det_id, one_mul]

end LinearMap

namespace TauCeti

open TauCeti

namespace LinearMap

/-- Between spaces of equal dimension, a linear map and its adjoint have the same norm
determinant. This compares the area and coarea factors for an invertible linear map. -/
theorem normDet_adjoint_of_finrank_eq {𝕜 U V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (f : U →ₗ[𝕜] V) (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) :
    f.adjoint.normDet = f.normDet := by
  let bU := stdOrthonormalBasis 𝕜 U
  let bV := (stdOrthonormalBasis 𝕜 V).reindex (finCongr h.symm)
  rw [LinearMap.normDet_eq_norm_det_toMatrix _ bV bU,
    LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose,
    LinearMap.normDet_eq_norm_det_toMatrix _ bU bV]
  simp

end LinearMap

namespace ContinuousLinearMap

open scoped RealInnerProductSpace

/-- A surjective linear map restricts to a continuous linear equivalence from the orthogonal
complement of its kernel onto the target. -/
noncomputable def orthogonalKerEquivOfSurjective (L : U →L[ℝ] V) (hL : Surjective L) :
    L.kerᗮ ≃L[ℝ] V :=
  (LinearEquiv.ofBijective (L.toLinearMap.domRestrict L.kerᗮ)
    ⟨LinearMap.injective_domRestrict_iff.mpr L.ker.isCompl_orthogonal.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hL).mpr
        L.ker.isCompl_orthogonal.symm.codisjoint⟩).toContinuousLinearEquiv

omit [FiniteDimensional ℝ V] in
/-- The orthogonal-kernel restriction equivalence acts by the original map. -/
@[simp]
theorem orthogonalKerEquivOfSurjective_apply (L : U →L[ℝ] V) (hL : Surjective L)
    (u : L.kerᗮ) : L.orthogonalKerEquivOfSurjective hL u = L u := (rfl)

/-- The norm determinant of a surjective map restricted to the orthogonal complement of its
kernel equals the norm determinant of its adjoint. -/
theorem normDet_orthogonalKerEquivOfSurjective (L : U →L[ℝ] V) (hL : Surjective L) :
    (L.orthogonalKerEquivOfSurjective hL).toLinearMap.normDet = L.adjoint.normDet := by
  let P := L.kerᗮ
  have hmem (y : V) : L.toLinearMap.adjoint y ∈ P := by
    simpa only [P, LinearMap.orthogonal_ker] using
      (LinearMap.mem_range_self L.toLinearMap.adjoint y)
  have heq : (L.orthogonalKerEquivOfSurjective hL).toLinearMap.adjoint =
      L.toLinearMap.adjoint.codRestrict P hmem := by
    apply LinearMap.ext
    intro y
    apply ext_inner_right ℝ
    intro u
    rw [LinearMap.adjoint_inner_left, Submodule.coe_inner,
      LinearEquiv.coe_toLinearMap, ContinuousLinearEquiv.coe_toLinearEquiv,
      orthogonalKerEquivOfSurjective_apply,
      LinearMap.codRestrict_apply]
    exact (L.toLinearMap.adjoint_inner_left u y).symm
  rw [← LinearMap.normDet_adjoint_of_finrank_eq _
    (L.orthogonalKerEquivOfSurjective hL).toLinearEquiv.finrank_eq,
    heq, LinearMap.normDet_codRestrict, ContinuousLinearMap.adjoint_toLinearMap]

end ContinuousLinearMap

end TauCeti
