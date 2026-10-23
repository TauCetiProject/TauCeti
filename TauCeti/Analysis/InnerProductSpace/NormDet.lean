/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Lp.GraphDomain
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Continuity, adjoints, one-dimensional values, and orthogonal extensions of the Jacobian `normDet`

For finite-dimensional real inner product spaces `U` and `V`, the `m`-dimensional Jacobian
`LinearMap.normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends continuously on the map.
This follows from `normDet² = det (A† A)` (`ContinuousLinearMap.normDet_sq`). Consequently, near an
injective linear map the Jacobian is controlled up to any factor `τ > 1`, uniformly with the
antilipschitz constant.

Between spaces of equal finite dimension, a linear map and its adjoint have the same Jacobian.
Consequently the Jacobian of the adjoint of a surjective map is the Jacobian of its restriction to
the orthogonal complement of the kernel; this is the Jacobian of the coarea formula.

Extending a linear map `T : U → V` to the Euclidean product `ℝ × U` by sending the new direction
to a unit vector orthogonal to the range of `T` does not change the Jacobian. This is the linear
algebra behind cones: for `t > 0`, the Jacobian of `(t, u) ↦ t • ψ u` for a parametrization `ψ`
of a piece of the unit sphere is `tᵐ` times the Jacobian of `ψ`.

The Jacobian of the linear normal graph `x ↦ (A x, x)` of a functional `A` is
`sqrt (1 + ‖A‖²)`: its Gram matrix in an orthonormal basis is a rank-one perturbation of the
identity.

## Main declarations

* `ContinuousLinearMap.continuous_normDet`: the Jacobian `normDet` is continuous.
* `LinearMap.normDet_eq_norm_apply_one`: for a map from `ℝ`, the Jacobian is the norm of the
  image of `1`.
* `LinearMap.normDet_adjoint`: between spaces of equal dimension, the adjoint has the same
  Jacobian.
* `LinearMap.normDet_adjoint_eq_normDet_comp_subtype`: the Jacobian of the adjoint of a surjective
  map is the Jacobian of its restriction to the orthogonal complement of the kernel.
* `ContinuousLinearMap.exists_ball_antilipschitzWith_normDet_le`: around an injective linear map
  there is a ball with a uniform antilipschitz constant on which `normDet` varies by a factor at
  most `τ`.
* `LinearMap.normDet_toSpanSingleton_coprod`: an orthogonal unit extension of a linear map has the
  same Jacobian.
* `ContinuousLinearMap.normDet_normalGraphL`: the Jacobian of a linear normal graph.
-/

public section

open Function Metric Set
open scoped NNReal Topology

namespace LinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The one-dimensional geometric Jacobian of a linear map is the norm of the image of `1`. -/
theorem normDet_eq_norm_apply_one (A : ℝ →ₗ[ℝ] V) : A.normDet = ‖A 1‖ := by
  have h := A.normDet_sq_eq_det_gram (OrthonormalBasis.singleton Unit ℝ)
  rw [Matrix.det_unique] at h
  simp only [OrthonormalBasis.singleton_apply, Matrix.gram_apply,
    real_inner_self_eq_norm_sq, RCLike.ofReal_real_eq_id] at h
  exact sq_eq_sq₀ A.normDet_nonneg (norm_nonneg (A 1)) |>.mp h

/-- Between spaces of the same finite dimension, a linear map and its adjoint have the same
Jacobian `normDet`. The dimension hypothesis is necessary: an injective map into a larger space
has positive Jacobian, while its adjoint has a nontrivial kernel. -/
theorem normDet_adjoint {𝕜 U W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [FiniteDimensional 𝕜 U] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] (f : U →ₗ[𝕜] W) (h : Module.finrank 𝕜 U = Module.finrank 𝕜 W) :
    f.adjoint.normDet = f.normDet := by
  let bu := stdOrthonormalBasis 𝕜 U
  let bw := (stdOrthonormalBasis 𝕜 W).reindex (finCongr h.symm)
  rw [f.normDet_eq_norm_det_toMatrix bu bw, f.adjoint.normDet_eq_norm_det_toMatrix bw bu,
    toMatrix_adjoint, Matrix.det_conjTranspose, norm_star]

/-- The Jacobian of the adjoint of a surjective linear map is the Jacobian of the restriction of
the map to the orthogonal complement of its kernel. This restriction is a linear isomorphism onto
the codomain. -/
theorem normDet_adjoint_eq_normDet_comp_subtype {𝕜 U W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] (f : U →ₗ[𝕜] W)
    (hf : Function.Surjective f) :
    f.adjoint.normDet = (f ∘ₗ (ker f)ᗮ.subtype).normDet := by
  have hmem (y : W) : f.adjoint y ∈ (ker f)ᗮ := by
    rw [orthogonal_ker]
    exact mem_range_self _ y
  have hM : f.adjoint.codRestrict _ hmem = (f ∘ₗ (ker f)ᗮ.subtype).adjoint := by
    rw [eq_adjoint_iff]
    intro y w
    simp [adjoint_inner_left]
  rw [← normDet_codRestrict hmem, hM,
    normDet_adjoint _ (f.finrank_orthogonal_ker_of_surjective hf)]

end LinearMap

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

/-- The geometric Jacobian of the linear normal graph `x ↦ (A x, x)` is
`sqrt (1 + ‖A‖²)`. -/
theorem ContinuousLinearMap.normDet_normalGraphL (A : U →L[ℝ] ℝ) :
    A.normalGraphL.normDet = Real.sqrt (1 + ‖A‖ ^ 2) := by
  let b := stdOrthonormalBasis ℝ U
  let u : Fin (Module.finrank ℝ U) → ℝ := fun i => A (b i)
  have hgram : Matrix.gram ℝ (fun i => A.normalGraphL.toLinearMap (b i)) =
      1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit u := by
    ext i j
    simp only [Matrix.gram_apply, ContinuousLinearMap.coe_coe, A.coe_normalGraphL,
      WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
      TauCeti.normalGraphEmbedding_fst, TauCeti.normalGraphEmbedding_snd,
      orthonormal_iff_ite.mp b.orthonormal i j]
    simp [Matrix.mul_apply, u, Matrix.one_apply, mul_comm, add_comm]
  have hu : u ⬝ᵥ u = ‖A‖ ^ 2 := by
    simpa [u, dotProduct, Real.norm_eq_abs, sq] using b.sum_sq_norm_apply_eq_norm_sq A
  have hsq : A.normalGraphL.normDet ^ 2 = 1 + ‖A‖ ^ 2 := by
    have h := A.normalGraphL.toLinearMap.normDet_sq_eq_det_gram b
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h, hgram, Matrix.det_one_add_replicateCol_mul_replicateRow, hu]
  rw [← Real.sqrt_sq A.normalGraphL.normDet_nonneg, hsq]
