/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Conformal
public import TauCeti.Analysis.Normed.Lp.GraphDomain
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Continuity, adjoints, Hadamard bounds, and orthogonal extensions of the Jacobian `normDet`

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

Over any `RCLike` scalar field `𝕜` and arbitrary (possibly infinite-dimensional) inner product
codomain `W`, Hadamard's inequality bounds `A.normDet` by `∏ i, ‖A (b i)‖` on any orthonormal
basis `b` of `U`, and hence by `‖A‖ ^ Module.finrank 𝕜 U`. Equality holds if and only if `A = 0` or
`A` is conformal (`IsConformalMap A`).

## Main declarations

* `ContinuousLinearMap.continuous_normDet`, `ContinuousLinearMap.continuous_normDet_adjoint`:
  the Jacobian `normDet` and the coarea Jacobian `A ↦ A†.normDet` are continuous.
* `LinearMap.normDet_eq_norm_apply_one`, `LinearMap.normDet_toSpanSingleton`: for a map from an
  `RCLike` scalar field `𝕜`, the Jacobian is the norm of the image of `1`.
* `LinearMap.normDet_adjoint`: between spaces of equal dimension, the adjoint has the same
  Jacobian.
* `LinearMap.normDet_adjoint_eq_normDet_comp_subtype`: the Jacobian of the adjoint of a surjective
  map is the Jacobian of its restriction to the orthogonal complement of the kernel.
* `LinearMap.normDet_adjoint_pos_iff`, `LinearMap.normDet_adjoint_ne_zero_iff`,
  `LinearMap.normDet_adjoint_eq_zero_iff` (and their `ContinuousLinearMap` counterparts): the
  Jacobian of the adjoint is positive (nonzero) exactly for surjective maps, and vanishes exactly
  for nonsurjective maps.
* `ContinuousLinearMap.normDet_adjoint_eq_norm`: the Jacobian of the adjoint of a linear functional
  is its norm.
* `LinearMap.normDet_coprod_of_orthogonal`: the Jacobian of a sum of maps with orthogonal ranges
  on a Euclidean product is the product of their Jacobians.
* `ContinuousLinearMap.exists_ball_antilipschitzWith_normDet_le`: around an injective linear map
  there is a ball with a uniform antilipschitz constant on which `normDet` varies by a factor at
  most `τ`.
* `LinearMap.normDet_toSpanSingleton_coprod`: an orthogonal unit extension of a linear map has the
  same Jacobian.
* `ContinuousLinearMap.normDet_normalGraphL`: the Jacobian of a linear normal graph.
* `LinearMap.normDet_le_prod_norm`, `ContinuousLinearMap.normDet_le_norm_pow`,
  `IsConformalMap.normDet_eq_norm_pow`, `ContinuousLinearMap.norm_apply_eq_of_normDet_eq_norm_pow`,
  `ContinuousLinearMap.normDet_eq_norm_pow_iff`: Hadamard's inequality for `normDet` and its
  conformality equality characterization.
* `LinearMap.pow_finrank_le_normDet_of_mul_norm_le`, `LinearMap.normDet_le_pow_finrank_of_norm_le`,
  `LinearMap.normDet_eq_pow_finrank_of_norm_eq`: uniform lower, upper, and exact norm bounds on a
  linear map control its `normDet` by the `finrank`-th power of the factor.
* `LinearMap.normDet_eq_mul_normDet_orthogonal`,
  `LinearMap.normDet_eq_div_mul_normDet_orthogonal`,
  `LinearMap.normDet_eq_norm_mul_normDet_orthogonal`: when `f` maps a submodule `K` and `Kᗮ` to
  orthogonal subspaces, `f.normDet` factors as the product of the restrictions; along a single line
  `𝕜 ∙ u`, this splits off the radial stretch `‖f u‖ / ‖u‖`.
-/

public section

open Function Metric Set
open scoped NNReal Topology

namespace LinearMap

/-- The one-dimensional geometric Jacobian of a linear map is the norm of the image of `1`. -/
theorem normDet_eq_norm_apply_one {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (A : 𝕜 →ₗ[𝕜] V) : A.normDet = ‖A 1‖ := by
  have h := A.normDet_sq_eq_det_gram (OrthonormalBasis.singleton Unit 𝕜)
  rw [Matrix.det_unique] at h
  simp only [OrthonormalBasis.singleton_apply, Matrix.gram_apply,
    inner_self_eq_norm_sq_to_K] at h
  have hreal : A.normDet ^ 2 = ‖A 1‖ ^ 2 :=
    RCLike.ofReal_injective (K := 𝕜) (by simpa using h)
  exact (sq_eq_sq₀ A.normDet_nonneg (norm_nonneg (A 1))).mp hreal

/-- Over any `RCLike` scalar field, the one-dimensional `normDet` of `a ↦ a • y` is `‖y‖`. -/
@[simp]
theorem normDet_toSpanSingleton {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (y : V) : (toSpanSingleton 𝕜 V y).normDet = ‖y‖ := by
  simp [normDet_eq_norm_apply_one]

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

/-- The Jacobian of the adjoint of a linear map is positive exactly when the map is surjective. -/
theorem normDet_adjoint_pos_iff {𝕜 U W : Type*} [RCLike 𝕜] [NormedAddCommGroup U]
    [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] {f : U →ₗ[𝕜] W} :
    0 < f.adjoint.normDet ↔ Function.Surjective f := by
  rw [f.adjoint.normDet_nonneg.lt_iff_ne', Ne, normDet_eq_zero_iff_ker_ne_bot, not_not,
    ← orthogonal_range, Submodule.orthogonal_eq_bot_iff, range_eq_top]

/-- The Jacobian of the adjoint of a linear map is nonzero exactly when the map is surjective. -/
theorem normDet_adjoint_ne_zero_iff {𝕜 U W : Type*} [RCLike 𝕜] [NormedAddCommGroup U]
    [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] {f : U →ₗ[𝕜] W} :
    f.adjoint.normDet ≠ 0 ↔ Function.Surjective f := by
  rw [← f.adjoint.normDet_nonneg.lt_iff_ne', normDet_adjoint_pos_iff]

/-- The Jacobian of the adjoint of a linear map vanishes exactly when the map is not
surjective. -/
theorem normDet_adjoint_eq_zero_iff {𝕜 U W : Type*} [RCLike 𝕜] [NormedAddCommGroup U]
    [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] {f : U →ₗ[𝕜] W} :
    f.adjoint.normDet = 0 ↔ ¬Function.Surjective f := by
  simpa using (normDet_adjoint_ne_zero_iff (f := f)).not

/-- The norm determinant of `(u, w) ↦ A u + B w` on the Euclidean product is the product of the
norm determinants of `A` and `B` when their ranges are orthogonal. The codomain need not be
finite dimensional. -/
theorem normDet_coprod_of_orthogonal {𝕜 U W V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (A : U →ₗ[𝕜] V) (B : W →ₗ[𝕜] V)
    (horth : ∀ u w, inner 𝕜 (A u) (B w) = 0) :
    (A.coprod B ∘ₗ (WithLp.linearEquiv 2 𝕜 (U × W)).toLinearMap).normDet =
      A.normDet * B.normDet := by
  classical
  let C := A.coprod B ∘ₗ (WithLp.linearEquiv 2 𝕜 (U × W)).toLinearMap
  let bU := stdOrthonormalBasis 𝕜 U
  let bW := stdOrthonormalBasis 𝕜 W
  have horth' (w : W) (u : U) : inner 𝕜 (B w) (A u) = 0 := by
    rw [← inner_conj_symm, horth, map_zero]
  have hgram : Matrix.gram 𝕜 (fun i => C (bU.prod bW i)) =
      Matrix.fromBlocks (Matrix.gram 𝕜 (fun i => A (bU i))) 0 0
        (Matrix.gram 𝕜 (fun i => B (bW i))) := by
    ext i j
    cases i <;> cases j <;>
      simp [C, OrthonormalBasis.prod_apply, horth, horth']
  have hsq : C.normDet ^ 2 = A.normDet ^ 2 * B.normDet ^ 2 := by
    apply RCLike.ofReal_injective (K := 𝕜)
    rw [RCLike.ofReal_mul, C.normDet_sq_eq_det_gram (bU.prod bW), hgram,
      Matrix.det_fromBlocks_zero₂₁, ← A.normDet_sq_eq_det_gram bU,
      ← B.normDet_sq_eq_det_gram bW]
  exact (sq_eq_sq₀ C.normDet_nonneg (mul_nonneg A.normDet_nonneg B.normDet_nonneg)).mp
    (by simpa [mul_pow] using hsq)

end LinearMap

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The `m`-dimensional Jacobian `normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends
continuously on the map. -/
theorem ContinuousLinearMap.continuous_normDet :
    Continuous fun A : U →L[ℝ] V => A.normDet := by
  let b := stdOrthonormalBasis ℝ U
  have h (A : U →L[ℝ] V) :
      A.normDet = √(Matrix.gram ℝ fun i => A (b i)).det := by
    have hsq := (A : U →ₗ[ℝ] V).normDet_sq_eq_det_gram b
    simp only [RCLike.ofReal_real_eq_id, id] at hsq
    exact (hsq ▸ Real.sqrt_sq A.normDet_nonneg).symm
  simp_rw [h]
  refine Continuous.sqrt (Continuous.matrix_det (continuous_matrix fun i j => ?_))
  simp only [Matrix.gram_apply]
  fun_prop

omit [FiniteDimensional ℝ U] in
/-- The coarea Jacobian `A ↦ A.adjoint.normDet` of a continuous linear map `U →L[ℝ] V` depends
continuously on the map. -/
theorem ContinuousLinearMap.continuous_normDet_adjoint [CompleteSpace U] :
    Continuous fun A : U →L[ℝ] V => A.adjoint.normDet :=
  ContinuousLinearMap.continuous_normDet.comp ContinuousLinearMap.adjoint.continuous

namespace ContinuousLinearMap

/-- The Jacobian of the adjoint of a continuous linear map into a finite-dimensional inner product
space is positive exactly when the map is surjective. The domain need only be complete, not
finite-dimensional. -/
theorem normDet_adjoint_pos_iff {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F] {f : E →L[𝕜] F} :
    0 < f.adjoint.normDet ↔ Function.Surjective f := by
  rw [f.adjoint.normDet_nonneg.lt_iff_ne', Ne, LinearMap.normDet_eq_zero_iff_ker_ne_bot, not_not,
    ← f.orthogonal_range, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top, coe_coe]

/-- The Jacobian of the adjoint of a continuous linear map into a finite-dimensional inner product
space is nonzero exactly when the map is surjective. The domain need only be complete, not
finite-dimensional. -/
theorem normDet_adjoint_ne_zero_iff {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F] {f : E →L[𝕜] F} :
    f.adjoint.normDet ≠ 0 ↔ Function.Surjective f := by
  rw [← f.adjoint.normDet_nonneg.lt_iff_ne', normDet_adjoint_pos_iff]

/-- The Jacobian of the adjoint of a continuous linear map into a finite-dimensional inner product
space vanishes exactly when the map is not surjective. The domain need only be complete, not
finite-dimensional. -/
theorem normDet_adjoint_eq_zero_iff {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [CompleteSpace F] {f : E →L[𝕜] F} :
    f.adjoint.normDet = 0 ↔ ¬Function.Surjective f := by
  simpa using (normDet_adjoint_ne_zero_iff (f := f)).not

omit [FiniteDimensional ℝ V] in
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

omit [FiniteDimensional ℝ V] in
/-- Extending `T : U →ₗ[ℝ] V` to the Euclidean product `WithLp 2 (ℝ × U)` by a unit vector `e`
orthogonal to the range of `T`, `(a, u) ↦ a • e + T u`, does not change the Jacobian `normDet`. -/
theorem normDet_toSpanSingleton_coprod {e : V} (he : ‖e‖ = 1) {T : U →ₗ[ℝ] V}
    (hT : ∀ u, ⟪e, T u⟫ = 0) :
    ((toSpanSingleton ℝ V e).coprod T ∘ₗ (WithLp.linearEquiv 2 ℝ (ℝ × U)).toLinearMap).normDet =
      T.normDet := by
  rw [normDet_coprod_of_orthogonal _ _ (by simp [inner_smul_left, hT]),
    normDet_eq_norm_apply_one]
  simp [he]

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

omit [FiniteDimensional ℝ U] in
/-- The Jacobian of the adjoint of a linear functional is its norm. This is the coarea Jacobian
of a real-valued map, the norm of its gradient. -/
theorem ContinuousLinearMap.normDet_adjoint_eq_norm [CompleteSpace U] (A : U →L[ℝ] ℝ) :
    A.adjoint.normDet = ‖A‖ := by
  rw [LinearMap.normDet_eq_norm_apply_one, ContinuousLinearMap.coe_coe,
    ← ContinuousLinearMap.toSpanSingletonLIE_symm_apply ℝ U, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

section Hadamard

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Basis-wise Hadamard inequality for `normDet`**: on any orthonormal basis `b` of `E`,
`A.normDet ≤ ∏ i, ‖A (b i)‖`. The codomain `F` need not be finite-dimensional. -/
theorem LinearMap.normDet_le_prod_norm {ι : Type*} [Fintype ι] (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) :
    A.normDet ≤ ∏ i : ι, ‖A (b i)‖ := by
  classical
  have hsq : A.normDet ^ 2 ≤ (∏ i : ι, ‖A (b i)‖) ^ 2 := by
    have hgram := congrArg RCLike.re (A.normDet_sq_eq_det_gram b)
    rw [RCLike.ofReal_re] at hgram
    rw [hgram, ← Finset.prod_pow]
    exact Matrix.re_det_gram_le_prod_norm_sq (𝕜 := 𝕜) (fun i ↦ A (b i))
  exact (sq_le_sq₀ A.normDet_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).mp hsq

/-- **Hadamard's inequality for `normDet`**: `A.normDet ≤ ‖A‖ ^ Module.finrank 𝕜 E`. The codomain
`F` need not be finite-dimensional. -/
theorem ContinuousLinearMap.normDet_le_norm_pow (A : E →L[𝕜] F) :
    A.normDet ≤ ‖A‖ ^ Module.finrank 𝕜 E := by
  let b := stdOrthonormalBasis 𝕜 E
  calc
    A.normDet ≤ ∏ i : Fin (Module.finrank 𝕜 E), ‖A (b i)‖ := by
      simpa only [ContinuousLinearMap.coe_coe] using A.toLinearMap.normDet_le_prod_norm b
    _ ≤ ∏ _i : Fin (Module.finrank 𝕜 E), ‖A‖ := by
      gcongr with i
      simpa [b.orthonormal.1 i] using A.le_opNorm (b i)
    _ = ‖A‖ ^ Module.finrank 𝕜 E := by simp

/-- A conformal continuous linear map achieves equality in Hadamard's inequality for `normDet`:
`A.normDet = ‖A‖ ^ Module.finrank 𝕜 E`. -/
theorem IsConformalMap.normDet_eq_norm_pow {A : E →L[𝕜] F} (hA : IsConformalMap A) :
    A.normDet = ‖A‖ ^ Module.finrank 𝕜 E := by
  nontriviality E
  obtain ⟨c, _, li, rfl⟩ := hA
  simp [norm_smul]

/-- Equality `A.normDet = ‖A‖ ^ Module.finrank 𝕜 E` in Hadamard's inequality forces `A` to scale
the norm of every vector by `‖A‖`. -/
theorem ContinuousLinearMap.norm_apply_eq_of_normDet_eq_norm_pow {A : E →L[𝕜] F}
    (heq : A.normDet = ‖A‖ ^ Module.finrank 𝕜 E) (x : E) :
    ‖A x‖ = ‖A‖ * ‖x‖ := by
  rcases eq_or_ne A 0 with rfl | hA0
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := 𝕜) (M := E)).ne'
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let u : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hx0]
  obtain ⟨b, hb0⟩ := TauCeti.exists_orthonormalBasis_fin_apply_zero_eq hm hu
  have hprod : ‖A‖ ^ (m + 1) ≤ ∏ j : Fin (m + 1), ‖A (b j)‖ := by
    have hle := A.toLinearMap.normDet_le_prod_norm b
    simp only [ContinuousLinearMap.coe_coe] at hle
    rwa [heq, hm] at hle
  have hAu : ‖A u‖ = ‖A‖ := by
    by_contra hne
    have hlt : ‖A u‖ < ‖A‖ := lt_of_le_of_ne (by simpa [hu] using A.le_opNorm u) hne
    have hrest : ∏ j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A (b j)‖ ≤ ‖A‖ ^ m := by
      calc
        ∏ j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A (b j)‖ ≤
            ∏ _j ∈ Finset.univ.erase (0 : Fin (m + 1)), ‖A‖ := by
          gcongr with j
          simpa [b.orthonormal.1 j] using A.le_opNorm (b j)
        _ = ‖A‖ ^ m := by simp
    have hstrict : ∏ j : Fin (m + 1), ‖A (b j)‖ < ‖A‖ ^ (m + 1) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 0), hb0, pow_succ']
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrest (norm_nonneg _))
        (mul_lt_mul_of_pos_right hlt (pow_pos hApos m))
    exact hstrict.not_ge hprod
  simpa [u, map_smul, norm_smul, inv_mul_eq_iff_eq_mul₀ hx0, mul_comm ‖x‖ ‖A‖] using hAu

/-- **Equality case of Hadamard's inequality for `normDet`**: `A.normDet = ‖A‖ ^ Module.finrank 𝕜 E`
holds if and only if `A = 0` or `A` is conformal (`IsConformalMap A`). -/
theorem ContinuousLinearMap.normDet_eq_norm_pow_iff (A : E →L[𝕜] F) :
    A.normDet = ‖A‖ ^ Module.finrank 𝕜 E ↔ A = 0 ∨ IsConformalMap A := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · rcases eq_or_ne A 0 with rfl | hA0
    · exact .inl rfl
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    have hc : (‖A‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hApos.ne'
    refine .inr ⟨(‖A‖ : 𝕜), hc, ⟨(‖A‖ : 𝕜)⁻¹ • A.toLinearMap, fun x ↦ ?_⟩, ?_⟩
    · simp [norm_smul, A.norm_apply_eq_of_normDet_eq_norm_pow heq x,
        inv_mul_cancel_left₀ hApos.ne']
    · ext x
      simp [smul_smul, mul_inv_cancel₀ hc]
  · rintro (rfl | hconf)
    · simp
    · exact hconf.normDet_eq_norm_pow

end Hadamard

namespace LinearMap

section Bounds

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Lower bound on `normDet` from a uniform lower norm bound.** If `f` expands every vector by
at least `c ≥ 0`, then `f.normDet ≥ c ^ finrank 𝕜 E`. The codomain need not be finite
dimensional. -/
theorem pow_finrank_le_normDet_of_mul_norm_le (f : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ u : E, c * ‖u‖ ≤ ‖f u‖) :
    c ^ Module.finrank 𝕜 E ≤ f.normDet := by
  let g : E →ₗ[𝕜] f.range := f.rangeRestrict
  rw [← f.normDet_codRestrict f.mem_range_self, g.normDet_eq_prod_singularValues]
  calc c ^ Module.finrank 𝕜 E
      = ∏ _ ∈ Finset.range (Module.finrank 𝕜 E), c := by simp
    _ ≤ ∏ i ∈ Finset.range (Module.finrank 𝕜 E), g.singularValues i := by
        gcongr with i hi
        rw [← g.norm_apply_rightSingularBasis ⟨i, Finset.mem_range.mp hi⟩, ← Submodule.norm_coe]
        simpa [g] using hf (g.rightSingularBasis ⟨i, Finset.mem_range.mp hi⟩)

/-- **Upper bound on `normDet` from a uniform upper norm bound.** If `‖f u‖ ≤ c * ‖u‖` for all
`u`, then `f.normDet ≤ c ^ finrank 𝕜 E`. The codomain need not be finite dimensional. -/
theorem normDet_le_pow_finrank_of_norm_le (f : E →ₗ[𝕜] F) {c : ℝ}
    (hf : ∀ u : E, ‖f u‖ ≤ c * ‖u‖) :
    f.normDet ≤ c ^ Module.finrank 𝕜 E := by
  let g : E →ₗ[𝕜] f.range := f.rangeRestrict
  rw [← f.normDet_codRestrict f.mem_range_self, g.normDet_eq_prod_singularValues]
  calc ∏ i ∈ Finset.range (Module.finrank 𝕜 E), g.singularValues i
      ≤ ∏ _ ∈ Finset.range (Module.finrank 𝕜 E), c := by
        gcongr with i hi
        · intro j _
          exact g.singularValues_nonneg j
        · rw [← g.norm_apply_rightSingularBasis ⟨i, Finset.mem_range.mp hi⟩, ← Submodule.norm_coe]
          simpa [g] using hf (g.rightSingularBasis ⟨i, Finset.mem_range.mp hi⟩)
    _ = c ^ Module.finrank 𝕜 E := by simp

/-- **Exact `normDet` of a scalar similarity.** If `‖f u‖ = c * ‖u‖` for all `u`, then
`f.normDet = c ^ finrank 𝕜 E`. -/
theorem normDet_eq_pow_finrank_of_norm_eq (f : E →ₗ[𝕜] F) {c : ℝ}
    (hf : ∀ u : E, ‖f u‖ = c * ‖u‖) :
    f.normDet = c ^ Module.finrank 𝕜 E := by
  nontriviality E
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hc : 0 ≤ c :=
    nonneg_of_mul_nonneg_left (hf u ▸ norm_nonneg (f u)) (norm_pos_iff.mpr hu)
  exact le_antisymm
    (f.normDet_le_pow_finrank_of_norm_le fun v ↦ (hf v).le)
    (f.pow_finrank_le_normDet_of_mul_norm_le hc fun v ↦ (hf v).ge)

end Bounds

section Orthogonal

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Splitting `normDet` along a submodule and its orthogonal complement.** If `f` maps `K` and
`Kᗮ` to mutually orthogonal subspaces of `F`, then `f.normDet` is the product of the `normDet`s
of `f` restricted to `K` and to `Kᗮ`. -/
theorem normDet_eq_mul_normDet_orthogonal (f : E →ₗ[𝕜] F) (K : Submodule 𝕜 E)
    (horth : ∀ u ∈ K, ∀ w ∈ Kᗮ, inner 𝕜 (f u) (f w) = 0) :
    f.normDet = (f ∘ₗ K.subtype).normDet * (f ∘ₗ Kᗮ.subtype).normDet := by
  let Ψ : WithLp 2 (K × Kᗮ) ≃ₗᵢ[𝕜] E := K.orthogonalDecomposition.symm
  have hcomp : f ∘ₗ Ψ.toLinearIsometry.toLinearMap =
      ((f ∘ₗ K.subtype).coprod (f ∘ₗ Kᗮ.subtype)) ∘ₗ
        (WithLp.linearEquiv 2 𝕜 (K × Kᗮ)).toLinearMap := by
    ext p
    simp [Ψ]
  calc f.normDet
      = (f ∘ₗ Ψ.toLinearIsometry.toLinearMap).normDet := by
        rw [normDet_comp_of_finrank_eq Ψ.toLinearIsometry.toLinearMap f Ψ.toLinearEquiv.finrank_eq,
          Ψ.toLinearIsometry.normDet_eq_one, mul_one]
    _ = (f ∘ₗ K.subtype).normDet * (f ∘ₗ Kᗮ.subtype).normDet := by
        rw [hcomp, normDet_coprod_of_orthogonal _ _ fun u w ↦ horth u.val u.property w.val
            w.property]

/-- **Splitting `normDet` along a nonzero vector and its orthogonal complement.** If `u ≠ 0` and
`f u` is orthogonal to `f w` for every `w ∈ (𝕜 ∙ u)ᗮ`, then `f.normDet` is the radial stretch
`‖f u‖ / ‖u‖` times the `normDet` of `f` restricted to `(𝕜 ∙ u)ᗮ`. -/
theorem normDet_eq_div_mul_normDet_orthogonal (f : E →ₗ[𝕜] F) {u : E} (hu : u ≠ 0)
    (horth : ∀ w ∈ (𝕜 ∙ u)ᗮ, inner 𝕜 (f u) (f w) = 0) :
    f.normDet = ‖f u‖ / ‖u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
  have horth' : ∀ x ∈ 𝕜 ∙ u, ∀ w ∈ (𝕜 ∙ u)ᗮ, inner 𝕜 (f x) (f w) = 0 := by
    intro x hx w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [inner_smul_left, horth w hw]
  have hline : (f ∘ₗ (𝕜 ∙ u).subtype).normDet = ‖f u‖ / ‖u‖ := by
    have hscale : ∀ x : 𝕜 ∙ u, ‖(f ∘ₗ (𝕜 ∙ u).subtype) x‖ = (‖f u‖ / ‖u‖) * ‖x‖ := by
      intro x
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
      have hxu : (x : E) = a • u := ha.symm
      simp only [comp_apply, Submodule.coe_subtype, ← Submodule.norm_coe, hxu, map_smul, norm_smul]
      field_simp [norm_ne_zero_iff.mpr hu]
    rw [(f ∘ₗ (𝕜 ∙ u).subtype).normDet_eq_pow_finrank_of_norm_eq hscale,
      finrank_span_singleton hu, pow_one]
  rw [f.normDet_eq_mul_normDet_orthogonal (𝕜 ∙ u) horth', hline]

/-- **Splitting `normDet` along a unit vector and its orthogonal complement.** If `‖u‖ = 1` and
`f u` is orthogonal to `f w` for every `w ∈ (𝕜 ∙ u)ᗮ`, then
`f.normDet = ‖f u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet`. -/
theorem normDet_eq_norm_mul_normDet_orthogonal (f : E →ₗ[𝕜] F) {u : E} (hu : ‖u‖ = 1)
    (horth : ∀ w ∈ (𝕜 ∙ u)ᗮ, inner 𝕜 (f u) (f w) = 0) :
    f.normDet = ‖f u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  rw [f.normDet_eq_div_mul_normDet_orthogonal hu0 horth, hu, div_one]

end Orthogonal

end LinearMap
