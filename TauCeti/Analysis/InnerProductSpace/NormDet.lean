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

* `ContinuousLinearMap.continuous_normDet`, `ContinuousLinearMap.continuous_normDet_adjoint`:
  the Jacobian `normDet` and the coarea Jacobian `A ↦ A†.normDet` are continuous.
* `LinearMap.normDet_eq_norm_apply_one`: for a map from `ℝ`, the Jacobian is the norm of the
  image of `1`.
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
* `LinearMap.pow_finrank_le_normDet_of_norm_le`, `LinearMap.normDet_le_pow_finrank_of_norm_le`,
  `LinearMap.normDet_eq_pow_finrank_of_norm_eq`: uniform lower, upper, and exact norm bounds on a
  linear map control its `normDet` by the `finrank`-th power of the factor.
* `LinearMap.normDet_eq_div_mul_normDet_orthogonal`,
  `LinearMap.normDet_eq_norm_mul_normDet_orthogonal`: when `f u` is orthogonal to the image of
  `(𝕜 ∙ u)ᗮ`, the Jacobian splits into the radial stretch `‖f u‖ / ‖u‖` times the Jacobian on
  `(𝕜 ∙ u)ᗮ`.
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

namespace LinearMap

section Bounds

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- At each singular value of index `i < finrank 𝕜 E`, a linear map between finite-dimensional
inner product spaces stretches the corresponding unit eigenvector of `f† f` by
`singularValues i`. -/
private theorem exists_unit_norm_apply_eq_singularValues [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F)
    {i : ℕ} (hi : i < Module.finrank 𝕜 E) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖f v‖ = f.singularValues i := by
  have hS := f.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis rfl
  let j : Fin (Module.finrank 𝕜 E) := ⟨i, hi⟩
  refine ⟨b j, b.orthonormal.1 j, ?_⟩
  have heig : inner 𝕜 (b j) ((f.adjoint ∘ₗ f) (b j)) = (hS.eigenvalues rfl j : 𝕜) := by
    rw [hS.apply_eigenvectorBasis rfl j, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    simp
  have hnorm : ((‖f (b j)‖ ^ 2 : ℝ) : 𝕜) = (hS.eigenvalues rfl j : 𝕜) := by
    rw [← heig, comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsq : ‖f (b j)‖ ^ 2 = f.singularValues i ^ 2 := by
    rw [f.sq_singularValues_of_lt rfl hi]
    exact RCLike.ofReal_injective hnorm
  exact (sq_eq_sq₀ (norm_nonneg _) (f.singularValues_nonneg i)).mp hsq

/-- **Lower bound on `normDet` from a uniform lower norm bound.** If `f` expands every vector by
at least `c ≥ 0`, then `f.normDet ≥ c ^ finrank 𝕜 E`. The codomain need not be finite
dimensional. -/
theorem pow_finrank_le_normDet_of_norm_le (f : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ u : E, c * ‖u‖ ≤ ‖f u‖) :
    c ^ Module.finrank 𝕜 E ≤ f.normDet := by
  let g : E →ₗ[𝕜] f.range := f.rangeRestrict
  rw [← f.normDet_codRestrict f.mem_range_self, g.normDet_eq_prod_singularValues]
  calc c ^ Module.finrank 𝕜 E
      = ∏ _ ∈ Finset.range (Module.finrank 𝕜 E), c := by simp
    _ ≤ ∏ i ∈ Finset.range (Module.finrank 𝕜 E), g.singularValues i := by
        gcongr with i hi
        obtain ⟨v, hv1, hgv⟩ := exists_unit_norm_apply_eq_singularValues g (Finset.mem_range.mp hi)
        rw [← hgv]
        simpa [g, hv1] using hf v

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
        · obtain ⟨v, hv1, hgv⟩ :=
            exists_unit_norm_apply_eq_singularValues g (Finset.mem_range.mp hi)
          rw [← hgv]
          simpa [g, hv1] using hf v
    _ = c ^ Module.finrank 𝕜 E := by simp

/-- **Exact `normDet` of a scalar similarity.** If `‖f u‖ = c * ‖u‖` for all `u`, then
`f.normDet = c ^ finrank 𝕜 E`. -/
theorem normDet_eq_pow_finrank_of_norm_eq (f : E →ₗ[𝕜] F) {c : ℝ}
    (hf : ∀ u : E, ‖f u‖ = c * ‖u‖) :
    f.normDet = c ^ Module.finrank 𝕜 E := by
  by_cases h0 : Module.finrank 𝕜 E = 0
  · let g : E →ₗ[𝕜] f.range := f.rangeRestrict
    rw [← f.normDet_codRestrict f.mem_range_self, g.normDet_eq_prod_singularValues, h0]
    simp
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
    obtain ⟨u, hu⟩ := exists_ne (0 : E)
    have hc : 0 ≤ c :=
      nonneg_of_mul_nonneg_left (hf u ▸ norm_nonneg (f u)) (norm_pos_iff.mpr hu)
    exact le_antisymm
      (f.normDet_le_pow_finrank_of_norm_le fun v ↦ (hf v).le)
      (f.pow_finrank_le_normDet_of_norm_le hc fun v ↦ (hf v).ge)

end Bounds

section OrthogonalLine

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Over any `RCLike` scalar field, the one-dimensional `normDet` of `a ↦ a • y` is `‖y‖`. -/
private theorem normDet_toSpanSingleton (y : F) : (toSpanSingleton 𝕜 F y).normDet = ‖y‖ := by
  have h := (toSpanSingleton 𝕜 F y).normDet_sq_eq_det_gram (OrthonormalBasis.singleton Unit 𝕜)
  rw [Matrix.det_unique] at h
  simp only [OrthonormalBasis.singleton_apply, Matrix.gram_apply, toSpanSingleton_apply, one_smul,
    inner_self_eq_norm_sq_to_K] at h
  have hreal : (toSpanSingleton 𝕜 F y).normDet ^ 2 = ‖y‖ ^ 2 :=
    RCLike.ofReal_injective (K := 𝕜) (by simpa using h)
  exact (sq_eq_sq₀ (normDet_nonneg _) (norm_nonneg y)).mp hreal

/-- **Splitting `normDet` along a nonzero vector and its orthogonal complement.** If `u ≠ 0` and
`f u` is orthogonal to `f w` for every `w ∈ (𝕜 ∙ u)ᗮ`, then `f.normDet` is the radial stretch
`‖f u‖ / ‖u‖` times the `normDet` of `f` restricted to `(𝕜 ∙ u)ᗮ`. -/
theorem normDet_eq_div_mul_normDet_orthogonal (f : E →ₗ[𝕜] F) {u : E} (hu : u ≠ 0)
    (horth : ∀ w ∈ (𝕜 ∙ u)ᗮ, inner 𝕜 (f u) (f w) = 0) :
    f.normDet = ‖f u‖ / ‖u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
  let e : E := (‖u‖ : 𝕜)⁻¹ • u
  have he_norm : ‖e‖ = 1 := by
    simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  -- Map the Euclidean product `𝕜 × (𝕜 ∙ u)ᗮ` isometrically onto `E` via `(a, w) ↦ a • e + w`.
  let ψ : WithLp 2 (𝕜 × (𝕜 ∙ u)ᗮ) →ₗ[𝕜] E :=
    ((toSpanSingleton 𝕜 E e).coprod (𝕜 ∙ u)ᗮ.subtype) ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (𝕜 × (𝕜 ∙ u)ᗮ)).toLinearMap
  have hψ_iso : ∀ p : WithLp 2 (𝕜 × (𝕜 ∙ u)ᗮ), ‖ψ p‖ = ‖p‖ := by
    intro p
    have he_mem : p.fst • e ∈ 𝕜 ∙ u :=
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
    have hinner : inner 𝕜 (p.fst • e) (p.snd : E) = 0 :=
      (Submodule.mem_orthogonal (𝕜 ∙ u) (p.snd : E)).mp p.snd.2 _ he_mem
    have hsq : ‖ψ p‖ ^ 2 = ‖p‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      calc ‖p.fst • e + (p.snd : E)‖ ^ 2
          = ‖p.fst • e‖ ^ 2 + ‖(p.snd : E)‖ ^ 2 := by
            simpa only [sq] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p.fst • e) (p.snd : E) hinner
        _ = ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 := by
            rw [norm_smul, he_norm, mul_one, Submodule.norm_coe]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  let Ψ : WithLp 2 (𝕜 × (𝕜 ∙ u)ᗮ) →ₗᵢ[𝕜] E := { toLinearMap := ψ, norm_map' := hψ_iso }
  have hdim : Module.finrank 𝕜 (WithLp 2 (𝕜 × (𝕜 ∙ u)ᗮ)) = Module.finrank 𝕜 E := by
    rw [(WithLp.linearEquiv 2 𝕜 (𝕜 × (𝕜 ∙ u)ᗮ)).finrank_eq, Module.finrank_prod,
      Module.finrank_self, ← finrank_span_singleton (K := 𝕜) hu]
    exact (𝕜 ∙ u).finrank_add_finrank_orthogonal
  have hcomp : f ∘ₗ Ψ.toLinearMap =
      ((toSpanSingleton 𝕜 F (f e)).coprod (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype)) ∘ₗ
        (WithLp.linearEquiv 2 𝕜 (𝕜 × (𝕜 ∙ u)ᗮ)).toLinearMap := by
    ext p
    simp [Ψ, ψ]
  have hcoprod := normDet_coprod_of_orthogonal (toSpanSingleton 𝕜 F (f e))
    (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype) fun a w ↦ by
      simp [e, inner_smul_left, horth w.1 w.2]
  have hfe : ‖f e‖ = ‖f u‖ / ‖u‖ := by
    rw [show f e = (‖u‖ : 𝕜)⁻¹ • f u from f.map_smul _ _, norm_smul, norm_inv,
      RCLike.norm_ofReal, abs_norm, inv_mul_eq_div]
  calc f.normDet
      = (f ∘ₗ Ψ.toLinearMap).normDet := by
        rw [normDet_comp_of_finrank_eq Ψ.toLinearMap f hdim, Ψ.normDet_eq_one, mul_one]
    _ = (toSpanSingleton 𝕜 F (f e)).normDet * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
        rw [hcomp, hcoprod]
    _ = ‖f u‖ / ‖u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
        rw [normDet_toSpanSingleton, hfe]

/-- **Splitting `normDet` along a unit vector and its orthogonal complement.** If `‖u‖ = 1` and
`f u` is orthogonal to `f w` for every `w ∈ (𝕜 ∙ u)ᗮ`, then
`f.normDet = ‖f u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet`. -/
theorem normDet_eq_norm_mul_normDet_orthogonal (f : E →ₗ[𝕜] F) {u : E} (hu : ‖u‖ = 1)
    (horth : ∀ w ∈ (𝕜 ∙ u)ᗮ, inner 𝕜 (f u) (f w) = 0) :
    f.normDet = ‖f u‖ * (f ∘ₗ (𝕜 ∙ u)ᗮ.subtype).normDet := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  rw [f.normDet_eq_div_mul_normDet_orthogonal hu0 horth, hu, div_one]

end OrthogonalLine

end LinearMap
