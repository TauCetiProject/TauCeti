/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# The signature normal form of a self-adjoint operator

Let `A` be a self-adjoint operator on a finite-dimensional real inner product space `E`, let `P₋`
and `P₊` be the orthogonal projections onto its negative and positive spectral subspaces, and let
`T = (A * A) ^ (1 / 4)`, the positive square root of the absolute value `|A| = (A * A) ^ (1 / 2)`.
Then `A = T (P₊ - P₋) T` (`ContinuousLinearMap.eq_rpow_mul_self_mul_sub_mul_rpow_mul_self`): on an
eigenvector with eigenvalue `μ` the right side acts by `√|μ| · sign μ · √|μ| = μ`. Since `T` is
self-adjoint, the quadratic form of `A` is therefore a difference of two squared norms,

  `⟪A v, v⟫ = ‖P₊ (T v)‖ ^ 2 - ‖P₋ (T v)‖ ^ 2`

(`ContinuousLinearMap.inner_apply_self_eq_norm_sq_sub_norm_sq`). The operator `T` commutes with
every spectral projection of `A`
(`ContinuousLinearMap.commute_rpow_mul_self_starProjection_pointSpectralSubspace`), so it maps the
negative and positive spectral subspaces into themselves, and it is invertible when `A` is
(`IsUnit.cfcRpow`). So for a nondegenerate symmetric form the linear change of variables `v ↦ T v`
carries its quadratic form to the standard form `-‖u‖ ^ 2 + ‖w‖ ^ 2`, in which `u` and `w` are the
components along the negative and positive spectral subspaces of `A`. This is Sylvester's law of
inertia made canonical: no eigenbasis is chosen.

For a smooth family of invertible self-adjoint operators, the operators `T`
(`ContDiffOn.rpow_mul_self`) and the spectral projections
(`ContDiffOn.starProjection_pointSpectralSubspace_Iio_zero` and
`ContDiffOn.starProjection_pointSpectralSubspace_Ioi_zero`) are smooth families as well. Applied to
a family of nondegenerate Hessians along a parameter space, this is the linear step of a parametric
Morse lemma: once a function has been brought to the form `c + ½ H (w, w)` with a smoothly varying
nondegenerate form `H`, a smooth fibrewise linear change of variables preserving the splitting into
negative and positive parts turns it into `c - ‖u‖ ^ 2 + ‖w‖ ^ 2`.

## Main results

* `ContinuousLinearMap.rpow_mul_self_apply_of_apply_eq_smul`: on an eigenvector of `A` with
  eigenvalue `μ`, the power `(A * A) ^ r` acts by `(μ ^ 2) ^ r`.
* `ContinuousLinearMap.starProjection_pointSpectralSubspace_apply_of_apply_eq_smul`: on such an
  eigenvector, the spectral projection selected by `Ω` acts by the indicator of `Ω` at `μ`.
* `ContinuousLinearMap.commute_rpow_mul_self_starProjection_pointSpectralSubspace`: the powers of
  `A * A` commute with the spectral projections of `A`.
* `ContinuousLinearMap.eq_rpow_mul_self_mul_sub_mul_rpow_mul_self`: the factorization
  `A = T (P₊ - P₋) T`.
* `ContinuousLinearMap.inner_apply_self_eq_norm_sq_sub_norm_sq`: the quadratic form of `A` is
  `‖P₊ (T v)‖ ^ 2 - ‖P₋ (T v)‖ ^ 2`.

## References

* R. Bhatia, *Matrix Analysis*, Springer, 1997, Chapter V (matrix functions).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →L[ℝ] E}

/-- On an eigenvector of a self-adjoint operator `A` with eigenvalue `μ`, every real power of
`A * A` acts by the same power of `μ ^ 2`. -/
theorem rpow_mul_self_apply_of_apply_eq_smul (hA : IsSelfAdjoint A) {μ : ℝ} {v : E}
    (hv : A v = μ • v) (r : ℝ) : ((A * A) ^ r) v = (μ ^ 2) ^ r • v := by
  have hpos : 0 ≤ A * A := by simpa only [hA.star_eq] using star_mul_self_nonneg A
  have heig : (A * A) v = (μ ^ 2 : ℝ) • v := by
    rw [mul_apply_eq_comp, hv, map_smul, hv, smul_smul, sq]
  rw [CFC.rpow_eq_cfc_real hpos, cfc_apply_of_apply_eq_smul (fun x : ℝ ↦ x ^ r) heig
    (nonneg_iff_isPositive.mp hpos).isSelfAdjoint]
  -- The scalar is coerced from `ℝ` to `ℝ` by `RCLike.ofReal`, which is the identity.
  rfl

/-- On an eigenvector of a self-adjoint operator `A` with eigenvalue `μ`, the orthogonal
projection onto the spectral subspace selected by `Ω` acts by the indicator of `Ω` at `μ`: it
fixes the eigenvector when `μ ∈ Ω` and kills it otherwise. -/
theorem starProjection_pointSpectralSubspace_apply_of_apply_eq_smul (hA : IsSelfAdjoint A)
    (Ω : Set ℝ) {μ : ℝ} {v : E} (hv : A v = μ • v) :
    (Module.End.pointSpectralSubspace A.toLinearMap Ω).starProjection v =
      Ω.indicator (1 : ℝ → ℝ) μ • v := by
  rw [← cfc_indicator_eq_starProjection Ω hA, cfc_apply_of_apply_eq_smul _ hv hA,
    RCLike.ofReal_real_eq_id, id_eq]

/-- **The powers of `A * A` preserve the spectral splitting of `A`.** For a self-adjoint `A`,
every real power of `A * A` commutes with the orthogonal projection onto every spectral subspace
of `A`. In particular it maps the negative and positive spectral subspaces of `A` into
themselves. -/
theorem commute_rpow_mul_self_starProjection_pointSpectralSubspace (hA : IsSelfAdjoint A)
    (r : ℝ) (Ω : Set ℝ) :
    Commute ((A * A) ^ r) (Module.End.pointSpectralSubspace A.toLinearMap Ω).starProjection := by
  have hpos : 0 ≤ A * A := by simpa only [hA.star_eq] using star_mul_self_nonneg A
  -- The projection is a function of `A`, so it commutes with `A * A` and then with its powers.
  have hP : Commute (A * A) (Module.End.pointSpectralSubspace A.toLinearMap Ω).starProjection := by
    rw [← cfc_indicator_eq_starProjection Ω hA]
    exact ((Commute.refl A).cfc_real _).symm.mul_left ((Commute.refl A).cfc_real _).symm
  rw [CFC.rpow_eq_cfc_real hpos]
  exact hP.cfc_real _

/-- **The signature factorization.** A self-adjoint operator `A` is `T (P₊ - P₋) T`, where
`T = (A * A) ^ (1 / 4)` is the square root of its absolute value and `P₊`, `P₋` are the orthogonal
projections onto its positive and negative spectral subspaces. -/
theorem eq_rpow_mul_self_mul_sub_mul_rpow_mul_self (hA : IsSelfAdjoint A) :
    A = (A * A) ^ (1 / 4 : ℝ) *
      ((Module.End.pointSpectralSubspace A.toLinearMap (Ioi 0)).starProjection -
        (Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection) *
      (A * A) ^ (1 / 4 : ℝ) := by
  have hs := isSelfAdjoint_iff_isSymmetric.mp hA
  apply coe_injective
  -- Both sides act by `μ` on the eigenvector basis of `A`.
  refine (hs.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_
  set μ := hs.eigenvalues rfl i
  have hv : A (hs.eigenvectorBasis rfl i) = μ • hs.eigenvectorBasis rfl i :=
    hs.apply_eigenvectorBasis rfl i
  have hT := rpow_mul_self_apply_of_apply_eq_smul hA hv (1 / 4)
  have hP (Ω : Set ℝ) := starProjection_pointSpectralSubspace_apply_of_apply_eq_smul hA Ω hv
  rw [OrthonormalBasis.coe_toBasis, coe_coe, coe_coe, mul_apply_eq_comp, mul_apply_eq_comp, hT,
    map_smul, sub_apply, hP, hP, ← sub_smul, map_smul, map_smul, hT, smul_smul, smul_smul, hv]
  congr 1
  -- The scalar identity `μ = √|μ| · (𝟙_{μ > 0} - 𝟙_{μ < 0}) · √|μ|`.
  have hq : (μ ^ 2) ^ (1 / 4 : ℝ) * (μ ^ 2) ^ (1 / 4 : ℝ) = |μ| := by
    rw [← Real.rpow_add' (sq_nonneg μ) (by norm_num), show (1 / 4 + 1 / 4 : ℝ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy μ 0 with hμ | hμ | hμ
  · rw [indicator_of_notMem (notMem_Ioi.mpr hμ.le), indicator_of_mem (mem_Iio.mpr hμ),
      Pi.one_apply]
    linear_combination hq + abs_of_neg hμ
  · simp [hμ]
  · rw [indicator_of_mem (mem_Ioi.mpr hμ), indicator_of_notMem (notMem_Iio.mpr hμ.le),
      Pi.one_apply]
    linear_combination -hq - abs_of_pos hμ

/-- **The quadratic form of a self-adjoint operator as a difference of squares.** For a
self-adjoint operator `A` with orthogonal projections `P₊`, `P₋` onto its positive and negative
spectral subspaces, and `T = (A * A) ^ (1 / 4)` the square root of its absolute value,
`⟪A v, v⟫ = ‖P₊ (T v)‖ ^ 2 - ‖P₋ (T v)‖ ^ 2` for every `v`. -/
theorem inner_apply_self_eq_norm_sq_sub_norm_sq (hA : IsSelfAdjoint A) (v : E) :
    ⟪A v, v⟫_ℝ =
      ‖(Module.End.pointSpectralSubspace A.toLinearMap (Ioi 0)).starProjection
          (((A * A) ^ (1 / 4 : ℝ)) v)‖ ^ 2 -
        ‖(Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection
          (((A * A) ^ (1 / 4 : ℝ)) v)‖ ^ 2 := by
  have hT : IsSelfAdjoint ((A * A) ^ (1 / 4 : ℝ)) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
  -- Move one factor `T` across the inner product, then expand the two projections.
  conv_lhs => rw [eq_rpow_mul_self_mul_sub_mul_rpow_mul_self hA]
  have hsq (K : Submodule ℝ E) (y : E) : ⟪K.starProjection y, y⟫_ℝ = ‖K.starProjection y‖ ^ 2 := by
    rw [Submodule.starProjection_apply, Submodule.norm_coe,
      ← Submodule.re_inner_starProjection_eq_normSq, RCLike.re_to_real,
      Submodule.starProjection_apply]
  have hTsymm (x y : E) :
      ⟪((A * A) ^ (1 / 4 : ℝ)) x, y⟫_ℝ = ⟪x, ((A * A) ^ (1 / 4 : ℝ)) y⟫_ℝ :=
    hT.isSymmetric x y
  rw [mul_apply_eq_comp, mul_apply_eq_comp, hTsymm, sub_apply, inner_sub_left, hsq, hsq]

end ContinuousLinearMap
