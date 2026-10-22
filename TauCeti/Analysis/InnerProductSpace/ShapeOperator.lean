/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
public import TauCeti.LinearAlgebra.Eigenspace.Anticommute

/-!
# The shape operator of a map into a real inner product space

Let `i : V → E` be a map from a finite-dimensional real normed space into a real inner product
space whose derivative `L = Di(x)` is injective, so that `g(v, w) = ⟪L v, L w⟫` is a metric on
`V`, the metric induced by `i`. For a vector `ν : E`, the **shape operator** `S_ν` is the
endomorphism of `V` determined by

`g(S_ν v, w) = ⟪ν, B(v, w)⟫`,

where `B` is the second fundamental form `TauCeti.secondFundamentalForm ℝ i x`. It depends
linearly on `ν`, only through the normal component of `ν`, and it is `g`-self-adjoint for a `C²`
map.

The shape operator controls the squared-distance function `ρ_a(y) = ‖i y - a‖²`. At a critical
point `x`, where `a - i x` is normal, the Hessian of `ρ_a` is `2 g((1 - S_{a - i x}) v, w)`, so its
null space is the `1`-eigenspace of `S_{a - i x}`. Along the normal line `a = i x + t ν` with
`t ≠ 0` this is the `t⁻¹`-eigenspace of `S_ν`: such a point `i x + t ν` is a focal point of `i`
at `x` exactly when `t⁻¹` is an eigenvalue of `S_ν`, with multiplicity the dimension of that
eigenspace. A zero eigenvalue of `S_ν` gives no focal point, and `i x` itself (`t = 0`) is never
one.

For a holomorphic immersion into a complex inner product space, with the real inner product
`re ⟪x, y⟫`, the complex identities of the second fundamental form give

`S_ν J = -J S_ν` and `S_{Jν} = J S_ν`,

where `J` is multiplication by `I`. Hence `J` identifies the `κ`- and `-κ`-eigenspaces of `S_ν`
and preserves its generalized `0`-eigenspaces: the principal curvatures of a complex submanifold
come in pairs `±κ` with equal multiplicities, and on every normal line the focal points at
distances `t` and `-t` have the same multiplicity.

## Main definitions

* `TauCeti.shapeOperator i x ν`: the shape operator `S_ν` of `i` at `x`.

## Main results

* `TauCeti.inner_fderiv_shapeOperator_apply`: the defining identity `g(S_ν v, w) = ⟪ν, B(v, w)⟫`.
* `TauCeti.eq_shapeOperator_iff`: the shape operator is the unique endomorphism satisfying it.
* `ContDiffAt.inner_fderiv_shapeOperator_apply_comm`: the shape operator is `g`-self-adjoint.
* `TauCeti.fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator`: the Hessian of squared
  distance at a critical point is `2 g((1 - S_{a - i x}) v, w)`.
* `TauCeti.ker_fderiv_fderiv_norm_sq_sub_comp`: the null space of that Hessian is the
  `1`-eigenspace of `S_{a - i x}`.
* `TauCeti.ker_fderiv_fderiv_norm_sq_sub_add_smul_comp`: at the point `i x + t ν` of a normal
  line with `t ≠ 0`, this is the `t⁻¹`-eigenspace of `S_ν`.
* `ContDiffAt.shapeOperator_apply_I_smul`, `ContDiffAt.shapeOperator_I_smul_apply`: the identities
  `S_ν J = -J S_ν` and `S_{Jν} = J S_ν` for a holomorphic immersion.
* `ContDiffAt.finrank_genEigenspace_shapeOperator_neg`: the paired principal curvatures.
* `ContDiffAt.I_smul_mem_genEigenspace_shapeOperator_zero`: the zero principal curvature has a
  complex eigenspace.
* `ContDiffAt.finrank_ker_fderiv_fderiv_norm_sq_sub_sub_comp`: the symmetric focal points.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 6 and 7.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX.
-/

public section

open Complex Function Module Module.End
open scoped RealInnerProductSpace

namespace TauCeti

section Real

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {i : V → E} {x : V}

open scoped Classical in
/-- The **shape operator** `S_ν` of `i : V → E` at `x` in the direction `ν`: the endomorphism of
`V` with `⟪Di(x) (S_ν v), Di(x) w⟫ = ⟪ν, B(v, w)⟫` for all `v` and `w`, where `B` is the second
fundamental form. It is defined when `Di(x)` is injective, so that the induced metric
`⟪Di(x) v, Di(x) w⟫` is nondegenerate, and is `0` otherwise. -/
noncomputable def shapeOperator (i : V → E) (x : V) (ν : E) : Module.End ℝ V :=
  if h : Injective (fderiv ℝ i x) then
    LinearMap.BilinForm.symmCompOfNondegenerate
      ((ContinuousLinearMap.toLinearMap₁₂ (secondFundamentalForm ℝ i x)).compr₂ (innerₗ E ν))
      (LinearMap.BilinForm.comp (innerₗ E) (fderiv ℝ i x : V →ₗ[ℝ] E) (fderiv ℝ i x))
      (nondegenerate_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) h)
  else 0

/-- **The defining identity of the shape operator.** For an immersion, the induced metric pairs
`S_ν v` with `w` as `ν` pairs with the second fundamental form `B(v, w)`. -/
theorem inner_fderiv_shapeOperator_apply (h : Injective (fderiv ℝ i x)) (ν : E) (v w : V) :
    ⟪fderiv ℝ i x (shapeOperator i x ν v), fderiv ℝ i x w⟫ =
      ⟪ν, secondFundamentalForm ℝ i x v w⟫ := by
  have key := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    ((ContinuousLinearMap.toLinearMap₁₂ (secondFundamentalForm ℝ i x)).compr₂ (innerₗ E ν))
    (nondegenerate_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) h) w v
  simp only [LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe, innerₗ_apply_apply,
    LinearMap.compr₂_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at key
  simpa only [shapeOperator, h, ↓reduceDIte] using key

/-- The shape operator of a map whose derivative is not injective is `0` by convention. -/
theorem shapeOperator_of_not_injective (h : ¬Injective (fderiv ℝ i x)) (ν : E) :
    shapeOperator i x ν = 0 := by
  simp [shapeOperator, h]

/-- **Uniqueness of the shape operator.** For an immersion, `S_ν` is the only endomorphism `S`
with `⟪Di(x) (S v), Di(x) w⟫ = ⟪ν, B(v, w)⟫` for all `v` and `w`. -/
theorem eq_shapeOperator_iff (h : Injective (fderiv ℝ i x)) {ν : E} {S : Module.End ℝ V} :
    S = shapeOperator i x ν ↔
      ∀ v w, ⟪fderiv ℝ i x (S v), fderiv ℝ i x w⟫ = ⟪ν, secondFundamentalForm ℝ i x v w⟫ := by
  refine ⟨fun hS ↦ hS ▸ inner_fderiv_shapeOperator_apply h ν, fun hS ↦ ?_⟩
  exact LinearMap.ext fun v ↦ eq_of_forall_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) h
    fun w ↦ by simp only [ContinuousLinearMap.coe_coe, hS, inner_fderiv_shapeOperator_apply h]

/-- The shape operator is additive in the normal direction. -/
@[simp]
theorem shapeOperator_add (ν ν' : E) :
    shapeOperator i x (ν + ν') = shapeOperator i x ν + shapeOperator i x ν' := by
  by_cases h : Injective (fderiv ℝ i x)
  · refine ((eq_shapeOperator_iff h).2 fun v w ↦ ?_).symm
    simp [inner_add_left, inner_fderiv_shapeOperator_apply h]
  · simp [shapeOperator_of_not_injective h]

/-- The shape operator is homogeneous in the normal direction. -/
@[simp]
theorem shapeOperator_smul (c : ℝ) (ν : E) :
    shapeOperator i x (c • ν) = c • shapeOperator i x ν := by
  by_cases h : Injective (fderiv ℝ i x)
  · refine ((eq_shapeOperator_iff h).2 fun v w ↦ ?_).symm
    simp [real_inner_smul_left, inner_fderiv_shapeOperator_apply h]
  · simp [shapeOperator_of_not_injective h]

@[simp]
theorem shapeOperator_zero : shapeOperator i x 0 = 0 := by
  simpa using shapeOperator_smul (i := i) (x := x) 0 0

@[simp]
theorem shapeOperator_neg (ν : E) : shapeOperator i x (-ν) = -shapeOperator i x ν := by
  simpa using shapeOperator_smul (i := i) (x := x) (-1) ν

@[simp]
theorem shapeOperator_sub (ν ν' : E) :
    shapeOperator i x (ν - ν') = shapeOperator i x ν - shapeOperator i x ν' := by
  simp [sub_eq_add_neg]

/-- The shape operator depends only on the normal component of `ν`: tangent vectors have shape
operator `0`. -/
theorem shapeOperator_of_mem_range {ν : E} (hν : ν ∈ (fderiv ℝ i x).range) :
    shapeOperator i x ν = 0 := by
  by_cases h : Injective (fderiv ℝ i x)
  · refine ((eq_shapeOperator_iff h).2 fun v w ↦ ?_).symm
    rw [LinearMap.zero_apply, map_zero, inner_zero_left, Submodule.inner_right_of_mem_orthogonal hν
      (secondFundamentalForm_apply_mem_orthogonal i x v w)]
  · exact shapeOperator_of_not_injective h ν

/-- The shape operator of a `C²` map is self-adjoint for the induced metric:
`g(S_ν v, w) = g(v, S_ν w)`. -/
theorem _root_.ContDiffAt.inner_fderiv_shapeOperator_apply_comm (hi : ContDiffAt ℝ 2 i x)
    (ν : E) (v w : V) :
    ⟪fderiv ℝ i x (shapeOperator i x ν v), fderiv ℝ i x w⟫ =
      ⟪fderiv ℝ i x v, fderiv ℝ i x (shapeOperator i x ν w)⟫ := by
  by_cases h : Injective (fderiv ℝ i x)
  swap
  · simp [shapeOperator_of_not_injective h]
  rw [real_inner_comm (fderiv ℝ i x (shapeOperator i x ν w)), inner_fderiv_shapeOperator_apply h,
    inner_fderiv_shapeOperator_apply h, hi.secondFundamentalForm_apply_comm]

/-! ### Squared distance and focal points -/

variable {a : E}

/-- **The Hessian of squared distance at a critical point.** If `i x - a` is normal, the Hessian
of `y ↦ ‖i y - a‖²` at `x` is `2 g((1 - S_{a - i x}) v, w)`, for the induced metric `g`. -/
theorem fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) (ha : i x - a ∈ (fderiv ℝ i x).rangeᗮ) (v w : V) :
    fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - a‖ ^ 2) x v w =
      2 * ⟪fderiv ℝ i x (v - shapeOperator i x (a - i x) v), fderiv ℝ i x w⟫ := by
  have hν : a - i x ∈ (fderiv ℝ i x).rangeᗮ := by
    simpa using Submodule.neg_mem _ ha
  rw [fderiv_fderiv_norm_sq_sub_comp_apply hi, map_sub, inner_sub_left (fderiv ℝ i x v),
    inner_fderiv_shapeOperator_apply h, inner_secondFundamentalForm_apply_of_mem_orthogonal hν,
    ← neg_sub a, inner_neg_left]
  ring

/-- **The null space of the squared-distance Hessian.** If `i x - a` is normal, the kernel of the
Hessian of `y ↦ ‖i y - a‖²` at `x` is the `1`-eigenspace of the shape operator `S_{a - i x}`.
Its dimension is the multiplicity of `a` as a focal point of `i` at `x`. -/
theorem ker_fderiv_fderiv_norm_sq_sub_comp (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) (ha : i x - a ∈ (fderiv ℝ i x).rangeᗮ) :
    LinearMap.ker (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - a‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ) =
      eigenspace (shapeOperator i x (a - i x)) 1 := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_eigenspace_iff, one_smul,
    eq_comm (a := shapeOperator i x (a - i x) v), ← sub_eq_zero (a := v)]
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · refine sub_eq_zero.2 <| eq_of_forall_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) h
      fun w ↦ ?_
    have hw := DFunLike.congr_fun hv w
    rw [fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator hi h ha] at hw
    simpa [inner_sub_left, sub_eq_zero] using hw
  · ext w
    rw [fderiv_fderiv_norm_sq_sub_comp_apply_eq_inner_shapeOperator hi h ha, hv]
    simp

/-- **Focal points on a normal line.** For a normal vector `ν` and `t ≠ 0`, the kernel of the
Hessian at `x` of squared distance from `i x + t • ν` is the `t⁻¹`-eigenspace of `S_ν`. Thus
`i x + t • ν` is a focal point of `i` at `x` exactly when `t⁻¹` is an eigenvalue of `S_ν`, with
multiplicity the dimension of that eigenspace. -/
theorem ker_fderiv_fderiv_norm_sq_sub_add_smul_comp (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) {ν : E} (hν : ν ∈ (fderiv ℝ i x).rangeᗮ) {t : ℝ}
    (ht : t ≠ 0) :
    LinearMap.ker
        (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ) =
      eigenspace (shapeOperator i x ν) t⁻¹ := by
  rw [ker_fderiv_fderiv_norm_sq_sub_comp hi h (by simpa using Submodule.smul_mem _ (-t) hν),
    add_sub_cancel_left, shapeOperator_smul, eigenspace, genEigenspace_smul _ ht, mul_one]

/-- The base point is not a focal point: squared distance from `i x` has nondegenerate Hessian
at `x` along an immersion. -/
theorem ker_fderiv_fderiv_norm_sq_sub_self_comp (hi : ContDiffAt ℝ 2 i x)
    (h : Injective (fderiv ℝ i x)) :
    LinearMap.ker (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - i x‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ) = ⊥ := by
  rw [ker_fderiv_fderiv_norm_sq_sub_comp hi h (by simp), sub_self, shapeOperator_zero,
    eigenspace_def]
  simp only [zero_sub, one_smul, LinearMap.ker_neg, Module.End.one_eq_id, LinearMap.ker_id]

end Real

section Complex

/-! ### Holomorphic immersions

The real inner product `re ⟪x, y⟫` on a complex inner product space is enabled locally; the shape
operators below are taken with respect to it. -/

attribute [local instance] InnerProductSpace.complexToReal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {i : V → E} {x : V}

/-- **The shape operator anticommutes with `J`.** For a `C²` holomorphic map,
`S_ν (I • v) = -(I • S_ν v)`. -/
theorem _root_.ContDiffAt.shapeOperator_apply_I_smul (hi : ContDiffAt ℂ 2 i x) (ν : E) (v : V) :
    shapeOperator i x ν (I • v) = -(I • shapeOperator i x ν v) := by
  by_cases hR : Injective (fderiv ℝ i x)
  swap
  · simp [shapeOperator_of_not_injective hR]
  refine eq_of_forall_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) hR fun w ↦ ?_
  have hw := inner_fderiv_shapeOperator_apply hR ν v (I • w)
  simp only [ContinuousLinearMap.coe_coe]
  have hI := (hi.differentiableAt (by norm_num)).fderiv_restrictScalars_smul ℝ I
  rw [inner_fderiv_shapeOperator_apply hR, hi.secondFundamentalForm_I_smul_left,
    ← hi.secondFundamentalForm_I_smul_right, ← hw, map_neg, hI, hI]
  simp [real_inner_eq_re_inner, inner_smul_left, inner_smul_right]

/-- **Rotating the normal vector by `J`.** For a `C²` holomorphic map,
`S_{I • ν} v = I • S_ν v`. -/
theorem _root_.ContDiffAt.shapeOperator_I_smul_apply (hi : ContDiffAt ℂ 2 i x) (ν : E) (v : V) :
    shapeOperator i x (I • ν) v = I • shapeOperator i x ν v := by
  by_cases hR : Injective (fderiv ℝ i x)
  swap
  · simp [shapeOperator_of_not_injective hR]
  refine eq_of_forall_inner_comp (L := (fderiv ℝ i x : V →ₗ[ℝ] E)) hR fun w ↦ ?_
  have hw := inner_fderiv_shapeOperator_apply hR ν v (I • w)
  have hI := (hi.differentiableAt (by norm_num)).fderiv_restrictScalars_smul ℝ I
  rw [hI, hi.secondFundamentalForm_I_smul_right] at hw
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_fderiv_shapeOperator_apply hR, hI]
  -- Both sides are the imaginary part of `⟪ν, B(v, w)⟫_ℂ`, which `hw` computes.
  simp only [real_inner_eq_re_inner, inner_smul_left, inner_smul_right] at hw ⊢
  simp at hw ⊢
  linarith

/-- In the form used by the eigenspace API: the shape operator anticommutes with the real linear
equivalence given by multiplication by `I`. -/
private theorem shapeOperator_mul_add_mul_eq_zero (hi : ContDiffAt ℂ 2 i x) (ν : E) :
    shapeOperator i x ν * ((LinearEquiv.smulOfNeZero ℂ V I I_ne_zero).restrictScalars ℝ :
        Module.End ℝ V) +
      ((LinearEquiv.smulOfNeZero ℂ V I I_ne_zero).restrictScalars ℝ : Module.End ℝ V) *
        shapeOperator i x ν = 0 := by
  ext v
  simp [hi.shapeOperator_apply_I_smul]

/-- **Paired principal curvatures.** For a `C²` holomorphic map, multiplication by `I` identifies
the generalized `κ`- and `-κ`-eigenspaces of each shape operator, so they have the same
dimension. For `k = 1` these are the geometric multiplicities of the principal curvatures `κ`
and `-κ`. -/
theorem _root_.ContDiffAt.finrank_genEigenspace_shapeOperator_neg (hi : ContDiffAt ℂ 2 i x)
    (ν : E) (κ : ℝ) (k : ℕ∞) :
    finrank ℝ (genEigenspace (shapeOperator i x ν) (-κ) k) =
      finrank ℝ (genEigenspace (shapeOperator i x ν) κ k) :=
  finrank_genEigenspace_neg_of_anticommute _ (shapeOperator_mul_add_mul_eq_zero hi ν) κ k

/-- For a `C²` holomorphic map, `-κ` is a principal curvature in the direction `ν` exactly when
`κ` is. -/
theorem _root_.ContDiffAt.hasEigenvalue_shapeOperator_neg_iff (hi : ContDiffAt ℂ 2 i x)
    (ν : E) {κ : ℝ} :
    (shapeOperator i x ν).HasEigenvalue (-κ) ↔ (shapeOperator i x ν).HasEigenvalue κ :=
  hasEigenvalue_neg_iff_of_anticommute _ (shapeOperator_mul_add_mul_eq_zero hi ν)

/-- **The zero principal curvature.** For a `C²` holomorphic map, the generalized
`0`-eigenspaces of a shape operator, in particular its kernel, are complex subspaces. -/
theorem _root_.ContDiffAt.I_smul_mem_genEigenspace_shapeOperator_zero (hi : ContDiffAt ℂ 2 i x)
    (ν : E) (k : ℕ∞) {v : V}
    (hv : v ∈ genEigenspace (shapeOperator i x ν) 0 k) :
    I • v ∈ genEigenspace (shapeOperator i x ν) 0 k := by
  simpa using mapsTo_genEigenspace_neg_of_anticommute
    (shapeOperator_mul_add_mul_eq_zero hi ν) 0 k hv

/-- **Symmetric focal points.** For a holomorphic immersion and a normal vector `ν`, the points
`i x + ν` and `i x - ν` have the same focal multiplicity, possibly zero: one is a focal point of
`i` at `x` exactly when the other is, and the Hessians at `x` of squared distance from them have
null spaces of the same dimension. -/
theorem _root_.ContDiffAt.finrank_ker_fderiv_fderiv_norm_sq_sub_sub_comp
    (hi : ContDiffAt ℂ 2 i x) (h : Injective (fderiv ℂ i x)) {ν : E}
    (hν : ν ∈ (fderiv ℝ i x).rangeᗮ) :
    finrank ℝ (LinearMap.ker
        (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ)) =
      finrank ℝ (LinearMap.ker
        (fderiv ℝ (fderiv ℝ fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x : V →ₗ[ℝ] V →L[ℝ] ℝ)) := by
  have hiR : ContDiffAt ℝ 2 i x := hi.restrict_scalars ℝ
  have hR := ((hi.differentiableAt (by norm_num)).injective_fderiv_restrictScalars_iff ℝ).2 h
  rw [ker_fderiv_fderiv_norm_sq_sub_comp hiR hR (by simpa using hν),
    ker_fderiv_fderiv_norm_sq_sub_comp hiR hR (by simpa using Submodule.neg_mem _ hν),
    sub_sub_cancel_left, add_sub_cancel_left, shapeOperator_neg, eigenspace, eigenspace,
    genEigenspace_neg]
  exact hi.finrank_genEigenspace_shapeOperator_neg ν 1 1

end Complex

end TauCeti
