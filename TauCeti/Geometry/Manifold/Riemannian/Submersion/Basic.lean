/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic

/-!
# Riemannian submersions and horizontal lifts

A Riemannian submersion is a smooth submersion whose differential preserves norms on the
orthogonal complement of its kernel. Surjectivity of the map itself is not required. The vertical
space is the native kernel of the differential, and the horizontal space is its orthogonal
complement, for the given Riemannian metric.

The adjoint of the differential is the canonical isometric horizontal lift. Its composite with
the differential is exactly the native orthogonal projection onto the horizontal space; the
complementary projection is the vertical one. Thus the differential decreases norms, with
equality exactly on horizontal vectors. The gradient of a pulled-back function is the horizontal
lift of its gradient. Product projections give submersions with arbitrary-dimensional fibres.

These are pointwise splitting and metric identities. They do not assert regularity of the
horizontal distribution or construct horizontal lifts of curves.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (Riemannian submersions).
-/

public section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

variable (I J) in
/-- A smooth submersion whose differential is an isometry on the horizontal space, the
orthogonal complement of its kernel for the given metric. The map need not be surjective. -/
structure IsRiemannianSubmersion (f : M → N) : Prop where
  /-- The underlying map is a smooth submersion in native manifold charts. -/
  isSubmersion : Manifold.IsSubmersion I J ∞ f
  /-- The differential preserves the norm of every horizontal vector. -/
  norm_mfderiv : ∀ x (v : TangentSpace I x), v ∈ (mfderiv I J f x).kerᗮ →
    ‖mfderiv I J f x v‖ = ‖v‖

namespace IsRiemannianSubmersion

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  (h : IsRiemannianSubmersion I J f)

include h

/-- The differential of a Riemannian submersion is a partial isometry. -/
theorem isPartialIsometry_mfderiv (x : M) : (mfderiv I J f x).IsPartialIsometry :=
  ContinuousLinearMap.isPartialIsometry_iff_norm_map.mpr (h.norm_mfderiv x)

/-- The adjoint of the differential is a right inverse. -/
@[simp]
theorem mfderiv_adjoint_apply (x : M) (v : TangentSpace J (f x)) :
    mfderiv I J f x ((mfderiv I J f x).adjoint v) = v := by
  obtain ⟨w, rfl⟩ := h.isSubmersion.surjective_mfderiv (by simp) x v
  exact (h.isPartialIsometry_mfderiv x).apply_adjoint_apply w

/-- The canonical horizontal lift is the adjoint of the differential, as a linear isometry. -/
def horizontalLift (x : M) : TangentSpace J (f x) →ₗᵢ[ℝ] TangentSpace I x :=
  ((mfderiv I J f x).adjoint.toLinearMap).isometryOfInner fun v w ↦ by
    simp only [ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.adjoint_inner_left, h.mfderiv_adjoint_apply]

/-- The horizontal lift is computed by the metric adjoint of the differential. -/
theorem horizontalLift_apply (x : M) (v : TangentSpace J (f x)) :
    h.horizontalLift x v = (mfderiv I J f x).adjoint v := (rfl)

/-- Taking the differential of a horizontal lift recovers the original vector. -/
@[simp]
theorem mfderiv_horizontalLift (x : M) (v : TangentSpace J (f x)) :
    mfderiv I J f x (h.horizontalLift x v) = v := by
  rw [h.horizontalLift_apply, h.mfderiv_adjoint_apply]

/-- Horizontal lifting after differentiation is precisely the orthogonal horizontal projection.
This identifies the splitting with the native kernel and orthogonal-complement carriers. -/
theorem horizontalLift_comp_mfderiv (x : M) :
    (h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x =
      (mfderiv I J f x).kerᗮ.starProjection := by
  rw [← (h.isPartialIsometry_mfderiv x).adjoint_comp_self_eq_starProjection]
  ext v
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    h.horizontalLift_apply]

/-- Horizontally lifting a differential gives the horizontal component of the vector. -/
@[simp]
theorem horizontalLift_mfderiv (x : M) (v : TangentSpace I x) :
    h.horizontalLift x (mfderiv I J f x v) = (mfderiv I J f x).kerᗮ.starProjection v :=
  DFunLike.congr_fun (h.horizontalLift_comp_mfderiv x) v

/-- The complementary projection is exactly the orthogonal vertical projection. -/
theorem id_sub_horizontalLift_comp_mfderiv (x : M) :
    ContinuousLinearMap.id ℝ (TangentSpace I x) -
        (h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x =
      (mfderiv I J f x).ker.starProjection := by
  rw [h.horizontalLift_comp_mfderiv, Submodule.starProjection_orthogonal]
  abel

/-- Every horizontal lift is horizontal. -/
theorem horizontalLift_mem_orthogonal_ker (x : M) (v : TangentSpace J (f x)) :
    h.horizontalLift x v ∈ (mfderiv I J f x).kerᗮ := by
  rw [h.horizontalLift_apply]
  exact ContinuousLinearMap.adjoint_apply_mem_orthogonal_ker _ _

/-- A horizontal vector is recovered by horizontally lifting its differential. -/
theorem horizontalLift_mfderiv_of_mem (x : M) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    h.horizontalLift x (mfderiv I J f x v) = v := by
  rw [h.horizontalLift_mfderiv, Submodule.starProjection_eq_self_iff.mpr hv]

/-- The horizontal lift is the unique horizontal vector mapping to the specified base vector. -/
theorem eq_horizontalLift_iff (x : M) (v : TangentSpace I x)
    (w : TangentSpace J (f x)) :
    v = h.horizontalLift x w ↔
      v ∈ (mfderiv I J f x).kerᗮ ∧ mfderiv I J f x v = w := by
  constructor
  · rintro rfl
    exact ⟨h.horizontalLift_mem_orthogonal_ker x w, h.mfderiv_horizontalLift x w⟩
  · rintro ⟨hv, hw⟩
    rw [← hw, h.horizontalLift_mfderiv_of_mem x hv]

/-- The horizontal space is exactly the range of the horizontal lift. -/
theorem range_horizontalLift (x : M) :
    (h.horizontalLift x).toLinearMap.range = (mfderiv I J f x).kerᗮ := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact h.horizontalLift_mem_orthogonal_ker x w
  · intro hv
    exact ⟨mfderiv I J f x v, h.horizontalLift_mfderiv_of_mem x hv⟩

/-- The differential of a Riemannian submersion decreases tangent-vector norms. -/
theorem norm_mfderiv_le (x : M) (v : TangentSpace I x) :
    ‖mfderiv I J f x v‖ ≤ ‖v‖ := by
  rw [← (h.horizontalLift x).norm_map, h.horizontalLift_mfderiv]
  exact Submodule.norm_starProjection_apply_le _ _

/-- Equality in the differential norm bound holds exactly for horizontal vectors. -/
theorem norm_mfderiv_eq_iff (x : M) (v : TangentSpace I x) :
    ‖mfderiv I J f x v‖ = ‖v‖ ↔ v ∈ (mfderiv I J f x).kerᗮ := by
  rw [← (h.horizontalLift x).norm_map, h.horizontalLift_mfderiv]
  exact (Submodule.mem_iff_norm_starProjection _ v).symm

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- The gradient of a pullback is the horizontal lift of the gradient on the base. -/
theorem mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    Manifold.mgradient I (g ∘ f) x = h.horizontalLift x (Manifold.mgradient J g (f x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [Manifold.inner_mgradient_comp hg (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)),
    h.horizontalLift_apply, ContinuousLinearMap.adjoint_inner_left]

/-- A pulled-back gradient projects to the base gradient. -/
@[simp]
theorem mfderiv_mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    mfderiv I J f x (Manifold.mgradient I (g ∘ f) x) = Manifold.mgradient J g (f x) := by
  rw [h.mgradient_comp hg, h.mfderiv_horizontalLift]

end IsRiemannianSubmersion

section Product

open scoped TauCeti

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The first projection, with the product Riemannian metric, is a Riemannian submersion. -/
theorem isRiemannianSubmersion_fst :
    IsRiemannianSubmersion (I.prod J) I (@Prod.fst M N) := by
  refine ⟨Manifold.isSubmersion_fst, fun p v hv ↦ ?_⟩
  let w : TangentSpace (I.prod J) p := (Manifold.tangentSpaceProdEquiv p).symm
    (0, (Manifold.tangentSpaceProdEquiv p v).2)
  have hw : w ∈ (mfderiv (I.prod J) I (@Prod.fst M N) p).ker := by
    rw [LinearMap.mem_ker, mfderiv_fst]
    simp only [w, Manifold.tangentSpaceProdEquiv_symm_apply]
    erw [ContinuousLinearMap.coe_fst']
  have hzero : inner ℝ w v = 0 := hv w hw
  rw [Manifold.inner_tangentSpace_prod] at hzero
  simp only [w, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add] at hzero
  have hv₂ : (Manifold.tangentSpaceProdEquiv p v).2 = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp hzero
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    Manifold.inner_tangentSpace_prod, hv₂, inner_zero_left, add_zero]
  simp only [mfderiv_fst, Manifold.tangentSpaceProdEquiv_apply]
  erw [ContinuousLinearMap.coe_fst']

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The horizontal lift for the first product projection inserts a zero second component. -/
@[simp]
theorem horizontalLift_fst (p : M × N) (v : TangentSpace I p.1) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p v =
      (Manifold.tangentSpaceProdEquiv p).symm (v, 0) := by
  apply ext_inner_right ℝ
  intro w
  rw [IsRiemannianSubmersion.horizontalLift_apply,
    ContinuousLinearMap.adjoint_inner_left, Manifold.inner_tangentSpace_prod]
  simp only [mfderiv_fst,
    ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, add_zero,
    Manifold.tangentSpaceProdEquiv_apply]
  erw [ContinuousLinearMap.coe_fst']

end Product

end TauCeti
