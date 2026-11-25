/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
public import TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Riemannian submersions and horizontal lifts

A Riemannian submersion is a smooth submersion whose differential preserves norms on the
orthogonal complement of its kernel. Surjectivity of the map itself is not required. The vertical
space is the native kernel of the differential, and the horizontal space is its orthogonal
complement, for the given Riemannian metric.

The adjoint of the differential is the canonical isometric horizontal lift. Its composite with
the differential is exactly the native orthogonal projection onto the horizontal space; the
complementary projection is the vertical one. Thus the differential decreases norms, with
equality exactly on horizontal vectors, and horizontal lifting and the differential on horizontal
families preserve Gram matrices, linear independence, and orthonormality. Horizontal lifts of an
orthonormal basis of the base tangent space, followed by an orthonormal basis of the vertical
space, form an orthonormal basis of `T_x M` (`IsRiemannianSubmersion.horizontalVerticalBasis`).
The gradient of a pulled-back function is the horizontal lift of its gradient, so it has the same
length. Product projections give submersions with arbitrary-dimensional fibres.

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

/-- The horizontal lift of a base vector `u` pairs with `w` as `u` pairs with `df_x w`. -/
theorem inner_horizontalLift_left (x : M) (u : TangentSpace J (f x)) (w : TangentSpace I x) :
    ⟪h.horizontalLift x u, w⟫_ℝ = ⟪u, mfderiv I J f x w⟫_ℝ := by
  rw [h.horizontalLift_apply, ContinuousLinearMap.adjoint_inner_left]

/-- A tangent vector `w` pairs with the horizontal lift of `u` as `df_x w` pairs with `u`. -/
theorem inner_horizontalLift_right (x : M) (u : TangentSpace J (f x)) (w : TangentSpace I x) :
    ⟪w, h.horizontalLift x u⟫_ℝ = ⟪mfderiv I J f x w, u⟫_ℝ := by
  rw [h.horizontalLift_apply, ContinuousLinearMap.adjoint_inner_right]

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

/-- Every tangent vector decomposes into its vertical projection plus the horizontal lift of its
differential. -/
theorem starProjection_ker_add_horizontalLift_mfderiv (x : M) (v : TangentSpace I x) :
    (mfderiv I J f x).ker.starProjection v + h.horizontalLift x (mfderiv I J f x v) = v := by
  rw [h.horizontalLift_mfderiv, Submodule.starProjection_add_starProjection_orthogonal]

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

/-- Horizontal lifting preserves the Gram matrix of any family of base tangent vectors. -/
@[simp]
theorem gram_horizontalLift (x : M) {ι : Type*} (u : ι → TangentSpace J (f x)) :
    Matrix.gram ℝ (fun i ↦ h.horizontalLift x (u i)) = Matrix.gram ℝ u := by
  ext i j
  exact (h.horizontalLift x).inner_map_map (u i) (u j)

/-- On a family of horizontal vectors, `mfderiv` preserves the Gram matrix. -/
theorem gram_mfderiv_of_mem {x : M} {ι : Type*} {u : ι → TangentSpace I x}
    (hu : ∀ i, u i ∈ (mfderiv I J f x).kerᗮ) :
    Matrix.gram ℝ (fun i ↦ mfderiv I J f x (u i)) = Matrix.gram ℝ u := by
  rw [← h.gram_horizontalLift x]
  congr 1
  ext i
  exact h.horizontalLift_mfderiv_of_mem x (hu i)

/-- A family of horizontal vectors at `x` is linearly independent if and only if its projection in
`TangentSpace J (f x)` is linearly independent. -/
theorem linearIndependent_mfderiv_iff_of_mem {x : M} {ι : Type*} {u : ι → TangentSpace I x}
    (hu : ∀ i, u i ∈ (mfderiv I J f x).kerᗮ) :
    LinearIndependent ℝ (fun i ↦ mfderiv I J f x (u i)) ↔ LinearIndependent ℝ u := by
  rw [← Matrix.posDef_gram_iff_linearIndependent (𝕜 := ℝ),
    ← Matrix.posDef_gram_iff_linearIndependent (𝕜 := ℝ),
    h.gram_mfderiv_of_mem hu]

/-- A family of horizontal vectors at `x` is orthonormal if and only if its projection in
`TangentSpace J (f x)` is orthonormal. -/
theorem orthonormal_mfderiv_iff_of_mem {x : M} {ι : Type*} {u : ι → TangentSpace I x}
    (hu : ∀ i, u i ∈ (mfderiv I J f x).kerᗮ) :
    Orthonormal ℝ (fun i ↦ mfderiv I J f x (u i)) ↔ Orthonormal ℝ u := by
  classical
  rw [← Matrix.gram_eq_one_iff_orthonormal (𝕜 := ℝ),
    ← Matrix.gram_eq_one_iff_orthonormal (𝕜 := ℝ),
    h.gram_mfderiv_of_mem hu]

/-! ### The adapted orthonormal basis -/

section Basis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Horizontal lifts of an orthonormal basis of `T_(f x) N`, followed by an orthonormal basis of the
vertical space `ker (df_x)`, form an orthonormal family. -/
theorem orthonormal_sumElim_horizontalLift (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    Orthonormal ℝ (Sum.elim (fun i ↦ h.horizontalLift x (b i))
      fun a ↦ (c a : TangentSpace I x)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro (i | a) (j | a')
  · rw [Sum.elim_inl, Sum.elim_inl, LinearIsometry.inner_map_map,
      orthonormal_iff_ite.mp b.orthonormal i j]
    simp
  · rw [Sum.elim_inl, Sum.elim_inr, Submodule.inner_left_of_mem_orthogonal (c a').property
      (h.horizontalLift_mem_orthogonal_ker x (b i))]
    simp
  · rw [Sum.elim_inr, Sum.elim_inl, Submodule.inner_right_of_mem_orthogonal (c a).property
      (h.horizontalLift_mem_orthogonal_ker x (b j))]
    simp
  · rw [Sum.elim_inr, Sum.elim_inr, ← Submodule.coe_inner,
      orthonormal_iff_ite.mp c.orthonormal a a']
    simp

/-- A tangent vector orthogonal to the horizontal lifts of an orthonormal basis of `T_(f x) N` and
to an orthonormal basis of `ker (df_x)` is zero. -/
theorem eq_zero_of_forall_inner_horizontalLift_eq_zero (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) {w : TangentSpace I x}
    (hb : ∀ i, ⟪h.horizontalLift x (b i), w⟫_ℝ = 0)
    (hc : ∀ a, ⟪(c a : TangentSpace I x), w⟫_ℝ = 0) :
    w = 0 := by
  have hdw : mfderiv I J f x w = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, ← b.sum_sq_inner_right]
    simp [← h.inner_horizontalLift_left, hb]
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  calc ‖w‖ ^ 2 = ‖(⟨w, hdw⟩ : (mfderiv I J f x).ker)‖ ^ 2 := by rw [← Submodule.norm_coe]
    _ = ∑ a, ⟪c a, (⟨w, hdw⟩ : (mfderiv I J f x).ker)⟫_ℝ ^ 2 := (c.sum_sq_inner_right _).symm
    _ = 0 := Finset.sum_eq_zero fun a _ ↦ by rw [Submodule.coe_inner, hc a, sq, mul_zero]

/-- The orthonormal basis of `T_x M` adapted to the splitting into horizontal and vertical spaces:
horizontal lifts of an orthonormal basis `b` of `T_(f x) N`, followed by an orthonormal basis `c` of
the vertical space `ker (df_x)`. -/
def horizontalVerticalBasis (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) :
    OrthonormalBasis (ι ⊕ κ) ℝ (TangentSpace I x) :=
  .mkOfOrthogonalEqBot (h.orthonormal_sumElim_horizontalLift x b c) <| by
    refine (Submodule.eq_bot_iff _).2 fun w hw ↦
      h.eq_zero_of_forall_inner_horizontalLift_eq_zero x b c (fun i ↦ ?_) fun a ↦ ?_
    · exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inl i))) hw
    · exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inr a))) hw

/-- The first block of the adapted basis consists of the horizontal lifts. -/
@[simp]
theorem horizontalVerticalBasis_inl (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) (i : ι) :
    h.horizontalVerticalBasis x b c (.inl i) = h.horizontalLift x (b i) := by
  simp [horizontalVerticalBasis]

/-- The second block of the adapted basis is the vertical basis. -/
@[simp]
theorem horizontalVerticalBasis_inr (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    (c : OrthonormalBasis κ ℝ (mfderiv I J f x).ker) (a : κ) :
    h.horizontalVerticalBasis x b c (.inr a) = c a := by
  simp [horizontalVerticalBasis]

/-- For a horizontal vector `w`, the squared coefficients of `w` on the horizontal lifts of an
orthonormal basis of `T_(f x) N` add up to `‖w‖²`. -/
theorem sum_sq_inner_horizontalLift {x : M} (b : OrthonormalBasis ι ℝ (TangentSpace J (f x)))
    {w : TangentSpace I x} (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ∑ i, ⟪h.horizontalLift x (b i), w⟫_ℝ ^ 2 = ‖w‖ ^ 2 := by
  simp_rw [h.inner_horizontalLift_left, b.sum_sq_inner_right, (h.norm_mfderiv_eq_iff x w).2 hw]

end Basis

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- The gradient of a pullback is the horizontal lift of the gradient on the base. -/
theorem mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    Manifold.mgradient I (g ∘ f) x = h.horizontalLift x (Manifold.mgradient J g (f x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [Manifold.inner_mgradient_comp hg (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)),
    h.inner_horizontalLift_left]

/-- A pulled-back gradient projects to the base gradient. -/
@[simp]
theorem mfderiv_mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    mfderiv I J f x (Manifold.mgradient I (g ∘ f) x) = Manifold.mgradient J g (f x) := by
  rw [h.mgradient_comp hg, h.mfderiv_horizontalLift]

/-- A pulled-back negative gradient projects to the negative gradient on the base. -/
theorem mfderiv_neg_mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    mfderiv I J f x (-Manifold.mgradient I (g ∘ f) x) = -Manifold.mgradient J g (f x) := by
  rw [map_neg, h.mfderiv_mgradient_comp hg]

/-- A pulled-back gradient has the length of the gradient on the base. -/
theorem norm_mgradient_comp {g : N → ℝ} {x : M}
    (hg : MDifferentiableAt J 𝓘(ℝ) g (f x)) :
    ‖Manifold.mgradient I (g ∘ f) x‖ = ‖Manifold.mgradient J g (f x)‖ := by
  rw [h.mgradient_comp hg, LinearIsometry.norm_map]

end IsRiemannianSubmersion

section Product

open scoped TauCeti

section Submersion

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The first projection, with the product Riemannian metric, is a Riemannian submersion. -/
theorem isRiemannianSubmersion_fst :
    IsRiemannianSubmersion (I.prod J) I (@Prod.fst M N) := by
  refine ⟨Manifold.isSubmersion_fst, fun p v hv ↦ ?_⟩
  let w : TangentSpace (I.prod J) p := (Manifold.tangentSpaceProdEquiv p).symm
    (0, (Manifold.tangentSpaceProdEquiv p v).2)
  have hw : w ∈ (mfderiv (I.prod J) I (@Prod.fst M N) p).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mfderiv_fst_apply,
      ← Manifold.tangentSpaceProdEquiv_apply (I := I) (J := J) p w]
    simp only [w, ContinuousLinearEquiv.apply_symm_apply]
  have hzero : inner ℝ w v = 0 := hv w hw
  rw [Manifold.inner_tangentSpace_prod] at hzero
  simp only [w, ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, zero_add] at hzero
  have hv₂ : (Manifold.tangentSpaceProdEquiv p v).2 = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp hzero
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    Manifold.inner_tangentSpace_prod, hv₂, inner_zero_left, add_zero, mfderiv_fst_apply,
    Manifold.tangentSpaceProdEquiv_apply]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The horizontal lift for the first product projection inserts a zero second component. -/
@[simp]
theorem horizontalLift_fst (p : M × N) (v : TangentSpace I p.1) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift p v =
      (Manifold.tangentSpaceProdEquiv p).symm (v, 0) := by
  apply ext_inner_right ℝ
  intro w
  rw [IsRiemannianSubmersion.inner_horizontalLift_left, Manifold.inner_tangentSpace_prod,
    ContinuousLinearEquiv.apply_symm_apply, inner_zero_left, add_zero,
    mfderiv_fst_apply, Manifold.tangentSpaceProdEquiv_apply]

end Submersion

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- For the first projection `Prod.fst : M × N → M` with the product Riemannian metric, the
orthogonal projection onto `(ker df_p)ᗮ` keeps the first tangent component and zeroes the
second. -/
theorem starProjection_orthogonal_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm ((Manifold.tangentSpaceProdEquiv p v).1, 0) := by
  let u : TangentSpace (I.prod J) p :=
    (Manifold.tangentSpaceProdEquiv p).symm ((Manifold.tangentSpaceProdEquiv p v).1, 0)
  let w : TangentSpace (I.prod J) p :=
    (Manifold.tangentSpaceProdEquiv p).symm (0, (Manifold.tangentSpaceProdEquiv p v).2)
  have hu : u ∈ (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mfderiv_fst_apply,
      ← Manifold.tangentSpaceProdEquiv_apply (I := I) (J := J) p z] at hz
    rw [Manifold.inner_tangentSpace_prod, ContinuousLinearEquiv.apply_symm_apply, hz,
      inner_zero_left, inner_zero_right, add_zero]
  have hw : w ∈ (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮᗮ := by
    apply (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.le_orthogonal_orthogonal
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mfderiv_fst_apply,
      ← Manifold.tangentSpaceProdEquiv_apply (I := I) (J := J) p w]
    simp only [w, ContinuousLinearEquiv.apply_symm_apply]
  have hv : v = u + w := by
    apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add]
  exact Submodule.eq_starProjection_of_mem_orthogonal' hu hw hv

/-- For the first projection `Prod.fst : M × N → M` with the product Riemannian metric, the
orthogonal projection onto `ker df_p` zeroes the first tangent component and keeps the second. -/
theorem starProjection_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm (0, (Manifold.tangentSpaceProdEquiv p v).2) := by
  apply (Manifold.tangentSpaceProdEquiv p).injective
  rw [eq_sub_of_add_eq
      ((mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection_add_starProjection_orthogonal v),
    starProjection_orthogonal_ker_fst, map_sub,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero]

end Product

end TauCeti
