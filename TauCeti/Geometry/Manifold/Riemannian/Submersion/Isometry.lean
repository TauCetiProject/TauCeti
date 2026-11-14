/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Isometry transport of Riemannian submersion splittings

Horizontal lifting and the orthogonal horizontal and vertical projections commute with local
Riemannian isometries of the source or the base. More generally, local isometries intertwining
two submersions near a point transport both projections there, without any submersion
assumption on the diagonal composite. The formulas use the native metric-adjoint
horizontal lift and the orthogonal projections onto the kernel of the differential and its
orthogonal complement. They supply the splitting comparison needed to transport the
fundamental tensors and the connection formulas of a Riemannian submersion.

In the composition special cases, the composite maps are assumed to be Riemannian submersions
too. This retains their actual submersion normal forms, including when the manifolds have
boundary: an invertible isometric differential alone does not assert a submersion normal form
at a boundary point. No global
injectivity or surjectivity of the isometries is needed.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
-/

public section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

section Intertwining

variable
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type*} [TopologicalSpace G'] {L : ModelWithCorners ℝ F' G'}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace G' Q]
  [RiemannianBundle (fun y : Q ↦ TangentSpace L y)]
  {f' : P → Q} (h' : IsRiemannianSubmersion K L f')
  {φ : P → M} (hφ : IsLocalRiemannianIsometry K I φ)
  {ψ : Q → N} (hψ : IsLocalRiemannianIsometry L J ψ)

include h' hφ hψ

omit [FiniteDimensional ℝ F] in
/-- Local isometries intertwining two submersions near `x` transport the vertical projection
at `x`. No submersion hypothesis on either diagonal composite is needed. -/
theorem mfderiv_starProjection_ker_of_eventuallyEq {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K L f' x).ker.starProjection v) =
      (mfderiv I J f (φ x)).ker.starProjection (mfderiv K I φ x v) := by
  obtain ⟨e, he⟩ := hφ.exists_linearIsometryEquiv_eq_mfderiv x
  have hd (w : TangentSpace K x) :
      mfderiv I J f (φ x) (mfderiv K I φ x w) =
        tangentSpaceCast J (ψ (f' x)) (f (φ x))
          (mfderiv L J ψ (f' x) (mfderiv K L f' x w)) := by
    have hc := congrArg (fun A ↦ A w) (hcomm.mfderiv_eq (I := K) (I' := J))
    simpa only [mfderiv_comp x (h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
        (hφ.mdifferentiableAt x),
      mfderiv_comp x (hψ.mdifferentiableAt (f' x))
        (h'.isSubmersion.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Function.comp_apply] using hc
  have hk : (mfderiv K L f' x).ker.map (e.toLinearEquiv : _ →ₗ[ℝ] _) =
      (mfderiv I J f (φ x)).ker := by
    ext y
    simp only [Submodule.mem_map_equiv, LinearMap.mem_ker,
      LinearIsometryEquiv.coe_symm_toLinearEquiv, ContinuousLinearMap.coe_coe]
    have hd' := hd (e.symm y)
    simp only [← he, e.apply_symm_apply] at hd'
    rw [hd', (tangentSpaceCast J (ψ (f' x)) (f (φ x))).map_eq_zero_iff,
      map_eq_zero_iff _ (hψ.mfderiv_injective (f' x))]
  simpa only [hk, ← he, e.symm_apply_apply] using
    (Submodule.starProjection_map_apply e (mfderiv K L f' x).ker (e v)).symm

omit [FiniteDimensional ℝ F] in
/-- Local isometries intertwining two submersions near `x` transport the horizontal projection
at `x`. No submersion hypothesis on either diagonal composite is needed. -/
theorem mfderiv_starProjection_orthogonal_ker_of_eventuallyEq {x : P}
    (hcomm : f ∘ φ =ᶠ[𝓝 x] ψ ∘ f') (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K L f' x).kerᗮ.starProjection v) =
      (mfderiv I J f (φ x)).kerᗮ.starProjection (mfderiv K I φ x v) := by
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub,
    h.mfderiv_starProjection_ker_of_eventuallyEq h' hφ hψ hcomm]

end Intertwining

/-- Horizontal lifting commutes with a local isometry of the source, after applying its
invertible differential. -/
theorem mfderiv_horizontalLift_comp {φ : P → M}
    (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
    (hφ : IsLocalRiemannianIsometry K I φ) (x : P) (v : TangentSpace J (f (φ x))) :
    mfderiv K I φ x (hcomp.horizontalLift x v) = h.horizontalLift (φ x) v := by
  apply ext_inner_right ℝ
  intro w
  obtain ⟨u, rfl⟩ := hφ.mfderiv_surjective x w
  rw [hφ.inner_mfderiv, hcomp.horizontalLift_apply, ContinuousLinearMap.adjoint_inner_left,
    h.horizontalLift_apply, ContinuousLinearMap.adjoint_inner_left,
    mfderiv_comp_apply x (h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
      (hφ.mdifferentiableAt x)]

omit [FiniteDimensional ℝ F] in
/-- Horizontal projection commutes with a local isometry of the source. -/
@[simp]
theorem mfderiv_starProjection_orthogonal_ker_comp {φ : P → M}
    (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
    (hφ : IsLocalRiemannianIsometry K I φ) (x : P) (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K J (f ∘ φ) x).kerᗮ.starProjection v) =
      (mfderiv I J f (φ x)).kerᗮ.starProjection (mfderiv K I φ x v) := by
  exact h.mfderiv_starProjection_orthogonal_ker_of_eventuallyEq hcomp hφ
    (IsLocalRiemannianIsometry.id J N) Filter.EventuallyEq.rfl v

omit [FiniteDimensional ℝ F] in
/-- Vertical projection commutes with a local isometry of the source. -/
@[simp]
theorem mfderiv_starProjection_ker_comp {φ : P → M}
    (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
    (hφ : IsLocalRiemannianIsometry K I φ) (x : P) (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K J (f ∘ φ) x).ker.starProjection v) =
      (mfderiv I J f (φ x)).ker.starProjection (mfderiv K I φ x v) := by
  exact h.mfderiv_starProjection_ker_of_eventuallyEq hcomp hφ
    (IsLocalRiemannianIsometry.id J N) Filter.EventuallyEq.rfl v

/-- Horizontal lifting commutes with a local isometry of the base. -/
theorem horizontalLift_mfderiv_comp {ψ : N → P}
    (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
    (hψ : IsLocalRiemannianIsometry J K ψ) (x : M) (v : TangentSpace J (f x)) :
    hcomp.horizontalLift x (mfderiv J K ψ (f x) v) = h.horizontalLift x v := by
  apply ext_inner_right ℝ
  intro w
  rw [hcomp.horizontalLift_apply, h.horizontalLift_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    mfderiv_comp_apply x (hψ.mdifferentiableAt (f x))
      (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)), hψ.inner_mfderiv]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E'] in
/-- A local isometry of the base preserves the horizontal projection. -/
@[simp]
theorem starProjection_orthogonal_ker_comp {ψ : N → P}
    (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
    (hψ : IsLocalRiemannianIsometry J K ψ) (x : M) (v : TangentSpace I x) :
    (mfderiv I K (ψ ∘ f) x).kerᗮ.starProjection v =
      (mfderiv I J f x).kerᗮ.starProjection v := by
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
    (hcomp.mfderiv_starProjection_orthogonal_ker_of_eventuallyEq h
      (IsLocalRiemannianIsometry.id I M) hψ Filter.EventuallyEq.rfl v).symm

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E'] in
/-- A local isometry of the base preserves the vertical projection. -/
@[simp]
theorem starProjection_ker_comp {ψ : N → P}
    (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
    (hψ : IsLocalRiemannianIsometry J K ψ) (x : M) (v : TangentSpace I x) :
    (mfderiv I K (ψ ∘ f) x).ker.starProjection v =
      (mfderiv I J f x).ker.starProjection v := by
  simpa only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
    (hcomp.mfderiv_starProjection_ker_of_eventuallyEq h
      (IsLocalRiemannianIsometry.id I M) hψ Filter.EventuallyEq.rfl v).symm

end TauCeti.IsRiemannianSubmersion
