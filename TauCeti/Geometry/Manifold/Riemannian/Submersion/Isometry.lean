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
Riemannian isometries of the source or the base. The formulas use the native metric-adjoint
horizontal lift and the orthogonal projections onto the kernel of the differential and its
orthogonal complement. They supply the splitting comparison needed to transport the
fundamental tensors and the connection formulas of a Riemannian submersion.

The composite maps are assumed to be Riemannian submersions too. This retains their actual
submersion normal forms, including when the manifolds have boundary: an invertible isometric
differential alone does not assert a submersion normal form at a boundary point. No global
injectivity or surjectivity of the isometries is needed.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
-/

public section

open Bundle Manifold
open scoped ContDiff InnerProductSpace Manifold

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

/-- Horizontal projection commutes with a local isometry of the source. -/
@[simp]
theorem mfderiv_starProjection_orthogonal_ker_comp {φ : P → M}
    (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
    (hφ : IsLocalRiemannianIsometry K I φ) (x : P) (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K J (f ∘ φ) x).kerᗮ.starProjection v) =
      (mfderiv I J f (φ x)).kerᗮ.starProjection (mfderiv K I φ x v) := by
  rw [← hcomp.horizontalLift_mfderiv, h.mfderiv_horizontalLift_comp hcomp hφ,
    mfderiv_comp_apply x (h.isSubmersion.contMDiff.mdifferentiableAt (by simp))
      (hφ.mdifferentiableAt x), h.horizontalLift_mfderiv]

/-- Vertical projection commutes with a local isometry of the source. -/
@[simp]
theorem mfderiv_starProjection_ker_comp {φ : P → M}
    (hcomp : IsRiemannianSubmersion K J (f ∘ φ))
    (hφ : IsLocalRiemannianIsometry K I φ) (x : P) (v : TangentSpace K x) :
    mfderiv K I φ x ((mfderiv K J (f ∘ φ) x).ker.starProjection v) =
      (mfderiv I J f (φ x)).ker.starProjection (mfderiv K I φ x v) := by
  have heq := h.mfderiv_starProjection_orthogonal_ker_comp hcomp hφ x v
  simp only [Submodule.starProjection_orthogonal_val, map_sub] at heq
  exact sub_right_inj.mp heq

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

/-- A local isometry of the base preserves the horizontal projection. -/
@[simp]
theorem starProjection_orthogonal_ker_comp {ψ : N → P}
    (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
    (hψ : IsLocalRiemannianIsometry J K ψ) (x : M) (v : TangentSpace I x) :
    (mfderiv I K (ψ ∘ f) x).kerᗮ.starProjection v =
      (mfderiv I J f x).kerᗮ.starProjection v := by
  rw [← hcomp.horizontalLift_mfderiv,
    mfderiv_comp_apply x (hψ.mdifferentiableAt (f x))
      (h.isSubmersion.contMDiff.mdifferentiableAt (by simp)),
    h.horizontalLift_mfderiv_comp hcomp hψ, h.horizontalLift_mfderiv]

/-- A local isometry of the base preserves the vertical projection. -/
@[simp]
theorem starProjection_ker_comp {ψ : N → P}
    (hcomp : IsRiemannianSubmersion I K (ψ ∘ f))
    (hψ : IsLocalRiemannianIsometry J K ψ) (x : M) (v : TangentSpace I x) :
    (mfderiv I K (ψ ∘ f) x).ker.starProjection v =
      (mfderiv I J f x).ker.starProjection v := by
  have heq := h.starProjection_orthogonal_ker_comp hcomp hψ x v
  simp only [Submodule.starProjection_orthogonal_val] at heq
  exact sub_right_inj.mp heq

end TauCeti.IsRiemannianSubmersion
