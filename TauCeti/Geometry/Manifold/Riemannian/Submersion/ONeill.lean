/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom

/-!
# O'Neill's fundamental tensors

For a Riemannian submersion, the fundamental tensors measure the part of a connection
which exchanges the horizontal and vertical distributions. They are continuous bilinear
maps on the actual tangent fibres, not operators depending on a choice of extending fields.
For horizontal and vertical orthogonal projections `h` and `v`, their formulas are
`A(X,Y) = v ∇_(hX)(hY) + h ∇_(hX)(vY)` and
`T(X,Y) = v ∇_(vX)(hY) + h ∇_(vX)(vY)`.

The construction uses the native induced endomorphism connection:
`A(X,Y) = (v-h)(∇_(hX) h)Y`, and likewise for `T` with `vX`.
It therefore makes tensoriality in both arguments explicit. The connection may be arbitrary;
the usual Riemannian fundamental tensors result on taking the Levi-Civita connection.
The evaluation and projection-exchange laws need only C¹ metrics and a C² source manifold;
smoothness of the tensors follows when the metrics and connection are smooth. Symmetry and
curvature identities for the Levi-Civita specialization are not asserted here.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7.

The construction uses `CovariantDerivative.hom` and the native orthogonal projections,
whose regularity is supplied by `IsRiemannianSubmersion.contMDiff_starProjection_orthogonal_ker`.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 2 M]
  {f : M → N} (h : IsRiemannianSubmersion I J f)
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))

/-- O'Neill's horizontal fundamental tensor for a connection. It differentiates the splitting
in the horizontal part of its first argument and exchanges horizontal and vertical components. -/
def oneillA (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _
    ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)).comp
      ((cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x).comp
        ((h.horizontalLift x).toContinuousLinearMap.comp (mfderiv I J f x)))

/-- O'Neill's vertical fundamental tensor for a connection. It differentiates the splitting
in the vertical part of its first argument and exchanges horizontal and vertical components. -/
def oneillT (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _
    ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)).comp
      ((cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x).comp
        (ContinuousLinearMap.id ℝ _ -
          (h.horizontalLift x).toContinuousLinearMap.comp (mfderiv I J f x)))

/-- The horizontal fundamental tensor is the reflected covariant derivative of the
horizontal projection, in a horizontal direction. -/
theorem oneillA_apply_eq_hom (x : M) (u w : TangentSpace I x) :
    h.oneillA cov x u w =
      ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)
        (cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x
          ((mfderiv I J f x).kerᗮ.starProjection u) w) := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]

/-- The vertical fundamental tensor is the reflected covariant derivative of the
horizontal projection, in a vertical direction. -/
theorem oneillT_apply_eq_hom (x : M) (u w : TangentSpace I x) :
    h.oneillT cov x u w =
      ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)
        (cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x
          ((mfderiv I J f x).ker.starProjection u) w) := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]

/-- The horizontal tensor ignores the vertical part of its first argument. -/
@[simp]
theorem oneillA_starProjection_orthogonal_ker (x : M) (u w : TangentSpace I x) :
    h.oneillA cov x ((mfderiv I J f x).kerᗮ.starProjection u) w = h.oneillA cov x u w := by
  simp only [oneillA_apply_eq_hom,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The horizontal tensor vanishes on a vertical first argument. -/
@[simp]
theorem oneillA_starProjection_ker (x : M) (u w : TangentSpace I x) :
    h.oneillA cov x ((mfderiv I J f x).ker.starProjection u) w = 0 := by
  rw [h.oneillA_apply_eq_hom,
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.starProjection_apply_mem _ _)]
  simp

/-- The vertical tensor ignores the horizontal part removed from its first argument. -/
@[simp]
theorem oneillT_starProjection_ker (x : M) (u w : TangentSpace I x) :
    h.oneillT cov x ((mfderiv I J f x).ker.starProjection u) w = h.oneillT cov x u w := by
  simp only [oneillT_apply_eq_hom,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The vertical tensor vanishes on a horizontal first argument. -/
@[simp]
theorem oneillT_starProjection_orthogonal_ker (x : M) (u w : TangentSpace I x) :
    h.oneillT cov x ((mfderiv I J f x).kerᗮ.starProjection u) w = 0 := by
  rw [h.oneillT_apply_eq_hom,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (Submodule.starProjection_apply_mem _ _)]
  simp

variable [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

include h

private theorem reflected_hom_projection_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)
        (cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x u (Y x)) =
      (mfderiv I J f x).ker.starProjection
          (cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x u) +
        (mfderiv I J f x).kerᗮ.starProjection
          (cov (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x u) := by
  let : IsManifold I (1 + 1) M := IsManifold.of_le (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := 1) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hPY := hP.clm_bundle_apply hY
  have hQ := (h.contMDiff_starProjection_ker (n := 1) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hQY := hQ.clm_bundle_apply hY
  have hsum : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) +
      (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) = Y := by
    ext y
    simp [Submodule.starProjection_orthogonal]
  have hc := congrArg (fun L ↦ L u)
    (cov.isCovariantDerivativeOnUniv.add hPY hQY)
  rw [hsum] at hc
  rw [cov.hom_apply cov hP hY]
  have hz := Submodule.starProjection_orthogonal_apply_eq_zero
    (K := (mfderiv I J f x).kerᗮ)
    (Submodule.starProjection_apply_mem _ (cov Y x u))
  simp only [Submodule.orthogonal_orthogonal] at hz
  simp only [add_apply] at hc
  simp only [sub_apply, map_sub, hz,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  rw [hc]
  simp only [map_add]
  abel

/-- The intrinsic field formula for O'Neill's horizontal tensor. Only the second field
needs to be differentiable at the evaluated point; the first input is a fibre vector. -/
theorem oneillA_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillA cov x u (Y x) =
      (mfderiv I J f x).ker.starProjection
          (cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
            ((mfderiv I J f x).kerᗮ.starProjection u)) +
        (mfderiv I J f x).kerᗮ.starProjection
          (cov (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
            ((mfderiv I J f x).kerᗮ.starProjection u)) := by
  rw [h.oneillA_apply_eq_hom]
  exact reflected_hom_projection_apply h cov hY _

/-- The intrinsic field formula for O'Neill's vertical tensor. -/
theorem oneillT_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillT cov x u (Y x) =
      (mfderiv I J f x).ker.starProjection
          (cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
            ((mfderiv I J f x).ker.starProjection u)) +
        (mfderiv I J f x).kerᗮ.starProjection
          (cov (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
            ((mfderiv I J f x).ker.starProjection u)) := by
  rw [h.oneillT_apply_eq_hom]
  exact reflected_hom_projection_apply h cov hY _

private theorem reflected_hom_projection_horizontal (x : M) (u w : TangentSpace I x) :
    let P := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
    let Q := (mfderiv I J f x).ker.starProjection
    (Q - P x) (cov.hom cov P x u (P x w)) =
      Q ((Q - P x) (cov.hom cov P x u w)) := by
  let : IsManifold I (1 + 1) M := IsManifold.of_le (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  dsimp only
  let Y := FiberBundle.extend E w
  have hY : MDiffAt (T% Y) x := FiberBundle.mdifferentiableAt_extend ..
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := 1) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hPY := hP.clm_bundle_apply hY
  have hPPY : (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
      ((mfderiv I J f y).kerᗮ.starProjection (Y y))) =
      (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) := by
    ext y
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have heq : Y x = w := FiberBundle.extend_apply_self ..
  rw [← heq, cov.hom_apply cov hP hPY, hPPY, cov.hom_apply cov hP hY]
  simp only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, map_sub,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  abel

/-- Horizontal projection in the second argument of `A` is vertical projection in its output. -/
theorem oneillA_apply_starProjection_orthogonal_ker (x : M) (u w : TangentSpace I x) :
    h.oneillA cov x u ((mfderiv I J f x).kerᗮ.starProjection w) =
      (mfderiv I J f x).ker.starProjection (h.oneillA cov x u w) := by
  simp only [h.oneillA_apply_eq_hom]
  exact reflected_hom_projection_horizontal h cov x _ w

/-- Horizontal projection in the second argument of `T` is vertical projection in its output. -/
theorem oneillT_apply_starProjection_orthogonal_ker (x : M) (u w : TangentSpace I x) :
    h.oneillT cov x u ((mfderiv I J f x).kerᗮ.starProjection w) =
      (mfderiv I J f x).ker.starProjection (h.oneillT cov x u w) := by
  simp only [h.oneillT_apply_eq_hom]
  exact reflected_hom_projection_horizontal h cov x _ w

/-- Vertical projection in the second argument of `A` is horizontal projection in its output. -/
theorem oneillA_apply_starProjection_ker (x : M) (u w : TangentSpace I x) :
    h.oneillA cov x u ((mfderiv I J f x).ker.starProjection w) =
      (mfderiv I J f x).kerᗮ.starProjection (h.oneillA cov x u w) := by
  have heq := h.oneillA_apply_starProjection_orthogonal_ker cov x u w
  rw [Submodule.starProjection_orthogonal] at heq ⊢
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub] at heq ⊢
  rw [← heq]
  abel

/-- Vertical projection in the second argument of `T` is horizontal projection in its output. -/
theorem oneillT_apply_starProjection_ker (x : M) (u w : TangentSpace I x) :
    h.oneillT cov x u ((mfderiv I J f x).ker.starProjection w) =
      (mfderiv I J f x).kerᗮ.starProjection (h.oneillT cov x u w) := by
  have heq := h.oneillT_apply_starProjection_orthogonal_ker cov x u w
  rw [Submodule.starProjection_orthogonal] at heq ⊢
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub] at heq ⊢
  rw [← heq]
  abel

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [T2Space M] [cov.ContMDiffCovariantDerivative ∞]

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

private theorem contMDiff_reflected_hom_projection
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ TotalSpace.mk' E x
        (((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)
          (cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x (X x) (Y x)))) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  exact (hQ.sub_section hP).clm_bundle_apply
    (((cov.contMDiff_hom cov hP).clm_bundle_apply hX).clm_bundle_apply hY)

/-- For smooth metrics and a smooth connection, the horizontal fundamental tensor is smooth
as a section of the native bundle of continuous bilinear tangent maps. -/
theorem contMDiff_oneillA :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillA cov x)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  apply (contMDiff_reflected_hom_projection h cov (hP.clm_bundle_apply hX) hY).congr
  intro x
  exact congrArg (TotalSpace.mk' E x) (h.oneillA_apply_eq_hom cov x (X x) (Y x))

/-- For smooth metrics and a smooth connection, the vertical fundamental tensor is smooth
as a section of the native bundle of continuous bilinear tangent maps. -/
theorem contMDiff_oneillT :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillT cov x)) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  apply (contMDiff_reflected_hom_projection h cov (hQ.clm_bundle_apply hX) hY).congr
  intro x
  exact congrArg (TotalSpace.mk' E x) (h.oneillT_apply_eq_hom cov x (X x) (Y x))

end TauCeti.IsRiemannianSubmersion
