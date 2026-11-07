/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# O'Neill's tensors of a Riemannian submersion

The fundamental tensors `A` and `T` measure the failure of the Levi-Civita connection to
preserve the horizontal/vertical splitting. With `h` and `v` the orthogonal projections,
our conventions are

* `A_X Y = v ∇_(hX)(hY) + h ∇_(hX)(vY)`;
* `T_X Y = v ∇_(vX)(hY) + h ∇_(vX)(vY)`.

Both are continuous bilinear maps on each tangent space, not operators depending on a
choice of extensions of the input vectors. The construction uses the existing induced
Hom connection to differentiate the smooth orthogonal projections. The evaluation formulas
identify the tensors with the usual vector-field formulas, and their smoothness makes them
available for the fundamental curvature equations of a submersion.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

/-- The sum of the off-diagonal parts of the derivatives of the two projections. -/
private def oneillAux (_h : IsRiemannianSubmersion I J f) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  let cov := leviCivitaConnection I M
  (ContinuousLinearMap.compL ℝ _ _ _ (mfderiv I J f x).kerᗮ.starProjection).comp
      (cov.hom cov (fun y ↦ (mfderiv I J f y).ker.starProjection) x) +
    (ContinuousLinearMap.compL ℝ _ _ _ (mfderiv I J f x).ker.starProjection).comp
      (cov.hom cov (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x)

/-- O'Neill's horizontal fundamental tensor. It is bilinear on tangent vectors and is
characterized on differentiable fields by `oneillA_apply`. -/
def oneillA (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (h.oneillAux x).comp (mfderiv I J f x).kerᗮ.starProjection

/-- O'Neill's vertical fundamental tensor. It is bilinear on tangent vectors and is
characterized on differentiable fields by `oneillT_apply`. -/
def oneillT (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (h.oneillAux x).comp (mfderiv I J f x).ker.starProjection

/-- The horizontal tensor ignores the vertical part of its first argument. -/
@[simp]
theorem oneillA_starProjection_orthogonal_ker (x : M) (u : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection u) = h.oneillA x u := by
  simp [oneillA, Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker u)]

/-- The horizontal tensor vanishes on vertical first arguments. -/
@[simp]
theorem oneillA_starProjection_ker (x : M) (u : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).ker.starProjection u) = 0 := by
  simp [oneillA, Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker u)]

/-- The vertical tensor ignores the horizontal part of its first argument. -/
@[simp]
theorem oneillT_starProjection_ker (x : M) (u : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).ker.starProjection u) = h.oneillT x u := by
  simp [oneillT, Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker u)]

/-- The vertical tensor vanishes on horizontal first arguments. -/
@[simp]
theorem oneillT_starProjection_orthogonal_ker (x : M) (u : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).kerᗮ.starProjection u) = 0 := by
  simp [oneillT, Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker u)]

section Evaluation

variable [FiniteDimensional ℝ F] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {Y : Π x : M, TangentSpace I x} {x : M}

private theorem oneillAux_apply (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillAux x u (Y x) =
      (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x u) +
      (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x u) := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  have hV := (h.contMDiff_starProjection_ker (n := 1) (by simp)).mdifferentiable (by simp) x
  have hH := (h.contMDiff_starProjection_orthogonal_ker (n := 1)
    (by simp)).mdifferentiable (by simp) x
  simp only [oneillAux, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, hom_apply _ _ hV hY, hom_apply _ _ hH hY, map_sub]
  simp [Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem (mfderiv I J f x).ker
      (leviCivitaConnection I M Y x u))]

/-- The defining formula `A_X Y = v ∇_(hX)(hY) + h ∇_(hX)(vY)`.
Only differentiability of `Y` at the evaluated point is needed. -/
theorem oneillA_apply (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillA x u (Y x) =
      (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection u)) +
      (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection u)) := by
  rw [oneillA, ContinuousLinearMap.comp_apply, h.oneillAux_apply hY, add_comm]

/-- The defining formula `T_X Y = v ∇_(vX)(hY) + h ∇_(vX)(vY)`.
Only differentiability of `Y` at the evaluated point is needed. -/
theorem oneillT_apply (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    h.oneillT x u (Y x) =
      (mfderiv I J f x).ker.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection u)) +
      (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection u)) := by
  rw [oneillT, ContinuousLinearMap.comp_apply, h.oneillAux_apply hY, add_comm]

private theorem inner_oneillAux_add_inner (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) (u : TangentSpace I x) :
    ⟪h.oneillAux x u (Y x), Z x⟫_ℝ + ⟪Y x, h.oneillAux x u (Z x)⟫_ℝ = 0 := by
  have : IsManifold I (1 + 1) M := by rw [one_add_one_eq_two]; infer_instance
  have hV := (h.contMDiff_starProjection_ker (n := 1) (by simp)).mdifferentiable (by simp) x
  have hH := (h.contMDiff_starProjection_orthogonal_ker (n := 1)
    (by simp)).mdifferentiable (by simp) x
  have hzero (U W : Π y : M, TangentSpace I y) :
      (fun y ↦ ⟪(mfderiv I J f y).ker.starProjection (U y),
        (mfderiv I J f y).kerᗮ.starProjection (W y)⟫_ℝ) = fun _ ↦ 0 := by
    funext y
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _)
  have hmetric := isMetricCompatible_leviCivitaConnection I (M := M)
  have h₁ := hmetric.mvfderiv_inner_eq (FiberBundle.extend E u)
    (hV.clm_bundle_apply hY) (hH.clm_bundle_apply hZ)
  have h₂ := hmetric.mvfderiv_inner_eq (FiberBundle.extend E u)
    (hH.clm_bundle_apply hY) (hV.clm_bundle_apply hZ)
  have hzero₂ : (fun y ↦ ⟪(mfderiv I J f y).kerᗮ.starProjection (Y y),
      (mfderiv I J f y).ker.starProjection (Z y)⟫_ℝ) = fun _ ↦ 0 :=
    (funext fun _ ↦ real_inner_comm _ _).trans (hzero Z Y)
  rw [hzero] at h₁
  rw [hzero₂] at h₂
  simp only [mvfderiv_const, zero_apply, FiberBundle.extend_apply_self] at h₁ h₂
  rw [h.oneillAux_apply hY, h.oneillAux_apply hZ]
  simp only [inner_add_left, inner_add_right, Submodule.starProjection_orthogonal,
    sub_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    Submodule.inner_starProjection_left_eq_right] at h₁ h₂ ⊢
  linarith

/-- For fixed first argument, O'Neill's horizontal tensor is skew-adjoint. -/
theorem inner_oneillA (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillA x u v, w⟫_ℝ = -⟪v, h.oneillA x u w⟫_ℝ := by
  have hskew := h.inner_oneillAux_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).kerᗮ.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillA, ContinuousLinearMap.comp_apply] using hskew

/-- For fixed first argument, O'Neill's vertical tensor is skew-adjoint. -/
theorem inner_oneillT (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillT x u v, w⟫_ℝ = -⟪v, h.oneillT x u w⟫_ℝ := by
  have hskew := h.inner_oneillAux_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).ker.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillT, ContinuousLinearMap.comp_apply] using hskew

end Evaluation

section Smoothness

variable [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem contMDiff_oneillAux :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillAux x)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hV := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hH := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hDV := contMDiff_hom (leviCivitaConnection I M) (leviCivitaConnection I M) hV
  have hDH := contMDiff_hom (leviCivitaConnection I M) (leviCivitaConnection I M) hH
  apply (TauCeti.Manifold.contMDiff_hom_iff _).mpr
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).mpr
  intro Y hY
  exact ((hH.clm_bundle_apply ((hDV.clm_bundle_apply hX).clm_bundle_apply hY)).add_section
    (hV.clm_bundle_apply ((hDH.clm_bundle_apply hX).clm_bundle_apply hY))).congr
      (fun x ↦ by simp [oneillAux])

/-- O'Neill's horizontal tensor is a smooth section of the bilinear tangent bundle. -/
theorem contMDiff_oneillA :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillA x)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).mpr
  intro X hX
  exact ((h.contMDiff_oneillAux).clm_bundle_apply
    ((h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply hX)).congr
      (fun _ ↦ rfl)

/-- O'Neill's vertical tensor is a smooth section of the bilinear tangent bundle. -/
theorem contMDiff_oneillT :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
        x (h.oneillT x)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  apply (TauCeti.Manifold.contMDiff_hom_iff _).mpr
  intro X hX
  exact ((h.contMDiff_oneillAux).clm_bundle_apply
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hX)).congr
      (fun _ ↦ rfl)

end Smoothness

end TauCeti.IsRiemannianSubmersion
