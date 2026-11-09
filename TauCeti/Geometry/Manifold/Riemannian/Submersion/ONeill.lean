/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# O'Neill's fundamental tensors

For a Riemannian submersion, the fundamental tensors measure the parts of the
Levi-Civita derivative that exchange the horizontal and vertical distributions.
`oneillA` takes the horizontal part of its first argument, while `oneillT` takes
its vertical part. Both are continuous bilinear maps on each tangent space,
not differential operators on freely chosen extensions of tangent vectors.

The construction uses the induced endomorphism connection to differentiate the
native horizontal orthogonal projection. The evaluation theorems identify it with
O'Neill's formulas on differentiable vector fields; metric compatibility gives
skew-adjointness in the last two arguments. Both tensors are smooth
sections of the native iterated Hom bundle, so smooth vector fields give smooth
evaluations.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13
  (1966), 459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.

The construction uses `CovariantDerivative.hom_apply` and the native smooth
orthogonal projections from `Submersion.Smoothness`.
-/

public section

open Bundle CovariantDerivative Manifold
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

private def exchangeTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.compL ℝ _ _ _
    ((mfderiv I J f x).ker.starProjection - (mfderiv I J f x).kerᗮ.starProjection)).comp
      ((CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M)
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x)

/-- O'Neill's horizontal fundamental tensor, as a continuous bilinear map.
Its defining field formula is `oneillA_apply`. -/
def oneillA (_h : IsRiemannianSubmersion I J f) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    (mfderiv I J f x).kerᗮ.starProjection

/-- O'Neill's vertical fundamental tensor, as a continuous bilinear map.
Its defining field formula is `oneillT_apply`. -/
def oneillT (_h : IsRiemannianSubmersion I J f) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    (mfderiv I J f x).ker.starProjection

include h

section Evaluation

variable [FiniteDimensional ℝ F] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

local instance : IsManifold I (1 + 1) M := by
  rw [one_add_one_eq_two]
  infer_instance

private theorem mdifferentiableAt_starProjections (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        y (mfderiv I J f y).ker.starProjection) x ∧
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        y (mfderiv I J f y).kerᗮ.starProjection) x :=
  ⟨(h.contMDiff_starProjection_ker (n := 1) (by simp)).mdifferentiable (by simp) x,
    (h.contMDiff_starProjection_orthogonal_ker (n := 1) (by simp)).mdifferentiable (by simp) x⟩

private theorem exchangeTensor_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    exchangeTensor (I := I) (J := J) (f := f) x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x v) +
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x v) := by
  let P := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
  let Q := fun y ↦ (mfderiv I J f y).ker.starProjection
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hP := (h.mdifferentiableAt_starProjections x).2
  have hPY := hP.clm_bundle_apply hY
  have hsplit : (fun y ↦ Q y (Y y)) = Y - fun y ↦ P y (Y y) := by
    ext y
    simp only [P, Q, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply]
    abel
  have hQY : cov (fun y ↦ Q y (Y y)) x v =
      cov Y x v - cov (fun y ↦ P y (Y y)) x v := by
    rw [hsplit, cov.isCovariantDerivativeOnUniv.sub hY hPY]
    rfl
  have hPP (w : TangentSpace I x) : P x (P x w) = P x w :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hQP (w : TangentSpace I x) : Q x (P x w) = 0 := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Submodule.starProjection_orthogonal_apply_eq_zero
        (Submodule.starProjection_apply_mem (mfderiv I J f x).kerᗮ w)
  dsimp only [P, Q, cov] at hPP hQP hQY
  simp only [exchangeTensor, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    sub_apply, CovariantDerivative.hom_apply _ _ hP hY,
    map_sub, hPP, hQP]
  rw [hQY, map_sub]
  abel

/-- The horizontal fundamental tensor has O'Neill's field formula
`A_X Y = v ∇_(hX)(hY) + h ∇_(hX)(vY)`. Only differentiability of `Y` at
this point is needed; the direction is a tangent vector, not an extended field. -/
theorem oneillA_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    h.oneillA x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection v)) +
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).kerᗮ.starProjection v)) := by
  simpa only [oneillA, ContinuousLinearMap.comp_apply] using
    h.exchangeTensor_apply hY ((mfderiv I J f x).kerᗮ.starProjection v)

/-- The vertical fundamental tensor has O'Neill's field formula
`T_X Y = h ∇_(vX)(vY) + v ∇_(vX)(hY)`. -/
theorem oneillT_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    h.oneillT x v (Y x) =
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection v)) +
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x
          ((mfderiv I J f x).ker.starProjection v)) := by
  simpa only [oneillT, ContinuousLinearMap.comp_apply, add_comm] using
    h.exchangeTensor_apply hY ((mfderiv I J f x).ker.starProjection v)

private theorem inner_exchangeTensor_add_inner
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (u : TangentSpace I x) :
    ⟪exchangeTensor (I := I) (J := J) (f := f) x u (Y x), Z x⟫_ℝ +
      ⟪Y x, exchangeTensor (I := I) (J := J) (f := f) x u (Z x)⟫_ℝ = 0 := by
  obtain ⟨hV, hH⟩ := h.mdifferentiableAt_starProjections x
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
  rw [h.exchangeTensor_apply hY, h.exchangeTensor_apply hZ]
  simp only [inner_add_left, inner_add_right, Submodule.starProjection_orthogonal,
    sub_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    Submodule.inner_starProjection_left_eq_right] at h₁ h₂ ⊢
  linarith

/-- For fixed first argument, O'Neill's horizontal tensor is skew-adjoint. -/
theorem inner_oneillA (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillA x u v, w⟫_ℝ = -⟪v, h.oneillA x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).kerᗮ.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillA,
    ContinuousLinearMap.comp_apply] using hskew

/-- For fixed first argument, O'Neill's vertical tensor is skew-adjoint. -/
theorem inner_oneillT (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillT x u v, w⟫_ℝ = -⟪v, h.oneillT x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).ker.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillT,
    ContinuousLinearMap.comp_apply] using hskew

end Evaluation

section Smoothness

variable [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem contMDiff_exchangeTensor_apply
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff I I.tangent ∞ (T% Y)) :
    ContMDiff I I.tangent ∞
      (T% (fun x ↦ exchangeTensor (I := I) (J := J) (f := f) x (X x) (Y x))) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hP := h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hD₁ := cov.contMDiff_apply hX ((hP.clm_bundle_apply hY).of_le (by simp))
  have hD₂ := cov.contMDiff_apply hX ((hQ.clm_bundle_apply hY).of_le (by simp))
  refine ((hQ.clm_bundle_apply hD₁).add_section (hP.clm_bundle_apply hD₂)).congr ?_
  intro x
  exact congrArg (TotalSpace.mk' E x)
    (h.exchangeTensor_apply (hY.mdifferentiableAt (by simp)) (X x))

variable [T2Space M]

/-- The horizontal fundamental tensor is a smooth section of the native bilinear Hom bundle. -/
theorem contMDiff_oneillA :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
        x (h.oneillA x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hPX := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).clm_bundle_apply hX
  simpa only [oneillA, ContinuousLinearMap.comp_apply] using
    h.contMDiff_exchangeTensor_apply hPX hY

/-- The vertical fundamental tensor is a smooth section of the native bilinear Hom bundle. -/
theorem contMDiff_oneillT :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
        x (h.oneillT x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hQX := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).clm_bundle_apply hX
  simpa only [oneillT, ContinuousLinearMap.comp_apply] using
    h.contMDiff_exchangeTensor_apply hQX hY

end Smoothness

/-- The first argument of `A` depends only on its horizontal component. -/
@[simp] theorem oneillA_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection v) = h.oneillA x v := by
  simp only [oneillA, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The first argument of `T` depends only on its vertical component. -/
@[simp] theorem oneillT_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).ker.starProjection v) = h.oneillT x v := by
  simp only [oneillT, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- `A` vanishes on vertical first arguments. -/
@[simp] theorem oneillA_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).ker.starProjection v) = 0 := by
  simp only [oneillA, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

/-- `T` vanishes on horizontal first arguments. -/
@[simp] theorem oneillT_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).kerᗮ.starProjection v) = 0 := by
  simp only [oneillT, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

end TauCeti.IsRiemannianSubmersion
