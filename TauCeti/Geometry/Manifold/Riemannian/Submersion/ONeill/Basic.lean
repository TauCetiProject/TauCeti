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
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# O'Neill's fundamental tensors

For a Riemannian submersion, the fundamental tensors measure the parts of the
Levi-Civita derivative that exchange the horizontal and vertical distributions.
`oneillA` takes the horizontal part of its first argument, while `oneillT` takes
its vertical part. Both are continuous bilinear maps on each tangent space,
not differential operators on freely chosen extensions of tangent vectors.

The construction uses the induced endomorphism connection to differentiate the
native horizontal orthogonal projection. Conversely, the endomorphism-connection
derivatives of the horizontal and vertical orthogonal projections are recovered
from `oneillA + oneillT` by `hom_starProjection_orthogonal_ker_apply` and
`hom_starProjection_ker_apply`. The evaluation theorems identify the tensors with
O'Neill's formulas on differentiable vector fields. For a fixed first argument, both tensors are
skew-adjoint, by metric compatibility of the Levi-Civita connection. Both tensors are smooth
sections of the native iterated Hom bundle, so smooth vector fields give smooth
evaluations, and both are bounded in the Riemannian fibre norm near each point
and on every compact subset of the source (`eventually_norm_oneillA_le`,
`exists_norm_oneillA_le_of_isCompact`, `eventually_norm_oneillT_le`,
`exists_norm_oneillT_le_of_isCompact`).

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13
  (1966), 459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.

The construction uses `CovariantDerivative.hom_apply` and the native smooth
orthogonal projections from `Submersion.Smoothness`.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
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
def oneillA (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    ((h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x)

/-- O'Neill's vertical fundamental tensor, as a continuous bilinear map.
Its defining field formula is `oneillT_apply`. -/
def oneillT (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (exchangeTensor (I := I) (J := J) (f := f) x).comp
    (ContinuousLinearMap.id ℝ _ -
      (h.horizontalLift x).toContinuousLinearMap ∘L mfderiv I J f x)

include h

private theorem exchangeTensor_apply {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    exchangeTensor (I := I) (J := J) (f := f) x v (Y x) =
      (mfderiv I J f x).ker.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection (Y y)) x v) +
      (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ (mfderiv I J f y).ker.starProjection (Y y)) x v) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let P := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
  let Q := fun y ↦ (mfderiv I J f y).ker.starProjection
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
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
  simpa only [oneillA, h.horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using
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
  simpa only [oneillT, h.id_sub_horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply, add_comm] using
    h.exchangeTensor_apply hY ((mfderiv I J f x).ker.starProjection v)

private theorem inner_exchangeTensor_add_inner {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (u : TangentSpace I x) :
    ⟪exchangeTensor (I := I) (J := J) (f := f) x u (Y x), Z x⟫_ℝ +
      ⟪Y x, exchangeTensor (I := I) (J := J) (f := f) x u (Z x)⟫_ℝ = 0 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hV := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hH := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hzero (U W : Π y : M, TangentSpace I y) :
      (fun y ↦ ⟪(mfderiv I J f y).ker.starProjection (U y),
        (mfderiv I J f y).kerᗮ.starProjection (W y)⟫_ℝ) = fun _ ↦ 0 := by
    funext y
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem _ _) (Submodule.starProjection_apply_mem _ _)
  have hmetric := CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)
  have h₁ := hmetric.mvfderiv_inner_eq (FiberBundle.extend E u)
    (hV.clm_bundle_apply hY) (hH.clm_bundle_apply hZ)
  have h₂ := hmetric.mvfderiv_inner_eq (FiberBundle.extend E u)
    (hH.clm_bundle_apply hY) (hV.clm_bundle_apply hZ)
  have hzero₂ : (fun y ↦ ⟪(mfderiv I J f y).kerᗮ.starProjection (Y y),
      (mfderiv I J f y).ker.starProjection (Z y)⟫_ℝ) = fun _ ↦ 0 :=
    (funext fun _ ↦ real_inner_comm _ _).trans (hzero Z Y)
  rw [hzero] at h₁
  rw [hzero₂] at h₂
  simp only [mvfderiv_const, zero_apply, FiberBundle.extend_apply_self]
    at h₁ h₂
  rw [h.exchangeTensor_apply hY, h.exchangeTensor_apply hZ]
  simp only [inner_add_left, inner_add_right, Submodule.starProjection_orthogonal,
    sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    inner_sub_right, Submodule.inner_starProjection_left_eq_right] at h₁ h₂ ⊢
  linarith

/-- For a fixed first argument, O'Neill's horizontal tensor is skew-adjoint. -/
theorem inner_oneillA (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillA x u v, w⟫_ℝ = -⟪v, h.oneillA x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).kerᗮ.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillA, h.horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using hskew

/-- For a fixed first argument, O'Neill's vertical tensor is skew-adjoint. -/
theorem inner_oneillT (x : M) (u v w : TangentSpace I x) :
    ⟪h.oneillT x u v, w⟫_ℝ = -⟪v, h.oneillT x u w⟫_ℝ := by
  have hskew := h.inner_exchangeTensor_add_inner
    (FiberBundle.mdifferentiableAt_extend I E v) (FiberBundle.mdifferentiableAt_extend I E w)
    ((mfderiv I J f x).ker.starProjection u)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [FiberBundle.extend_apply_self, oneillT, h.id_sub_horizontalLift_comp_mfderiv,
    ContinuousLinearMap.comp_apply] using hskew

section Smoothness

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
  simpa only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply] using
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
  simpa only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply] using
    h.contMDiff_exchangeTensor_apply hQX hY

end Smoothness

section Bounds

private theorem contMDiffOn_exchangeTensor_apply {u : Set M} (hu : IsOpen u)
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I I.tangent ∞ (T% X) u)
    (hY : ContMDiffOn I I.tangent ∞ (T% Y) u) :
    ContMDiffOn I I.tangent ∞
      (T% (fun x ↦ exchangeTensor (I := I) (J := J) (f := f) x (X x) (Y x))) u := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).contMDiffOn (s := u)
  have hQ := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).contMDiffOn (s := u)
  have hPY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ + 1)
      (T% (fun x ↦ (mfderiv I J f x).kerᗮ.starProjection (Y x))) u :=
    (hP.clm_bundle_apply hY).of_le (by simp)
  have hQY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ + 1)
      (T% (fun x ↦ (mfderiv I J f x).ker.starProjection (Y x))) u :=
    (hQ.clm_bundle_apply hY).of_le (by simp)
  have hD₁ := (CovariantDerivative.contMDiffOn_leviCivitaConnection (I := I) (M := M)
    (n := ∞) (m := ∞) (k := ∞) hu (by simp) (by simp) hPY).clm_bundle_apply hX
  have hD₂ := (CovariantDerivative.contMDiffOn_leviCivitaConnection (I := I) (M := M)
    (n := ∞) (m := ∞) (k := ∞) hu (by simp) (by simp) hQY).clm_bundle_apply hX
  refine ContMDiffOn.congr (fun x hx ↦ ((hQ.clm_bundle_apply hD₁) x hx).add_section
      ((hP.clm_bundle_apply hD₂) x hx)) fun x hx ↦ ?_
  exact congrArg (TotalSpace.mk' E x)
    (h.exchangeTensor_apply (((hY x hx).contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp))
      (X x))

private theorem eventually_norm_exchangeTensor_le (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y,
      ‖exchangeTensor (I := I) (J := J) (f := f) y u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun y : M ↦ TangentSpace I y)
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  let L := fun i ↦ (b.coord i).toContinuousLinearMap
  let W := fun i j y ↦
    exchangeTensor (I := I) (J := J) (f := f) y (e.localFrame b i y) (e.localFrame b j y)
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hW (i j : Fin (Module.finrank ℝ E)) :
      ∀ᶠ y in 𝓝 x, ‖W i j y‖ ≤ ‖W i j x‖ + 1 := by
    have hc := (contMDiffOn_exchangeTensor_apply h e.open_baseSet
      (e.contMDiffOn_localFrame_baseSet (I := I) ∞ b i)
      (e.contMDiffOn_localFrame_baseSet (I := I) ∞ b j)).contMDiffAt
      (e.open_baseSet.mem_nhds hxe)
    exact ((TauCeti.continuous_norm_bundle E (TangentSpace I)).continuousAt.comp
      hc.continuousAt).eventually (Iic_mem_nhds (lt_add_one _))
  obtain ⟨K, hKpos, hK⟩ :=
    eventually_norm_trivializationAt_lt E (fun y : M ↦ TangentSpace I y) x
  refine ⟨∑ i, ∑ j, (‖L i‖ * K) * (‖L j‖ * K) * (‖W i j x‖ + 1),
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity, ?_⟩
  filter_upwards [e.open_baseSet.mem_nhds hxe, hK,
    Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦ hW i j]
    with y hye hyK hyW u v
  have hexp : exchangeTensor (I := I) (J := J) (f := f) y u v =
      ∑ i, ∑ j, (b.repr (e.continuousLinearMapAt ℝ y u) i *
        b.repr (e.continuousLinearMapAt ℝ y v) j) • W i j y := by
    conv_lhs => rw [b.eq_sum_repr_continuousLinearMapAt_smul_localFrame (𝕜 := ℝ) hye u]
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [b.eq_sum_repr_continuousLinearMapAt_smul_localFrame (𝕜 := ℝ) hye v]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, W]
  have hcoord {z : TangentSpace I y} (i : Fin (Module.finrank ℝ E)) :
      |b.repr (e.continuousLinearMapAt ℝ y z) i| ≤ ‖L i‖ * (K * ‖z‖) := by
    have hLi : b.repr (e.continuousLinearMapAt ℝ y z) i =
        L i (e.continuousLinearMapAt ℝ y z) := rfl
    rw [← Real.norm_eq_abs, hLi]
    exact ((L i).le_opNorm _).trans <| mul_le_mul_of_nonneg_left
      (((e.continuousLinearMapAt ℝ y).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right hyK.le (norm_nonneg z))) (norm_nonneg _)
  rw [hexp, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  calc |b.repr (e.continuousLinearMapAt ℝ y u) i| *
          |b.repr (e.continuousLinearMapAt ℝ y v) j| * ‖W i j y‖
      ≤ (‖L i‖ * (K * ‖u‖)) * (‖L j‖ * (K * ‖v‖)) * (‖W i j x‖ + 1) := by
        gcongr
        · exact hcoord i
        · exact hcoord j
        · exact hyW i j
    _ = (‖L i‖ * K) * (‖L j‖ * K) * (‖W i j x‖ + 1) * ‖u‖ * ‖v‖ := by ring

/-- O'Neill's horizontal fundamental tensor is locally bounded in the Riemannian fibre norm. -/
theorem eventually_norm_oneillA_le (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y,
      ‖h.oneillA y u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := eventually_norm_exchangeTensor_le h x
  refine ⟨C, hC0, hC.mono fun y hy u v ↦ ?_⟩
  rw [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  refine (hy _ v).trans ?_
  gcongr
  exact Submodule.norm_starProjection_apply_le _ _

/-- O'Neill's vertical fundamental tensor is locally bounded in the Riemannian fibre norm. -/
theorem eventually_norm_oneillT_le (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y,
      ‖h.oneillT y u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := eventually_norm_exchangeTensor_le h x
  refine ⟨C, hC0, hC.mono fun y hy u v ↦ ?_⟩
  rw [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  refine (hy _ v).trans ?_
  gcongr
  exact Submodule.norm_starProjection_apply_le _ _

/-- O'Neill's horizontal fundamental tensor is bounded in the Riemannian fibre norm on every
compact subset of the source manifold. -/
theorem exists_norm_oneillA_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u v : TangentSpace I x,
      ‖h.oneillA x u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  refine hK.induction_on ⟨0, le_rfl, by simp⟩
    (fun _ _ hst ⟨C, hC0, hC⟩ ↦ ⟨C, hC0, fun x hx ↦ hC x (hst hx)⟩)
    (fun _ _ ⟨C, hC0, hC⟩ ⟨C', _, hC'⟩ ↦ ⟨max C C', le_max_of_le_left hC0, fun x hx u v ↦ ?_⟩)
    fun x _ ↦ ?_
  · rcases hx with hx | hx
    · exact (hC x hx u v).trans (by gcongr; exact le_max_left C C')
    · exact (hC' x hx u v).trans (by gcongr; exact le_max_right C C')
  · obtain ⟨C, hC0, hC⟩ := h.eventually_norm_oneillA_le x
    exact ⟨{y | ∀ u v : TangentSpace I y, ‖h.oneillA y u v‖ ≤ C * ‖u‖ * ‖v‖},
      mem_nhdsWithin_of_mem_nhds hC, C, hC0, fun _ hy ↦ hy⟩

/-- O'Neill's vertical fundamental tensor is bounded in the Riemannian fibre norm on every
compact subset of the source manifold. -/
theorem exists_norm_oneillT_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u v : TangentSpace I x,
      ‖h.oneillT x u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  refine hK.induction_on ⟨0, le_rfl, by simp⟩
    (fun _ _ hst ⟨C, hC0, hC⟩ ↦ ⟨C, hC0, fun x hx ↦ hC x (hst hx)⟩)
    (fun _ _ ⟨C, hC0, hC⟩ ⟨C', _, hC'⟩ ↦ ⟨max C C', le_max_of_le_left hC0, fun x hx u v ↦ ?_⟩)
    fun x _ ↦ ?_
  · rcases hx with hx | hx
    · exact (hC x hx u v).trans (by gcongr; exact le_max_left C C')
    · exact (hC' x hx u v).trans (by gcongr; exact le_max_right C C')
  · obtain ⟨C, hC0, hC⟩ := h.eventually_norm_oneillT_le x
    exact ⟨{y | ∀ u v : TangentSpace I y, ‖h.oneillT y u v‖ ≤ C * ‖u‖ * ‖v‖},
      mem_nhdsWithin_of_mem_nhds hC, C, hC0, fun _ hy ↦ hy⟩

end Bounds

section Projections

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
private theorem oneillA_add_oneillT (x : M) (u : TangentSpace I x) :
    h.oneillA x u + h.oneillT x u = exchangeTensor (I := I) (J := J) (f := f) x u := by
  simp only [oneillA, oneillT, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, add_sub_cancel]

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- The endomorphism-connection derivative of the horizontal orthogonal projection is expressed
in terms of O'Neill's tensors by `(∇_u P) w = Q (A_u w + T_u w) - P (A_u w + T_u w)`. -/
theorem hom_starProjection_orthogonal_ker_apply (x : M) (u w : TangentSpace I x) :
    (CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M)
        (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x u w =
      (mfderiv I J f x).ker.starProjection (h.oneillA x u w + h.oneillT x u w) -
        (mfderiv I J f x).kerᗮ.starProjection (h.oneillA x u w + h.oneillT x u w) := by
  let P := (mfderiv I J f x).kerᗮ.starProjection
  let Q := (mfderiv I J f x).ker.starProjection
  let z := (CovariantDerivative.leviCivitaConnection I M).hom
    (CovariantDerivative.leviCivitaConnection I M)
    (fun y ↦ (mfderiv I J f y).kerᗮ.starProjection) x u w
  have hPP : P (P z) = P z :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hQQ : Q (Q z) = Q z :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hPQ : P (Q z) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.starProjection_apply_mem _ _)
  have hQP : Q (P z) = 0 := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Submodule.starProjection_orthogonal_apply_eq_zero
        (Submodule.starProjection_apply_mem (mfderiv I J f x).kerᗮ z)
  have hsum : Q z + P z = z := by
    simp only [P, Q, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, add_sub_cancel]
  have hex : h.oneillA x u w + h.oneillT x u w = Q z - P z := by
    rw [← add_apply, oneillA_add_oneillT h]
    simp [exchangeTensor, P, Q, z]
  rw [hex]
  dsimp only [P, Q] at hPP hQQ hPQ hQP hsum
  rw [map_sub, map_sub, hQQ, hQP, hPQ, hPP, sub_zero, zero_sub, sub_neg_eq_add, hsum]

/-- The endomorphism-connection derivative of the vertical orthogonal projection is expressed
in terms of O'Neill's tensors by `(∇_u Q) w = P (A_u w + T_u w) - Q (A_u w + T_u w)`. -/
theorem hom_starProjection_ker_apply (x : M) (u w : TangentSpace I x) :
    (CovariantDerivative.leviCivitaConnection I M).hom
        (CovariantDerivative.leviCivitaConnection I M)
        (fun y ↦ (mfderiv I J f y).ker.starProjection) x u w =
      (mfderiv I J f x).kerᗮ.starProjection (h.oneillA x u w + h.oneillT x u w) -
        (mfderiv I J f x).ker.starProjection (h.oneillA x u w + h.oneillT x u w) := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let P := fun y ↦ (mfderiv I J f y).kerᗮ.starProjection
  let Q := fun y ↦ (mfderiv I J f y).ker.starProjection
  let cov := CovariantDerivative.leviCivitaConnection I M
  let Y := FiberBundle.extend E w
  have hP := (h.contMDiff_starProjection_orthogonal_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hQ := (h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
    (by simp) (x := x)
  have hY : MDiffAt (T% Y) x := FiberBundle.mdifferentiableAt_extend I E w
  have hsplit : (fun y ↦ Q y (Y y)) = Y - fun y ↦ P y (Y y) := by
    ext y
    simp only [P, Q, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply]
    abel
  have hQY : cov (fun y ↦ Q y (Y y)) x u =
      cov Y x u - cov (fun y ↦ P y (Y y)) x u := by
    rw [hsplit, cov.isCovariantDerivativeOnUniv.sub hY (hP.clm_bundle_apply hY)]
    rfl
  have hhomQ := CovariantDerivative.hom_apply cov cov hQ hY u
  have hhomP := CovariantDerivative.hom_apply cov cov hP hY u
  simp only [Y, FiberBundle.extend_apply_self] at hhomQ hhomP hQY
  have hneg : cov.hom cov Q x u w = -cov.hom cov P x u w := by
    rw [hhomQ, hhomP, hQY]
    simp only [P, Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply]
    abel
  dsimp only [P, Q, cov] at hneg
  rw [hneg, h.hom_starProjection_orthogonal_ker_apply, neg_sub]

end Projections

omit [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- The first argument of `A` depends only on its horizontal component. -/
@[simp] theorem oneillA_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).kerᗮ.starProjection v) = h.oneillA x v := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- The first argument of `T` depends only on its vertical component. -/
@[simp] theorem oneillT_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).ker.starProjection v) = h.oneillT x v := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]

/-- `A` vanishes on vertical first arguments. -/
@[simp] theorem oneillA_starProjection_ker (x : M) (v : TangentSpace I x) :
    h.oneillA x ((mfderiv I J f x).ker.starProjection v) = 0 := by
  simp only [oneillA, h.horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

/-- `T` vanishes on horizontal first arguments. -/
@[simp] theorem oneillT_starProjection_orthogonal_ker (x : M) (v : TangentSpace I x) :
    h.oneillT x ((mfderiv I J f x).kerᗮ.starProjection v) = 0 := by
  simp only [oneillT, h.id_sub_horizontalLift_comp_mfderiv, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  simp

end TauCeti.IsRiemannianSubmersion
