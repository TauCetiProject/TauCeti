/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Weingarten
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Immersions into a Euclidean space: affine maps and the round sphere

Let `F` be a finite-dimensional real inner product space with its flat Levi-Civita connection.
For a map `f : M → F`, a field `V` along `f` is an `F`-valued map, and its covariant derivative
along `f` is its ordinary derivative
(`TauCeti.Manifold.alongMap_leviCivitaConnection_model_space`), since the Christoffel map of the
flat metric vanishes. So the second fundamental form of `f` is the
normal part of the derivative of `y ↦ df_y (Y y)`
(`TauCeti.immersionSecondFundamentalForm_model_space`).

This computes the second fundamental form, shape operator, principal curvatures and mean curvature
vector of two basic examples:

* An affine map `y ↦ p + L y` from a normed space `E` (for instance an affine hyperplane or plane)
  has vanishing second fundamental form. So every shape operator vanishes, every principal
  curvature is `0`, and the mean curvature vector is `0`: affine maps are minimal.
* For the inclusion of the unit sphere `Sⁿ ⊆ E`, `dim E = n + 1`, with its round metric, the
  second fundamental form is `B_x(v, w) = -⟪v, w⟫ x`. Hence the shape operator in the direction `ν`
  is `S_ν = -⟪x, ν⟫ id`: in the outward direction `ν = x` every principal curvature is `-1`, and in
  the inward direction `-x` every principal curvature is `1`. The trace of `B` is `-n x`, and for
  `n > 0` the mean curvature vector is `H = -x`. For the unit two-sphere `tr B = -2ν` and `H = -ν`
  for the outward normal `ν = x`.

## Main results

* `TauCeti.immersionSecondFundamentalForm_model_space`: `B(X, Y) = (D_X (df Y))^⊥`.
* `TauCeti.immersionSecondFundamentalFormAt_affine`, `TauCeti.immersionShapeOperatorAt_affine`,
  `TauCeti.immersionPrincipalCurvatures_affine`, `TauCeti.immersionMeanCurvatureVector_affine`:
  affine maps have `B = 0`, `S_ν = 0`, principal curvatures `0` and `H = 0`.
* `TauCeti.orthogonalNormalSpace_subtypeVal_sphere`: the normal space of `Sⁿ` at `x` is `ℝ x`.
* `TauCeti.immersionSecondFundamentalFormAt_subtypeVal_sphere`: `B_x(v, w) = -⟪v, w⟫ x`.
* `TauCeti.immersionShapeOperatorAt_subtypeVal_sphere`: `S_ν = -⟪x, ν⟫ id`, and
  `TauCeti.immersionShapeOperatorAt_subtypeVal_sphere_self`: `S_x = -id`.
* `TauCeti.immersionPrincipalCurvatures_subtypeVal_sphere_self` and
  `TauCeti.immersionPrincipalCurvatures_subtypeVal_sphere_neg`: the outward principal curvatures
  are all `-1` and the inward ones are all `1`.
* `TauCeti.metricTrace_immersionSecondFundamentalFormAt_subtypeVal_sphere`: `tr B = -n x`.
* `TauCeti.immersionMeanCurvatureVector_subtypeVal_sphere`: `H = -x` for `n > 0`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8
  (the second fundamental form, the shape operator and the mean curvature of hypersurfaces).
-/

public section

noncomputable section

open Bundle Manifold Module Metric
open scoped InnerProductSpace Manifold ContDiff

namespace TauCeti

open TauCeti.Manifold CovariantDerivative

section Flat

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The second fundamental form of a map into a Euclidean space**: `B(X, Y)` is the normal part
of the derivative, in the direction `X`, of the `F`-valued map `y ↦ df_y (Y y)`. -/
theorem immersionSecondFundamentalForm_model_space {f : M → F} {X Y : Π y : M, TangentSpace I y}
    {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (hY : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ (mfderiv I 𝓘(ℝ, F) f y (Y y) : F)) x) :
    immersionSecondFundamentalForm (leviCivitaConnection 𝓘(ℝ, F) F) f X Y x =
      (orthogonalNormalSpace I 𝓘(ℝ, F) f x).starProjection
        (mfderiv I 𝓘(ℝ, F) (fun y ↦ (mfderiv I 𝓘(ℝ, F) f y (Y y) : F)) x (X x)) := by
  rw [immersionSecondFundamentalForm_def, alongMap_leviCivitaConnection_model_space hf hY]

end Flat

/-! ### Affine maps -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **An affine map into a Euclidean space has vanishing second fundamental form.** This includes
affine hyperplanes and affine planes. -/
@[simp]
theorem immersionSecondFundamentalFormAt_affine (p : F) (L : E →L[ℝ] F) (x : E) :
    immersionSecondFundamentalFormAt (I := 𝓘(ℝ, E)) (leviCivitaConnection 𝓘(ℝ, F) F)
      (fun y ↦ p + L y) x = 0 := by
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 (fun y ↦ p + L y) x := by
    rw [contMDiffAt_iff_contDiffAt]; fun_prop
  have hd (y w : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y ↦ p + L y) y w = L w :=
    DFunLike.congr_fun ((L.hasFDerivAt.const_add p).hasMFDerivAt).mfderiv w
  ext v w
  have hc (u : E) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun z ↦ (⟨z, u⟩ : TangentBundle 𝓘(ℝ, E) E)) x :=
    ((contMDiff_tangentBundle_mk_const u (n := 1)).mdifferentiable one_ne_zero) x
  rw [zero_apply, zero_apply,
    immersionSecondFundamentalFormAt_apply (X := fun _ ↦ v) (Y := fun _ ↦ w) hf (hc v) (hc w),
    immersionSecondFundamentalForm_model_space (I := 𝓘(ℝ, E)) (X := fun _ ↦ v)
      (Y := fun _ ↦ w) (hf.mdifferentiableAt (by norm_num))]
  · have hY : (fun y ↦ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun y ↦ p + L y) y w : F)) = fun _ ↦ L w :=
      funext fun y ↦ hd y w
    rw [hY, mfderiv_const]
    exact map_zero _
  · exact (mdifferentiableAt_const (c := L w)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ hd y w)

variable [RiemannianBundle (fun y : E ↦ TangentSpace 𝓘(ℝ, E) y)]

/-- Every shape operator of an affine map into a Euclidean space vanishes. -/
theorem immersionShapeOperatorAt_affine (p : F) (L : E →L[ℝ] F) (x : E)
    (ν : TangentSpace 𝓘(ℝ, F) (p + L x)) :
    immersionShapeOperatorAt (I := 𝓘(ℝ, E)) (leviCivitaConnection 𝓘(ℝ, F) F)
      (fun y ↦ p + L y) x ν = 0 := by
  refine ((eq_immersionShapeOperatorAt_iff (I := 𝓘(ℝ, E))
    (cov := leviCivitaConnection 𝓘(ℝ, F) F) (f := fun y ↦ p + L y) ν
    (0 : Module.End ℝ (TangentSpace 𝓘(ℝ, E) x))).mpr fun v w ↦ ?_).symm
  rw [immersionSecondFundamentalFormAt_affine, LinearMap.zero_apply,
    zero_apply, zero_apply, inner_zero_left, inner_zero_left]

/-- **Every principal curvature of an affine map vanishes**, in every normal direction. In
particular an affine hyperplane in a Euclidean space has all principal curvatures `0`. -/
theorem immersionPrincipalCurvatures_affine (p : F) (L : E →L[ℝ] F) (x : E)
    (ht : (leviCivitaConnection 𝓘(ℝ, F) F).IsTorsionFree) {m : ℕ} (hm : finrank ℝ E = m)
    (ν : TangentSpace 𝓘(ℝ, F) (p + L x)) (i : Fin m) :
    immersionPrincipalCurvatures 𝓘(ℝ, E) (fun y ↦ p + L y) x ht hm ν i = 0 :=
  immersionPrincipalCurvatures_eq_of_immersionShapeOperatorAt_eq_smul (I := 𝓘(ℝ, E))
    (cov := leviCivitaConnection 𝓘(ℝ, F) F) (f := fun y ↦ p + L y) (x := x) ht hm ν (c := 0)
    ((immersionShapeOperatorAt_affine p L x ν).trans (zero_smul ℝ _).symm) i

/-- **Affine maps are minimal**: the mean curvature vector of an affine map into a Euclidean space
vanishes. In particular an affine plane has `H = 0`. -/
@[simp]
theorem immersionMeanCurvatureVector_affine (p : F) (L : E →L[ℝ] F) (x : E) :
    immersionMeanCurvatureVector (I := 𝓘(ℝ, E)) (leviCivitaConnection 𝓘(ℝ, F) F)
      (fun y ↦ p + L y) x = 0 :=
  immersionMeanCurvatureVector_eq_zero_of_immersionSecondFundamentalFormAt_eq_zero
    (immersionSecondFundamentalFormAt_affine p L x)

end Affine

/-! ### The round sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in
/-- The normal space of the unit sphere at `x` is the line through `x`. -/
@[simp]
theorem orthogonalNormalSpace_subtypeVal_sphere (x : sphere (0 : E) 1) :
    orthogonalNormalSpace (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x = ℝ ∙ (x : E) := by
  rw [orthogonalNormalSpace_def]
  have h := range_mvfderiv_subtypeVal (n := n) x
  -- For a map into the vector space `E`, `mfderiv` and `mvfderiv` are the same linear map up to
  -- the identification `TangentSpace 𝓘(ℝ, E) x = E`; restate the range with `mvfderiv`.
  change (LinearMap.range (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap)ᗮ = _
  rw [h, Submodule.orthogonal_orthogonal]

/-- The Weingarten pairing of the sphere with the outward position field `ν y = y`: its shape
operator is `-df`, so `⟪B(X, Y), x⟫ = -⟪X x, Y x⟫`. -/
private theorem inner_immersionSecondFundamentalForm_subtypeVal_sphere (x : sphere (0 : E) 1)
    {X Y : Π y : sphere (0 : E) 1, TangentSpace (𝓡 n) y}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) x) :
    ⟪immersionSecondFundamentalForm (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) X Y x, (x : E)⟫_ℝ = -⟪X x, Y x⟫_ℝ := by
  set ι : sphere (0 : E) 1 → E := (↑)
  have hι : MDifferentiable (𝓡 n) 𝓘(ℝ, E) ι :=
    (contMDiff_coe_sphere (n := n) (m := 1)).mdifferentiable one_ne_zero
  let ν : Π y : sphere (0 : E) 1, TangentSpace 𝓘(ℝ, E) (ι y) := fun y ↦ (y : E)
  have hν : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (sectionCoord ℝ (F := E) ι ν (ι x)) x := by
    rw [sectionCoord_model_space]; exact hι x
  have hνn : ∀ᶠ y in nhds x, ν y ∈ orthogonalNormalSpace (𝓡 n) 𝓘(ℝ, E) ι y :=
    Filter.Eventually.of_forall fun y ↦ by
      rw [orthogonalNormalSpace_subtypeVal_sphere]; exact Submodule.mem_span_singleton_self (y : E)
  have hdY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (sectionCoord ℝ (F := E) ι (fun y ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) ι y (Y y)) (ι x)) x := by
    rw [sectionCoord_model_space]
    refine ((contMDiff_coe_sphereTangentEquiv (E := E) (n := n) (m := 1)).mdifferentiable
      one_ne_zero _).comp x hY |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    exact (coe_sphereTangentEquiv_apply y (Y y)).symm
  have hW := inner_immersionShapeOperator_mfderiv (isMetricCompatible_leviCivitaConnection _)
    (hι x) hν hνn X hdY
  rw [← hW, immersionShapeOperator_def,
    alongMap_leviCivitaConnection_model_space (hι x) (hι x)]
  have hmem : mfderiv (𝓡 n) 𝓘(ℝ, E) ι x (X x) ∈
      LinearMap.range (mfderiv (𝓡 n) 𝓘(ℝ, E) ι x).toLinearMap := LinearMap.mem_range_self _ _
  rw [Submodule.starProjection_eq_self_iff.mpr hmem, inner_neg_left, inner_tangentSpace_sphere,
    mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- The two sides differ only by unfolding the local name `ι` for the inclusion.
  rfl

/-- The second fundamental form of the unit sphere paired with the outward normal `x`:
`⟪B_x(v, w), x⟫ = -⟪v, w⟫`. -/
theorem inner_immersionSecondFundamentalFormAt_subtypeVal_sphere (x : sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ⟪immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x v w, (x : E)⟫_ℝ = -⟪v, w⟫_ℝ := by
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) 2 ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere x
  have h := immersionSecondFundamentalFormAt_apply (cov := leviCivitaConnection 𝓘(ℝ, E) E) hf
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
  simp only [FiberBundle.extend_apply_self] at h
  rw [h, inner_immersionSecondFundamentalForm_subtypeVal_sphere x
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w),
    FiberBundle.extend_apply_self, FiberBundle.extend_apply_self]

/-- **The second fundamental form of the unit sphere** in a Euclidean space, with its round metric:
`B_x(v, w) = -⟪v, w⟫ x`. -/
theorem immersionSecondFundamentalFormAt_subtypeVal_sphere (x : sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    (immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x v w : E) = -⟪v, w⟫_ℝ • (x : E) := by
  have hmem := immersionSecondFundamentalFormAt_mem (cov := leviCivitaConnection 𝓘(ℝ, E) E)
    (f := ((↑) : sphere (0 : E) 1 → E)) v w
  rw [orthogonalNormalSpace_subtypeVal_sphere] at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton (R := ℝ) (M := E)).mp hmem
  have h := inner_immersionSecondFundamentalFormAt_subtypeVal_sphere x v w
  rw [← hc] at h
  -- `h` pairs vectors of `TangentSpace 𝓘(ℝ, E) x`; restate it in `E`, which is that space by
  -- definition, so that the inner product lemmas of `E` apply.
  change ⟪c • (x : E), (x : E)⟫_ℝ = _ at h
  rw [real_inner_smul_left, inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x),
    mul_one] at h
  rw [← hc, h]

/-- **The shape operator of the unit sphere** in the direction of a vector `ν` at `x` is
`S_ν = -⟪x, ν⟫ id`. -/
theorem immersionShapeOperatorAt_subtypeVal_sphere (x : sphere (0 : E) 1)
    (ν : TangentSpace 𝓘(ℝ, E) (x : E)) :
    immersionShapeOperatorAt (I := 𝓡 n) (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x ν = -⟪(x : E), ν⟫_ℝ • 1 := by
  refine ((eq_immersionShapeOperatorAt_iff (I := 𝓡 n) (cov := leviCivitaConnection 𝓘(ℝ, E) E)
    (f := ((↑) : sphere (0 : E) 1 → E)) (x := x) ν _).mpr fun v w ↦ ?_).symm
  have hB := immersionSecondFundamentalFormAt_subtypeVal_sphere x v w
  have key : ⟪immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x v w, ν⟫_ℝ = -⟪v, w⟫_ℝ * ⟪(x : E), ν⟫_ℝ := by
    rw [hB]; exact real_inner_smul_left _ _ _
  rw [LinearMap.smul_apply, one_apply_eq_self, real_inner_smul_left, key]
  ring

/-- In the outward direction `x`, the shape operator of the unit sphere is `-id`. -/
theorem immersionShapeOperatorAt_subtypeVal_sphere_self (x : sphere (0 : E) 1) :
    immersionShapeOperatorAt (I := 𝓡 n) (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x (x : E) = -1 := by
  rw [immersionShapeOperatorAt_subtypeVal_sphere x (x : E),
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x), neg_smul, one_smul]

/-- **The principal curvatures of the unit sphere** in the direction `ν` all equal `-⟪x, ν⟫`. -/
theorem immersionPrincipalCurvatures_subtypeVal_sphere (x : sphere (0 : E) 1)
    (ht : (leviCivitaConnection 𝓘(ℝ, E) E).IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ (EuclideanSpace ℝ (Fin n)) = m) (ν : TangentSpace 𝓘(ℝ, E) (x : E))
    (i : Fin m) :
    immersionPrincipalCurvatures (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x ht hm ν i =
      -⟪(x : E), ν⟫_ℝ :=
  immersionPrincipalCurvatures_eq_of_immersionShapeOperatorAt_eq_smul (I := 𝓡 n)
    (cov := leviCivitaConnection 𝓘(ℝ, E) E) (f := ((↑) : sphere (0 : E) 1 → E)) (x := x) ht hm
    ν (immersionShapeOperatorAt_subtypeVal_sphere x ν) i

/-- **The outward principal curvatures of the unit sphere are all `-1`.** -/
theorem immersionPrincipalCurvatures_subtypeVal_sphere_self (x : sphere (0 : E) 1)
    (ht : (leviCivitaConnection 𝓘(ℝ, E) E).IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ (EuclideanSpace ℝ (Fin n)) = m) (i : Fin m) :
    immersionPrincipalCurvatures (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x ht hm (x : E) i = -1 := by
  rw [immersionPrincipalCurvatures_subtypeVal_sphere x ht hm (x : E) i,
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)]

/-- **The inward principal curvatures of the unit sphere are all `1`**: in the direction `-x`
opposite to the outward normal `x`. -/
theorem immersionPrincipalCurvatures_subtypeVal_sphere_neg (x : sphere (0 : E) 1)
    (ht : (leviCivitaConnection 𝓘(ℝ, E) E).IsTorsionFree) {m : ℕ}
    (hm : finrank ℝ (EuclideanSpace ℝ (Fin n)) = m) (i : Fin m) :
    immersionPrincipalCurvatures (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x ht hm (-(x : E)) i = 1 := by
  refine (immersionPrincipalCurvatures_subtypeVal_sphere x ht hm _ i).trans ?_
  rw [inner_neg_right, inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x), neg_neg]

/-- In the standard orthonormal basis of `T_xSⁿ`, `∑ᵢ B_x(eᵢ, eᵢ) = -n x`. -/
private theorem sum_immersionSecondFundamentalFormAt_subtypeVal_sphere (x : sphere (0 : E) 1) :
    (∑ i, immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
        ((↑) : sphere (0 : E) 1 → E) x (stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x) i)
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x) i) : E) = -(n : ℝ) • (x : E) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x)
  have hterm (i) : (immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x (b i) (b i) : E) = (-1 : ℝ) • (x : E) := by
    rw [immersionSecondFundamentalFormAt_subtypeVal_sphere, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i, one_pow]
  have hcard : Fintype.card (Fin (finrank ℝ (TangentSpace (𝓡 n) x))) = n :=
    (Fintype.card_fin _).trans (finrank_euclideanSpace_fin (𝕜 := ℝ))
  calc (∑ i, immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
        ((↑) : sphere (0 : E) 1 → E) x (b i) (b i) : E)
      = ∑ _i : Fin (finrank ℝ (TangentSpace (𝓡 n) x)), (-1 : ℝ) • (x : E) :=
        Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = -(n : ℝ) • (x : E) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          mul_neg_one]

/-- **The trace of the second fundamental form of the unit sphere** `Sⁿ` is `tr B = -n x`; for
the unit two-sphere it is `-2ν` for the outward normal `ν = x`. -/
theorem metricTrace_immersionSecondFundamentalFormAt_subtypeVal_sphere (x : sphere (0 : E) 1) :
    LinearMap.BilinMap.metricTrace (W := TangentSpace (𝓡 n) x)
      (immersionSecondFundamentalFormAt (leviCivitaConnection 𝓘(ℝ, E) E)
        ((↑) : sphere (0 : E) 1 → E) x).toLinearMap₁₂ = -(n : ℝ) • (x : E) := by
  rw [LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x))]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  exact sum_immersionSecondFundamentalFormAt_subtypeVal_sphere x

/-- **The mean curvature vector of the unit sphere** `Sⁿ`, `n > 0`, is `H = -x`, minus the
outward normal. -/
theorem immersionMeanCurvatureVector_subtypeVal_sphere (hn : n ≠ 0) (x : sphere (0 : E) 1) :
    (immersionMeanCurvatureVector (I := 𝓡 n) (leviCivitaConnection 𝓘(ℝ, E) E)
      ((↑) : sphere (0 : E) 1 → E) x : E) = -(x : E) := by
  rw [immersionMeanCurvatureVector_eq_sum (stdOrthonormalBasis ℝ (TangentSpace (𝓡 n) x)),
    finrank_euclideanSpace_fin]
  exact (congrArg ((n : ℝ)⁻¹ • ·) (sum_immersionSecondFundamentalFormAt_subtypeVal_sphere x)).trans
    ((smul_smul (n : ℝ)⁻¹ (-(n : ℝ)) (x : E)).trans (by
      rw [mul_neg, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), neg_one_smul]))

end Sphere

end TauCeti
