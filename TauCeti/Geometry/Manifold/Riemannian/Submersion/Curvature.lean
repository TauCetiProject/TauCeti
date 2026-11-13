/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's horizontal curvature equations for a Riemannian submersion

For a Riemannian submersion `f : M → N` between smooth Riemannian manifolds, O'Neill's horizontal
curvature equation expresses the horizontal part of the curvature of `M` in terms of the curvature
of `N` and O'Neill's horizontal tensor `A` (`IsRiemannianSubmersion.oneillA`). Under the curvature
convention `R(X, Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` and
`Rm(u, v, w, z) = ⟪R(u, v)w, z⟫`, for base tangent vectors `u, v, w, z` at `f x` with horizontal
lifts `u', v', w', z'` at `x`:

* the horizontal projection of `R_M(u', v')w'` is
  `horizontalLift x (R_N(u, v)w) + A_u'(A_v' w') - A_v'(A_u' w') - 2 A_w'(A_u' v')`;
* the `(0, 4)` Riemann curvature tensors satisfy
  `Rm_N(u, v, w, z) = Rm_M(u', v', w', z') + ⟪A_v' w', A_u' z'⟫ - ⟪A_u' w', A_v' z'⟫`
  `- 2 ⟪A_u' v', A_w' z'⟫`;
* the sectional curvatures satisfy
  `K_N(u, v) = K_M(u', v') + 3 ‖A_u' v'‖² / det(Gram(u, v))`,
  which reduces on orthonormal horizontal pairs to `K_N(df_x u, df_x v) = K_M(u, v) + 3 ‖A_u v‖²`
  and on horizontal vector fields `X, Y` to
  `K_N(df_x(X x), df_x(Y x)) = K_M(X x, Y x) + (3 / 4) ‖v [X, Y]_x‖² / det(Gram(X x, Y x))`.

In particular, a Riemannian submersion is sectional-curvature non-decreasing on horizontal planes:
`K_M(u', v') ≤ K_N(u, v)`, with equality on any pair if and only if `A_u' v' = 0`, and equality on
every pair at `f x` if and only if `oneillA x = 0` (as verified for Riemannian products in
`TauCeti.Geometry.Manifold.Riemannian.Submersion.Prod`). Summing over an orthonormal basis of
`T_(f x) N` expresses the Ricci and scalar curvatures of `N` in terms of horizontal curvature
components of `M` and squared norms of `A`.

The operator-level formulas require no Hausdorff assumptions. Pointwise tensor, sectional, Ricci,
and scalar identities assume `[T2Space M] [T2Space N]` so tangent vectors extend globally to smooth
fields. Neither boundarylessness, completeness, compactness, nor global surjectivity of `f` is
assumed, except surjectivity when transferring a global lower curvature bound to all of `N`.

## Main results

* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureOperator_horizontalLift`
  and `TauCeti.IsRiemannianSubmersion.inner_curvatureOperator_horizontalLift`: O'Neill's
  horizontal curvature equations at the operator level on smooth base vector fields.
* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureTensor_horizontalLift` and
  `TauCeti.IsRiemannianSubmersion.curvatureTensor_eq_mfderiv_horizontalLift_add`: the horizontal
  part of `R_M` and the pushforward formula for `R_N`.
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_eq_horizontalLift_add` and
  `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_mfderiv_eq_add_of_mem`: O'Neill's `(0, 4)`
  horizontal curvature equation.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_eq_horizontalLift_add_div`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_div_of_mem`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_of_orthonormal`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_div_norm_mlieBracket`, and
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_norm_mlieBracket_of_orthonormal`
  (O'Neill's horizontal sectional curvature formulas in `A`-tensor and Lie-bracket forms).
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontalLift_le`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_eq_horizontalLift_iff`, and
  `TauCeti.IsRiemannianSubmersion.forall_sectionalCurvature_eq_horizontalLift_iff`: monotonicity
  and rigidity of horizontal sectional curvature.
* `TauCeti.IsRiemannianSubmersion.ricciTensor_eq_sum_horizontalLift` and
  `TauCeti.IsRiemannianSubmersion.scalarCurvature_eq_sum_horizontalLift`: horizontal contractions
  for the base Ricci and scalar curvatures.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 and Corollary 1.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (Proposition 9.28(f),
  Corollary 9.29, and Proposition 9.36).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (Theorem 7.47).
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

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

include h

-- These regularity indices are propositionally, but not definitionally, equal to two or `∞`.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (by norm_cast)

local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold I (∞ + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

/-! ### Curvature operator on basic horizontal lifts -/

section Operator

/-- Second covariant derivative of basic horizontal lifts, projected horizontally:
`h(∇_v' (∇_Y' Z')) = horizontalLift x (∇_v (∇_Y Z)) + A_v' (A_Y' Z')`. -/
private theorem starProjection_orthogonal_ker_second_leviCivitaConnection_horizontalLift
    {Y Z : Π z : N, TangentSpace J z} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (v : TangentSpace J (f x)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M
            (fun q ↦ h.horizontalLift q (Z (f q))) y (h.horizontalLift y (Y (f y))))
          x (h.horizontalLift x v)) =
      h.horizontalLift x
          (leviCivitaConnection J N
            (fun z ↦ leviCivitaConnection J N Z z (Y z)) (f x) v) +
        h.oneillA x (h.horizontalLift x v)
          (h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x)))) := by
  set YL : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  set ZL : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  set YZ : Π z : N, TangentSpace J z := fun z ↦ leviCivitaConnection J N Z z (Y z)
  set U : Π y : M, TangentSpace I y := fun y ↦ leviCivitaConnection I M ZL y (YL y)
  set HField : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (YZ (f y))
  set VField : Π y : M, TangentSpace I y := fun y ↦ h.oneillA y (YL y) (ZL y)
  have hYZ : CMDiff ∞ (T% YZ) := (leviCivitaConnection J N).contMDiff_apply hY (hZ.of_le (by simp))
  have hYL : CMDiff ∞ (T% YL) := h.contMDiff_horizontalLift hY (by simp)
  have hZL : CMDiff ∞ (T% ZL) := h.contMDiff_horizontalLift hZ (by simp)
  have hU : CMDiff ∞ (T% U) :=
    (leviCivitaConnection I M).contMDiff_apply hYL (hZL.of_le (by simp))
  have hHField : CMDiff ∞ (T% HField) := h.contMDiff_horizontalLift hYZ (by simp)
  have hUeq : U = HField + VField := funext fun y ↦
    h.leviCivitaConnection_horizontalLift ((hZ (f y)).of_le (by simp)) (Y (f y))
  have hVField : CMDiff ∞ (T% VField) := by
    refine (hU.sub_section hHField).congr fun y ↦ ?_
    simp only [Pi.sub_apply]
    exact congrArg (TotalSpace.mk' E y) (eq_sub_of_add_eq' (congrFun hUeq y).symm)
  have hHd : MDiffAt (T% HField) x := (hHField x).mdifferentiableAt (by simp)
  have hVd : MDiffAt (T% VField) x := (hVField x).mdifferentiableAt (by simp)
  have hA := h.oneillA_apply_of_eventually_mem_ker hVd
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _))
    (h.horizontalLift x v)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x v)] at hA
  rw [hUeq,
    (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hHd hVd,
    add_apply, map_add,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) ((hYZ (f x)).of_le (by simp)) v,
    ← hA]

/-- **O'Neill's horizontal curvature operator formula.** For smooth vector fields `X, Y, Z` on `N`
with basic horizontal lifts `X', Y', Z'` on `M`, the horizontal part of `R_M(X', Y')Z'` at `x` is
`horizontalLift x (R_N(X, Y)Z (f x)) + A_X'(A_Y' Z') - A_Y'(A_X' Z') - 2 A_Z'(A_X' Y')`. -/
theorem starProjection_orthogonal_ker_curvatureOperator_horizontalLift
    {X Y Z : Π z : N, TangentSpace J z}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureOperator
          (fun y ↦ h.horizontalLift y (X (f y)))
          (fun y ↦ h.horizontalLift y (Y (f y)))
          (fun y ↦ h.horizontalLift y (Z (f y))) x) =
      h.horizontalLift x ((leviCivitaConnection J N).curvatureOperator X Y Z (f x)) +
        h.oneillA x (h.horizontalLift x (X (f x)))
          (h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x)))) -
        h.oneillA x (h.horizontalLift x (Y (f x)))
          (h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Z (f x)))) -
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (Z (f x)))
          (h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x)))) := by
  have hX1 : CMDiffAt 1 (T% X) (f x) := (hX (f x)).of_le (by simp)
  have hY1 : CMDiffAt 1 (T% Y) (f x) := (hY (f x)).of_le (by simp)
  have hZ1 : CMDiffAt 1 (T% Z) (f x) := (hZ (f x)).of_le (by simp)
  have hXd := (h.contMDiffAt_horizontalLift hX1 (by norm_num)).mdifferentiableAt one_ne_zero
  have hYd := (h.contMDiffAt_horizontalLift hY1 (by norm_num)).mdifferentiableAt one_ne_zero
  rw [curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_orthogonal_ker_second_leviCivitaConnection_horizontalLift hY hZ x (X (f x)),
    h.starProjection_orthogonal_ker_second_leviCivitaConnection_horizontalLift hX hZ x (Y (f x)),
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift hZ1,
    h.mfderiv_mlieBracket_horizontalLift hX1 hY1,
    h.starProjection_ker_mlieBracket hXd hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
    curvatureOperator_apply, map_sub, map_sub, map_smul]
  abel

/-- **O'Neill's horizontal curvature equation at the operator level.** Pairing `R_M(X', Y')Z'` at
`x` with a horizontal lift `w'` relates it to `⟪R_N(X, Y)Z (f x), w⟫` and inner products of
O'Neill's `A` tensor. -/
theorem inner_curvatureOperator_horizontalLift
    {X Y Z : Π z : N, TangentSpace J z}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (w : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection I M).curvatureOperator
        (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y)))
        (fun y ↦ h.horizontalLift y (Z (f y))) x,
      h.horizontalLift x w⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureOperator X Y Z (f x), w⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x))),
          h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x w)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Z (f x))),
          h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x w)⟫_ℝ +
        2 * ⟪h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x))),
          h.oneillA x (h.horizontalLift x (Z (f x))) (h.horizontalLift x w)⟫_ℝ := by
  have hw := Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x w)
  conv_lhs =>
    rw [← hw, ← Submodule.inner_starProjection_left_eq_right,
      h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift hX hY hZ x]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    (h.horizontalLift x).inner_map_map, h.inner_oneillA]
  ring

end Operator

/-! ### Pointwise horizontal curvature equations -/

section Tensor

variable [T2Space M] [T2Space N] {x : M}

/-- **Horizontal projection of the `(1, 3)` curvature tensor on horizontal lifts.** -/
theorem starProjection_orthogonal_ker_curvatureTensor_horizontalLift
    (u v w : TangentSpace J (f x)) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x w)) =
      h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x) u v w) +
        h.oneillA x (h.horizontalLift x u)
          (h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)) -
        h.oneillA x (h.horizontalLift x v)
          (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)) -
        (2 : ℝ) • h.oneillA x (h.horizontalLift x w)
          (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq J F ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq J F ∞ v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq J F ∞ w
  have hXL := h.contMDiff_horizontalLift hX (by simp)
  have hYL := h.contMDiff_horizontalLift hY (by simp)
  have hZL := h.contMDiff_horizontalLift hZ (by simp)
  have hcurvM := (leviCivitaConnection I M).curvatureTensor_apply x hXL hYL hZL
  have hcurvN := (leviCivitaConnection J N).curvatureTensor_apply (f x) hX hY hZ
  rw [hcurvM, hcurvN]
  exact h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift hX hY hZ x

/-- **Horizontal projection of the `(1, 3)` curvature tensor on horizontal vectors.** -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem
    {u v w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v w) =
      h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)) +
        h.oneillA x u (h.oneillA x v w) -
        h.oneillA x v (h.oneillA x u w) -
        (2 : ℝ) • h.oneillA x w (h.oneillA x u v) := by
  conv_lhs =>
    rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv,
      ← h.horizontalLift_mfderiv_of_mem x hw]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw]

/-- The `(1, 3)` curvature tensor of the base manifold `N` expressed as the differential of
horizontal curvature and quadratic `A`-tensor terms on `M`. -/
theorem curvatureTensor_eq_mfderiv_horizontalLift_add (u v w : TangentSpace J (f x)) :
    (leviCivitaConnection J N).curvatureTensor (f x) u v w =
      mfderiv I J f x
        ((leviCivitaConnection I M).curvatureTensor x
            (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x w) -
          h.oneillA x (h.horizontalLift x u)
            (h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)) +
          h.oneillA x (h.horizontalLift x v)
            (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)) +
          (2 : ℝ) • h.oneillA x (h.horizontalLift x w)
            (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v))) := by
  have hcurv := congrArg (mfderiv I J f x)
    (h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift u v w)
  rw [← ContinuousLinearMap.comp_apply, (mfderiv I J f x).comp_starProjection_orthogonal_ker]
    at hcurv
  simp only [map_add, map_sub, map_smul, h.mfderiv_horizontalLift] at hcurv ⊢
  rw [hcurv]
  abel

/-- **O'Neill's horizontal curvature equation** expressing the `(0, 4)` Riemann curvature tensor of
the base `N` in terms of `M` and O'Neill's `A` tensor. -/
theorem riemannCurvatureTensor_eq_horizontalLift_add (u v w z : TangentSpace J (f x)) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x) u v w z =
      (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v)
          (h.horizontalLift x w) (h.horizontalLift x z) +
        ⟪h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x u) (h.horizontalLift x z)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x v) (h.horizontalLift x z)⟫_ℝ -
        2 * ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v),
          h.oneillA x (h.horizontalLift x w) (h.horizontalLift x z)⟫_ℝ := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq J F ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq J F ∞ v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq J F ∞ w
  have hcurv := h.inner_curvatureOperator_horizontalLift hX hY hZ x z
  rw [← (leviCivitaConnection I M).curvatureTensor_apply x
      (h.contMDiff_horizontalLift hX (by simp)) (h.contMDiff_horizontalLift hY (by simp))
      (h.contMDiff_horizontalLift hZ (by simp)),
    ← (leviCivitaConnection J N).curvatureTensor_apply (f x) hX hY hZ,
    ← riemannCurvatureTensor_apply, ← riemannCurvatureTensor_apply] at hcurv
  linarith

/-- **O'Neill's horizontal curvature equation** on four horizontal vectors in `T_x M`. -/
theorem riemannCurvatureTensor_mfderiv_eq_add_of_mem
    {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) =
      (leviCivitaConnection I M).riemannCurvatureTensor x u v w z +
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ -
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ -
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ := by
  rw [h.riemannCurvatureTensor_eq_horizontalLift_add,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw, h.horizontalLift_mfderiv_of_mem x hz]

/-! ### Sectional curvature of horizontal planes -/

/-- Sectional-curvature numerator identity on horizontal lifts:
`⟪R_N(u, v)v, u⟫ = ⟪R_M(u', v')v', u'⟫ + 3 ‖A_u' v'‖²` for arbitrary base vectors `u, v`. -/
theorem inner_curvatureTensor_self_eq_horizontalLift_add (u v : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) u v v, u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v)
          (h.horizontalLift x v), h.horizontalLift x u⟫_ℝ +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  have hu := h.horizontalLift_mem_orthogonal_ker x u
  have hv := h.horizontalLift_mem_orthogonal_ker x v
  have hcurv := h.riemannCurvatureTensor_eq_horizontalLift_add u v v u
  simp only [riemannCurvatureTensor_apply, h.oneillA_self hu, h.oneillA_self hv,
    inner_zero_left, h.oneillA_antisymm hv hu, inner_neg_right,
    real_inner_self_eq_norm_sq] at hcurv
  linarith

/-- Sectional-curvature numerator identity on horizontal tangent vectors `u, v ∈ (ker df_x)ᗮ`. -/
theorem inner_curvatureTensor_self_mfderiv_eq_add_of_mem
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
      mfderiv I J f x u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.inner_curvatureTensor_self_eq_horizontalLift_add,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv]

/-- **O'Neill's horizontal sectional curvature formula** on arbitrary base tangent vectors `u, v`.
On linearly dependent pairs both totalized Gram-determinant quotients vanish, so no linear
independence hypothesis is required. -/
theorem sectionalCurvature_eq_horizontalLift_add_div (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 /
          (Matrix.gram ℝ ![u, v]).det := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, (h.horizontalLift x).det_gram_pair,
    h.inner_curvatureTensor_self_eq_horizontalLift_add, add_div]

/-- **O'Neill's horizontal sectional curvature formula** for horizontal vectors `u, v` at `x`. -/
theorem sectionalCurvature_mfderiv_eq_add_div_of_mem
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  rw [h.sectionalCurvature_eq_horizontalLift_add_div, ← (h.horizontalLift x).det_gram_pair,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv]

/-- On an orthonormal pair in `T_(f x) N`, the base sectional curvature exceeds the horizontal
sectional curvature by `3 ‖A_u' v'‖²`. -/
theorem sectionalCurvature_eq_horizontalLift_add_of_orthonormal
    {u v : TangentSpace J (f x)} (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  rw [h.sectionalCurvature_eq_horizontalLift_add_div, Matrix.gram_eq_one_iff_orthonormal.mpr huv,
    Matrix.det_one, div_one]

/-- On an orthonormal horizontal pair `u, v ∈ (ker df_x)ᗮ`, the base sectional curvature is
`K_M(u, v) + 3 ‖A_u v‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_of_orthonormal
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_div_of_mem hu hv,
    Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one, div_one]

/-- **O'Neill's horizontal sectional curvature formula in Lie-bracket form** for vector fields `X`
and `Y` which are differentiable at `x` and horizontal near `x`. -/
theorem sectionalCurvature_mfderiv_eq_add_div_norm_mlieBracket
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv_eq_add_div_of_mem hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's horizontal sectional curvature formula in Lie-bracket form** for horizontal vector
fields `X, Y` whose values at `x` are orthonormal:
`K_N(df_x(X x), df_x(Y x)) = K_M(X x, Y x) + (3 / 4) ‖v [X, Y]_x‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_norm_mlieBracket_of_orthonormal
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (hXY : Orthonormal ℝ ![X x, Y x]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_div_norm_mlieBracket hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr hXY, Matrix.det_one, div_one]

/-! ### Curvature monotonicity, rigidity, and prescribed total-space curvature -/

/-- **A Riemannian submersion is sectional-curvature non-decreasing on horizontal planes.** -/
theorem sectionalCurvature_horizontalLift_le (u v : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v := by
  rw [h.sectionalCurvature_eq_horizontalLift_add_div]
  exact le_add_of_nonneg_right
    (div_nonneg (by positivity) (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg)

/-- Horizontal sectional curvature at `x` is bounded above by the base sectional curvature of the
projected plane at `f x`. -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] using
    h.sectionalCurvature_horizontalLift_le (mfderiv I J f x u) (mfderiv I J f x v)

/-- For any pair `u, v ∈ T_(f x) N`, the base sectional curvature equals the horizontal sectional
curvature if and only if `A_u' v' = 0`. On linearly dependent pairs both sides hold trivially since
the Gram-determinant quotients vanish and `A` is alternating on horizontal vectors. -/
theorem sectionalCurvature_eq_horizontalLift_iff (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) ↔
      h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · have hdet : 0 < (Matrix.gram ℝ ![u, v]).det :=
      (Matrix.posDef_gram_of_linearIndependent huv).det_pos
    rw [h.sectionalCurvature_eq_horizontalLift_add_div, add_eq_left, div_eq_zero_iff,
      or_iff_left hdet.ne', mul_eq_zero, or_iff_right (by norm_num), sq_eq_zero_iff, norm_eq_zero]
  · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
      not_ne_iff.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
    have hA : h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
      by_cases hu : u = 0
      · simp [hu]
      · obtain ⟨c, hc⟩ := not_forall.mp ((LinearIndependent.pair_iff' hu).not.mp huv)
        rw [← not_not.mp hc, map_smul, map_smul,
          h.oneillA_self (h.horizontalLift_mem_orthogonal_ker x u), smul_zero]
    rw [h.sectionalCurvature_eq_horizontalLift_add_div, hdet, hA, div_zero, add_zero]
    simp

/-- For any horizontal vectors `u, v ∈ (ker df_x)ᗮ`, the base sectional curvature equals the
total-space sectional curvature if and only if `A_u v = 0`. -/
theorem sectionalCurvature_mfderiv_eq_iff
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ↔
      h.oneillA x u v = 0 := by
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] using
    h.sectionalCurvature_eq_horizontalLift_iff (mfderiv I J f x u) (mfderiv I J f x v)

/-- When `oneillA x = 0`, horizontal lifts preserve the `(0, 4)` Riemann curvature tensor at `x`. -/
theorem riemannCurvatureTensor_eq_of_oneillA_eq_zero (hA : h.oneillA x = 0)
    (u v w z : TangentSpace J (f x)) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x) u v w z =
      (leviCivitaConnection I M).riemannCurvatureTensor x
        (h.horizontalLift x u) (h.horizontalLift x v)
        (h.horizontalLift x w) (h.horizontalLift x z) := by
  simp [h.riemannCurvatureTensor_eq_horizontalLift_add, hA]

/-- When `oneillA x = 0`, the `(1, 3)` base curvature tensor at `f x` is the differential of the
total-space curvature tensor on horizontal lifts at `x`. -/
theorem curvatureTensor_eq_mfderiv_of_oneillA_eq_zero (hA : h.oneillA x = 0)
    (u v w : TangentSpace J (f x)) :
    (leviCivitaConnection J N).curvatureTensor (f x) u v w =
      mfderiv I J f x
        ((leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x w)) := by
  simp [h.curvatureTensor_eq_mfderiv_horizontalLift_add, hA]

/-- **Pointwise sectional-curvature rigidity.** Every tangent pair at `f x` has the same sectional
curvature in `N` as its horizontal lift in `M` at `x` if and only if O'Neill's horizontal tensor
`A` vanishes at `x`. -/
theorem forall_sectionalCurvature_eq_horizontalLift_iff :
    (∀ u v : TangentSpace J (f x),
      (leviCivitaConnection J N).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection J) (f x) u v =
        (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x u) (h.horizontalLift x v)) ↔
      h.oneillA x = 0 := by
  rw [h.oneillA_eq_zero_iff_horizontalLift]
  exact forall₂_congr fun u v ↦ h.sectionalCurvature_eq_horizontalLift_iff u v

/-- A lower sectional-curvature bound on horizontal planes at `x` descends to `T_(f x) N`. -/
theorem le_sectionalCurvature_of_forall_mem_orthogonal_ker {κ : ℝ}
    (hκ : ∀ u' v' : TangentSpace I x,
      u' ∈ (mfderiv I J f x).kerᗮ → v' ∈ (mfderiv I J f x).kerᗮ →
      LinearIndependent ℝ ![u', v'] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u' v')
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection J) (f x) u v :=
  (hκ _ _ (h.horizontalLift_mem_orthogonal_ker x u) (h.horizontalLift_mem_orthogonal_ker x v)
    ((h.horizontalLift x).linearIndependent_pair_iff.mpr huv)).trans
    (h.sectionalCurvature_horizontalLift_le u v)

/-- A lower sectional-curvature bound on all planes at `x` descends to `T_(f x) N`. -/
theorem le_sectionalCurvature_of_forall {κ : ℝ}
    (hκ : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v)
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection J) (f x) u v :=
  h.le_sectionalCurvature_of_forall_mem_orthogonal_ker (fun u' v' _ _ ↦ hκ u' v') huv

/-- Under a surjective Riemannian submersion, a global lower sectional-curvature bound on `M`
descends to a global lower sectional-curvature bound on `N`. -/
theorem le_sectionalCurvature_of_surjective (hsurj : Function.Surjective f) {κ : ℝ}
    (hκ : ∀ (p : M) (u v : TangentSpace I p), LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) p u v)
    (y : N) {u v : TangentSpace J y} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection J) y u v := by
  obtain ⟨p, rfl⟩ := hsurj y
  exact h.le_sectionalCurvature_of_forall (hκ p) huv

/-- When `M` has prescribed sectional curvature `κ` at `x`, the base sectional curvature of any
linearly independent pair `u, v ∈ T_(f x) N` is `κ + 3 ‖A_u' v'‖² / det(Gram(u, v))`. -/
theorem sectionalCurvature_eq_add_div_of_hasSectionalCurvatureAt {κ : ℝ}
    (hκ : (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) x κ)
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      κ + 3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 /
        (Matrix.gram ℝ ![u, v]).det := by
  rw [h.sectionalCurvature_eq_horizontalLift_add_div,
    hκ.sectionalCurvature_eq _ _ ((h.horizontalLift x).linearIndependent_pair_iff.mpr huv)]

/-- When `M` has prescribed sectional curvature `κ` at `x`, the base sectional curvature of any
orthonormal pair `u, v ∈ T_(f x) N` is `κ + 3 ‖A_u' v'‖²`. -/
theorem sectionalCurvature_eq_add_of_orthonormal_of_hasSectionalCurvatureAt {κ : ℝ}
    (hκ : (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) x κ)
    {u v : TangentSpace J (f x)} (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      κ + 3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  rw [h.sectionalCurvature_eq_add_div_of_hasSectionalCurvatureAt hκ huv.linearIndependent,
    Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one, div_one]

/-! ### Horizontal trace formulas for base Ricci and scalar curvature -/

/-- In an orthonormal basis `b` of `T_(f x) N`, the base Ricci curvature is the horizontal trace of
the Riemann curvature tensor of `M` plus `3 ∑ i, ⟪A_(b' i) u', A_(b' i) v'⟫`. -/
theorem ricciTensor_eq_sum_horizontalLift {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x))) (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).ricciTensor (f x) u v =
      (∑ i, (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x (b i)) (h.horizontalLift x u)
          (h.horizontalLift x v) (h.horizontalLift x (b i))) +
        3 * ∑ i, ⟪h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x u),
          h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x v)⟫_ℝ := by
  rw [(leviCivitaConnection J N).ricciTensor_eq_sum_riemannCurvatureTensor (f x) b u v,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hbi := h.horizontalLift_mem_orthogonal_ker x (b i)
  have hu := h.horizontalLift_mem_orthogonal_ker x u
  have hv := h.horizontalLift_mem_orthogonal_ker x v
  rw [h.riemannCurvatureTensor_eq_horizontalLift_add (b i) u v (b i),
    h.oneillA_self hbi, inner_zero_right,
    h.oneillA_antisymm hu hbi, h.oneillA_antisymm hv hbi,
    inner_neg_right, inner_neg_right,
    real_inner_comm (h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x v))]
  ring

/-- On the diagonal, the base Ricci curvature `Ric_N(u, u)` is the horizontal sectional-numerator
sum on `M` plus `3 ∑ i, ‖A_(b' i) u'‖²`. -/
theorem ricciTensor_self_eq_sum_horizontalLift {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x))) (u : TangentSpace J (f x)) :
    (leviCivitaConnection J N).ricciTensor (f x) u u =
      (∑ i, (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x (b i)) (h.horizontalLift x u)
          (h.horizontalLift x u) (h.horizontalLift x (b i))) +
        3 * ∑ i, ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x u)‖ ^ 2 := by
  rw [h.ricciTensor_eq_sum_horizontalLift b u u]
  simp only [real_inner_self_eq_norm_sq]

/-- In an orthonormal basis `b` of `T_(f x) N`, the base scalar curvature is the double horizontal
trace of `Rm_M` plus `3 ∑ j, ∑ i, ‖A_(b' i) (b' j)‖²`. -/
theorem scalarCurvature_eq_sum_horizontalLift {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace J (f x))) :
    (leviCivitaConnection J N).scalarCurvature (f x) =
      (∑ j, ∑ i, (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x (b i)) (h.horizontalLift x (b j))
          (h.horizontalLift x (b j)) (h.horizontalLift x (b i))) +
        3 * ∑ j, ∑ i, ‖h.oneillA x (h.horizontalLift x (b i)) (h.horizontalLift x (b j))‖ ^ 2 := by
  rw [(leviCivitaConnection J N).scalarCurvature_eq_sum_riemannCurvatureTensor (f x) b,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj := h.ricciTensor_self_eq_sum_horizontalLift b (b j)
  rwa [(leviCivitaConnection J N).ricciTensor_eq_sum_riemannCurvatureTensor (f x) b (b j) (b j)]
    at hj

end Tensor

end TauCeti.IsRiemannianSubmersion
