/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's horizontal curvature equations for a Riemannian submersion

For a smooth Riemannian submersion `f : M → N`, let `h` and `v` be the horizontal and vertical
orthogonal projections on `TM`, and let `A` be O'Neill's horizontal fundamental tensor
(`IsRiemannianSubmersion.oneillA`). With the curvature sign convention
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z` and `Rm(u, v, w, z) = ⟪R(u, v) w, z⟫_ℝ`, the
curvatures of `M` and `N` on horizontal vectors satisfy O'Neill's horizontal curvature equations:

* **Horizontal curvature (`{3}`).** Writing `q'` for `horizontalLift q`, on horizontal vectors
  `u, v, w, z`,
  `h (R_M(u, v) w) = (R_N(df u, df v) (df w))' + A_u (A_v w) - A_v (A_u w) - 2 A_w (A_u v)` and
  `Rm_M(u, v, w, z) = Rm_N(df u, df v, df w, df z) + 2 ⟪A_u v, A_w z⟫ + ⟪A_u w, A_v z⟫`
  `- ⟪A_v w, A_u z⟫`.
* **Horizontal sectional curvature.** For horizontal vectors `u, v`,
  `K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))`. Consequently a Riemannian
  submersion is curvature-nondecreasing on horizontal planes (`K_M(u, v) ≤ K_N(df u, df v)`), with
  equality on a linearly independent horizontal pair if and only if `A_u v = 0`. On horizontal
  vector fields `X, Y` which are orthonormal at the point,
  `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]‖²`.

Note that O'Neill (1966) uses the opposite sign for the `(1, 3)` curvature operator
(`R^{O'Neill}_{X Y} Z = -R(X, Y) Z`), while agreeing on sectional curvature
`K(u, v) = ⟪R(u, v) v, u⟫ / det(Gram(u, v))`.

## Main results

* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureOperator_horizontalLift`:
  operator-level horizontal curvature formula on basic horizontal fields (requiring neither
  Hausdorffness of `M` nor of `N`).
* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureTensor_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_of_mem_orthogonal_ker`: O'Neill's
  horizontal curvature formulas (`{3}`).
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_of_mem_orthogonal_ker`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_of_orthonormal`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_of_orthonormal_mlieBracket`:
  O'Neill's horizontal sectional curvature formulas.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_le_sectionalCurvature_mfderiv`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_iff`: curvature monotonicity on
  horizontal planes and characterization of equality.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 (`{3}`) and Corollary 1(1).
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C, 9.28f and 9.29a.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8.
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

-- Regularity indices propositionally equal to `∞` or `2`.
private local instance : IsManifold I (∞ + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

private local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (by norm_cast)

private local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

private local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Horizontal curvature on basic vector fields -/

section Operator

/-- Horizontal projection of an iterated Levi-Civita derivative `∇_{U'} (∇_{W'} Z')` of basic
horizontal fields. -/
private theorem starProjection_orthogonal_ker_iterated_horizontalLift
    (U : Π y : N, TangentSpace J y) {W Z : Π y : N, TangentSpace J y}
    (hW : CMDiff ∞ (T% W)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M
            (fun z ↦ h.horizontalLift z (Z (f z))) y (h.horizontalLift y (W (f y)))) x
          (h.horizontalLift x (U (f x)))) =
      h.horizontalLift x
          (leviCivitaConnection J N (fun z ↦ leviCivitaConnection J N Z z (W z)) (f x) (U (f x))) +
        h.oneillA x (h.horizontalLift x (U (f x)))
          (h.oneillA x (h.horizontalLift x (W (f x))) (h.horizontalLift x (Z (f x)))) := by
  let : IsManifold J 2 N := .of_le (n := ∞) (by norm_cast)
  let : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (n := ∞) (by simp)
  let : IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y) :=
    .of_le (n := ∞) (by simp)
  set W' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (W (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  have hW' : CMDiff ∞ (T% W') := h.contMDiff_horizontalLift hW (by simp)
  have hZ' : CMDiff ∞ (T% Z') := h.contMDiff_horizontalLift hZ (by simp)
  have hQ := h.contMDiff_starProjection_ker (n := ∞) (by simp)
  have hZW : CMDiff ∞ (T% (fun z ↦ leviCivitaConnection J N Z z (W z))) :=
    (leviCivitaConnection J N).contMDiff_apply hW hZ
  have hZW' : MDiffAt (T% (fun y ↦ h.horizontalLift y
      (leviCivitaConnection J N Z (f y) (W (f y))))) x :=
    ((h.contMDiff_horizontalLift hZW (by simp)) x).mdifferentiableAt (by simp)
  have hAd : MDiffAt (T% (fun y ↦ h.oneillA y (W' y) (Z' y))) x := by
    refine (((hQ.clm_bundle_apply
      ((leviCivitaConnection I M).contMDiff_apply hW' hZ')).congr fun y ↦ ?_) x).mdifferentiableAt
        (by simp)
    refine congrArg (TotalSpace.mk' E y) ?_
    rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker ((hZ' y).mdifferentiableAt (by simp))
        (.of_forall fun z ↦ h.horizontalLift_mem_orthogonal_ker z _),
      Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker y _)]
  have hsplit : (fun y ↦ leviCivitaConnection I M Z' y (W' y)) =
      (fun y ↦ h.horizontalLift y (leviCivitaConnection J N Z (f y) (W (f y)))) +
        fun y ↦ h.oneillA y (W' y) (Z' y) :=
    funext fun y ↦ h.leviCivitaConnection_horizontalLift ((hZ (f y)).of_le (by simp)) (W (f y))
  have ha := h.oneillA_apply_of_eventually_mem_ker hAd
    (.of_forall fun y ↦ h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _))
    (h.horizontalLift x (U (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at ha
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hZW' hAd,
    add_apply, map_add,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) ((hZW (f x)).of_le (by simp)),
    ← ha]

/-- On basic horizontal vector fields `X', Y', Z'`, the horizontal component of the total-space
curvature operator equals `(R_N(X, Y) Z)' + A_X' (A_Y' Z') - A_Y' (A_X' Z') - 2 A_Z' (A_X' Y')`.
Neither Hausdorffness of `M` nor of `N` is needed at the operator level. -/
theorem starProjection_orthogonal_ker_curvatureOperator_horizontalLift
    {X Y Z : Π y : N, TangentSpace J y}
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
  let : IsManifold J 2 N := .of_le (n := ∞) (by norm_cast)
  let : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    .of_le (n := ∞) (by simp)
  let : IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y) :=
    .of_le (n := ∞) (by simp)
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  have hbr : (mfderiv I J f x).kerᗮ.starProjection
      (leviCivitaConnection I M Z' x (mlieBracket I X' Y' x)) =
      h.horizontalLift x (leviCivitaConnection J N Z (f x) (mlieBracket J X Y (f x))) +
        (2 : ℝ) • h.oneillA x (Z' x) (h.oneillA x (X' x) (Y' x)) := by
    rw [h.mlieBracket_horizontalLift ((hX (f x)).of_le (by simp)) ((hY (f x)).of_le (by simp)),
      map_add, map_smul, map_add, map_smul,
      h.starProjection_covariantDerivative_horizontalLift
        (isLeviCivitaConnection_leviCivitaConnection I)
        (isLeviCivitaConnection_leviCivitaConnection J) ((hZ (f x)).of_le (by simp)),
      h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
        ((hZ (f x)).of_le (by simp))
        (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))]
  rw [curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_orthogonal_ker_iterated_horizontalLift X hY hZ x,
    h.starProjection_orthogonal_ker_iterated_horizontalLift Y hX hZ x,
    hbr, curvatureOperator_apply, map_sub, map_sub]
  abel

end Operator

/-! ### O'Neill's horizontal curvature formulas (`{3}`) -/

section HorizontalCurvature

variable [T2Space M] [T2Space N] {x : M}

/-- **O'Neill's horizontal `(1, 3)` curvature equation** on lifted base vectors:
`h (R_M(u', v') w') = (R_N(u, v) w)' + A_u' (A_v' w') - A_v' (A_u' w') - 2 A_w' (A_u' v')`. -/
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
  obtain ⟨X, hX, hXx⟩ := exists_contMDiff_section_eq J F ∞ u
  obtain ⟨Y, hY, hYx⟩ := exists_contMDiff_section_eq J F ∞ v
  obtain ⟨Z, hZ, hZx⟩ := exists_contMDiff_section_eq J F ∞ w
  rw [← hXx, ← hYx, ← hZx,
    (leviCivitaConnection I M).curvatureTensor_apply x
      (h.contMDiff_horizontalLift hX (by simp))
      (h.contMDiff_horizontalLift hY (by simp))
      (h.contMDiff_horizontalLift hZ (by simp)),
    (leviCivitaConnection J N).curvatureTensor_apply (f x) hX hY hZ,
    h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift hX hY hZ x]

/-- **O'Neill's horizontal `(1, 3)` curvature equation** on horizontal tangent vectors. -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker
    {u v w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x u v w) =
      h.horizontalLift x
          ((leviCivitaConnection J N).curvatureTensor (f x)
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

/-- Projecting `R_M(u', v') w'` by `df_x` recovers `R_N(u, v) w` up to the projected `A²` terms. -/
theorem mfderiv_curvatureTensor_horizontalLift (u v w : TangentSpace J (f x)) :
    mfderiv I J f x
        ((leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x w)) =
      (leviCivitaConnection J N).curvatureTensor (f x) u v w +
        mfderiv I J f x
          (h.oneillA x (h.horizontalLift x u)
              (h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)) -
            h.oneillA x (h.horizontalLift x v)
              (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)) -
            (2 : ℝ) • h.oneillA x (h.horizontalLift x w)
              (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v))) := by
  have hm (q : TangentSpace I x) :
      mfderiv I J f x ((mfderiv I J f x).kerᗮ.starProjection q) = mfderiv I J f x q := by
    rw [← h.horizontalLift_mfderiv, h.mfderiv_horizontalLift]
  have heq :
      h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x) u v w) +
          h.oneillA x (h.horizontalLift x u)
            (h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)) -
          h.oneillA x (h.horizontalLift x v)
            (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)) -
          (2 : ℝ) • h.oneillA x (h.horizontalLift x w)
            (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)) =
        h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x) u v w) +
          (h.oneillA x (h.horizontalLift x u)
              (h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w)) -
            h.oneillA x (h.horizontalLift x v)
              (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w)) -
            (2 : ℝ) • h.oneillA x (h.horizontalLift x w)
              (h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v))) := by abel
  rw [← hm ((leviCivitaConnection I M).curvatureTensor x _ _ _),
    h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift, heq, map_add,
    h.mfderiv_horizontalLift]

/-- **O'Neill's `(0, 4)` horizontal curvature equation** on lifted base vectors (O'Neill,
Theorem 2, `{3}`). -/
theorem riemannCurvatureTensor_horizontalLift (u v w z : TangentSpace J (f x)) :
    (leviCivitaConnection I M).riemannCurvatureTensor x
        (h.horizontalLift x u) (h.horizontalLift x v)
        (h.horizontalLift x w) (h.horizontalLift x z) =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x) u v w z +
        2 * ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v),
          h.oneillA x (h.horizontalLift x w) (h.horizontalLift x z)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x v) (h.horizontalLift x z)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x u) (h.horizontalLift x z)⟫_ℝ := by
  have hz' : (mfderiv I J f x).kerᗮ.starProjection (h.horizontalLift x z) = h.horizontalLift x z :=
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x z)
  rw [riemannCurvatureTensor_apply, riemannCurvatureTensor_apply]
  conv_lhs => rw [← hz', ← Submodule.inner_starProjection_left_eq_right]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    (h.horizontalLift x).inner_map_map, h.inner_oneillA]
  linarith

/-- **O'Neill's `(0, 4)` horizontal curvature equation** on horizontal tangent vectors (O'Neill,
Theorem 2, `{3}`). -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ -
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ := by
  conv_lhs =>
    rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv,
      ← h.horizontalLift_mfderiv_of_mem x hw, ← h.horizontalLift_mfderiv_of_mem x hz]
  rw [h.riemannCurvatureTensor_horizontalLift,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw, h.horizontalLift_mfderiv_of_mem x hz]

/-- Base `(0, 4)` Riemann curvature expressed in terms of total-space curvature on horizontal
lifts. -/
theorem riemannCurvatureTensor_base_eq (u v w z : TangentSpace J (f x)) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x) u v w z =
      (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v)
          (h.horizontalLift x w) (h.horizontalLift x z) -
        2 * ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v),
          h.oneillA x (h.horizontalLift x w) (h.horizontalLift x z)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x v) (h.horizontalLift x z)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x u) (h.horizontalLift x z)⟫_ℝ := by
  linarith [h.riemannCurvatureTensor_horizontalLift u v w z]

/-! ### Horizontal sectional curvature -/

/-- Comparison of sectional-curvature numerators on lifted base vectors:
`⟪R_N(u, v) v, u⟫ = ⟪R_M(u', v') v', u'⟫ + 3 ‖A_u' v'‖²`. -/
theorem inner_curvatureTensor_horizontalLift_self (u v : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) u v v, u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x v),
        h.horizontalLift x u⟫_ℝ +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  have hr := h.riemannCurvatureTensor_base_eq u v v u
  simp only [riemannCurvatureTensor_apply,
    h.oneillA_self (h.horizontalLift_mem_orthogonal_ker x u),
    h.oneillA_self (h.horizontalLift_mem_orthogonal_ker x v),
    h.oneillA_antisymm (h.horizontalLift_mem_orthogonal_ker x v)
      (h.horizontalLift_mem_orthogonal_ker x u),
    inner_zero_right, inner_neg_right, real_inner_self_eq_norm_sq] at hr
  linarith

/-- Comparison of sectional-curvature numerators on horizontal tangent vectors:
`⟪R_N(df u, df v) (df v), df u⟫ = ⟪R_M(u, v) v, u⟫ + 3 ‖A_u v‖²`. -/
theorem inner_curvatureTensor_mfderiv_of_mem_orthogonal_ker
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
      mfderiv I J f x u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] using
    h.inner_curvatureTensor_horizontalLift_self (mfderiv I J f x u) (mfderiv I J f x v)

/-- **O'Neill's horizontal sectional curvature formula** on lifted base vectors (O'Neill,
Corollary 1). On linearly dependent pairs both Gram determinants vanish, so the identity holds
for all pairs `u, v` without an independence hypothesis. -/
theorem sectionalCurvature_horizontalLift (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 /
          (Matrix.gram ℝ ![u, v]).det := by
  have hg : (Matrix.gram ℝ ![h.horizontalLift x u, h.horizontalLift x v]).det =
      (Matrix.gram ℝ ![u, v]).det := by
    simp only [Matrix.real_det_gram_fin_two, (h.horizontalLift x).inner_map_map]
  rw [sectionalCurvature_apply, sectionalCurvature_apply, hg,
    h.inner_curvatureTensor_horizontalLift_self, add_div]

/-- **O'Neill's horizontal sectional curvature formula** on horizontal tangent vectors. -/
theorem sectionalCurvature_mfderiv_of_mem_orthogonal_ker
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  have hg : (Matrix.gram ℝ ![mfderiv I J f x u, mfderiv I J f x v]).det =
      (Matrix.gram ℝ ![u, v]).det := by
    conv_rhs =>
      rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv]
    simp only [Matrix.real_det_gram_fin_two, (h.horizontalLift x).inner_map_map]
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv, hg] using
    h.sectionalCurvature_horizontalLift (mfderiv I J f x u) (mfderiv I J f x v)

/-- On an orthonormal pair of base vectors, `K_N(u, v) = K_M(u', v') + 3 ‖A_u' v'‖²`. -/
theorem sectionalCurvature_horizontalLift_of_orthonormal
    {u v : TangentSpace J (f x)} (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  rw [h.sectionalCurvature_horizontalLift, Matrix.gram_eq_one_iff_orthonormal.mpr huv,
    Matrix.det_one, div_one]

/-- On an orthonormal pair of horizontal vectors, `K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖²`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv,
    Matrix.gram_eq_one_iff_orthonormal.mpr huv, Matrix.det_one, div_one]

/-- **O'Neill's horizontal sectional curvature formula in Lie-bracket form.** For vector fields
`X, Y` which are horizontal near `x` and orthonormal at `x`,
`K_N(df (X x), df (Y x)) = K_M(X x, Y x) + (3 / 4) ‖v [X, Y]_x‖²`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal_mlieBracket
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (hXY : Orthonormal ℝ ![X x, Y x]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_of_orthonormal hXh.self_of_nhds hYh.self_of_nhds hXY,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's curvature-nondecreasing theorem** on lifted base planes:
`K_M(u', v') ≤ K_N(u, v)`. -/
theorem sectionalCurvature_horizontalLift_le (u v : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x
        (h.horizontalLift x u) (h.horizontalLift x v) ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v := by
  rw [h.sectionalCurvature_horizontalLift]
  have hdet : 0 ≤ (Matrix.gram ℝ ![u, v]).det := (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg
  exact le_add_of_nonneg_right (div_nonneg (by positivity) hdet)

/-- **O'Neill's curvature-nondecreasing theorem** on horizontal planes:
`K_M(u, v) ≤ K_N(df u, df v)`. -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv]
  have hdet : 0 ≤ (Matrix.gram ℝ ![u, v]).det := (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg
  exact le_add_of_nonneg_right (div_nonneg (by positivity) hdet)

/-- On a linearly independent horizontal pair `u, v`, the base and total-space sectional
curvatures agree if and only if `A_u v = 0`. -/
theorem sectionalCurvature_mfderiv_eq_iff
    {u v : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v ↔
      h.oneillA x u v = 0 := by
  have hdet : 0 < (Matrix.gram ℝ ![u, v]).det :=
    (Matrix.posDef_gram_of_linearIndependent huv).det_pos
  rw [h.sectionalCurvature_mfderiv_of_mem_orthogonal_ker hu hv, add_eq_left,
    div_eq_zero_iff, or_iff_left hdet.ne', mul_eq_zero, or_iff_right (by norm_num),
    sq_eq_zero_iff, norm_eq_zero]

/-- When `A_x = 0`, the `(0, 4)` Riemann curvature on horizontal vectors coincides with the
pulled-back base curvature. -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker_of_oneillA_eq_zero
    (ha : h.oneillA x = 0) {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) := by
  simp [h.riemannCurvatureTensor_of_mem_orthogonal_ker hu hv hw hz, ha]

end HorizontalCurvature

end TauCeti.IsRiemannianSubmersion
