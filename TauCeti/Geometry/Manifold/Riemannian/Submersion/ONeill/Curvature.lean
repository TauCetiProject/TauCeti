/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's horizontal curvature equations for a Riemannian submersion

For a Riemannian submersion `f : M → N`, O'Neill's horizontal tensor `A` (`oneillA`) determines the
difference between the horizontal curvature of `M` and the curvature of the base `N`:

* On three horizontal vectors `u, v, w` at `x`, the horizontal projection of `R_M(u, v) w` is
  `(R_N(df u, df v) (df w))^ + A_u (A_v w) - A_v (A_u w) - 2 A_w (A_u v)`.
* Pairing with a fourth horizontal vector `z` and using skew-adjointness of `A` yields O'Neill's
  `(0, 4)` horizontal curvature equation
  `Rm_M(u, v, w, z) = Rm_N(df u, df v, df w, df z) + 2 ⟪A_u v, A_w z⟫ - ⟪A_v w, A_u z⟫ +
    ⟪A_u w, A_v z⟫`.
* Setting `w = v` and `z = u` gives the sectional-curvature numerator identity
  `⟪R_N(df u, df v) (df v), df u⟫ = ⟪R_M(u, v) v, u⟫ + 3 ‖A_u v‖²` and O'Neill's sectional
  curvature formula
  `K_N(df u, df v) = K_M(u, v) + 3 ‖A_u v‖² / det(Gram(u, v))`.
  Because both sides divide by the same totalized Gram determinant, this equality holds for all
  horizontal pairs without a linear-independence guard.
* For orthonormal horizontal fields `X` and `Y`, `v [X, Y] = 2 A_X Y` rewrites the correction as
  `(3 / 4) ‖v [X, Y]‖²`, giving `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]‖²`.

In particular, a Riemannian submersion is curvature-nondecreasing on horizontal two-planes, with
equality on a linearly independent horizontal pair `(u, v)` if and only if `A_u v = 0`, and lower
bounds on sectional curvature descend to the base.

The curvature sign convention follows Lee: `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`, with
`Rm(u, v, w, z) = ⟪R(u, v) w, z⟫` and sectional-curvature numerator `⟪R(u, v) v, u⟫`.

## Main results

In the namespace `TauCeti.IsRiemannianSubmersion`:

* `starProjection_orthogonal_ker_curvatureOperator_horizontalLift`: operator-level horizontal
  curvature formula on basic horizontal lifts, without `T2Space`.
* `starProjection_orthogonal_ker_curvatureTensor_horizontalLift`, `curvatureTensor_map`: `(1, 3)`
  horizontal curvature formulas.
* `riemannCurvatureTensor_horizontalLift`, `riemannCurvatureTensor_of_mem_orthogonal_ker`,
  `riemannCurvatureTensor_mfderiv`: O'Neill's `(0, 4)` horizontal curvature equation.
* `sectionalCurvature_map`, `sectionalCurvature_mfderiv`,
  `sectionalCurvature_mfderiv_of_orthonormal`,
  `sectionalCurvature_mfderiv_eq_add_three_div_four_mul_norm_mlieBracket_sq`: O'Neill's sectional
  curvature formulas in `A`-tensor and vertical-Lie-bracket form.
* `sectionalCurvature_le_sectionalCurvature_mfderiv`,
  `sectionalCurvature_mfderiv_eq_iff_oneillA_eq_zero`, `le_sectionalCurvature_of_forall_le`:
  monotonicity, equality characterization, and descent of lower sectional-curvature bounds.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 and Corollary 1.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D, Theorem 9.28 and
  Corollary 9.29.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8 (Theorem 7.47 and Problem 8-19).
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

-- These regularity indices are propositionally, but not definitionally, equal to `∞` or `2`.
local instance : IsManifold I (∞ + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  exact .of_le (n := ∞) (by simp)

local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Curvature operator on basic horizontal lifts -/

section Operator

/-- Horizontal projection of an iterated Levi-Civita derivative `∇_{X₁} (∇_{X₂} X₃)` of basic
horizontal lifts: the vertical part `A_{X₂} X₃` of `∇_{X₂} X₃` contributes `A_{X₁} (A_{X₂} X₃)`. -/
private theorem starProjection_orthogonal_ker_iterated_horizontalLift {x : M}
    {B₁ B₂ B₃ : Π y : N, TangentSpace J y}
    (hB₂ : CMDiff ∞ (T% B₂)) (hB₃ : CMDiff ∞ (T% B₃)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M
            (fun z ↦ h.horizontalLift z (B₃ (f z))) y (h.horizontalLift y (B₂ (f y))))
          x (h.horizontalLift x (B₁ (f x)))) =
      h.horizontalLift x
          (leviCivitaConnection J N
            (fun z ↦ leviCivitaConnection J N B₃ z (B₂ z)) (f x) (B₁ (f x))) +
        h.oneillA x (h.horizontalLift x (B₁ (f x)))
          (h.oneillA x (h.horizontalLift x (B₂ (f x))) (h.horizontalLift x (B₃ (f x)))) := by
  set X₂ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₂ (f y))
  set X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hX₂ : CMDiff ∞ (T% X₂) := fun y ↦ h.contMDiffAt_horizontalLift (hB₂ (f y)) (by simp)
  have hX₃ : CMDiff ∞ (T% X₃) := fun y ↦ h.contMDiffAt_horizontalLift (hB₃ (f y)) (by simp)
  have hB₂₃ : CMDiff ∞ (T% (fun z ↦ leviCivitaConnection J N B₃ z (B₂ z))) :=
    (leviCivitaConnection J N).contMDiff_apply hB₂ hB₃
  set H₂₃ : Π y : M, TangentSpace I y :=
    fun y ↦ h.horizontalLift y (leviCivitaConnection J N B₃ (f y) (B₂ (f y)))
  set V₂₃ : Π y : M, TangentSpace I y := fun y ↦ h.oneillA y (X₂ y) (X₃ y)
  have hH₂₃ : CMDiff ∞ (T% H₂₃) := fun y ↦ h.contMDiffAt_horizontalLift (hB₂₃ (f y)) (by simp)
  have hdecomp : (fun y ↦ leviCivitaConnection I M X₃ y (X₂ y)) = H₂₃ + V₂₃ :=
    funext fun y ↦ h.leviCivitaConnection_horizontalLift ((hB₃ (f y)).of_le (by simp)) (B₂ (f y))
  have hVeq : V₂₃ = (fun y ↦ leviCivitaConnection I M X₃ y (X₂ y)) - H₂₃ := by
    rw [hdecomp, add_sub_cancel_left]
  have hV₂₃ : CMDiff ∞ (T% V₂₃) := by
    rw [hVeq]
    exact ((leviCivitaConnection I M).contMDiff_apply hX₂ hX₃).sub_section hH₂₃
  have hV₂₃v (y : M) : V₂₃ y ∈ (mfderiv I J f y).ker :=
    h.oneillA_apply_mem_ker (X₂ y) (h.horizontalLift_mem_orthogonal_ker y _)
  rw [hdecomp, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hH₂₃ x).mdifferentiableAt (by simp)) ((hV₂₃ x).mdifferentiableAt (by simp)),
    add_apply, map_add,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J)
      ((hB₂₃ (f x)).of_le (by simp)) (B₁ (f x))]
  have hAV := h.oneillA_apply_of_eventually_mem_ker
    ((hV₂₃ x).mdifferentiableAt (by simp)) (.of_forall hV₂₃v) (h.horizontalLift x (B₁ (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hAV
  rw [← hAV]

/-- Horizontal projection of the Lie-bracket term `∇_{[X₁, X₂]} X₃` for basic horizontal lifts:
the vertical bracket component `v [X₁, X₂] = 2 A_{X₁} X₂` contributes `2 A_{X₃} (A_{X₁} X₂)`. -/
private theorem starProjection_orthogonal_ker_mlieBracket_horizontalLift {x : M}
    {B₁ B₂ B₃ : Π y : N, TangentSpace J y}
    (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂)) (hB₃ : CMDiff ∞ (T% B₃)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M (fun z ↦ h.horizontalLift z (B₃ (f z))) x
          (mlieBracket I (fun y ↦ h.horizontalLift y (B₁ (f y)))
            (fun y ↦ h.horizontalLift y (B₂ (f y))) x)) =
      h.horizontalLift x
          (leviCivitaConnection J N B₃ (f x) (mlieBracket J B₁ B₂ (f x))) +
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (B₃ (f x)))
          (h.oneillA x (h.horizontalLift x (B₁ (f x))) (h.horizontalLift x (B₂ (f x)))) := by
  set X₁ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₁ (f y))
  set X₂ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₂ (f y))
  set X₃ : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B₃ (f y))
  have hX₁d : MDiffAt (T% X₁) x :=
    (h.contMDiffAt_horizontalLift (hB₁ (f x)) (by simp)).mdifferentiableAt (by simp)
  have hX₂d : MDiffAt (T% X₂) x :=
    (h.contMDiffAt_horizontalLift (hB₂ (f x)) (by simp)).mdifferentiableAt (by simp)
  have hzeroA : (mfderiv I J f x).kerᗮ.starProjection
      (h.oneillA x (mlieBracket I X₁ X₂ x) (X₃ x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)
  have hzeroT : (mfderiv I J f x).kerᗮ.starProjection
      (h.oneillT x (mlieBracket I X₁ X₂ x) (X₃ x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr <| by
      rw [Submodule.orthogonal_orthogonal]
      exact h.oneillT_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)
  have hmemA : h.oneillA x (X₃ x) (h.oneillA x (X₁ x) (X₂ x)) ∈
      (mfderiv I J f x).kerᗮ :=
    h.oneillA_apply_mem_orthogonal_ker (X₃ x)
      (h.oneillA_apply_mem_ker (X₁ x) (h.horizontalLift_mem_orthogonal_ker x _))
  rw [h.leviCivitaConnection_horizontalLift_apply ((hB₃ (f x)).of_le (by simp))
      (mlieBracket I X₁ X₂ x),
    h.mfderiv_mlieBracket_horizontalLift ((hB₁ (f x)).of_le (by simp))
      ((hB₂ (f x)).of_le (by simp)),
    h.starProjection_ker_mlieBracket hX₁d hX₂d
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _)
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
    map_smul, map_add, map_add, map_add, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _),
    Submodule.starProjection_eq_self_iff.mpr hmemA, hzeroA, hzeroT]
  abel

/-- **O'Neill's horizontal curvature formula at the operator level.** For smooth vector fields
`B₁, B₂, B₃` on `N`, the horizontal part of the curvature operator of `M` on their horizontal
lifts is the horizontal lift of the base curvature operator plus
`A_{X₁} (A_{X₂} X₃) - A_{X₂} (A_{X₁} X₃) - 2 A_{X₃} (A_{X₁} X₂)`. No `T2Space` hypothesis is
needed. -/
theorem starProjection_orthogonal_ker_curvatureOperator_horizontalLift (x : M)
    {B₁ B₂ B₃ : Π y : N, TangentSpace J y}
    (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂)) (hB₃ : CMDiff ∞ (T% B₃)) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureOperator
          (fun y ↦ h.horizontalLift y (B₁ (f y)))
          (fun y ↦ h.horizontalLift y (B₂ (f y)))
          (fun y ↦ h.horizontalLift y (B₃ (f y))) x) =
      h.horizontalLift x
          ((leviCivitaConnection J N).curvatureOperator B₁ B₂ B₃ (f x)) +
        h.oneillA x (h.horizontalLift x (B₁ (f x)))
          (h.oneillA x (h.horizontalLift x (B₂ (f x))) (h.horizontalLift x (B₃ (f x)))) -
        h.oneillA x (h.horizontalLift x (B₂ (f x)))
          (h.oneillA x (h.horizontalLift x (B₁ (f x))) (h.horizontalLift x (B₃ (f x)))) -
        (2 : ℝ) • h.oneillA x (h.horizontalLift x (B₃ (f x)))
          (h.oneillA x (h.horizontalLift x (B₁ (f x))) (h.horizontalLift x (B₂ (f x)))) := by
  rw [curvatureOperator_apply, curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_orthogonal_ker_iterated_horizontalLift (B₁ := B₁) hB₂ hB₃,
    h.starProjection_orthogonal_ker_iterated_horizontalLift (B₁ := B₂) hB₁ hB₃,
    h.starProjection_orthogonal_ker_mlieBracket_horizontalLift hB₁ hB₂ hB₃,
    map_sub, map_sub]
  abel

end Operator

/-! ### Pointwise `(1, 3)` and `(0, 4)` horizontal curvature tensors -/

section Tensor

variable [T2Space M] [T2Space N]

/-- **O'Neill's `(1, 3)` horizontal curvature equation on horizontal lifts.** -/
theorem starProjection_orthogonal_ker_curvatureTensor_horizontalLift (x : M)
    (b₁ b₂ b₃ : TangentSpace J (f x)) :
    (mfderiv I J f x).kerᗮ.starProjection
        ((leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂) (h.horizontalLift x b₃)) =
      h.horizontalLift x
          ((leviCivitaConnection J N).curvatureTensor (f x) b₁ b₂ b₃) +
        h.oneillA x (h.horizontalLift x b₁)
          (h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₃)) -
        h.oneillA x (h.horizontalLift x b₂)
          (h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₃)) -
        (2 : ℝ) • h.oneillA x (h.horizontalLift x b₃)
          (h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂)) := by
  obtain ⟨B₁, hB₁, rfl⟩ := exists_contMDiff_section_eq J F ∞ b₁
  obtain ⟨B₂, hB₂, rfl⟩ := exists_contMDiff_section_eq J F ∞ b₂
  obtain ⟨B₃, hB₃, rfl⟩ := exists_contMDiff_section_eq J F ∞ b₃
  have hX₁ : CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B₁ (f y)))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hB₁ (f y)) (by simp)
  have hX₂ : CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B₂ (f y)))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hB₂ (f y)) (by simp)
  have hX₃ : CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (B₃ (f y)))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hB₃ (f y)) (by simp)
  rw [curvatureTensor_apply _ x hX₁ hX₂ hX₃, curvatureTensor_apply _ (f x) hB₁ hB₂ hB₃]
  exact h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift x hB₁ hB₂ hB₃

/-- **O'Neill's `(1, 3)` horizontal curvature equation on horizontal tangent vectors.** -/
theorem starProjection_orthogonal_ker_curvatureTensor_of_mem_orthogonal_ker {x : M}
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
  have h₁ := h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift x
    (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)
  rwa [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw] at h₁

/-- The `(1, 3)` curvature tensor of the base expressed via the differential of the total-space
curvature on horizontal lifts and O'Neill's `A` tensor. -/
theorem curvatureTensor_map (x : M) (b₁ b₂ b₃ : TangentSpace J (f x)) :
    (leviCivitaConnection J N).curvatureTensor (f x) b₁ b₂ b₃ =
      mfderiv I J f x
        ((leviCivitaConnection I M).curvatureTensor x
            (h.horizontalLift x b₁) (h.horizontalLift x b₂) (h.horizontalLift x b₃) -
          h.oneillA x (h.horizontalLift x b₁)
            (h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₃)) +
          h.oneillA x (h.horizontalLift x b₂)
            (h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₃)) +
          (2 : ℝ) • h.oneillA x (h.horizontalLift x b₃)
            (h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂))) := by
  have hproj (y : TangentSpace I x) :
      mfderiv I J f x ((mfderiv I J f x).kerᗮ.starProjection y) = mfderiv I J f x y := by
    rw [← h.horizontalLift_mfderiv x y, h.mfderiv_horizontalLift]
  have hcurv := congrArg (mfderiv I J f x)
    (h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift x b₁ b₂ b₃)
  rw [hproj, map_sub, map_sub, map_add, h.mfderiv_horizontalLift] at hcurv
  rw [map_add, map_add, map_sub, hcurv]
  abel

/-- **O'Neill's `(0, 4)` horizontal curvature equation on horizontal lifts.** -/
theorem riemannCurvatureTensor_horizontalLift (x : M) (b₁ b₂ b₃ b₄ : TangentSpace J (f x)) :
    (leviCivitaConnection I M).riemannCurvatureTensor x
        (h.horizontalLift x b₁) (h.horizontalLift x b₂)
        (h.horizontalLift x b₃) (h.horizontalLift x b₄) =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x) b₁ b₂ b₃ b₄ +
        2 * ⟪h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂),
          h.oneillA x (h.horizontalLift x b₃) (h.horizontalLift x b₄)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₃),
          h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₄)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₃),
          h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₄)⟫_ℝ := by
  rw [riemannCurvatureTensor_apply, riemannCurvatureTensor_apply,
    ← Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x b₄),
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x b₄),
    h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    (h.horizontalLift x).inner_map_map, h.inner_oneillA]
  ring

/-- **O'Neill's `(0, 4)` horizontal curvature equation on horizontal tangent vectors.** -/
theorem riemannCurvatureTensor_of_mem_orthogonal_ker {x : M}
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ -
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ := by
  have h₁ := h.riemannCurvatureTensor_horizontalLift x
    (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z)
  rwa [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw, h.horizontalLift_mfderiv_of_mem x hz] at h₁

/-- The `(0, 4)` Riemann curvature tensor of the base expressed on differentials of horizontal
vectors. -/
theorem riemannCurvatureTensor_mfderiv {x : M}
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) =
      (leviCivitaConnection I M).riemannCurvatureTensor x u v w z -
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ +
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ -
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ := by
  linarith [h.riemannCurvatureTensor_of_mem_orthogonal_ker hu hv hw hz]

/-- The `(0, 4)` Riemann curvature tensor of the base expressed via horizontal lifts. -/
theorem riemannCurvatureTensor_map (x : M) (b₁ b₂ b₃ b₄ : TangentSpace J (f x)) :
    (leviCivitaConnection J N).riemannCurvatureTensor (f x) b₁ b₂ b₃ b₄ =
      (leviCivitaConnection I M).riemannCurvatureTensor x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂)
          (h.horizontalLift x b₃) (h.horizontalLift x b₄) -
        2 * ⟪h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂),
          h.oneillA x (h.horizontalLift x b₃) (h.horizontalLift x b₄)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₃),
          h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₄)⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₃),
          h.oneillA x (h.horizontalLift x b₂) (h.horizontalLift x b₄)⟫_ℝ := by
  linarith [h.riemannCurvatureTensor_horizontalLift x b₁ b₂ b₃ b₄]

/-- When O'Neill's horizontal tensor `A` vanishes at `x`, horizontal lifts intertwine the `(0, 4)`
Riemann curvature tensors at `x` and `f x`. -/
theorem riemannCurvatureTensor_horizontalLift_of_oneillA_eq_zero {x : M}
    (hA : h.oneillA x = 0) (b₁ b₂ b₃ b₄ : TangentSpace J (f x)) :
    (leviCivitaConnection I M).riemannCurvatureTensor x
        (h.horizontalLift x b₁) (h.horizontalLift x b₂)
        (h.horizontalLift x b₃) (h.horizontalLift x b₄) =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x) b₁ b₂ b₃ b₄ := by
  simp [h.riemannCurvatureTensor_horizontalLift, hA]

end Tensor

/-! ### Sectional curvature and curvature comparison -/

section Sectional

variable [T2Space M] [T2Space N]

omit [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [T2Space M] [T2Space N] in
private theorem det_gram_horizontalLift (x : M) (b₁ b₂ : TangentSpace J (f x)) :
    (Matrix.gram ℝ ![h.horizontalLift x b₁, h.horizontalLift x b₂]).det =
      (Matrix.gram ℝ ![b₁, b₂]).det := by
  rw [Matrix.real_det_gram_fin_two, Matrix.real_det_gram_fin_two]
  simp only [(h.horizontalLift x).inner_map_map]

/-- **O'Neill's sectional-curvature numerator formula on horizontal lifts.** -/
theorem inner_curvatureTensor_self_horizontalLift (x : M) (b₁ b₂ : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) b₁ b₂ b₂, b₁⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂) (h.horizontalLift x b₂),
        h.horizontalLift x b₁⟫_ℝ +
        3 * ‖h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂)‖ ^ 2 := by
  have h₁ := h.riemannCurvatureTensor_horizontalLift x b₁ b₂ b₂ b₁
  simp only [riemannCurvatureTensor_apply,
    h.oneillA_self (h.horizontalLift_mem_orthogonal_ker x b₂),
    h.oneillA_antisymm (h.horizontalLift_mem_orthogonal_ker x b₂)
      (h.horizontalLift_mem_orthogonal_ker x b₁),
    inner_zero_left, inner_neg_right, real_inner_self_eq_norm_sq] at h₁
  linarith

/-- **O'Neill's sectional-curvature numerator formula on horizontal tangent vectors.** -/
theorem inner_curvatureTensor_mfderiv_self {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
      mfderiv I J f x u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  have h₁ := h.inner_curvatureTensor_self_horizontalLift x (mfderiv I J f x u) (mfderiv I J f x v)
  rwa [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] at h₁

/-- **O'Neill's sectional curvature formula on base vectors.** No linear-independence guard is
needed: on dependent pairs both Gram determinants vanish and all three quotients are zero. -/
theorem sectionalCurvature_map (x : M) (b₁ b₂ : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂) +
        3 * ‖h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂)‖ ^ 2 /
          (Matrix.gram ℝ ![b₁, b₂]).det := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, h.det_gram_horizontalLift,
    h.inner_curvatureTensor_self_horizontalLift, add_div]

/-- O'Neill's sectional curvature formula solved for the horizontal plane in the total space. -/
theorem sectionalCurvature_horizontalLift (x : M) (b₁ b₂ : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x b₁) (h.horizontalLift x b₂) =
      (leviCivitaConnection J N).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ -
        3 * ‖h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂)‖ ^ 2 /
          (Matrix.gram ℝ ![b₁, b₂]).det := by
  linarith [h.sectionalCurvature_map x b₁ b₂]

/-- **O'Neill's sectional curvature formula on horizontal tangent vectors.** No linear-independence
guard is needed. -/
theorem sectionalCurvature_mfderiv {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  have h₁ := h.sectionalCurvature_map x (mfderiv I J f x u) (mfderiv I J f x v)
  have hdet := h.det_gram_horizontalLift x (mfderiv I J f x u) (mfderiv I J f x v)
  rw [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] at h₁ hdet
  rwa [← hdet] at h₁

/-- **O'Neill's sectional curvature formula on an orthonormal pair of base vectors.** -/
theorem sectionalCurvature_map_of_orthonormal (x : M) {b₁ b₂ : TangentSpace J (f x)}
    (hb : Orthonormal ℝ ![b₁, b₂]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂) +
        3 * ‖h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂)‖ ^ 2 := by
  rw [h.sectionalCurvature_map, Matrix.gram_eq_one_iff_orthonormal.mpr hb, Matrix.det_one, div_one]

/-- **O'Neill's sectional curvature formula on an orthonormal pair of horizontal vectors.** -/
theorem sectionalCurvature_mfderiv_of_orthonormal {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv hu hv, Matrix.gram_eq_one_iff_orthonormal.mpr huv,
    Matrix.det_one, div_one]

/-- **O'Neill's sectional curvature formula in vertical-Lie-bracket form**, for vector fields
differentiable at `x` and horizontal near `x`. No linear-independence guard is needed. -/
theorem sectionalCurvature_mfderiv_eq_add_three_div_four_mul_norm_mlieBracket_sq_div {x : M}
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's sectional curvature formula in vertical-Lie-bracket form** for horizontal vector
fields orthonormal at `x`: `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_three_div_four_mul_norm_mlieBracket_sq {x : M}
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (horth : Orthonormal ℝ ![X x, Y x]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_three_div_four_mul_norm_mlieBracket_sq_div hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr horth, Matrix.det_one, div_one]

/-- When O'Neill's horizontal tensor `A` vanishes on the horizontal lift of `(b₁, b₂)` at `x`, that
horizontal plane has the same sectional curvature as `span {b₁, b₂}` in `N`. -/
theorem sectionalCurvature_map_of_oneillA_eq_zero {x : M} {b₁ b₂ : TangentSpace J (f x)}
    (hA : h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂) = 0) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x b₁) (h.horizontalLift x b₂) := by
  rw [h.sectionalCurvature_map, hA]
  simp

/-- When `A_u v = 0` on a horizontal pair `(u, v)`, the horizontal plane spanned by `u` and `v` has
the same sectional curvature as its image in `N`. -/
theorem sectionalCurvature_mfderiv_of_oneillA_eq_zero {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hA : h.oneillA x u v = 0) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x u v := by
  rw [h.sectionalCurvature_mfderiv hu hv, hA]
  simp

/-- **Riemannian submersions are curvature-nondecreasing on horizontal lifts.** -/
theorem sectionalCurvature_horizontalLift_le (x : M) (b₁ b₂ : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x b₁) (h.horizontalLift x b₂) ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ := by
  rw [h.sectionalCurvature_map]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (Matrix.posSemidef_gram ℝ ![b₁, b₂]).det_nonneg)

/-- **Riemannian submersions are curvature-nondecreasing on horizontal planes.** -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  rw [h.sectionalCurvature_mfderiv hu hv]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg)

/-- On a linearly independent base pair, the base sectional curvature equals that of its horizontal
lift at `x` if and only if O'Neill's tensor `A` vanishes on the lifted pair. -/
theorem sectionalCurvature_map_eq_iff_oneillA_eq_zero {x : M}
    {b₁ b₂ : TangentSpace J (f x)} (hb : LinearIndependent ℝ ![b₁, b₂]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x b₁) (h.horizontalLift x b₂) ↔
      h.oneillA x (h.horizontalLift x b₁) (h.horizontalLift x b₂) = 0 := by
  rw [h.sectionalCurvature_map, add_eq_left, div_eq_zero_iff,
    or_iff_left (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hb),
    mul_eq_zero, or_iff_right (by norm_num), sq_eq_zero_iff, norm_eq_zero]

/-- On a linearly independent horizontal pair, the base sectional curvature equals the horizontal
sectional curvature if and only if `A_u v = 0`. -/
theorem sectionalCurvature_mfderiv_eq_iff_oneillA_eq_zero {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : LinearIndependent ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ↔
      h.oneillA x u v = 0 := by
  rw [h.sectionalCurvature_mfderiv hu hv, add_eq_left, div_eq_zero_iff,
    or_iff_left (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr huv),
    mul_eq_zero, or_iff_right (by norm_num), sq_eq_zero_iff, norm_eq_zero]

/-- **Descent of lower sectional-curvature bounds at a point.** If every horizontal two-plane at
`x` has sectional curvature at least `κ`, then every tangent two-plane of `N` at `f x` has
sectional curvature at least `κ`. -/
theorem le_sectionalCurvature_of_forall_le {x : M} {κ : ℝ}
    (hκ : ∀ u v : TangentSpace I x, u ∈ (mfderiv I J f x).kerᗮ →
      v ∈ (mfderiv I J f x).kerᗮ → LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v)
    {b₁ b₂ : TangentSpace J (f x)} (hb : LinearIndependent ℝ ![b₁, b₂]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection J) (f x) b₁ b₂ := by
  have hli : LinearIndependent ℝ ![h.horizontalLift x b₁, h.horizontalLift x b₂] :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mp
      (h.det_gram_horizontalLift x b₁ b₂ ▸ Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hb)
  exact (hκ _ _ (h.horizontalLift_mem_orthogonal_ker x b₁)
    (h.horizontalLift_mem_orthogonal_ker x b₂) hli).trans
    (h.sectionalCurvature_horizontalLift_le x b₁ b₂)

/-- **Global descent of lower sectional-curvature bounds along a surjective Riemannian
submersion.** -/
theorem le_sectionalCurvature_of_surjective {κ : ℝ} (hsurj : Function.Surjective f)
    (hκ : ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v)
    (y : N) {b₁ b₂ : TangentSpace J y} (hb : LinearIndependent ℝ ![b₁, b₂]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection J) y b₁ b₂ := by
  obtain ⟨x, rfl⟩ := hsurj y
  exact h.le_sectionalCurvature_of_forall_le (fun u v _ _ huv ↦ hκ x u v huv) hb

end Sectional

end TauCeti.IsRiemannianSubmersion
