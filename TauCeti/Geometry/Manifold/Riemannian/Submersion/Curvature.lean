/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Analysis.InnerProductSpace.Gram.Pair
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's horizontal curvature formula

Let `f : M → N` be a Riemannian submersion, with O'Neill's horizontal tensor `A`
(`TauCeti.IsRiemannianSubmersion.oneillA`). For horizontal tangent vectors `u` and `w` at `x`,

`⟨R_M(u, w) w, u⟩ = ⟨R_N(f_* u, f_* w) f_* w, f_* u⟩ - 3 |A_u w|²`.

Since `f_*` is isometric on horizontal vectors, the Gram determinants of `u, w` and of
`f_* u, f_* w` agree, so the sectional curvature of a horizontal plane increases by
`3 |A_u w|² / |u ∧ w|²` under `f`. As `v [X, Y] = 2 A_X Y` for horizontal fields, this is the
formula `K_N = K_M + ¾ |v [X, Y]|²` for horizontal orthonormal `X, Y`. These formulas compute the
curvature of quotient metrics, such as those of the projective spaces as quotients of round
spheres, and of connection metrics on fibre bundles.

The proof differentiates horizontal lifts of fields on the base. For such basic fields the
Levi-Civita derivative is `∇_X Y = (∇_X Y)^~ + A_X Y`, the lift of the base derivative plus the
vertical correction (`TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`).
Expanding `R(X, Y) Y = ∇_X ∇_Y Y - ∇_Y ∇_X Y - ∇_[X,Y] Y`, the vertical correction contributes
`|A_X Y|²` through the second term and `2 |A_X Y|²` through the vertical part `2 A_X Y` of the
bracket in the third. The curvature convention is `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`.

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`: the Levi-Civita
  derivative of basic horizontal fields.
* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_of_mem_orthogonal_ker`: O'Neill's
  horizontal curvature formula.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv`: the sectional curvature of the
  image of a horizontal plane.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemma 1 and Corollary 1 of Theorem 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9.
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
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

-- These regularity indices are propositionally, but not definitionally, equal to two.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := by
  rw [one_add_one_eq_two]
  infer_instance

local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  infer_instance

include h

/-- **The Levi-Civita derivative of basic horizontal fields.** For the horizontal lift `Ỹ` of a
field `Y` on the base and a base vector `v`, `∇_ṽ Ỹ = (∇_v Y)^~ + A_ṽ Ỹ`: the horizontal part is
the lift of the base derivative and the vertical part is O'Neill's tensor. -/
theorem leviCivitaConnection_horizontalLift {Y : Π y : N, TangentSpace J y} {x : M}
    (hY : CMDiffAt 1 (T% Y) (f x)) (v : TangentSpace J (f x)) :
    leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v) =
      h.horizontalLift x (leviCivitaConnection J N Y (f x) v) +
        h.oneillA x (h.horizontalLift x v) (h.horizontalLift x (Y (f x))) := by
  have hYd : MDiffAt (T% (fun y ↦ h.horizontalLift y (Y (f y)))) x :=
    (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  rw [h.oneillA_apply_of_eventually_mem_orthogonal_ker hYd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _),
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x v),
    ← h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) hY v,
    add_comm, Submodule.starProjection_add_starProjection_orthogonal]

/-- Pairing the Levi-Civita derivative of a basic horizontal field with a horizontal lift only sees
the base derivative. -/
private theorem inner_leviCivitaConnection_horizontalLift {Y : Π y : N, TangentSpace J y} {x : M}
    (hY : CMDiffAt 1 (T% Y) (f x)) (v w : TangentSpace J (f x)) :
    ⟪leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x (h.horizontalLift x v),
        h.horizontalLift x w⟫_ℝ =
      ⟪leviCivitaConnection J N Y (f x) v, w⟫_ℝ := by
  rw [h.leviCivitaConnection_horizontalLift hY, inner_add_left, LinearIsometry.inner_map_map,
    Submodule.inner_right_of_mem_orthogonal
      (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _))
      (h.horizontalLift_mem_orthogonal_ker x w), add_zero]

/-- For a vertical field `V` and a basic horizontal field `X̃`, `⟨∇_w̃ V, X̃⟩ = ⟨V, A_X̃ w̃⟩`, since
`⟨V, X̃⟩ = 0` and the vertical part of `∇_w̃ X̃` is `A_w̃ X̃ = -A_X̃ w̃`. -/
private theorem inner_leviCivitaConnection_of_mem_ker {V : Π y : M, TangentSpace I y}
    {X : Π y : N, TangentSpace J y} {x : M} (hV : MDiffAt (T% V) x)
    (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker) (hX : CMDiffAt 1 (T% X) (f x))
    (w : TangentSpace J (f x)) :
    ⟪leviCivitaConnection I M V x (h.horizontalLift x w), h.horizontalLift x (X (f x))⟫_ℝ =
      ⟪V x, h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x w)⟫_ℝ := by
  have h₁ := (isMetricCompatible_leviCivitaConnection I (M := M)).mvfderiv_inner_eq
    (FiberBundle.extend E (h.horizontalLift x w)) hV
    ((h.contMDiffAt_horizontalLift hX (by norm_num)).mdifferentiableAt one_ne_zero)
  have hzero : (fun y ↦ ⟪V y, h.horizontalLift y (X (f y))⟫_ℝ) = fun _ ↦ 0 := funext fun y ↦
    Submodule.inner_right_of_mem_orthogonal (hVv y) (h.horizontalLift_mem_orthogonal_ker y _)
  rw [hzero, mvfderiv_const, zero_apply] at h₁
  beta_reduce at h₁
  rw [FiberBundle.extend_apply_self, h.leviCivitaConnection_horizontalLift hX, inner_add_right,
    Submodule.inner_right_of_mem_orthogonal (hVv x) (h.horizontalLift_mem_orthogonal_ker x _),
    zero_add, h.oneillA_antisymm (h.horizontalLift_mem_orthogonal_ker x _)
      (h.horizontalLift_mem_orthogonal_ker x _), inner_neg_right] at h₁
  linarith

/-- For a vertical field `V` and basic horizontal fields `X̃` and `Ỹ`, `⟨∇_V Ỹ, X̃⟩ = ⟨V, A_X̃ Ỹ⟩`.
Since `[Ỹ, V]` is vertical, this reduces to `inner_leviCivitaConnection_of_mem_ker`. -/
private theorem inner_leviCivitaConnection_horizontalLift_of_mem_ker
    {V : Π y : M, TangentSpace I y} {X Y : Π y : N, TangentSpace J y} {x : M}
    (hV : MDiffAt (T% V) x) (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker)
    (hX : CMDiffAt 1 (T% X) (f x)) (hY : CMDiffAt 1 (T% Y) (f x)) :
    ⟪leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x (V x),
        h.horizontalLift x (X (f x))⟫_ℝ =
      ⟪V x, h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x)))⟫_ℝ := by
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  have hT := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I)) hYd hV
  have hbr := (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
    (by simp [minSmoothness_of_isRCLikeNormedField]) hYd hV (hY.mdifferentiableAt one_ne_zero)
    (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  rw [← h.inner_leviCivitaConnection_of_mem_ker hV hVv hX, ← sub_eq_zero, ← inner_sub_left,
    ← neg_sub, hT, inner_neg_left,
    Submodule.inner_right_of_mem_orthogonal hbr (h.horizontalLift_mem_orthogonal_ker x _),
    neg_zero]

/-- O'Neill's horizontal curvature formula on basic horizontal fields `X̃` and `Ỹ`, lifting smooth
fields `X` and `Y` on the base. -/
private theorem inner_curvatureOperator_horizontalLift {X Y : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (x : M) :
    ⟪(leviCivitaConnection I M).curvatureOperator (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) (fun y ↦ h.horizontalLift y (Y (f y))) x,
        h.horizontalLift x (X (f x))⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureOperator X Y Y (f x), X (f x)⟫_ℝ -
        3 * ‖h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x)))‖ ^ 2 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set covM := leviCivitaConnection I M
  set covN := leviCivitaConnection J N
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  have hX₁ (z : N) : CMDiffAt 1 (T% X) z := (hX z).of_le (by simp)
  have hY₁ (z : N) : CMDiffAt 1 (T% Y) z := (hY z).of_le (by simp)
  have hX' : CMDiff ∞ (T% X') := fun y ↦ h.contMDiffAt_horizontalLift (hX (f y)) (by simp)
  have hY' : CMDiff ∞ (T% Y') := fun y ↦ h.contMDiffAt_horizontalLift (hY (f y)) (by simp)
  -- `∇_Ỹ Ỹ` is the lift of `∇_Y Y`, since `A_Ỹ Ỹ = 0`.
  set Z : Π z : N, TangentSpace J z := fun z ↦ covN Y z (Y z)
  have hYY : (fun y ↦ covM Y' y (Y' y)) = fun y ↦ h.horizontalLift y (Z (f y)) := by
    funext y
    rw [h.leviCivitaConnection_horizontalLift (hY₁ (f y)),
      h.oneillA_self (h.horizontalLift_mem_orthogonal_ker y _), add_zero]
  -- `∇_X̃ Ỹ` is the lift of `∇_X Y` plus the vertical field `V = A_X̃ Ỹ`.
  set W : Π z : N, TangentSpace J z := fun z ↦ covN Y z (X z)
  set V : Π y : M, TangentSpace I y := fun y ↦ covM Y' y (X' y) - h.horizontalLift y (W (f y))
  have hV (y : M) : V y = h.oneillA y (X' y) (Y' y) :=
    sub_eq_of_eq_add' (h.leviCivitaConnection_horizontalLift (hY₁ (f y)) (X (f y)))
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker :=
    hV y ▸ h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _)
  have hW : CMDiffAt 1 (T% W) (f x) := (covN.contMDiff_apply hX hY (f x)).of_le (by simp)
  have hWd : MDiffAt (T% (fun y ↦ h.horizontalLift y (W (f y)))) x :=
    (h.contMDiffAt_horizontalLift hW (by norm_num)).mdifferentiableAt one_ne_zero
  have hVd : MDiffAt (T% V) x := mdifferentiableAt_sub_section
    ((covM.contMDiff_apply hX' hY' x).mdifferentiableAt (by simp)) hWd
  have hA : ⟪V x, V x⟫_ℝ = ‖h.oneillA x (X' x) (Y' x)‖ ^ 2 := by
    rw [hV x, real_inner_self_eq_norm_sq]
  -- The three terms of `R(X̃, Ỹ) Ỹ = ∇_X̃ ∇_Ỹ Ỹ - ∇_Ỹ ∇_X̃ Ỹ - ∇_[X̃,Ỹ] Ỹ`.
  have h₁ : ⟪covM (fun y ↦ covM Y' y (Y' y)) x (X' x), X' x⟫_ℝ =
      ⟪covN Z (f x) (X (f x)), X (f x)⟫_ℝ := by
    rw [hYY]
    exact h.inner_leviCivitaConnection_horizontalLift
      ((covN.contMDiff_apply hY hY (f x)).of_le (by simp)) _ _
  have h₂ : ⟪covM (fun y ↦ covM Y' y (X' y)) x (Y' x), X' x⟫_ℝ =
      ⟪covN W (f x) (Y (f x)), X (f x)⟫_ℝ + ‖h.oneillA x (X' x) (Y' x)‖ ^ 2 := by
    have hXY : (fun y ↦ covM Y' y (X' y)) = (fun y ↦ h.horizontalLift y (W (f y))) + V := by
      funext y
      simp only [V, Pi.add_apply, add_sub_cancel]
    have hVY := h.inner_leviCivitaConnection_of_mem_ker hVd hVv (hX₁ (f x)) (Y (f x))
    rw [← hV x] at hVY
    rw [hXY, covM.isCovariantDerivativeOnUniv.add hWd hVd, add_apply, inner_add_left, hVY, hA,
      h.inner_leviCivitaConnection_horizontalLift hW]
  have h₃ : ⟪covM Y' x (mlieBracket I X' Y' x), X' x⟫_ℝ =
      ⟪covN Y (f x) (mlieBracket J X Y (f x)), X (f x)⟫_ℝ +
        2 * ‖h.oneillA x (X' x) (Y' x)‖ ^ 2 := by
    have hYV := h.inner_leviCivitaConnection_horizontalLift_of_mem_ker hVd hVv (hX₁ (f x))
      (hY₁ (f x))
    rw [← hV x, hA, hV x] at hYV
    rw [h.mlieBracket_horizontalLift (hX₁ (f x)) (hY₁ (f x)), map_add, map_smul, inner_add_left,
      real_inner_smul_left, hYV, h.inner_leviCivitaConnection_horizontalLift (hY₁ (f x))]
  rw [curvatureOperator_apply, curvatureOperator_apply, inner_sub_left, inner_sub_left, h₁, h₂,
    h₃, inner_sub_left, inner_sub_left]
  ring

/-- **O'Neill's horizontal curvature formula.** For horizontal vectors `u` and `w`,
`⟨R_M(u, w) w, u⟩ = ⟨R_N(f_* u, f_* w) f_* w, f_* u⟩ - 3 |A_u w|²`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker [T2Space M] [T2Space N] {x : M}
    {u w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u w w, u⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x) (mfderiv I J f x u)
          (mfderiv I J f x w) (mfderiv I J f x w), mfderiv I J f x u⟫_ℝ -
        3 * ‖h.oneillA x u w‖ ^ 2 := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  -- Extend `f_* u` and `f_* w` to smooth fields on the base, whose lifts take the values `u`, `w`.
  obtain ⟨X, hX, hXx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨Y, hY, hYx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x w)
  have hu' : h.horizontalLift x (X (f x)) = u := by
    rw [hXx, h.horizontalLift_mfderiv_of_mem x hu]
  have hw' : h.horizontalLift x (Y (f x)) = w := by
    rw [hYx, h.horizontalLift_mfderiv_of_mem x hw]
  have hX' : CMDiff ∞ (T% fun y ↦ h.horizontalLift y (X (f y))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hX (f y)) (by simp)
  have hY' : CMDiff ∞ (T% fun y ↦ h.horizontalLift y (Y (f y))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hY (f y)) (by simp)
  have hcurv := h.inner_curvatureOperator_horizontalLift hX hY x
  rw [← curvatureTensor_apply _ x hX' hY' hY', ← curvatureTensor_apply _ (f x) hX hY hY, hu', hw',
    hXx, hYx] at hcurv
  exact hcurv

/-- **O'Neill's formula for sectional curvature.** The image under `f_*` of the plane spanned by
horizontal vectors `u` and `w` has sectional curvature larger by `3 |A_u w|² / |u ∧ w|²`. For an
orthonormal pair this is `K_N(f_* u, f_* w) = K_M(u, w) + 3 |A_u w|²`. On a dependent pair both
sides are zero. -/
theorem sectionalCurvature_mfderiv [T2Space M] [T2Space N] {x : M} {u w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature (isMetricCompatible_leviCivitaConnection J)
        (f x) (mfderiv I J f x u) (mfderiv I J f x w) =
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
          x u w + 3 * ‖h.oneillA x u w‖ ^ 2 / (Matrix.gram ℝ ![u, w]).det := by
  have hinner {a b : TangentSpace I x} (ha : a ∈ (mfderiv I J f x).kerᗮ)
      (hb : b ∈ (mfderiv I J f x).kerᗮ) :
      ⟪mfderiv I J f x a, mfderiv I J f x b⟫_ℝ = ⟪a, b⟫_ℝ := by
    conv_rhs => rw [← h.horizontalLift_mfderiv_of_mem x ha, ← h.horizontalLift_mfderiv_of_mem x hb]
    exact (LinearIsometry.inner_map_map _ _ _).symm
  rw [sectionalCurvature_apply, sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    Matrix.real_det_gram_fin_two, hinner hu hu, hinner hw hw, hinner hu hw,
    h.inner_curvatureTensor_of_mem_orthogonal_ker hu hw, ← add_div]
  ring

end TauCeti.IsRiemannianSubmersion
