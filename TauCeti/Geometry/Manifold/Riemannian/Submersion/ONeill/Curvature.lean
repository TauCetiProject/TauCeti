/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# O'Neill's horizontal curvature and sectional curvature formulas

For a Riemannian submersion `f : M → N`, O'Neill's horizontal curvature equation expresses the
horizontal part of the total-space Riemann curvature on horizontal vectors in terms of the base
Riemann curvature and O'Neill's horizontal integrability tensor `A`
(`IsRiemannianSubmersion.oneillA`). With Lee's curvature sign convention
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X, Y] Z`, for horizontal vectors `u, v, w ∈ (ker df_x)ᗮ`:

* `h(R_M(u, v) w) = hLift(R_N(df_x u, df_x v)(df_x w)) + A_u(A_v w) - A_v(A_u w) - 2 A_w(A_u v)`;
* `Rm_M(u, v, w, z) = Rm_N(df_x u, df_x v, df_x w, df_x z) - ⟪A_v w, A_u z⟫ + ⟪A_u w, A_v z⟫
    + 2 ⟪A_u v, A_w z⟫` for `u, v, w, z ∈ (ker df_x)ᗮ`;
* `⟪R_N(df_x u, df_x v)(df_x v), df_x u⟫ = ⟪R_M(u, v) v, u⟫ + 3 ‖A_u v‖²`.

Dividing by the Gram determinant—which horizontal lifting preserves identically—yields O'Neill's
sectional curvature formula for all `u, v : T_{f x} N`:
`K_N(u, v) = K_M(hLift u, hLift v) + 3 ‖A_(hLift u) (hLift v)‖² / det(Gram(u, v))`,
reducing on orthonormal pairs to `K_N(u, v) = K_M(hLift u, hLift v) + 3 ‖A_(hLift u) (hLift v)‖²`
and, for horizontal vector fields `X, Y` near `x`, to the Lie-bracket form with
`(3 / 4) ‖v [X, Y]_x‖²`. In particular, Riemannian submersions are curvature-nondecreasing on
horizontal planes, equality on a plane holds precisely when `A` vanishes on that plane, and
equality on all horizontal two-planes holds precisely when the horizontal distribution is
involutive.

The curvature-operator identities on basic horizontal lifts require no separation hypothesis;
`T2Space` enters only with the pointwise curvature tensors `curvatureTensor`,
`riemannCurvatureTensor`, and `sectionalCurvature`. Because both `sectionalCurvature` and `A`
vanish appropriately on linearly dependent pairs, the sectional curvature equations, monotonicity
inequality, and single-plane equality criterion hold without any linear-independence guard.

## Main results

* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureOperator_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.mfderiv_curvatureOperator_horizontalLift`: O'Neill's horizontal
  curvature equation at the `curvatureOperator` level (without `T2Space`).
* `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureTensor_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.starProjection_orthogonal_ker_curvatureTensor`,
  `TauCeti.IsRiemannianSubmersion.curvatureTensor_base_eq_mfderiv`: horizontal `(1,3)` curvature
  tensor formulas.
* `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.riemannCurvatureTensor_eq_of_mem_orthogonal_ker`: horizontal
  `(0,4)` Riemann curvature formulas (O'Neill, Theorem 2).
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_norm_mlieBracket`: O'Neill's
  sectional curvature formulas in tensor and Lie-bracket forms (O'Neill, Corollary 1).
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontalLift_le`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontalLift_eq_iff`,
  `IsRiemannianSubmersion.forall_linearIndependent_sectionalCurvature_horizontalLift_eq_iff`, and
  `IsRiemannianSubmersion.isInvolutiveDistribution_orthogonal_ker_iff_sectionalCurvature_eq`:
  monotonicity, plane rigidity, and equivalence between horizontal integrability and preservation
  of sectional curvature.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966), 459–469,
  Theorem 2 and Corollary 1.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Chapter 9, §C (9.28–9.29).
* J. Cheeger and D. G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland (1975),
  Chapter 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Manifold Set VectorField
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Gram

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

private theorem gram_horizontalLift_pair (x : M) (u v : TangentSpace J (f x)) :
    Matrix.gram ℝ ![h.horizontalLift x u, h.horizontalLift x v] = Matrix.gram ℝ ![u, v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem gram_mfderiv_pair {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    Matrix.gram ℝ ![mfderiv I J f x u, mfderiv I J f x v] = Matrix.gram ℝ ![u, v] := by
  rw [← h.gram_horizontalLift_pair x, h.horizontalLift_mfderiv_of_mem x hu,
    h.horizontalLift_mfderiv_of_mem x hv]

private theorem linearIndependent_horizontalLift_pair_iff (x : M) (u v : TangentSpace J (f x)) :
    LinearIndependent ℝ ![h.horizontalLift x u, h.horizontalLift x v] ↔
      LinearIndependent ℝ ![u, v] := by
  rw [← Matrix.posDef_gram_iff_linearIndependent (𝕜 := ℝ), h.gram_horizontalLift_pair,
    Matrix.posDef_gram_iff_linearIndependent]

end Gram

/-! ### Curvature operator on basic horizontal lifts -/

section Operator

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

-- These regularity indices are propositionally, but not definitionally, bounded by `∞`.
local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
local instance : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
local instance : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
local instance : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)

include h

private theorem contMDiff_horizontalLift {X : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) :
    CMDiff ∞ (T% (fun y ↦ h.horizontalLift y (X (f y)))) :=
  fun x ↦ h.contMDiffAt_horizontalLift (hX (f x)) (by simp)

/-- Horizontal part of a second iterated Levi-Civita derivative of basic horizontal fields along a
horizontal lift. Splitting `∇_(hLift Y)(hLift Z) = hLift(∇_Y Z) + A_(hLift Y)(hLift Z)` and
differentiating along `hLift u` yields the lift of `∇_u ∇_Y Z` plus `A_(hLift u)(A_(hLift Y) …)`. -/
private theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated
    {Y Z : Π y : N, TangentSpace J y} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (u : TangentSpace J (f x)) :
    (mfderiv I J f x).kerᗮ.starProjection
        (leviCivitaConnection I M
          (fun y ↦ leviCivitaConnection I M (fun q ↦ h.horizontalLift q (Z (f q))) y
            (h.horizontalLift y (Y (f y)))) x (h.horizontalLift x u)) =
      h.horizontalLift x
          (leviCivitaConnection J N (fun w ↦ leviCivitaConnection J N Z w (Y w)) (f x) u) +
        h.oneillA x (h.horizontalLift x u)
          (h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x)))) := by
  set W : Π w : N, TangentSpace J w := fun w ↦ leviCivitaConnection J N Z w (Y w)
  have hW : CMDiff ∞ (T% W) := (leviCivitaConnection J N).contMDiff_apply hY hZ
  set W' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (W (f y))
  have hW' : CMDiff ∞ (T% W') := h.contMDiff_horizontalLift hW
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ h.oneillA y (h.horizontalLift y (Y (f y))) (h.horizontalLift y (Z (f y)))
  have hV : CMDiff ∞ (T% V) := h.contMDiff_oneillA_apply
    (h.contMDiff_horizontalLift hY) (h.contMDiff_horizontalLift hZ)
  have hsplit : (fun y ↦ leviCivitaConnection I M (fun q ↦ h.horizontalLift q (Z (f q))) y
      (h.horizontalLift y (Y (f y)))) = W' + V :=
    funext fun y ↦ h.leviCivitaConnection_horizontalLift ((hZ (f y)).of_le (by simp)) (Y (f y))
  rw [hsplit, (leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      (hW'.mdifferentiable (by simp) x) (hV.mdifferentiable (by simp) x) trivial,
    add_apply, map_add,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) ((hW (f x)).of_le (by simp)) u]
  congr 1
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker :=
    h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _)
  rw [h.oneillA_apply_of_eventually_mem_ker (hV.mdifferentiable (by simp) x) (.of_forall hVv)
      (h.horizontalLift x u),
    Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x u)]

/-- **O'Neill's horizontal curvature operator formula.** For smooth vector fields `X, Y, Z` on the
base `N` (without any `T2Space` assumption), the horizontal part of the curvature operator on their
horizontal lifts equals the horizontal lift of the base curvature operator plus the three quadratic
`A`-terms. -/
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
  rw [curvatureOperator_apply, map_sub, map_sub,
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated hY hZ x (X (f x)),
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_iterated hX hZ x (Y (f x)),
    h.mlieBracket_horizontalLift ((hX (f x)).of_le (by simp)) ((hY (f x)).of_le (by simp)),
    map_add, map_smul, map_add, map_smul,
    h.starProjection_covariantDerivative_horizontalLift
      (isLeviCivitaConnection_leviCivitaConnection I)
      (isLeviCivitaConnection_leviCivitaConnection J) ((hZ (f x)).of_le (by simp))
      (mlieBracket J X Y (f x)),
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
      ((hZ (f x)).of_le (by simp))
      (h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker x _)),
    curvatureOperator_apply, map_sub, map_sub]
  abel

/-- Pushing the total-space curvature operator on basic horizontal lifts forward by `mfderiv`
recovers the base curvature operator plus the `mfderiv`-images of the quadratic `A`-terms. -/
theorem mfderiv_curvatureOperator_horizontalLift
    {X Y Z : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    mfderiv I J f x
        ((leviCivitaConnection I M).curvatureOperator
          (fun y ↦ h.horizontalLift y (X (f y)))
          (fun y ↦ h.horizontalLift y (Y (f y)))
          (fun y ↦ h.horizontalLift y (Z (f y))) x) =
      (leviCivitaConnection J N).curvatureOperator X Y Z (f x) +
        mfderiv I J f x (h.oneillA x (h.horizontalLift x (X (f x)))
          (h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x))))) -
        mfderiv I J f x (h.oneillA x (h.horizontalLift x (Y (f x)))
          (h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Z (f x))))) -
        (2 : ℝ) • mfderiv I J f x (h.oneillA x (h.horizontalLift x (Z (f x)))
          (h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x))))) := by
  conv_lhs => rw [← h.mfderiv_horizontalLift x (mfderiv I J f x _), h.horizontalLift_mfderiv]
  rw [h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift hX hY hZ x]
  simp only [map_sub, map_add, map_smul, h.mfderiv_horizontalLift]

end Operator

/-! ### Pointwise horizontal `(1,3)` and `(0,4)` curvature tensors -/

section Tensor

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [T2Space N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

local instance : IsManifold I ((1 : ℕ∞ω) + 1) M := .of_le (n := ∞) (by simp)
local instance : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)

include h

/-- **O'Neill's horizontal `(1,3)` curvature equation** evaluated on horizontal lifts of base
tangent vectors `u, v, w : T_{f x} N`. -/
theorem starProjection_orthogonal_ker_curvatureTensor_horizontalLift
    (x : M) (u v w : TangentSpace J (f x)) :
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
  rw [curvatureTensor_apply _ x (h.contMDiff_horizontalLift hX)
      (h.contMDiff_horizontalLift hY) (h.contMDiff_horizontalLift hZ),
    h.starProjection_orthogonal_ker_curvatureOperator_horizontalLift hX hY hZ x,
    curvatureTensor_apply _ (f x) hX hY hZ]

/-- **O'Neill's horizontal `(1,3)` curvature equation** for horizontal tangent vectors
`u, v, w ∈ (ker df_x)ᗮ`. -/
theorem starProjection_orthogonal_ker_curvatureTensor {x : M} {u v w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection ((leviCivitaConnection I M).curvatureTensor x u v w) =
      h.horizontalLift x ((leviCivitaConnection J N).curvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w)) +
        h.oneillA x u (h.oneillA x v w) -
        h.oneillA x v (h.oneillA x u w) -
        (2 : ℝ) • h.oneillA x w (h.oneillA x u v) := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv,
    ← h.horizontalLift_mfderiv_of_mem x hw]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift,
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.horizontalLift_mfderiv_of_mem x hw]

/-- The base `(1,3)` curvature tensor recovered by pushing the total-space curvature tensor and
quadratic `A`-terms forward along `mfderiv`. -/
theorem curvatureTensor_base_eq_mfderiv (x : M) (u v w : TangentSpace J (f x)) :
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
  have hproj := congrArg (mfderiv I J f x)
    (h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift x u v w)
  rw [← h.horizontalLift_mfderiv, h.mfderiv_horizontalLift] at hproj
  simp only [map_sub, map_add, map_smul, h.mfderiv_horizontalLift] at hproj ⊢
  rw [hproj]
  abel

/-- **O'Neill's horizontal `(0,4)` Riemann curvature equation (O'Neill, Theorem 2)** on horizontal
lifts of base tangent vectors `u, v, w, z : T_{f x} N`. -/
theorem riemannCurvatureTensor_horizontalLift (x : M) (u v w z : TangentSpace J (f x)) :
    (leviCivitaConnection I M).riemannCurvatureTensor x
        (h.horizontalLift x u) (h.horizontalLift x v)
        (h.horizontalLift x w) (h.horizontalLift x z) =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x) u v w z -
        ⟪h.oneillA x (h.horizontalLift x v) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x u) (h.horizontalLift x z)⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x w),
          h.oneillA x (h.horizontalLift x v) (h.horizontalLift x z)⟫_ℝ +
        2 * ⟪h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v),
          h.oneillA x (h.horizontalLift x w) (h.horizontalLift x z)⟫_ℝ := by
  simp only [riemannCurvatureTensor_apply]
  conv_lhs =>
    rw [← Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x z),
      ← Submodule.inner_starProjection_left_eq_right]
  rw [h.starProjection_orthogonal_ker_curvatureTensor_horizontalLift]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    (h.horizontalLift x).inner_map_map, h.inner_oneillA]
  ring

/-- **O'Neill's horizontal `(0,4)` Riemann curvature equation (O'Neill, Theorem 2)** for horizontal
tangent vectors `u, v, w, z ∈ (ker df_x)ᗮ`. -/
theorem riemannCurvatureTensor_eq_of_mem_orthogonal_ker {x : M} {u v w z : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).riemannCurvatureTensor x u v w z =
      (leviCivitaConnection J N).riemannCurvatureTensor (f x)
          (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) (mfderiv I J f x z) -
        ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu, ← h.horizontalLift_mfderiv_of_mem x hv,
    ← h.horizontalLift_mfderiv_of_mem x hw, ← h.horizontalLift_mfderiv_of_mem x hz]
  rw [h.riemannCurvatureTensor_horizontalLift, h.horizontalLift_mfderiv_of_mem x hu,
    h.horizontalLift_mfderiv_of_mem x hv, h.horizontalLift_mfderiv_of_mem x hw,
    h.horizontalLift_mfderiv_of_mem x hz]

/-- **Sectional-curvature numerator identity** on horizontal lifts of base tangent vectors
`u, v : T_{f x} N`. -/
theorem inner_curvatureTensor_horizontalLift_self (x : M) (u v : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) u v v, u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x v),
        h.horizontalLift x u⟫_ℝ +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  have hrm := h.riemannCurvatureTensor_horizontalLift x u v v u
  simp only [riemannCurvatureTensor_apply] at hrm
  have hu := h.horizontalLift_mem_orthogonal_ker x u
  have hv := h.horizontalLift_mem_orthogonal_ker x v
  rw [h.oneillA_self hv, inner_zero_left, h.oneillA_antisymm hv hu, inner_neg_right,
    real_inner_self_eq_norm_sq] at hrm
  linarith

/-- **Sectional-curvature numerator identity** for horizontal tangent vectors
`u, v ∈ (ker df_x)ᗮ`. -/
theorem inner_curvatureTensor_mfderiv_self {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
      mfderiv I J f x u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.inner_curvatureTensor_horizontalLift_self x (mfderiv I J f x u) (mfderiv I J f x v),
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv]

/-! ### O'Neill's sectional curvature formulas, monotonicity, and rigidity -/

/-- **O'Neill's sectional curvature formula (O'Neill, Corollary 1)** for arbitrary base vectors
`u, v : T_{f x} N`. On linearly dependent pairs both totalized quotients vanish, so no linear
independence hypothesis is required. -/
theorem sectionalCurvature_horizontalLift (x : M) (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 /
          (Matrix.gram ℝ ![u, v]).det := by
  simp only [sectionalCurvature_apply, h.gram_horizontalLift_pair,
    h.inner_curvatureTensor_horizontalLift_self, add_div]

/-- **O'Neill's sectional curvature formula** on an orthonormal pair in `T_{f x} N`. -/
theorem sectionalCurvature_horizontalLift_of_orthonormal {x : M} {u v : TangentSpace J (f x)}
    (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  rw [h.sectionalCurvature_horizontalLift, Matrix.gram_eq_one_iff_orthonormal.mpr huv,
    Matrix.det_one, div_one]

/-- **O'Neill's sectional curvature formula** for horizontal vectors `u, v ∈ (ker df_x)ᗮ`,
valid without a linear-independence guard. -/
theorem sectionalCurvature_mfderiv {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  rw [h.sectionalCurvature_horizontalLift x (mfderiv I J f x u) (mfderiv I J f x v),
    h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv,
    h.gram_mfderiv_pair hu hv]

/-- **O'Neill's sectional curvature formula** on an orthonormal pair of horizontal vectors
`u, v ∈ (ker df_x)ᗮ`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (huv : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv hu hv, Matrix.gram_eq_one_iff_orthonormal.mpr huv,
    Matrix.det_one, div_one]

/-- **Lie-bracket form of O'Neill's sectional curvature formula** for vector fields `X, Y` that are
differentiable at `x` and horizontal near `x`:
`K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]_x‖² / det(Gram(X_x, Y_x))`. -/
theorem sectionalCurvature_mfderiv_eq_add_norm_mlieBracket {x : M}
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x (X x) (Y x) +
        (3 / 4 : ℝ) * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat, mul_pow]
  ring

/-- **Lie-bracket form of O'Neill's sectional curvature formula** on horizontal vector fields that
are orthonormal at `x`: `K_N(df X, df Y) = K_M(X, Y) + (3 / 4) ‖v [X, Y]_x‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_norm_mlieBracket_of_orthonormal {x : M}
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
  rw [h.sectionalCurvature_mfderiv_eq_add_norm_mlieBracket hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr hXY, Matrix.det_one, div_one]

/-- **Curvature monotonicity for Riemannian submersions.** The base sectional curvature is bounded
below by the horizontal sectional curvature in the total space, for all `u, v : T_{f x} N`. -/
theorem sectionalCurvature_horizontalLift_le (x : M) (u v : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x
        (h.horizontalLift x u) (h.horizontalLift x v) ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v := by
  rw [h.sectionalCurvature_horizontalLift, le_add_iff_nonneg_right]
  have hdet : 0 ≤ (Matrix.gram ℝ ![u, v]).det := by
    by_cases huv : LinearIndependent ℝ ![u, v]
    · exact (Matrix.posDef_gram_of_linearIndependent huv).det_pos.le
    · rw [not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)]
  positivity

/-- **Curvature monotonicity** for horizontal vectors `u, v ∈ (ker df_x)ᗮ`. -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] using
    h.sectionalCurvature_horizontalLift_le x (mfderiv I J f x u) (mfderiv I J f x v)

/-- Equality in O'Neill's sectional curvature inequality on `u, v : T_{f x} N` holds if and only if
`A` vanishes on `(hLift u, hLift v)`. This equivalence holds without a linear-independence guard
because both sides hold automatically on linearly dependent pairs. -/
theorem sectionalCurvature_horizontalLift_eq_iff (x : M) (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x
        (h.horizontalLift x u) (h.horizontalLift x v) ↔
      h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
  rw [h.sectionalCurvature_horizontalLift, add_eq_left]
  by_cases huv : LinearIndependent ℝ ![u, v]
  · have hdet : (Matrix.gram ℝ ![u, v]).det ≠ 0 :=
      (Matrix.posDef_gram_of_linearIndependent huv).det_pos.ne'
    simp [div_eq_zero_iff, hdet]
  · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
    have hA : h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 :=
      h.oneillA_eq_zero_of_not_linearIndependent (h.horizontalLift_mem_orthogonal_ker x u)
        (mt (h.linearIndependent_horizontalLift_pair_iff x u v).mp huv)
    simp [hdet, hA]

/-- Equality in O'Neill's sectional curvature inequality on horizontal vectors `u, v ∈ (ker df_x)ᗮ`
holds if and only if `A_x u v = 0`. -/
theorem sectionalCurvature_mfderiv_eq_iff {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v ↔
      h.oneillA x u v = 0 := by
  simpa only [h.horizontalLift_mfderiv_of_mem x hu, h.horizontalLift_mfderiv_of_mem x hv] using
    h.sectionalCurvature_horizontalLift_eq_iff x (mfderiv I J f x u) (mfderiv I J f x v)

/-- **Pointwise sectional-curvature rigidity.** Base and horizontal sectional curvatures agree on
every two-plane at `f x` if and only if O'Neill's horizontal tensor `A_x` vanishes identically. No
dimension assumption on `N` is needed. -/
theorem forall_linearIndependent_sectionalCurvature_horizontalLift_eq_iff (x : M) :
    (∀ u v : TangentSpace J (f x), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection J N).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
        (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x
          (h.horizontalLift x u) (h.horizontalLift x v)) ↔
      h.oneillA x = 0 := by
  rw [h.oneillA_eq_zero_iff_horizontalLift]
  refine ⟨fun heq u v ↦ ?_, fun h0 u v _ ↦ (h.sectionalCurvature_horizontalLift_eq_iff x u v).mpr
    (h0 u v)⟩
  by_cases huv : LinearIndependent ℝ ![u, v]
  · exact (h.sectionalCurvature_horizontalLift_eq_iff x u v).mp (heq u v huv)
  · exact h.oneillA_eq_zero_of_not_linearIndependent (h.horizontalLift_mem_orthogonal_ker x u)
      (mt (h.linearIndependent_horizontalLift_pair_iff x u v).mp huv)

/-- **Integrability via sectional curvature.** The horizontal distribution `x ↦ (ker df_x)ᗮ` of a
Riemannian submersion is involutive if and only if horizontal lifting preserves sectional curvature
on every two-plane at every point. -/
theorem isInvolutiveDistribution_orthogonal_ker_iff_sectionalCurvature_eq :
    IsInvolutiveDistribution I (fun x ↦ (mfderiv I J f x).kerᗮ) ↔
      ∀ (x : M) (u v : TangentSpace J (f x)), LinearIndependent ℝ ![u, v] →
        (leviCivitaConnection J N).sectionalCurvature
            (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v =
          (leviCivitaConnection I M).sectionalCurvature
            (isMetricCompatible_leviCivitaConnection I (M := M)) x
            (h.horizontalLift x u) (h.horizontalLift x v) := by
  simp only [h.isInvolutiveDistribution_orthogonal_ker_iff,
    ← h.forall_linearIndependent_sectionalCurvature_horizontalLift_eq_iff]

/-- If the total space has sectional curvature `κ` at `x` and `A_x = 0`, then the base has
sectional curvature `κ` at `f x`. -/
theorem hasSectionalCurvatureAt_of_oneillA_eq_zero {x : M} {κ : ℝ}
    (hM : (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I (M := M)) x κ)
    (hA : h.oneillA x = 0) :
    (leviCivitaConnection J N).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) κ := by
  rw [hasSectionalCurvatureAt_iff]
  intro u v huv
  exact ((h.sectionalCurvature_horizontalLift_eq_iff x u v).mpr (by simp [hA])).trans
    (hM.sectionalCurvature_eq _ _ ((h.linearIndependent_horizontalLift_pair_iff x u v).mpr huv))

/-- A surjective Riemannian submersion with integrable horizontal distribution (`A = 0`) carries
constant sectional curvature `κ` from the total space to the base. -/
theorem hasConstantSectionalCurvature_of_surjective_of_oneillA_eq_zero
    (hf : Function.Surjective f) {κ : ℝ}
    (hM : (leviCivitaConnection I M).HasConstantSectionalCurvature
      (isMetricCompatible_leviCivitaConnection I (M := M)) κ)
    (hA : ∀ x, h.oneillA x = 0) :
    (leviCivitaConnection J N).HasConstantSectionalCurvature
      (isMetricCompatible_leviCivitaConnection J (M := N)) κ := by
  rw [hasConstantSectionalCurvature_iff]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact h.hasSectionalCurvatureAt_of_oneillA_eq_zero (hM.hasSectionalCurvatureAt x) (hA x)

/-- A lower sectional-curvature bound `κ` on horizontal two-planes at `x` descends to a lower
sectional-curvature bound `κ` on all two-planes at `f x`. -/
theorem le_sectionalCurvature_of_horizontal {x : M} {κ : ℝ}
    (hκ : ∀ u ∈ (mfderiv I J f x).kerᗮ, ∀ v ∈ (mfderiv I J f x).kerᗮ,
      LinearIndependent ℝ ![u, v] →
        κ ≤ (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v)
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v :=
  (hκ _ (h.horizontalLift_mem_orthogonal_ker x u) _ (h.horizontalLift_mem_orthogonal_ker x v)
    ((h.linearIndependent_horizontalLift_pair_iff x u v).mpr huv)).trans
    (h.sectionalCurvature_horizontalLift_le x u v)

/-- A strict lower sectional-curvature bound `κ` on horizontal two-planes at `x` descends to a
strict lower sectional-curvature bound `κ` on all two-planes at `f x`. -/
theorem lt_sectionalCurvature_of_horizontal {x : M} {κ : ℝ}
    (hκ : ∀ u ∈ (mfderiv I J f x).kerᗮ, ∀ v ∈ (mfderiv I J f x).kerᗮ,
      LinearIndependent ℝ ![u, v] →
        κ < (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I (M := M)) x u v)
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    κ < (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) (f x) u v :=
  (hκ _ (h.horizontalLift_mem_orthogonal_ker x u) _ (h.horizontalLift_mem_orthogonal_ker x v)
    ((h.linearIndependent_horizontalLift_pair_iff x u v).mpr huv)).trans_le
    (h.sectionalCurvature_horizontalLift_le x u v)

/-- For a surjective Riemannian submersion, a global lower sectional-curvature bound `κ` on the
total space descends to the base. -/
theorem le_sectionalCurvature_of_surjective (hf : Function.Surjective f) {κ : ℝ}
    (hκ : ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v)
    (y : N) {u v : TangentSpace J y} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) y u v := by
  obtain ⟨x, rfl⟩ := hf y
  exact h.le_sectionalCurvature_of_horizontal (fun u _ v _ ↦ hκ x u v) huv

/-- For a surjective Riemannian submersion, a global strict lower sectional-curvature bound `κ` on
the total space descends to the base. -/
theorem lt_sectionalCurvature_of_surjective (hf : Function.Surjective f) {κ : ℝ}
    (hκ : ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
      κ < (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I (M := M)) x u v)
    (y : N) {u v : TangentSpace J y} (huv : LinearIndependent ℝ ![u, v]) :
    κ < (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J (M := N)) y u v := by
  obtain ⟨x, rfl⟩ := hf y
  exact h.lt_sectionalCurvature_of_horizontal (fun u _ v _ ↦ hκ x u v) huv

end Tensor

end TauCeti.IsRiemannianSubmersion
