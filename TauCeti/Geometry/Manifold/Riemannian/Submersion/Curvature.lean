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
(`TauCeti.IsRiemannianSubmersion.oneillA`). For horizontal tangent vectors `u`, `v`, `w` and `z`
at `x`,

`⟨R_M(u, v) w, z⟩ = ⟨R_N(f_* u, f_* v) f_* w, f_* z⟩ + 2 ⟨A_u v, A_w z⟩ - ⟨A_v w, A_u z⟩ +
  ⟨A_u w, A_v z⟩`.

On a plane this reads `⟨R_M(u, w) w, u⟩ = ⟨R_N(f_* u, f_* w) f_* w, f_* u⟩ - 3 |A_u w|²`.
Since `f_*` is isometric on horizontal vectors, the Gram determinants of `u, w` and of
`f_* u, f_* w` agree, so the sectional curvature of a horizontal plane increases by
`3 |A_u w|² / |u ∧ w|²` under `f`. As `v [X, Y] = 2 A_X Y` for horizontal fields, this is the
formula `K_N = K_M + ¾ |v [X, Y]|²` for horizontal orthonormal `X, Y`. These formulas compute the
curvature of quotient metrics, such as those of the projective spaces as quotients of round
spheres, and of connection metrics on fibre bundles.

The proof differentiates the horizontal lifts `X'`, `Y'` and `Z'` of fields `X`, `Y` and `Z` on
the base. For such basic fields the Levi-Civita derivative is `∇_X' Y' = (∇_X Y)^~ + A_X' Y'`, the
lift of the base derivative plus the vertical correction
(`TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`), and the bracket is
`[X', Y'] = [X, Y]^~ + 2 A_X' Y'` (`TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift`).
Expanding `R(X', Y') Z' = ∇_X' ∇_Y' Z' - ∇_Y' ∇_X' Z' - ∇_[X',Y'] Z'` and pairing with a
horizontal vector, the vertical corrections contribute the `A`-terms. The curvature convention
is `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`.

## Main results

* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_of_mem_orthogonal_ker`: O'Neill's
  horizontal curvature equation.
* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_self_of_mem_orthogonal_ker`: its form on
  a horizontal plane.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv`: the sectional curvature of the
  image of a horizontal plane.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Theorem 2 {4} and its Corollary 1.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, 9.28f.
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

/-- For a vertical field `V` and horizontal vectors `u` and `w`, `⟨∇_u V, w⟩ = ⟨V, A_w u⟩`, since
`A_u V` is the horizontal part of `∇_u V` and `A_u` is skew-adjoint. -/
private theorem inner_leviCivitaConnection_of_mem_ker {V : Π y : M, TangentSpace I y} {x : M}
    (hV : MDiffAt (T% V) x) (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker) {u w : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M V x u, w⟫_ℝ = ⟪V x, h.oneillA x w u⟫_ℝ := by
  rw [h.oneillA_antisymm hw hu, inner_neg_right, ← h.inner_oneillA,
    h.oneillA_apply_of_eventually_mem_ker hV (.of_forall hVv),
    Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hw,
    Submodule.starProjection_eq_self_iff.mpr hu]

/-- For a vertical field `V`, a basic horizontal field `Y'` and a horizontal vector `w`,
`⟨∇_V Y', w⟩ = ⟨V, A_w Y'⟩`. Since `[Y', V]` is vertical, this reduces to
`inner_leviCivitaConnection_of_mem_ker`. -/
private theorem inner_leviCivitaConnection_horizontalLift_of_mem_ker
    {V : Π y : M, TangentSpace I y} {Y : Π y : N, TangentSpace J y} {x : M}
    (hV : MDiffAt (T% V) x) (hVv : ∀ y, V y ∈ (mfderiv I J f y).ker)
    (hY : CMDiffAt 1 (T% Y) (f x)) {w : TangentSpace I x} (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ⟪leviCivitaConnection I M (fun y ↦ h.horizontalLift y (Y (f y))) x (V x), w⟫_ℝ =
      ⟪V x, h.oneillA x w (h.horizontalLift x (Y (f x)))⟫_ℝ := by
  have hYd := (h.contMDiffAt_horizontalLift hY (by norm_num)).mdifferentiableAt one_ne_zero
  have hT := ((torsion_eq_zero_iff _).mp (torsion_leviCivitaConnection_eq_zero I)) hYd hV
  have hbr := (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
    (by simp [minSmoothness_of_isRCLikeNormedField]) hYd hV (hY.mdifferentiableAt one_ne_zero)
    (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  rw [← h.inner_leviCivitaConnection_of_mem_ker hV hVv (h.horizontalLift_mem_orthogonal_ker x _)
      hw, ← sub_eq_zero, ← inner_sub_left, ← neg_sub, hT, inner_neg_left,
    Submodule.inner_right_of_mem_orthogonal hbr hw, neg_zero]

/-- For basic horizontal fields `Y'` and `Z'`, lifting smooth fields `Y` and `Z` on the base, and
lifts `v'` and `t'` of base vectors, `⟨∇_v' ∇_Y' Z', t'⟩ = ⟨∇_v ∇_Y Z, t⟩ + ⟨A_Y' Z', A_t' v'⟩`. -/
private theorem inner_leviCivitaConnection_leviCivitaConnection_horizontalLift
    {Y Z : Π y : N, TangentSpace J y} (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M)
    (v t : TangentSpace J (f x)) :
    ⟪leviCivitaConnection I M (fun y ↦ leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (Z (f y))) y (h.horizontalLift y (Y (f y)))) x
        (h.horizontalLift x v), h.horizontalLift x t⟫_ℝ =
      ⟪leviCivitaConnection J N (fun z ↦ leviCivitaConnection J N Z z (Y z)) (f x) v, t⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x))),
          h.oneillA x (h.horizontalLift x t) (h.horizontalLift x v)⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set covM := leviCivitaConnection I M
  set covN := leviCivitaConnection J N
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  have hY' : CMDiff ∞ (T% Y') := fun y ↦ h.contMDiffAt_horizontalLift (hY (f y)) (by simp)
  have hZ' : CMDiff ∞ (T% Z') := fun y ↦ h.contMDiffAt_horizontalLift (hZ (f y)) (by simp)
  -- `∇_Y' Z'` is the lift of `∇_Y Z` plus the vertical field `V = A_Y' Z'`.
  set W : Π z : N, TangentSpace J z := fun z ↦ covN Z z (Y z)
  set V : Π y : M, TangentSpace I y := fun y ↦ covM Z' y (Y' y) - h.horizontalLift y (W (f y))
  have hV (y : M) : V y = h.oneillA y (Y' y) (Z' y) :=
    sub_eq_of_eq_add' (h.leviCivitaConnection_horizontalLift ((hZ (f y)).of_le (by simp)) _)
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker :=
    hV y ▸ h.oneillA_apply_mem_ker _ (h.horizontalLift_mem_orthogonal_ker y _)
  have hW : CMDiffAt 1 (T% W) (f x) := (covN.contMDiff_apply hY hZ (f x)).of_le (by simp)
  have hWd : MDiffAt (T% (fun y ↦ h.horizontalLift y (W (f y)))) x :=
    (h.contMDiffAt_horizontalLift hW (by norm_num)).mdifferentiableAt one_ne_zero
  have hVd : MDiffAt (T% V) x := mdifferentiableAt_sub_section
    ((covM.contMDiff_apply hY' hZ' x).mdifferentiableAt (by simp)) hWd
  have hYZ : (fun y ↦ covM Z' y (Y' y)) = (fun y ↦ h.horizontalLift y (W (f y))) + V := by
    funext y
    simp only [V, Pi.add_apply, add_sub_cancel]
  rw [hYZ, covM.isCovariantDerivativeOnUniv.add hWd hVd, add_apply, inner_add_left,
    h.inner_leviCivitaConnection_horizontalLift hW,
    h.inner_leviCivitaConnection_of_mem_ker hVd hVv (h.horizontalLift_mem_orthogonal_ker x v)
      (h.horizontalLift_mem_orthogonal_ker x t), hV x]

/-- O'Neill's horizontal curvature equation on basic horizontal fields `X'`, `Y'` and `Z'`, lifting
smooth fields `X`, `Y` and `Z` on the base, paired with the lift `t'` of a base vector `t`. -/
private theorem inner_curvatureOperator_horizontalLift {X Y Z : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M)
    (t : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection I M).curvatureOperator (fun y ↦ h.horizontalLift y (X (f y)))
        (fun y ↦ h.horizontalLift y (Y (f y))) (fun y ↦ h.horizontalLift y (Z (f y))) x,
        h.horizontalLift x t⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureOperator X Y Z (f x), t⟫_ℝ +
        ⟪h.oneillA x (h.horizontalLift x (Y (f x))) (h.horizontalLift x (Z (f x))),
          h.oneillA x (h.horizontalLift x t) (h.horizontalLift x (X (f x)))⟫_ℝ -
        ⟪h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Z (f x))),
          h.oneillA x (h.horizontalLift x t) (h.horizontalLift x (Y (f x)))⟫_ℝ -
        2 * ⟪h.oneillA x (h.horizontalLift x (X (f x))) (h.horizontalLift x (Y (f x))),
          h.oneillA x (h.horizontalLift x t) (h.horizontalLift x (Z (f x)))⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set covM := leviCivitaConnection I M
  set covN := leviCivitaConnection J N
  set X' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (X (f y))
  set Y' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Y (f y))
  set Z' : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (Z (f y))
  set T := h.horizontalLift x t
  have hX₁ (z : N) : CMDiffAt 1 (T% X) z := (hX z).of_le (by simp)
  have hY₁ (z : N) : CMDiffAt 1 (T% Y) z := (hY z).of_le (by simp)
  have hZ₁ (z : N) : CMDiffAt 1 (T% Z) z := (hZ z).of_le (by simp)
  have hX' : CMDiff ∞ (T% X') := fun y ↦ h.contMDiffAt_horizontalLift (hX (f y)) (by simp)
  have hY' : CMDiff ∞ (T% Y') := fun y ↦ h.contMDiffAt_horizontalLift (hY (f y)) (by simp)
  -- The vertical part `V = A_X' Y'` of `∇_Y' X'`, which is half the vertical part of `[X', Y']`.
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
  -- The three terms of `R(X', Y') Z' = ∇_X' ∇_Y' Z' - ∇_Y' ∇_X' Z' - ∇_[X',Y'] Z'`.
  have h₁ : ⟪covM (fun y ↦ covM Z' y (Y' y)) x (X' x), T⟫_ℝ =
      ⟪covN (fun z ↦ covN Z z (Y z)) (f x) (X (f x)), t⟫_ℝ +
        ⟪h.oneillA x (Y' x) (Z' x), h.oneillA x T (X' x)⟫_ℝ :=
    h.inner_leviCivitaConnection_leviCivitaConnection_horizontalLift hY hZ x _ t
  have h₂ : ⟪covM (fun y ↦ covM Z' y (X' y)) x (Y' x), T⟫_ℝ =
      ⟪covN (fun z ↦ covN Z z (X z)) (f x) (Y (f x)), t⟫_ℝ +
        ⟪h.oneillA x (X' x) (Z' x), h.oneillA x T (Y' x)⟫_ℝ :=
    h.inner_leviCivitaConnection_leviCivitaConnection_horizontalLift hX hZ x _ t
  have h₃ : ⟪covM Z' x (mlieBracket I X' Y' x), T⟫_ℝ =
      ⟪covN Z (f x) (mlieBracket J X Y (f x)), t⟫_ℝ +
        2 * ⟪h.oneillA x (X' x) (Y' x), h.oneillA x T (Z' x)⟫_ℝ := by
    have hZV := h.inner_leviCivitaConnection_horizontalLift_of_mem_ker hVd hVv (hZ₁ (f x))
      (h.horizontalLift_mem_orthogonal_ker x t)
    rw [hV x] at hZV
    rw [h.mlieBracket_horizontalLift (hX₁ (f x)) (hY₁ (f x)), map_add, map_smul, inner_add_left,
      real_inner_smul_left, hZV, h.inner_leviCivitaConnection_horizontalLift (hZ₁ (f x))]
  rw [curvatureOperator_apply, curvatureOperator_apply, inner_sub_left, inner_sub_left, h₁, h₂,
    h₃, inner_sub_left, inner_sub_left]
  ring

/-- **O'Neill's horizontal curvature equation.** For horizontal vectors `u`, `v`, `w` and `z`,
`⟨R_M(u, v) w, z⟩ = ⟨R_N(f_* u, f_* v) f_* w, f_* z⟩ + 2 ⟨A_u v, A_w z⟩ - ⟨A_v w, A_u z⟩ +
⟨A_u w, A_v z⟩`. -/
theorem inner_curvatureTensor_of_mem_orthogonal_ker [T2Space M] [T2Space N] {x : M}
    {u v w z : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hv : v ∈ (mfderiv I J f x).kerᗮ) (hw : w ∈ (mfderiv I J f x).kerᗮ)
    (hz : z ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v w, z⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x) (mfderiv I J f x u)
          (mfderiv I J f x v) (mfderiv I J f x w), mfderiv I J f x z⟫_ℝ +
        2 * ⟪h.oneillA x u v, h.oneillA x w z⟫_ℝ - ⟪h.oneillA x v w, h.oneillA x u z⟫_ℝ +
        ⟪h.oneillA x u w, h.oneillA x v z⟫_ℝ := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  -- Extend `f_* u`, `f_* v` and `f_* w` to smooth fields on the base, whose lifts take the values
  -- `u`, `v` and `w`.
  obtain ⟨X, hX, hXx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x u)
  obtain ⟨Y, hY, hYx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x v)
  obtain ⟨Z, hZ, hZx⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ (mfderiv I J f x w)
  have hu' : h.horizontalLift x (X (f x)) = u := by
    rw [hXx, h.horizontalLift_mfderiv_of_mem x hu]
  have hv' : h.horizontalLift x (Y (f x)) = v := by
    rw [hYx, h.horizontalLift_mfderiv_of_mem x hv]
  have hw' : h.horizontalLift x (Z (f x)) = w := by
    rw [hZx, h.horizontalLift_mfderiv_of_mem x hw]
  have hX' : CMDiff ∞ (T% fun y ↦ h.horizontalLift y (X (f y))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hX (f y)) (by simp)
  have hY' : CMDiff ∞ (T% fun y ↦ h.horizontalLift y (Y (f y))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hY (f y)) (by simp)
  have hZ' : CMDiff ∞ (T% fun y ↦ h.horizontalLift y (Z (f y))) :=
    fun y ↦ h.contMDiffAt_horizontalLift (hZ (f y)) (by simp)
  have hcurv := h.inner_curvatureOperator_horizontalLift hX hY hZ x (mfderiv I J f x z)
  rw [← curvatureTensor_apply _ x hX' hY' hZ', ← curvatureTensor_apply _ (f x) hX hY hZ, hu', hv',
    hw', h.horizontalLift_mfderiv_of_mem x hz, hXx, hYx, hZx] at hcurv
  rw [hcurv, h.oneillA_antisymm hz hu, h.oneillA_antisymm hz hv, h.oneillA_antisymm hz hw,
    inner_neg_right, inner_neg_right, inner_neg_right]
  ring

/-- **O'Neill's horizontal curvature formula.** For horizontal vectors `u` and `w`,
`⟨R_M(u, w) w, u⟩ = ⟨R_N(f_* u, f_* w) f_* w, f_* u⟩ - 3 |A_u w|²`. -/
theorem inner_curvatureTensor_self_of_mem_orthogonal_ker [T2Space M] [T2Space N] {x : M}
    {u w : TangentSpace I x} (hu : u ∈ (mfderiv I J f x).kerᗮ)
    (hw : w ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u w w, u⟫_ℝ =
      ⟪(leviCivitaConnection J N).curvatureTensor (f x) (mfderiv I J f x u)
          (mfderiv I J f x w) (mfderiv I J f x w), mfderiv I J f x u⟫_ℝ -
        3 * ‖h.oneillA x u w‖ ^ 2 := by
  rw [h.inner_curvatureTensor_of_mem_orthogonal_ker hu hw hw hu, h.oneillA_self hw,
    h.oneillA_antisymm hw hu, inner_zero_left, inner_neg_right, real_inner_self_eq_norm_sq]
  ring

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
    h.inner_curvatureTensor_self_of_mem_orthogonal_ker hu hw, ← add_div]
  ring

end TauCeti.IsRiemannianSubmersion
