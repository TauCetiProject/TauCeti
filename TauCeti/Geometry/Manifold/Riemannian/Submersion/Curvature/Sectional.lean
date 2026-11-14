/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature.Basic
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection

/-!
# O'Neill's sectional-curvature formulas for a Riemannian submersion

Specializing O'Neill's curvature equations `{2}` and `{4}` to two-planes yields O'Neill's
sectional-curvature formulas (Corollaries 1 and 2):

* For horizontal `u, v`,
  `K^N(df u, df v) = K(u, v) + 3 ‖A_u v‖² / det Gram(u, v)` (and on horizontal fields `X, Y`,
  `+ (3 / 4) ‖v [X, Y]‖² / det Gram(X, Y)`), so `K(u, v) ≤ K^N(df u, df v)` with equality iff
  `A_u v = 0`, and lower sectional-curvature bounds at `x` push forward to `f x`.
* For horizontal `u` and vertical `v` (requiring `[T2Space M]` only, not `[T2Space N]`),
  `K(u, v) = (⟪(∇_u T) v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`, which simplifies to
  `‖A_u v‖² / (‖u‖² ‖v‖²) ≥ 0` when `T` vanishes near `x` (totally geodesic fibres).

## Main results

* `TauCeti.IsRiemannianSubmersion.gram_horizontalLift`,
  `TauCeti.IsRiemannianSubmersion.gram_mfderiv_of_mem`,
  `TauCeti.IsRiemannianSubmersion.linearIndependent_mfderiv_iff_of_mem`, and
  `TauCeti.IsRiemannianSubmersion.orthonormal_mfderiv_iff_of_mem`: horizontal lifting and `mfderiv`
  preserve Gram matrices, linear independence, and orthonormality on horizontal pairs.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontal_vertical` and
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_nonneg_of_eventually_oneillT_eq_zero`:
  mixed horizontal-vertical sectional curvature and non-negativity for totally geodesic fibres.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_of_mem`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_eq_add_horizontalLift`, and
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_add_mlieBracket_of_orthonormal`:
  O'Neill's horizontal sectional-curvature formulas in `A`-tensor and Lie-bracket forms.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_le_sectionalCurvature_mfderiv`,
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv_eq_iff`, and
  `TauCeti.IsRiemannianSubmersion.le_sectionalCurvature_of_forall_le`: monotonicity, equality
  characterization, and pushforward of lower sectional-curvature bounds.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (9.29).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 7.47.
-/

public section

open Bundle CovariantDerivative Filter Manifold VectorField
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

-- These regularity indices are propositionally, but not definitionally, equal to `2`.
private instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

include h

/-! ### Gram matrices, linear independence, and orthonormality on horizontal pairs -/

section Gram

omit [IsManifold I ∞ M] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- Horizontal lifting preserves Gram matrices of tangent pairs. -/
@[simp]
theorem gram_horizontalLift (x : M) (u v : TangentSpace J (f x)) :
    Matrix.gram ℝ ![h.horizontalLift x u, h.horizontalLift x v] = Matrix.gram ℝ ![u, v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [(h.horizontalLift x).inner_map_map]

/-- On horizontal vectors, `mfderiv` preserves Gram matrices of tangent pairs. -/
theorem gram_mfderiv_of_mem {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    Matrix.gram ℝ ![mfderiv I J f x u, mfderiv I J f x v] = Matrix.gram ℝ ![u, v] := by
  rw [← h.gram_horizontalLift x, h.horizontalLift_mfderiv_of_mem x hu,
    h.horizontalLift_mfderiv_of_mem x hv]

/-- Two horizontal vectors at `x` are linearly independent if and only if their projections in
`TangentSpace J (f x)` are linearly independent. -/
theorem linearIndependent_mfderiv_iff_of_mem {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    LinearIndependent ℝ ![mfderiv I J f x u, mfderiv I J f x v] ↔
      LinearIndependent ℝ ![u, v] := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ),
    ← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ),
    h.gram_mfderiv_of_mem hu hv]

/-- Two horizontal vectors at `x` form an orthonormal pair if and only if their projections in
`TangentSpace J (f x)` form an orthonormal pair. -/
theorem orthonormal_mfderiv_iff_of_mem {x : M} {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    Orthonormal ℝ ![mfderiv I J f x u, mfderiv I J f x v] ↔ Orthonormal ℝ ![u, v] := by
  rw [← Matrix.gram_eq_one_iff_orthonormal (𝕜 := ℝ),
    ← Matrix.gram_eq_one_iff_orthonormal (𝕜 := ℝ),
    h.gram_mfderiv_of_mem hu hv]

end Gram

/-! ### Mixed horizontal-vertical sectional curvature -/

section MixedSectional

variable [T2Space M] {x : M}

/-- **Mixed sectional-curvature numerator.** For a horizontal vector `u` and a vertical vector `v`,
`⟪R(u, v) v, u⟫ = ⟪(∇_u T) v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²`. -/
theorem inner_curvatureTensor_horizontal_vertical_self
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ =
      ⟪((leviCivitaConnection I M).hom ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  have hDA0 : ⟪((leviCivitaConnection I M).hom
      ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
      h.oneillA x v u v, u⟫_ℝ = 0 := by
    rw [h.inner_hom_oneillA, real_inner_comm, h.inner_hom_oneillA_self v hu hv, neg_zero]
  rw [h.inner_curvatureTensor_horizontal_vertical_vertical_horizontal hu hv hv hu, hDA0, sub_zero,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- **O'Neill's mixed sectional-curvature formula (Corollary 1, vertical-horizontal planes).**
For a horizontal vector `u` and a vertical vector `v`,
`K(u, v) = (⟪(∇_u T) v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`.
Both sides vanish if either vector is zero, so no nonvanishing assumption is needed. -/
theorem sectionalCurvature_horizontal_vertical
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v =
      (⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2) / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have horth : ⟪u, v⟫_ℝ = 0 :=
    (real_inner_comm _ _).trans (Submodule.inner_right_of_mem_orthogonal hv hu)
  rw [sectionalCurvature_apply, h.inner_curvatureTensor_horizontal_vertical_self hu hv,
    Matrix.real_det_gram_fin_two, horth, sq (0 : ℝ), mul_zero, sub_zero,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- On unit horizontal `u` and unit vertical `v`, mixed sectional curvature is
`⟪(∇_u T) v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²`. -/
theorem sectionalCurvature_horizontal_vertical_of_norm_eq_one
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker)
    (hu₁ : ‖u‖ = 1) (hv₁ : ‖v‖ = 1) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v =
      ⟪((leviCivitaConnection I M).hom
          ((leviCivitaConnection I M).hom (leviCivitaConnection I M)))
          h.oneillT x u v v, u⟫_ℝ +
        ‖h.oneillA x u v‖ ^ 2 - ‖h.oneillT x v u‖ ^ 2 := by
  rw [h.sectionalCurvature_horizontal_vertical hu hv, hu₁, hv₁, one_pow, mul_one, div_one]

/-- **O'Neill's Corollary 2 (totally geodesic fibres, formula).** When `T` vanishes near `x`, a
mixed plane spanned by horizontal `u` and vertical `v` has sectional curvature
`‖A_u v‖² / (‖u‖² ‖v‖²)`. -/
theorem sectionalCurvature_horizontal_vertical_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
  have hTx : h.oneillT x = 0 := hT.self_of_nhds
  have hDTx : ((leviCivitaConnection I M).hom
      ((leviCivitaConnection I M).hom (leviCivitaConnection I M))) h.oneillT x = 0 := by
    rw [((leviCivitaConnection I M).hom
      ((leviCivitaConnection I M).hom (leviCivitaConnection I M))).isCovariantDerivativeOnUniv
        |>.congr_of_eventuallyEq (h.contMDiff_oneillT.mdifferentiableAt (by simp))
          (mdifferentiableAt_zeroSection ..) univ_mem hT]
    exact congrFun (CovariantDerivative.zero _) x
  rw [h.sectionalCurvature_horizontal_vertical hu hv, hDTx, hTx]
  simp

/-- **O'Neill's Corollary 2 (totally geodesic fibres, non-negativity).** When `T` vanishes near
`x`, every mixed horizontal-vertical plane at `x` has non-negative sectional curvature. -/
theorem sectionalCurvature_nonneg_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    0 ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v := by
  rw [h.sectionalCurvature_horizontal_vertical_of_eventually_oneillT_eq_zero hT hu hv]
  positivity

end MixedSectional

/-! ### Horizontal sectional curvature -/

section HorizontalSectional

variable [T2Space M] [T2Space N] {x : M}

/-- **Horizontal sectional-curvature numerator.** For horizontal tangent vectors `u, v`,
`⟪R^N(df u, df v)(df v), df u⟫ = ⟪R(u, v) v, u⟫ + 3 ‖A_u v‖²`. -/
theorem inner_curvatureTensor_mfderiv_self
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x v),
      mfderiv I J f x u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  have h₄ := h.inner_curvatureTensor_horizontal hu hv hv hu
  rw [h.oneillA_self hu, h.oneillA_self hv, inner_zero_left, h.oneillA_antisymm hv hu,
    inner_neg_right, real_inner_self_eq_norm_sq] at h₄
  linarith

/-- Sectional-curvature numerator on the base expressed via `horizontalLift`. -/
theorem inner_curvatureTensor_self_eq_horizontalLift (u v : TangentSpace J (f x)) :
    ⟪(leviCivitaConnection J N).curvatureTensor (f x) u v v, u⟫_ℝ =
      ⟪(leviCivitaConnection I M).curvatureTensor x
          (h.horizontalLift x u) (h.horizontalLift x v) (h.horizontalLift x v),
        h.horizontalLift x u⟫_ℝ +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  simpa only [h.mfderiv_horizontalLift] using
    h.inner_curvatureTensor_mfderiv_self (h.horizontalLift_mem_orthogonal_ker x u)
      (h.horizontalLift_mem_orthogonal_ker x v)

/-- **O'Neill's horizontal sectional-curvature formula (Corollary 1).** For horizontal tangent
vectors `u, v`, `K^N(df u, df v) = K(u, v) + 3 ‖A_u v‖² / det Gram(u, v)`. On dependent pairs both
sides use the same zero-denominator quotient, so no linear-independence hypothesis is needed. -/
theorem sectionalCurvature_mfderiv_of_mem
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 / (Matrix.gram ℝ ![u, v]).det := by
  rw [sectionalCurvature_apply, sectionalCurvature_apply, h.gram_mfderiv_of_mem hu hv,
    h.inner_curvatureTensor_mfderiv_self hu hv, add_div]

/-- **O'Neill's horizontal sectional-curvature formula on base vectors.** Writing
`L_x = h.horizontalLift x`, for arbitrary `u, v : TangentSpace J (f x)`,
`K^N(u, v) = K(L_x u, L_x v) + 3 ‖A_(L_x u) (L_x v)‖² / det Gram(u, v)`. -/
theorem sectionalCurvature_eq_add_horizontalLift (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 /
          (Matrix.gram ℝ ![u, v]).det := by
  simpa only [h.mfderiv_horizontalLift, h.gram_horizontalLift] using
    h.sectionalCurvature_mfderiv_of_mem (h.horizontalLift_mem_orthogonal_ker x u)
      (h.horizontalLift_mem_orthogonal_ker x v)

/-- On an orthonormal horizontal pair `u, v`, `K^N(df u, df v) = K(u, v) + 3 ‖A_u v‖²`. -/
theorem sectionalCurvature_mfderiv_of_orthonormal
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ)
    (horth : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x u v +
        3 * ‖h.oneillA x u v‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_of_mem hu hv, Matrix.gram_eq_one_iff_orthonormal.mpr horth,
    Matrix.det_one, div_one]

/-- On an orthonormal base pair `u, v`, writing `L_x = h.horizontalLift x`,
`K^N(u, v) = K(L_x u, L_x v) + 3 ‖A_(L_x u) (L_x v)‖²`. -/
theorem sectionalCurvature_eq_add_horizontalLift_of_orthonormal
    {u v : TangentSpace J (f x)} (horth : Orthonormal ℝ ![u, v]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x
          (h.horizontalLift x u) (h.horizontalLift x v) +
        3 * ‖h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v)‖ ^ 2 := by
  rw [h.sectionalCurvature_eq_add_horizontalLift, Matrix.gram_eq_one_iff_orthonormal.mpr horth,
    Matrix.det_one, div_one]

/-- **O'Neill's horizontal sectional-curvature formula in terms of the vertical Lie bracket.** For
fields `X, Y` differentiable at `x` and horizontal near `x`,
`K^N(df (X x), df (Y x)) = K(X x, Y x) + (3 / 4) ‖v [X, Y]_x‖² / det Gram(X x, Y x)`. -/
theorem sectionalCurvature_mfderiv_eq_add_mlieBracket
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 /
          (Matrix.gram ℝ ![X x, Y x]).det := by
  rw [h.sectionalCurvature_mfderiv_of_mem hXh.self_of_nhds hYh.self_of_nhds,
    h.starProjection_ker_mlieBracket hX hY hXh hYh, norm_smul, Real.norm_ofNat]
  ring

/-- **O'Neill's orthonormal Lie-bracket sectional-curvature formula.** For fields `X, Y`
differentiable at `x`, horizontal near `x`, and orthonormal at `x`,
`K^N(df (X x), df (Y x)) = K(X x, Y x) + (3 / 4) ‖v [X, Y]_x‖²`. -/
theorem sectionalCurvature_mfderiv_eq_add_mlieBracket_of_orthonormal
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXh : ∀ᶠ y in 𝓝 x, X y ∈ (mfderiv I J f y).kerᗮ)
    (hYh : ∀ᶠ y in 𝓝 x, Y y ∈ (mfderiv I J f y).kerᗮ)
    (horth : Orthonormal ℝ ![X x, Y x]) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x (X x)) (mfderiv I J f x (Y x)) =
      (leviCivitaConnection I M).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection I) x (X x) (Y x) +
        3 / 4 * ‖(mfderiv I J f x).ker.starProjection (mlieBracket I X Y x)‖ ^ 2 := by
  rw [h.sectionalCurvature_mfderiv_eq_add_mlieBracket hX hY hXh hYh,
    Matrix.gram_eq_one_iff_orthonormal.mpr horth, Matrix.det_one, div_one]

/-- **O'Neill's monotonicity inequality.** A Riemannian submersion does not decrease the sectional
curvature of horizontal planes: `K(u, v) ≤ K^N(df u, df v)`. -/
theorem sectionalCurvature_le_sectionalCurvature_mfderiv
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) := by
  rw [h.sectionalCurvature_mfderiv_of_mem hu hv]
  have hdet : 0 ≤ (Matrix.gram ℝ ![u, v]).det := (Matrix.posSemidef_gram ℝ ![u, v]).det_nonneg
  exact le_add_of_nonneg_right (div_nonneg (by positivity) hdet)

/-- Horizontal lifting does not increase sectional curvature:
`K(h.horizontalLift x u, h.horizontalLift x v) ≤ K^N(u, v)`. -/
theorem sectionalCurvature_horizontalLift_le (u v : TangentSpace J (f x)) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) ≤
      (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v := by
  simpa only [h.mfderiv_horizontalLift] using
    h.sectionalCurvature_le_sectionalCurvature_mfderiv
      (h.horizontalLift_mem_orthogonal_ker x u) (h.horizontalLift_mem_orthogonal_ker x v)

/-- For horizontal vectors `u, v`, equality `K^N(df u, df v) = K(u, v)` holds if and only if
`A_u v = 0`. On dependent horizontal pairs both sides hold automatically. -/
theorem sectionalCurvature_mfderiv_eq_iff
    {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).kerᗮ) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v ↔
      h.oneillA x u v = 0 := by
  constructor
  · intro heq
    by_cases huv : LinearIndependent ℝ ![u, v]
    · have hdet : (Matrix.gram ℝ ![u, v]).det ≠ 0 :=
        (Matrix.posDef_gram_of_linearIndependent huv).det_pos.ne'
      rw [h.sectionalCurvature_mfderiv_of_mem hu hv, add_eq_left, div_eq_zero_iff] at heq
      rcases heq with hnum | hfalse
      · have hsq : ‖h.oneillA x u v‖ ^ 2 = 0 := by linarith
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      · exact absurd hfalse hdet
    · by_cases hu₀ : u = 0
      · simp [hu₀]
      · obtain ⟨c, hc⟩ := not_forall.mp ((LinearIndependent.pair_iff' hu₀).not.mp huv)
        rw [← not_not.mp hc, map_smul, h.oneillA_self hu, smul_zero]
  · intro hA
    rw [h.sectionalCurvature_mfderiv_of_mem hu hv, hA, norm_zero, zero_pow two_ne_zero, mul_zero,
      zero_div, add_zero]

/-- On base vectors `u, v`, writing `L_x = h.horizontalLift x`, equality
`K^N(u, v) = K(L_x u, L_x v)` holds if and only if `A_(L_x u) (L_x v) = 0`. -/
theorem sectionalCurvature_eq_horizontalLift_iff (u v : TangentSpace J (f x)) :
    (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v =
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x
        (h.horizontalLift x u) (h.horizontalLift x v) ↔
      h.oneillA x (h.horizontalLift x u) (h.horizontalLift x v) = 0 := by
  simpa only [h.mfderiv_horizontalLift] using
    h.sectionalCurvature_mfderiv_eq_iff
      (h.horizontalLift_mem_orthogonal_ker x u) (h.horizontalLift_mem_orthogonal_ker x v)

/-- A lower bound `κ` on all sectional curvatures of `M` at `x` pushes forward to a lower bound
`κ` on all sectional curvatures of `N` at `f x`. -/
theorem le_sectionalCurvature_of_forall_le {κ : ℝ}
    (hκ : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      κ ≤ (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v)
    {u v : TangentSpace J (f x)} (huv : LinearIndependent ℝ ![u, v]) :
    κ ≤ (leviCivitaConnection J N).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection J) (f x) u v := by
  have hli : LinearIndependent ℝ ![h.horizontalLift x u, h.horizontalLift x v] := by
    rw [← h.linearIndependent_mfderiv_iff_of_mem
      (h.horizontalLift_mem_orthogonal_ker x u) (h.horizontalLift_mem_orthogonal_ker x v)]
    simpa only [h.mfderiv_horizontalLift] using huv
  exact (hκ _ _ hli).trans (h.sectionalCurvature_horizontalLift_le u v)

end HorizontalSectional

end TauCeti.IsRiemannianSubmersion
