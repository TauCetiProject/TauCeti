/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Curvature.Equations
import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
import TauCeti.Geometry.Manifold.Riemannian.Submersion.ONeill.Connection

/-!
# O'Neill's mixed sectional-curvature formula for a Riemannian submersion

Building on O'Neill's curvature equation `{2}` in `Submersion/Curvature/Equations.lean`, this file
proves the mixed horizontal-vertical case of O'Neill's sectional-curvature corollaries (Corollaries
1 and 2 of Theorem 2), requiring `[T2Space M]` only, not `[T2Space N]`. For horizontal `u` and
vertical `v`,
`K(u, v) = (⟪(∇_u T) v v, u⟫ + ‖A_u v‖² - ‖T_v u‖²) / (‖u‖² ‖v‖²)`, which simplifies to
`‖A_u v‖² / (‖u‖² ‖v‖²) ≥ 0` when `T` vanishes near `x` (totally geodesic fibres).

The horizontal case `K^N(df u, df v) = K(u, v) + 3 ‖A_u v‖² / det Gram(u, v)`, with its
orthonormal, horizontal-lift, and Lie-bracket forms, monotonicity, and equality characterization,
is `TauCeti.IsRiemannianSubmersion.sectionalCurvature_mfderiv` and its companions in
`Submersion/Curvature.lean`.

## Main results

* `TauCeti.IsRiemannianSubmersion.inner_curvatureTensor_horizontal_vertical_self`: the mixed
  sectional-curvature numerator.
* `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontal_vertical` and
  `TauCeti.IsRiemannianSubmersion.sectionalCurvature_horizontal_vertical_of_norm_eq_one`:
  O'Neill's mixed sectional-curvature formula.
* `inner_curvatureTensor_horizontal_vertical_self_of_eventually_oneillT_eq_zero`: the mixed
  numerator `‖A_u v‖²` for totally geodesic fibres.
* `IsRiemannianSubmersion.sectionalCurvature_horizontal_vertical_of_eventually_oneillT_eq_zero`
  and `TauCeti.IsRiemannianSubmersion.sectionalCurvature_nonneg_of_eventually_oneillT_eq_zero`:
  mixed sectional curvature and its non-negativity for totally geodesic fibres.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Corollaries 1–2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §D (9.29).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Theorem 7.47.
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

include h

-- These regularity indices are propositionally, but not definitionally, equal to `2`.
private instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

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

/-- **Mixed curvature numerator for totally geodesic fibres.** When `T` vanishes near `x`, for a
horizontal vector `u` and a vertical vector `v`, `⟪R(u, v) v, u⟫ = ‖A_u v‖²`. -/
theorem inner_curvatureTensor_horizontal_vertical_self_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    ⟪(leviCivitaConnection I M).curvatureTensor x u v v, u⟫_ℝ = ‖h.oneillA x u v‖ ^ 2 := by
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
  rw [h.inner_curvatureTensor_horizontal_vertical_self hu hv, hDTx, hTx]
  simp

/-- **O'Neill's Corollary 2 (totally geodesic fibres, formula).** When `T` vanishes near `x`, a
mixed plane spanned by horizontal `u` and vertical `v` has sectional curvature
`‖A_u v‖² / (‖u‖² ‖v‖²)`. -/
theorem sectionalCurvature_horizontal_vertical_of_eventually_oneillT_eq_zero
    (hT : ∀ᶠ y in 𝓝 x, h.oneillT y = 0) {u v : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) (hv : v ∈ (mfderiv I J f x).ker) :
    (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) x u v =
      ‖h.oneillA x u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  rw [h.sectionalCurvature_horizontal_vertical hu hv,
    ← h.inner_curvatureTensor_horizontal_vertical_self hu hv,
    h.inner_curvatureTensor_horizontal_vertical_self_of_eventually_oneillT_eq_zero hT hu hv]

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

end TauCeti.IsRiemannianSubmersion
