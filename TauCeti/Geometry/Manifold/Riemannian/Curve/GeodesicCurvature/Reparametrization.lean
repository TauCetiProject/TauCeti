/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Reparametrization of signed geodesic curvature

The geodesic curvature relative to a chosen normal field is invariant under regular
reparametrization. The chain rule for the covariant acceleration gives
`D_t (γ ∘ φ)' = φ'' γ' + (φ')² D_t γ'`. The first term is orthogonal to the chosen normal,
and the factor `(φ')²` in the second term cancels the same factor in the squared speed.
This statement holds in any dimension and also at points where the velocity of `γ` vanishes.

On an oriented surface, reversing a curve reverses its oriented unit normal, so its signed
geodesic curvature changes sign. This is the pointwise cancellation law for a common boundary
arc traversed in opposite directions.

## Main results

* `TauCeti.Manifold.geodesicCurvature_comp`: invariance relative to a transported normal field.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp_const_sub`: reversing a curve
  changes the sign of its curvature relative to the oriented unit normal.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}

/-- A regular reparametrization preserves geodesic curvature relative to a transported normal
field. Only orthogonality at the point is needed; the normal need not have unit length, and
the velocity of the original curve may vanish. -/
theorem geodesicCurvature_comp (n : ∀ r, TangentSpace I (γ r))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : ContDiffAt ℝ 2 φ t)
    (hφ₀ : deriv φ t ≠ 0) (hn : ⟪curveVelocity I γ (φ t), n (φ t)⟫_ℝ = 0) :
    geodesicCurvature (γ ∘ φ) (fun r ↦ n (φ r)) t = geodesicCurvature γ n (φ t) := by
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγ
  have hcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := γ)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  have hγnear : ∀ᶠ r in 𝓝 (φ t), MDifferentiableAt 𝓘(ℝ) I γ r := by
    filter_upwards [interior_mem_nhds.mpr hu] with r hr
    exact ((hγu.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hr))
      |>.mdifferentiableAt two_ne_zero
  have hvel : (fun r ↦ curveVelocity I (γ ∘ φ) r) =ᶠ[𝓝 t]
      fun r ↦ deriv φ r • curveVelocity I γ (φ r) := by
    filter_upwards [hφ.continuousAt.eventually hγnear, hφ.eventually (by simp)] with r hγr hφr
    exact curveVelocity_comp (hφr.differentiableAt two_ne_zero).hasDerivAt hγr
  have hφd := hφ.differentiableAt two_ne_zero
  have hφ' : DifferentiableAt ℝ (deriv φ) t :=
    (hφ.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcoordcomp : DifferentiableAt ℝ (sectionCoord (F := E) (γ ∘ φ)
      (fun r ↦ curveVelocity I γ (φ r)) (γ (φ t))) t := by
    rw [sectionCoord_comp]
    exact hcoord.comp t hφd
  have hacc : acceleration (leviCivitaConnection I M) (γ ∘ φ) t =
      deriv (deriv φ) t • curveVelocity I γ (φ t) +
        deriv φ t ^ 2 • acceleration (leviCivitaConnection I M) γ (φ t) := by
    rw [acceleration_def, alongCurve_congr _ (γ ∘ φ) _ hvel,
      alongCurve_smul _ (γ ∘ φ) _ (deriv φ) hφ' hcoordcomp,
      alongCurve_comp _ γ _ φ hφd
        (hasDerivAt_extChartAt_comp_curve
          (hasMFDerivAt_curveVelocity (hγ.mdifferentiableAt two_ne_zero))).differentiableAt hcoord,
      ← acceleration_def, smul_smul, ← sq]
  have hv : curveVelocity I (γ ∘ φ) t = deriv φ t • curveVelocity I γ (φ t) := hvel.self_of_nhds
  rw [geodesicCurvature_def, geodesicCurvature_def, hacc, hv,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, hn, mul_zero, zero_add,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hφ₀)

/-- Reversing a curve reverses its signed geodesic curvature relative to the oriented unit
normal. In particular, the curvatures on a common boundary arc cancel when its two
parametrizations traverse it in opposite directions. -/
theorem geodesicCurvature_orientedUnitNormal_comp_const_sub
    (o : Orientation I M (Fin 2)) (d t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (d - t)) :
    geodesicCurvature (fun r ↦ γ (d - r))
      (orientedUnitNormal o (fun r ↦ γ (d - r))) t =
        -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
  have hcomp := geodesicCurvature_comp (φ := fun r ↦ d - r) (t := t)
    (orientedUnitNormal o γ) hγ (by fun_prop) (by simp)
    (by rw [real_inner_comm]; exact inner_orientedUnitNormal_curveVelocity o γ (d - t))
  rw [geodesicCurvature_def, orientedUnitNormal_comp_const_sub, inner_neg_right, neg_div]
  rw [geodesicCurvature_def] at hcomp
  exact congrArg Neg.neg hcomp

end TauCeti.Manifold
