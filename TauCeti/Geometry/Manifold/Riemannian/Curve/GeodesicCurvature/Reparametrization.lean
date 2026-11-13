/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Reparametrization of signed geodesic curvature

The geodesic curvature relative to a chosen normal field is invariant under regular
reparametrization. The chain rule for the covariant acceleration gives
`D_t (γ ∘ φ)' = φ'' γ' + (φ')² D_t γ'`. The first term is orthogonal to the chosen normal,
and the factor `(φ')²` in the second term cancels the same factor in the squared speed.
This statement holds in any dimension and also at points where the velocity of `γ` vanishes.

On an oriented surface, an orientation-preserving regular reparametrization preserves signed
geodesic curvature relative to the oriented unit normal, while an orientation-reversing one
negates it. In particular, the affine parameter reflection `r ↦ γ (d - r)` negates this curvature
at each `C²` point of the original curve.

## Main results

* `TauCeti.Manifold.geodesicCurvature_comp`: invariance relative to a transported normal field.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp`: the sign law for a general
  reparametrization, including at zero derivative.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp_const_sub`: reflecting a curve
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
    (hφ₀ : deriv φ t ≠ 0) (hn : ⟪n (φ t), curveVelocity I γ (φ t)⟫_ℝ = 0) :
    geodesicCurvature (γ ∘ φ) (fun r ↦ n (φ r)) t = geodesicCurvature γ n (φ t) := by
  have hacc := acceleration_comp (leviCivitaConnection I M) γ
    (hφ.eventually_differentiableAt one_le_two) hφ.differentiableAt_deriv_two
    (hγ.eventually_mdifferentiableAt two_ne_zero) hγ.differentiableAt_sectionCoord_curveVelocity
  have hv := curveVelocity_comp (hφ.differentiableAt two_ne_zero).hasDerivAt
    (hγ.mdifferentiableAt two_ne_zero)
  have hn' : ⟪curveVelocity I γ (φ t), n (φ t)⟫_ℝ = 0 := (real_inner_comm _ _).trans hn
  rw [geodesicCurvature_def, geodesicCurvature_def, hacc, hv,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, hn', mul_zero, zero_add,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hφ₀)

/-- Reparametrization multiplies signed geodesic curvature relative to the oriented unit
normal by the sign of the derivative. At zero derivative both sides vanish. -/
theorem geodesicCurvature_orientedUnitNormal_comp (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : ContDiffAt ℝ 2 φ t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      (SignType.sign (deriv φ t) : ℝ) *
        geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  by_cases hφ₀ : deriv φ t = 0
  · rw [geodesicCurvature_def,
      curveVelocity_comp (hφ.differentiableAt two_ne_zero).hasDerivAt
        (hγ.mdifferentiableAt two_ne_zero)]
    simp [hφ₀]
  · have hcomp := geodesicCurvature_comp (orientedUnitNormal o γ) hγ hφ hφ₀
      (inner_orientedUnitNormal_curveVelocity o γ (φ t))
    rw [geodesicCurvature_def,
      orientedUnitNormal_comp o (hγ.mdifferentiableAt two_ne_zero)
        (hφ.differentiableAt two_ne_zero), real_inner_smul_right, mul_div_assoc]
    rw [geodesicCurvature_def] at hcomp
    rw [hcomp]

/-- An orientation-preserving regular reparametrization preserves signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_pos (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : ContDiffAt ℝ 2 φ t)
    (hφ₀ : 0 < deriv φ t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ hφ]
  simp [hφ₀]

/-- An orientation-reversing regular reparametrization negates signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_neg (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : ContDiffAt ℝ 2 φ t)
    (hφ₀ : deriv φ t < 0) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      -geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ hφ]
  simp [hφ₀]

/-- Reflecting the parameter via `r ↦ γ (d - r)` negates signed geodesic curvature relative to
the oriented unit normal at each `C²` point `d - t` of the original curve. -/
theorem geodesicCurvature_orientedUnitNormal_comp_const_sub
    (o : Orientation I M (Fin 2)) (d t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (d - t)) :
    geodesicCurvature (fun r ↦ γ (d - r))
      (orientedUnitNormal o (fun r ↦ γ (d - r))) t =
        -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
  exact geodesicCurvature_orientedUnitNormal_comp_of_deriv_neg o hγ (by fun_prop) (by simp)

end TauCeti.Manifold
