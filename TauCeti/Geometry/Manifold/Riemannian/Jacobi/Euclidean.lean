/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Jacobi fields in an inner-product space

A finite-dimensional real inner-product space `F` with its standard metric has vanishing
Christoffel map and vanishing curvature. Along every curve, the Levi-Civita covariant derivative
of a field is therefore its ordinary derivative, also within a parameter set. Along an affine
geodesic `t ↦ p + t • v` the Jacobi equation `D_t² J + R(J, γ') γ' = 0` becomes `J'' = 0`.

Every affine field `t ↦ u + t • w` is thus a Jacobi field along every affine geodesic, with
initial value `u` and initial covariant derivative `w`; this includes `u = w = 0` and the constant
geodesic `v = 0`. The Jacobi residual of any field is its ordinary second derivative within
the parameter set.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.isJacobiFieldOn_add_smul_model_space`:
  affine fields are Jacobi fields along geodesics on arbitrary parameter sets.
* `TauCeti.Manifold.isJacobiFieldOn_iff_model_space`: the flat-space Jacobi equation is
  the ordinary second-order equation.
* `TauCeti.Manifold.jacobiResidual_model_space`: the flat Jacobi residual is the second derivative.
* `TauCeti.Manifold.isJacobiFieldOn_iff_exists_eqOn_add_smul_model_space`: on a preconnected
  parameter set, Jacobi fields are exactly affine fields.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_add_smul_model_space`: a flat Jacobi field is determined
  by its value and derivative at one parameter.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §14 (the Jacobi equation).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- In flat space the Jacobi residual of any field along any curve is its ordinary second
derivative within the parameter set. No regularity or geodesic hypothesis is needed. -/
theorem jacobiResidual_model_space (γ V : ℝ → F) (s : Set ℝ) (t : ℝ) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
          (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) s) s t +
      (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (γ t) (V t)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t) = derivWithin (derivWithin V s) s t := by
  let W : ∀ r, TangentSpace 𝓘(ℝ, F) (γ r) := fun r ↦ V r
  -- Keep the field dependently typed so rewriting sees the tangent-bundle operators.
  change alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ W s) s t +
    (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (γ t) (W t)
      (curveVelocityWithin 𝓘(ℝ, F) γ s t)
      (curveVelocityWithin 𝓘(ℝ, F) γ s t) = _
  let DW : ∀ r, TangentSpace 𝓘(ℝ, F) (γ r) := fun r ↦ derivWithin V s r
  have hD : alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ W s =
      DW := funext (alongCurveWithin_leviCivitaConnection_model_space γ V s)
  have hDD : alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ DW s t =
      derivWithin (derivWithin V s) s t :=
    alongCurveWithin_leviCivitaConnection_model_space γ (derivWithin V s) s t
  rw [hD, hDD, curvatureTensor_leviCivitaConnection_model_space]
  simp only [LinearMap.zero_apply]
  exact add_zero _

/-- A field in flat space is Jacobi exactly when its base curve is geodesic, the field is
`C²`, and its ordinary second derivative within the parameter set vanishes. -/
theorem isJacobiFieldOn_iff_model_space (γ V : ℝ → F) (s : Set ℝ) :
    IsJacobiFieldOn 𝓘(ℝ, F) γ
        (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) s ↔
      IsGeodesicCurveOn 𝓘(ℝ, F) γ s ∧ ContDiffOn ℝ 2 V s ∧
        ∀ r ∈ s, derivWithin (derivWithin V s) s r = 0 := by
  let W : ∀ r, TangentSpace 𝓘(ℝ, F) (γ r) := fun r ↦ V r
  -- Naming the dependent field avoids inferring it as a nondependent map into F.
  change IsJacobiFieldOn 𝓘(ℝ, F) γ W s ↔ _
  rw [isJacobiFieldOn_iff]
  have hEq : (∀ r ∈ s, alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ W s) s r +
      (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (γ r) (W r)
        (curveVelocityWithin 𝓘(ℝ, F) γ s r)
        (curveVelocityWithin 𝓘(ℝ, F) γ s r) = 0) ↔
      ∀ r ∈ s, derivWithin (derivWithin V s) s r = 0 := by
    exact ⟨fun h r hr ↦ (jacobiResidual_model_space γ V s r).symm.trans (h r hr),
      fun h r hr ↦ (jacobiResidual_model_space γ V s r).trans (h r hr)⟩
  rw [hEq]
  refine and_congr_right fun hγ ↦ and_congr ?_ Iff.rfl
  simp only [ContMDiffOn, Bundle.contMDiffWithinAt_totalSpace_iff,
    trivializationAt_model_space_apply]
  exact ⟨fun h t ht ↦ (h t ht).2.contDiffWithinAt,
    fun h t ht ↦ ⟨hγ.contMDiffOn t ht, (h t ht).contMDiffWithinAt⟩⟩

/-- An affine field is Jacobi along every geodesic in flat space, on any parameter set.
This includes the zero field and constant geodesics. -/
theorem IsGeodesicCurveOn.isJacobiFieldOn_add_smul_model_space {γ : ℝ → F} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn 𝓘(ℝ, F) γ s) (u w : F) :
    IsJacobiFieldOn 𝓘(ℝ, F) γ
      (fun t ↦ (u + t • w : TangentSpace 𝓘(ℝ, F) (γ t))) s := by
  refine (isJacobiFieldOn_iff_model_space γ (fun t ↦ u + t • w) s).2
    ⟨hγ, by fun_prop, fun t ht ↦ ?_⟩
  have hD : EqOn (derivWithin (fun r : ℝ ↦ u + r • w) s) (fun _ ↦ w) s := by
    intro r hr
    simpa using ((((hasDerivAt_id r).smul_const w).const_add u).hasDerivWithinAt.derivWithin
      (hγ.uniqueDiffOn r hr))
  rw [derivWithin_congr hD (hD ht)]
  exact congrFun (derivWithin_const (𝕜 := ℝ) s w) t

/-- On a preconnected parameter set, flat-space Jacobi fields along a geodesic are exactly
the fields agreeing there with an affine function. -/
theorem isJacobiFieldOn_iff_exists_eqOn_add_smul_model_space {γ V : ℝ → F} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn 𝓘(ℝ, F) γ s) (hs : IsPreconnected s) :
    IsJacobiFieldOn 𝓘(ℝ, F) γ (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) s ↔
      ∃ u w : F, EqOn V (fun t ↦ u + t • w) s := by
  rw [isJacobiFieldOn_iff_model_space, and_iff_right hγ,
    ← isGeodesicCurveOn_iff_model_space hγ.uniqueDiffOn,
    isGeodesicCurveOn_iff_exists_eqOn_add_smul hγ.uniqueDiffOn hs]

/-- A flat Jacobi field on a preconnected parameter set is the affine field with its initial
value and ordinary derivative. The ordinary derivative equals the covariant derivative by
`alongCurveWithin_leviCivitaConnection_model_space`. -/
theorem IsJacobiFieldOn.eq_add_smul_model_space {γ V : ℝ → F} {s : Set ℝ} {a t : ℝ}
    (hV : IsJacobiFieldOn 𝓘(ℝ, F) γ (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) s)
    (hs : IsPreconnected s) (ha : a ∈ s) (ht : t ∈ s) :
    V t = V a + (t - a) • derivWithin V s a := by
  obtain ⟨u, w, h⟩ := (isJacobiFieldOn_iff_exists_eqOn_add_smul_model_space
    hV.isGeodesicCurveOn hs).mp hV
  have hd : HasDerivWithinAt V w s a := by
    refine HasDerivWithinAt.congr_of_mem ?_ h ha
    simpa using (((hasDerivAt_id a).smul_const w).const_add u).hasDerivWithinAt
  rw [hd.derivWithin (hV.uniqueDiffOn a ha), h ht, h ha, sub_smul]
  module

end TauCeti.Manifold
