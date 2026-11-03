/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Jacobi fields and their conserved Wronskian

A Jacobi field is a `C²` tangent field along a geodesic satisfying
`D²J + R(J, γ')γ' = 0`. Both derivatives are the native covariant derivatives within
the stated parameter set, so closed nondegenerate intervals are allowed. The section
retains its original tangent-space fibres and is not required to extend to an ambient field.

The Jacobi equation is linear, is unchanged by restriction to sets with unique derivatives,
and depends only on the field on its parameter set. For two solutions, the Wronskian
`⟨DJ, K⟩ - ⟨J, DK⟩` is constant on every preconnected parameter set. This conservation
law is the bilinear identity underlying the symmetry of the geodesic index form.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields and the Wronskian identity).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {s u : Set ℝ} {t : ℝ}

variable (I γ V s) in
/-- A `C²` Jacobi field along a geodesic on `s`, for the Levi-Civita connection.
The geodesic supplies the unique-derivative hypothesis on the parameter set. -/
structure IsJacobiFieldOn : Prop where
  /-- The base curve is a geodesic on the parameter set. -/
  isGeodesicCurveOn : IsGeodesicCurveOn I γ s
  /-- The section is `C²` as a map to the tangent bundle. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
    (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s
  /-- The Jacobi equation, with the convention `R(X,Y)Z = [∇_X,∇_Y]Z - ∇_[X,Y]Z`. -/
  equation : ∀ r ∈ s,
    alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V s) s r +
      (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
        (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r) = 0

/-- The characteristic conditions for a Jacobi field, including its lift regularity. -/
theorem isJacobiFieldOn_iff : IsJacobiFieldOn I γ V s ↔
    IsGeodesicCurveOn I γ s ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
        (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s ∧
      ∀ r ∈ s, alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ V s) s r +
        (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
          (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r) = 0 :=
  ⟨fun h ↦ ⟨h.isGeodesicCurveOn, h.contMDiffOn, h.equation⟩,
    fun ⟨hγ, hV, hEq⟩ ↦ ⟨hγ, hV, hEq⟩⟩

/-- The parameter set of a Jacobi field has unique derivatives. -/
theorem IsJacobiFieldOn.uniqueDiffOn (h : IsJacobiFieldOn I γ V s) : UniqueDiffOn ℝ s :=
  h.isGeodesicCurveOn.uniqueDiffOn

/-- The coordinate reading of a Jacobi field is differentiable within its parameter set. -/
theorem IsJacobiFieldOn.differentiableWithinAt_sectionCoord
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) :
    DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t :=
  TauCeti.Manifold.differentiableWithinAt_sectionCoord γ V
    ((h.contMDiffOn t ht).mdifferentiableWithinAt (by norm_num))
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))

/-- The first covariant derivative of a Jacobi field has a `C¹` tangent-bundle lift. -/
theorem IsJacobiFieldOn.contMDiffOn_alongCurveWithin (h : IsJacobiFieldOn I γ V s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ V s r)) s :=
  contMDiffOn_alongCurveWithin_leviCivitaConnection h.uniqueDiffOn h.contMDiffOn

/-- The covariant derivative has differentiable coordinate readings within the parameter set. -/
theorem IsJacobiFieldOn.differentiableWithinAt_sectionCoord_alongCurveWithin
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (alongCurveWithin (leviCivitaConnection I M) γ V s) (γ t)) s t :=
  differentiableWithinAt_sectionCoord_alongCurveWithin_leviCivitaConnection
    h.uniqueDiffOn h.contMDiffOn ht

/-- The Jacobi equation solved for the second covariant derivative. -/
theorem IsJacobiFieldOn.alongCurveWithin_alongCurveWithin_eq
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) :
    alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ V s) s t =
      -(leviCivitaConnection I M).curvatureTensor (γ t) (V t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) :=
  eq_neg_of_add_eq_zero_left (h.equation t ht)

/-- The zero field is a Jacobi field along every geodesic. -/
theorem isJacobiFieldOn_zero (hγ : IsGeodesicCurveOn I γ s) :
    IsJacobiFieldOn I γ (fun r ↦ (0 : TangentSpace I (γ r))) s := by
  refine ⟨hγ, ?_, ?_⟩
  · exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp_contMDiffOn hγ.contMDiffOn
  · intro r hr
    have hzero : alongCurveWithin (leviCivitaConnection I M) γ
        (fun r ↦ (0 : TangentSpace I (γ r))) s = fun r ↦ 0 := by
      funext r
      exact alongCurveWithin_zero _ γ s r
    simp [hzero]

/-- Multiplication by a constant real scalar preserves Jacobi fields. -/
theorem IsJacobiFieldOn.const_smul (h : IsJacobiFieldOn I γ V s) (c : ℝ) :
    IsJacobiFieldOn I γ (fun r ↦ c • V r) s := by
  refine ⟨h.isGeodesicCurveOn, ?_, ?_⟩
  · exact contMDiffOn_const.smul_totalSpace h.contMDiffOn
  · intro r hr
    have hsmul : alongCurveWithin (leviCivitaConnection I M) γ
        (fun r ↦ c • V r) s =
        fun r ↦ c • alongCurveWithin (leviCivitaConnection I M) γ V s r := by
      funext r
      exact alongCurveWithin_const_smul _ γ V c s r
    rw [hsmul]
    simpa only [alongCurveWithin_const_smul, map_smul, LinearMap.smul_apply, ← smul_add,
      smul_zero] using congrArg (c • ·) (h.equation r hr)

/-- A field agreeing with a Jacobi field on its parameter set is again a Jacobi field there. -/
theorem IsJacobiFieldOn.congr (h : IsJacobiFieldOn I γ V s)
    (hWV : ∀ r ∈ s, W r = V r) : IsJacobiFieldOn I γ W s := by
  have hfirst : ∀ r ∈ s, alongCurveWithin (leviCivitaConnection I M) γ W s r =
      alongCurveWithin (leviCivitaConnection I M) γ V s r := by
    intro r hr
    exact alongCurveWithin_congr _ γ W
      (Filter.mem_of_superset self_mem_nhdsWithin (hWV ·)) (hWV r hr)
  refine ⟨h.isGeodesicCurveOn, h.contMDiffOn.congr (fun r hr ↦ ?_), fun r hr ↦ ?_⟩
  · rw [hWV r hr]
  · rw [alongCurveWithin_congr _ γ _
      (Filter.mem_of_superset self_mem_nhdsWithin (hfirst ·)) (hfirst r hr), hWV r hr]
    exact h.equation r hr

/-- Sums of Jacobi fields along the same geodesic are Jacobi fields. -/
theorem IsJacobiFieldOn.add (hV : IsJacobiFieldOn I γ V s)
    (hW : IsJacobiFieldOn I γ W s) : IsJacobiFieldOn I γ (fun r ↦ V r + W r) s := by
  have hfirst : ∀ r ∈ s,
      alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ V r + W r) s r =
        alongCurveWithin (leviCivitaConnection I M) γ V s r +
          alongCurveWithin (leviCivitaConnection I M) γ W s r := by
    intro r hr
    exact alongCurveWithin_add _ γ V W s
      (hV.differentiableWithinAt_sectionCoord hr) (hW.differentiableWithinAt_sectionCoord hr)
  refine ⟨hV.isGeodesicCurveOn, ?_, fun r hr ↦ ?_⟩
  · exact hV.contMDiffOn.add_sectionAlong hW.contMDiffOn
  · rw [alongCurveWithin_congr _ γ _
      (Filter.mem_of_superset self_mem_nhdsWithin (hfirst ·)) (hfirst r hr),
      alongCurveWithin_add _ γ _ _ s
        (hV.differentiableWithinAt_sectionCoord_alongCurveWithin hr)
        (hW.differentiableWithinAt_sectionCoord_alongCurveWithin hr)]
    simp only [map_add, LinearMap.add_apply]
    have hv := hV.equation r hr
    have hw := hW.equation r hr
    simpa only [add_add_add_comm, add_zero] using congrArg₂ (· + ·) hv hw

/-- The covariant derivative of a Jacobi field within a smaller parameter set agrees with the one
within the original set, at points where the smaller set has unique derivatives. -/
theorem IsJacobiFieldOn.alongCurveWithin_subset (h : IsJacobiFieldOn I γ V s)
    (hu : UniqueDiffWithinAt ℝ u t) (hus : u ⊆ s) (ht : t ∈ u) :
    alongCurveWithin (leviCivitaConnection I M) γ V u t =
      alongCurveWithin (leviCivitaConnection I M) γ V s t :=
  CovariantDerivative.alongCurveWithin_subset _ γ V hus hu
    (h.differentiableWithinAt_sectionCoord (hus ht))
    (by simpa [writtenInExtChartAt] using
      (h.isGeodesicCurveOn.mdifferentiableOn t (hus ht)).differentiableWithinAt_writtenInExtChartAt)

/-- Restricting the parameter set preserves a Jacobi field, provided derivatives on the
smaller set are unique. Values outside the parameter set play no role. -/
theorem IsJacobiFieldOn.mono (h : IsJacobiFieldOn I γ V s)
    (hu : UniqueDiffOn ℝ u) (hus : u ⊆ s) : IsJacobiFieldOn I γ V u := by
  have hcurve (r : ℝ) (hr : r ∈ s) :
      DifferentiableWithinAt ℝ (extChartAt I (γ r) ∘ γ) s r :=
    by simpa [writtenInExtChartAt] using
      (h.isGeodesicCurveOn.mdifferentiableOn r hr).differentiableWithinAt_writtenInExtChartAt
  have hfirst : ∀ r ∈ u, alongCurveWithin (leviCivitaConnection I M) γ V u r =
      alongCurveWithin (leviCivitaConnection I M) γ V s r :=
    fun r hr ↦ h.alongCurveWithin_subset (hu r hr) hus hr
  refine ⟨h.isGeodesicCurveOn.mono hu hus, h.contMDiffOn.mono hus, fun r hr ↦ ?_⟩
  rw [alongCurveWithin_congr _ γ _
    (Filter.mem_of_superset self_mem_nhdsWithin (hfirst ·)) (hfirst r hr),
    CovariantDerivative.alongCurveWithin_subset _ γ _ hus (hu r hr)
      (h.differentiableWithinAt_sectionCoord_alongCurveWithin (hus hr)) (hcurve r (hus hr))]
  have hvel : curveVelocityWithin I γ u r = curveVelocityWithin I γ s r :=
    curveVelocityWithin_subset hus (hu r hr)
      (h.isGeodesicCurveOn.mdifferentiableOn r (hus hr))
  rw [hvel]
  exact h.equation r (hus hr)

/-- The Wronskian of two Jacobi fields has zero derivative, including within a closed interval. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_wronskian (hV : IsJacobiFieldOn I γ V s)
    (hW : IsJacobiFieldOn I γ W s) (ht : t ∈ s) :
    HasDerivWithinAt
      (fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s r) (W r) -
        inner ℝ (V r) (alongCurveWithin (leviCivitaConnection I M) γ W s r)) 0 s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ := hV.isGeodesicCurveOn.mdifferentiableOn t ht
  have h₁ := hm.hasDerivWithinAt_inner_alongCurveWithin (hV.uniqueDiffOn t ht) hγ
    (hV.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
    (hW.differentiableWithinAt_sectionCoord ht)
  have h₂ := hm.hasDerivWithinAt_inner_alongCurveWithin (hV.uniqueDiffOn t ht) hγ
    (hV.differentiableWithinAt_sectionCoord ht)
    (hW.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
  have hcurv : inner ℝ
      ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) (W t) =
      inner ℝ (V t) ((leviCivitaConnection I M).curvatureTensor (γ t) (W t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) := by
    rw [hm.inner_curvatureTensor_swap_pairs (torsion_leviCivitaConnection_eq_zero I),
      hm.inner_curvatureTensor_eq_neg, curvatureTensor_antisymm]
    simp
  apply (h₁.sub h₂).congr_deriv
  rw [hV.alongCurveWithin_alongCurveWithin_eq ht,
    hW.alongCurveWithin_alongCurveWithin_eq ht]
  simp only [inner_neg_left, inner_neg_right, hcurv]
  ring

/-- **Conservation of the Jacobi Wronskian.** For two Jacobi fields on a preconnected
parameter set, `⟨DV, W⟩ - ⟨V, DW⟩` has the same value at any two parameters. -/
theorem IsJacobiFieldOn.wronskian_eq (hV : IsJacobiFieldOn I γ V s)
    (hW : IsJacobiFieldOn I γ W s) (hs : IsPreconnected s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s a) (W a) -
        inner ℝ (V a) (alongCurveWithin (leviCivitaConnection I M) γ W s a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V s b) (W b) -
        inner ℝ (V b) (alongCurveWithin (leviCivitaConnection I M) γ W s b) := by
  apply (Real.convex_iff_isPreconnected.2 hs).is_const_of_fderivWithin_eq_zero
    (fun r hr ↦ (hV.hasDerivWithinAt_wronskian hW hr).differentiableWithinAt) ?_ ha hb
  intro r hr
  rw [← toSpanSingleton_derivWithin,
    (hV.hasDerivWithinAt_wronskian hW hr).derivWithin (hV.uniqueDiffOn r hr)]
  simp

end TauCeti.Manifold
