/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve
public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Maximal

/-!
# Metric conservation in variations through Killing trajectories

The transverse velocity `V(t) = ∂q F(0,t)` of a family of integral curves of `X` satisfies
`D_t V = ∇_V X`. Consequently its squared norm has derivative `2⟨∇_V X,V⟩`.
For a Killing field this derivative vanishes, so transverse lengths are conserved on each
connected time interval. Applied to `F(q,t) = flowOf X t (c q)`, this is the metric-preservation
calculation for the local flow, with its actual domain of existence retained.

The variational equation is supplied by
`CovariantDerivative.alongCurve_curveVelocity_eq_covariantDerivative`; the Killing equation
is `TauCeti.Manifold.IsKillingField.inner_covariantDerivative_eq_neg`.

## References

* P. Petersen, *Riemannian Geometry*, third edition, Chapter 8
  (Killing fields and local isometries).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  {X : Π x : M, TangentSpace I x} {F : ℝ → ℝ → M} {t : ℝ}

/-- In a family of integral curves of a Killing field, the squared length of the transverse
variation field has zero time derivative. -/
theorem IsKillingField.hasDerivAt_inner_variationField_self (h : IsKillingField I X)
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hcurve : ∀ᶠ q in 𝓝 0, curveVelocity I (F q) t = X (F q t)) :
    HasDerivAt (fun r ↦ inner ℝ (variationField I F r) (variationField I F r)) 0 t := by
  have hskew := h.inner_covariantDerivative_eq_neg (isMetricCompatible_leviCivitaConnection I)
    (torsion_leviCivitaConnection_eq_zero I) (F 0 t) (variationField I F t)
      (variationField I F t)
  have hz : 2 * inner ℝ (leviCivitaConnection I M X (F 0 t) (variationField I F t))
      (variationField I F t) = 0 := by
    linarith [real_inner_comm (variationField I F t)
      (leviCivitaConnection I M X (F 0 t) (variationField I F t))]
  have hcompat := isMetricCompatible_leviCivitaConnection (M := M) I
  have hp := hcompat.hasDerivAt_inner_curveVelocity_self_of_integralCurve
      ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)) hF
        (h.contMDiff.mdifferentiableAt (by simp)) hcurve
  simpa only [← variationField_apply, hz] using hp

/-- Transverse lengths in a family of integral curves of a Killing field are constant on
every open connected time domain on which the family is `C²` near its central trajectory. -/
theorem IsKillingField.norm_variationField_eq (h : IsKillingField I X)
    {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hF : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t))
    (hcurve : ∀ t ∈ s, ∀ᶠ q in 𝓝 0, curveVelocity I (F q) t = X (F q t))
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖variationField I F a‖ = ‖variationField I F b‖ := by
  have hd (t : ℝ) (ht : t ∈ s) := h.hasDerivAt_inner_variationField_self (hF t ht) (hcurve t ht)
  have heq := hs.is_const_of_deriv_eq_zero hconn
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) ha hb
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    congrArg Real.sqrt heq

section Flow

variable [I.Boundaryless]

private theorem IsKillingField.norm_variationField_flowOf (h : IsKillingField I X)
    {c : ℝ → M} (hc : ContMDiffAt 𝓘(ℝ) I 2 c 0) (ht : (t, c 0) ∈ flowDomain X) :
    ‖variationField I (fun q r ↦ flowOf X r (c q)) t‖ = ‖curveVelocity I c 0‖ := by
  have hX : CMDiff 1 (T% X) := h.contMDiff.of_le (by simp)
  have hX₂ : CMDiff 2 (T% X) := h.contMDiff.of_le (by simp)
  let F (q r : ℝ) := flowOf X r (c q)
  have hF (r : ℝ) (hr : r ∈ maximalIntegralCurveInterval X (c 0)) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, r) :=
    contMDiffAt_flowOf_comp (by norm_num) hX₂
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt
      (hc.comp (0, r) (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffAt)
      (mem_flowDomain.mpr hr)
  have hcurve (r : ℝ) (hr : r ∈ maximalIntegralCurveInterval X (c 0)) :
      ∀ᶠ q in 𝓝 0, curveVelocity I (F q) r = X (F q r) := by
    have hdom : ∀ᶠ q in 𝓝 0, (r, c q) ∈ flowDomain X :=
      (continuousAt_const.prodMk hc.continuousAt).preimage_mem_nhds
        ((isOpen_flowDomain hX).mem_nhds (mem_flowDomain.mpr hr))
    filter_upwards [hdom] with q hq
    have htime : {s | (s, c q) ∈ flowDomain X} ∈ 𝓝 r := by
      simpa only [mem_flowDomain, ofPred_mem_eq] using
        isOpen_maximalIntegralCurveInterval.mem_nhds (mem_flowDomain.mp hq)
    have hderiv := ((isMIntegralCurveOn_flowOf hX (c q)).isMIntegralCurveAt htime).hasMFDerivAt
    simpa only [curveVelocityWithin_univ, F] using
      curveVelocityWithin_eq_of_hasMFDerivWithinAt hderiv.hasMFDerivWithinAt
        uniqueDiffWithinAt_univ
  have heq := h.norm_variationField_eq isOpen_maximalIntegralCurveInterval
    isPreconnected_maximalIntegralCurveInterval hF hcurve (mem_flowDomain.mp ht)
      (mem_flowDomain.mp (mem_flowDomain_zero hX (c 0)))
  have hzero : (fun q ↦ F q 0) = c := funext fun q ↦ flowOf_zero hX (c q)
  simp only [variationField_apply] at heq
  rw [hzero] at heq
  -- Rewriting the velocity curve does not rewrite the base point of its dependent fibre norm.
  rw [show F 0 0 = c 0 from flowOf_zero hX (c 0)] at heq
  simpa only [variationField_apply, F] using heq

/-- The differential of the maximal flow of a Killing field preserves tangent norms wherever
that flow exists. No completeness of the vector field or the Riemannian metric is assumed. -/
@[simp] theorem IsKillingField.norm_mfderiv_flowOf (h : IsKillingField I X) {p : M}
    (ht : (t, p) ∈ flowDomain X) (v : TangentSpace I p) :
    ‖mfderiv I I (flowOf X t) p v‖ = ‖v‖ := by
  -- A local geodesic realizes the arbitrary tangent vector `v` at `p`.
  obtain ⟨s, hs, c, hgeo⟩ := exists_geodesicCurveOnFrom p v
  have hc0 := hgeo.base_eq
  have hc := hgeo.isGeodesicCurveOn.contMDiffOn.contMDiffAt hs
  have hvel : curveVelocity I c 0 = v := by
    simpa only [curveVelocityWithin_univ] using
      curveVelocityWithin_eq_of_hasMFDerivWithinAt
        (hgeo.hasMFDerivAt_zero hs).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  have hflow : MDifferentiableAt I I (flowOf X t) p := by
    have hf := contMDiffAt_flowOf_comp (by simp) h.contMDiff contMDiffAt_const contMDiffAt_id ht
    exact hf.mdifferentiableAt (by simp)
  have heq := h.norm_variationField_flowOf hc (by simpa only [hc0] using ht)
  have hmap : curveVelocity I ((flowOf X t) ∘ c) 0 =
      mfderiv I I (flowOf X t) (c 0) (curveVelocity I c 0) := by
    simpa only [curveVelocityWithin_univ] using
      curveVelocityWithin_map (by simpa only [hc0] using hflow) uniqueDiffWithinAt_univ
        (hc.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt
  rw [variationField_apply, ← Function.comp_def, hmap, hc0, hvel] at heq
  exact heq

/-- The maximal flow of a Killing field preserves the Riemannian inner product on tangent
vectors at every point of its domain of existence. -/
@[simp] theorem IsKillingField.inner_mfderiv_flowOf (h : IsKillingField I X) {p : M}
    (ht : (t, p) ∈ flowDomain X) (v w : TangentSpace I p) :
    inner ℝ (mfderiv I I (flowOf X t) p v) (mfderiv I I (flowOf X t) p w) = inner ℝ v w := by
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, h.norm_mfderiv_flowOf ht]

end Flow

end TauCeti.Manifold
