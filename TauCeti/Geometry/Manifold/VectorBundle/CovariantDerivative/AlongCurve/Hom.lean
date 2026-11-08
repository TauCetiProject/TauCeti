/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Differentiating a bundle endomorphism applied to a field along a curve

For an ambient endomorphism `A` and a field `V` along a curve `γ`, the covariant product rule is
`D(A V) = (∇ A)(γ') V + A (D V)`. The connection on endomorphisms is the induced Hom
connection. The rules `alongCurveWithin_clm_apply` and `alongCurve_clm_apply` apply within a
parameter set and on the full parameter line, respectively. They apply to the target-dependent
almost complex structures appearing in linearized Cauchy–Riemann equations.

At a zero of a tangent field `V` along a curve, the covariant derivative of `A V` is
`A (D V)` for every differentiable family of endomorphisms `A`. The derivative of `A`
and both connection correction terms vanish there. This zero-field rule,
`alongCurveWithin_clm_apply_of_eq_zero`, does not require a connection on the endomorphism
bundle, nor any compatibility of `A` with the tangent connection. It applies within parameter
sets, including at endpoints, and allows the Jacobi equation to be differentiated at a zero
of the Jacobi field.

The proof uses Mathlib's hom-bundle coordinates and the native along-curve derivative.
See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4,
for covariant differentiation along curves and its product rule.
-/

public section

open Bundle FiberBundle Filter
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t))

/-- If `V` vanishes at a parameter, differentiating `A V` covariantly there gives `A (D V)`.
The endomorphism family and the field need only be differentiable within the parameter set. -/
theorem alongCurveWithin_clm_apply_of_eq_zero
    (A : ∀ r, TangentSpace I (γ r) →L[𝕜] TangentSpace I (γ r))
    {s : Set 𝕜} {t : 𝕜} (hs : UniqueDiffWithinAt 𝕜 s t)
    (hA : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, E →L[𝕜] E))
      (fun r ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x ↦ TangentSpace I x →L[𝕜] TangentSpace I x) (γ r) (A r)) s t)
    (hV : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t) (hzero : V t = 0) :
    alongCurveWithin cov γ (fun r ↦ A r (V r)) s t =
      A t (alongCurveWithin cov γ V s t) := by
  let e := trivializationAt E (TangentSpace I) (γ t)
  let a : 𝕜 → E →L[𝕜] E := fun r ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I)
    E (TangentSpace I) (γ t) (γ r) (γ t) (γ r) (A r)
  have hbase : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ t)
  have hAc := (mdifferentiableWithinAt_hom_bundle _).1 hA
  have ha : DifferentiableWithinAt 𝕜 a s t := hAc.2.differentiableWithinAt
  have hv := differentiableWithinAt_sectionCoord γ V hV hbase
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hAc.1.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hread (r : 𝕜) (hr : γ r ∈ e.baseSet) :
      sectionCoord (F := E) γ (fun q ↦ A q (V q)) (γ t) r =
        a r (sectionCoord (F := E) γ V (γ t) r) := by
    simp only [a, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      sectionCoord_apply]
    rw [(trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt hr]
  have hd := (ha.hasDerivWithinAt.clm_apply hv.hasDerivWithinAt).congr_of_eventuallyEq
    (hnear.mono fun r hr ↦ hread r hr) (hread t hbase)
  rw [alongCurveWithin_eq_derivWithin_sectionCoord_of_eq_zero cov γ _ (by simp [hzero]),
    alongCurveWithin_eq_derivWithin_sectionCoord_of_eq_zero cov γ V hzero, hd.derivWithin hs]
  simp only [sectionCoord_apply, hzero, map_zero, a,
    ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    continuousLinearMapAt_trivializationAt_self, symmL_trivializationAt_self]
  exact zero_add _

/-- **Covariant product rule within a parameter set.** An ambient endomorphism acts on an
arbitrary field along the curve; its derivative uses the induced endomorphism connection.
Neither the connection nor the endomorphism needs to preserve a metric. -/
theorem alongCurveWithin_clm_apply
    (A : ∀ x : M, TangentSpace I x →L[𝕜] TangentSpace I x) {s : Set 𝕜} {t : 𝕜}
    (hs : UniqueDiffWithinAt 𝕜 s t)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hA : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[𝕜] E)
      (E := fun x ↦ TangentSpace I x →L[𝕜] TangentSpace I x) x (A x)) (γ t))
    (hV : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t) :
    alongCurveWithin cov γ (fun r ↦ A (γ r) (V r)) s t =
      cov.hom cov A (γ t) (curveVelocityWithin I γ s t) (V t) +
        A (γ t) (alongCurveWithin cov γ V s t) := by
  -- Split off an ambient extension of the value of V. The remainder vanishes at t,
  -- where the product rule is already independent of any Hom connection.
  let W := extend E (V t)
  have hW : MDiffAt (T% W) (γ t) := mdifferentiableAt_extend ..
  have hWγ := hW.comp_mdifferentiableWithinAt t hγ
  have hAγ := hA.comp_mdifferentiableWithinAt t hγ
  have hU := hV.sub_sectionAlong hWγ
  have hAU := hAγ.clm_bundle_apply hU
  have hAW := (hA.clm_bundle_apply hW).comp_mdifferentiableWithinAt t hγ
  have hbase := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hsplit : (fun r ↦ W (γ r) + (V r - W (γ r))) = V := by funext r; abel
  have hAsplit : (fun r ↦ A (γ r) (W (γ r)) + A (γ r) (V r - W (γ r))) =
      (fun r ↦ A (γ r) (V r)) := by funext r; simp
  have hzero : V t - W (γ t) = 0 := by simp [W]
  have hprod := alongCurveWithin_clm_apply_of_eq_zero cov γ
    (fun r ↦ V r - W (γ r)) (fun r ↦ A (γ r)) hs hAγ hU hzero
  have hsum := alongCurveWithin_add cov γ (fun r ↦ A (γ r) (W (γ r)))
    (fun r ↦ A (γ r) (V r - W (γ r))) s
    (differentiableWithinAt_sectionCoord _ _ hAW hbase)
    (differentiableWithinAt_sectionCoord _ _ hAU hbase)
  have hsumV := alongCurveWithin_add cov γ (fun r ↦ W (γ r)) (fun r ↦ V r - W (γ r)) s
    (differentiableWithinAt_sectionCoord _ _ hWγ hbase)
    (differentiableWithinAt_sectionCoord _ _ hU hbase)
  rw [hsplit] at hsumV
  rw [hAsplit, hprod, alongCurveWithin_pullback_curveVelocityWithin cov γ _ hs hγ
    (hA.clm_bundle_apply hW)] at hsum
  rw [alongCurveWithin_pullback_curveVelocityWithin cov γ W hs hγ hW] at hsumV
  have hhom := hom_apply cov cov hA hW (curveVelocityWithin I γ s t)
  simp only [W, extend_apply_self] at hhom
  rw [hsum, hhom, hsumV, map_add]
  abel

/-- **Covariant product rule along a curve.** An ambient endomorphism acts on an arbitrary
field along the curve; its derivative uses the induced endomorphism connection. Neither the
connection nor the endomorphism needs to preserve a metric. -/
theorem alongCurve_clm_apply
    (A : ∀ x : M, TangentSpace I x →L[𝕜] TangentSpace I x) {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t)
    (hA : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[𝕜] E)
      (E := fun x ↦ TangentSpace I x →L[𝕜] TangentSpace I x) x (A x)) (γ t))
    (hV : MDifferentiableAt 𝓘(𝕜, 𝕜) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) t) :
    alongCurve cov γ (fun r ↦ A (γ r) (V r)) t =
      cov.hom cov A (γ t) (curveVelocity I γ t) (V t) +
        A (γ t) (alongCurve cov γ V t) := by
  simpa only [alongCurveWithin_univ, curveVelocityWithin_univ] using
    alongCurveWithin_clm_apply cov γ V A uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt hA hV.mdifferentiableWithinAt

end CovariantDerivative
