/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Differentiating a bundle endomorphism applied to a vanishing field

At a zero of a tangent field `V` along a curve, the covariant derivative of `A V` is
`A (D V)` for every differentiable family of endomorphisms `A`. The derivative of `A`
and both connection correction terms vanish there. This does not require a connection
on the endomorphism bundle, nor any compatibility of `A` with the tangent connection.

The result applies within parameter sets, including at endpoints. In particular it
allows the Jacobi equation to be differentiated at a zero of the Jacobi field.

The proof uses Mathlib's hom-bundle coordinates and the native along-curve derivative.
See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4,
for covariant differentiation along curves and its product rule.
-/

public section

open Bundle Filter
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

end CovariantDerivative
