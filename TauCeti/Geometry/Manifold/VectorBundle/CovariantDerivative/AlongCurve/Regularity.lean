/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity of covariant differentiation along curves

A `C^(n + 1)` tangent field along a `C^(n + 1)` curve has a `C^n` covariant derivative.
The field is an arbitrary section along the curve, with its original tangent-space carriers;
it need not extend to a vector field on the manifold. The within-set version applies to
parameter sets with unique derivatives, including nondegenerate closed intervals.

The proof reads the native along-curve derivative in one fixed chart near each parameter.
Chart independence identifies that reading with the sum of the derivative of the section
coordinates and the Christoffel contraction. Smoothness of the connection is required locally
on the trivialization base sets, as in `ContMDiffCovariantDerivativeOn`.

The coordinate identification uses `CovariantDerivative.symmL_alongCurveInChartWithin`, and
the connection regularity is supplied by `TauCeti.Manifold.contMDiffOn_christoffelMap`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4 and 10.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t))

/-- Near a parameter where the curve and section lift are `C¹`, the reading of the native
covariant derivative in any fixed chart is its defining fixed-chart coordinate formula. -/
theorem eventuallyEq_sectionCoord_alongCurveWithin {s : Set 𝕜} {t : 𝕜} {x : M}
    (hs : UniqueDiffOn 𝕜 s) (ht : t ∈ s)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hV : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t) :
    sectionCoord (F := E) γ (alongCurveWithin cov γ V s) x =ᶠ[𝓝[s] t]
      alongCurveInChartWithin cov γ V s x := by
  let e := trivializationAt E (TangentSpace I) x
  have hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I 1 γ s t :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I)
      (n := 1)).contMDiffAt.comp_contMDiffWithinAt t hV
  have hbase := hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  have hγ' : ∀ᶠ r in 𝓝[s] t, ContMDiffWithinAt 𝓘(𝕜, 𝕜) I 1 γ s r := by
    simpa only [insert_eq_of_mem ht] using
      (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by norm_num)).1 hγ
  have hV' : ∀ᶠ r in 𝓝[s] t, ContMDiffWithinAt 𝓘(𝕜, 𝕜) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s r := by
    simpa only [insert_eq_of_mem ht] using
      (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by norm_num)).1 hV
  filter_upwards [self_mem_nhdsWithin, hbase, hγ', hV'] with r hr hxr hγr hVr
  have hread := symmL_alongCurveInChartWithin cov γ V hxr (hs r hr)
    (hγr.mdifferentiableWithinAt (by norm_num))
    (differentiableWithinAt_sectionCoord γ V
      (hVr.mdifferentiableWithinAt (by norm_num))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
  rw [sectionCoord_apply, ← hread]
  exact e.continuousLinearMapAt_symmL hxr _

variable {n : ℕ∞ω}
  [IsManifold I (n + 1) M]
  [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]

/-- Covariant differentiation loses one derivative for an arbitrary section lift along a curve.
Only local `C^n` regularity of the connection in one chart containing `γ t` is needed. -/
theorem contMDiffWithinAt_alongCurveWithin {s : Set 𝕜} {t : 𝕜} {x : M}
    [ContMDiffCovariantDerivativeOn E n cov.toFun
      (trivializationAt E (TangentSpace I) x).baseSet]
    (hs : UniqueDiffOn 𝕜 s) (ht : t ∈ s)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hV : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I.tangent (n + 1)
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t) :
    ContMDiffWithinAt 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V s r)) s t := by
  let e := trivializationAt E (TangentSpace I) x
  have hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I (n + 1) γ s t :=
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (IB := I)
      (n := n + 1)).contMDiffAt.comp_contMDiffWithinAt t hV
  have hn : n ≤ n + 1 := le_self_add
  have h1 : (1 : ℕ∞ω) ≤ n + 1 := le_add_of_nonneg_left (zero_le : 0 ≤ n)
  have hv : ContDiffWithinAt 𝕜 (n + 1) (sectionCoord (F := E) γ V x) s t :=
    (contMDiffWithinAt_sectionCoord_iff γ V hγ hx).2 hV
  have hu : ContDiffWithinAt 𝕜 (n + 1) (extChartAt I x ∘ γ) s t :=
    ((contMDiffAt_extChartAt' (by
      simpa only [TangentBundle.trivializationAt_baseSet] using hx)).comp_contMDiffWithinAt
        t hγ).contDiffWithinAt
  have hΓ : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E →L[𝕜] E) n
      (christoffelMap (Module.finBasis 𝕜 E)
        (cov.isCovariantDerivativeOn (s := e.baseSet))) (γ t) :=
    (contMDiffOn_christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn (s := e.baseSet))).contMDiffAt (e.open_baseSet.mem_nhds hx)
  have hcoord : ContDiffWithinAt 𝕜 n (alongCurveInChartWithin cov γ V s x) s t := by
    rw [funext (alongCurveInChartWithin_apply cov γ V s x)]
    exact (hv.derivWithin hs le_rfl ht).add
      (((hΓ.comp_contMDiffWithinAt t (hγ.of_le hn)).contDiffWithinAt.clm_apply
        (hv.of_le hn)).clm_apply (hu.derivWithin hs le_rfl ht))
  apply (contMDiffWithinAt_sectionCoord_iff γ (alongCurveWithin cov γ V s)
    (hγ.of_le hn) hx).1
  exact hcoord.congr_of_eventuallyEq_of_mem
    (eventuallyEq_sectionCoord_alongCurveWithin cov γ V hs ht hx
      (hV.of_le h1)) ht

/-- On a parameter set with unique derivatives, differentiating a `C^(n + 1)` section lift
along a `C^(n + 1)` curve produces a `C^n` section lift. The connection is `C^n` on each
canonical trivialization base set. -/
theorem contMDiffOn_alongCurveWithin {s : Set 𝕜}
    (hcov : ∀ x : M, ContMDiffCovariantDerivativeOn E n cov.toFun
      (trivializationAt E (TangentSpace I) x).baseSet)
    (hs : UniqueDiffOn 𝕜 s)
    (hV : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent (n + 1)
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s) :
    ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V s r)) s := by
  intro t ht
  let := hcov (γ t)
  exact contMDiffWithinAt_alongCurveWithin cov γ V hs ht
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)) (hV t ht)

/-- The unrestricted covariant derivative of a `C^(n + 1)` section along a `C^(n + 1)` curve
is `C^n`, for a connection `C^n` on the canonical trivialization base sets. -/
theorem contMDiff_alongCurve
    (hcov : ∀ x : M, ContMDiffCovariantDerivativeOn E n cov.toFun
      (trivializationAt E (TangentSpace I) x).baseSet)
    (hV : ContMDiff 𝓘(𝕜, 𝕜) I.tangent (n + 1)
      (fun r ↦ TotalSpace.mk' E (γ r) (V r))) :
    ContMDiff 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurve cov γ V r)) := by
  rw [← contMDiffOn_univ]
  simpa only [alongCurveWithin_univ] using
    contMDiffOn_alongCurveWithin cov γ V hcov uniqueDiffOn_univ hV.contMDiffOn

end CovariantDerivative
