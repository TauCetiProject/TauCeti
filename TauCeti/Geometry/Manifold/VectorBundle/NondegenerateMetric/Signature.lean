/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import Mathlib.Topology.Connected.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Signature of a smooth nondegenerate metric

The positive and negative inertia indices of a continuous family of symmetric nondegenerate
tangent bilinear forms are locally constant.  The family is any continuous map into the total
space of the tangent bilinear-form bundle, so this covers a smooth nondegenerate metric as well as
a family of metrics depending on a parameter.  The proof reads the forms in a tangent-bundle
trivialization and applies stability of the signature for continuous families of forms on the
fixed model space.  The coordinate form is isometric to the original form, so its inertia indices
are intrinsic.

Thus a smooth nondegenerate metric has one fixed signature on each connected component.  This is
the topological input for treating a nondegenerate metric of fixed signature as a
pseudo-Riemannian metric.

## Main results

* `TauCeti.Manifold.isLocallyConstant_sigPos_sigNeg_of_continuous` proves that the inertia
  indices of a continuous family of symmetric nondegenerate tangent bilinear forms are locally
  constant.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.signature` is the pair consisting of the positive
  and negative inertia indices.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.isLocallyConstant_signature` proves that this pair
  is locally constant.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.signature_eq_of_mem_connectedComponent` and
  `signature_eq` give the connected-component and preconnected-space consequences.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983, Chapter 3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Chapter 2.
-/

public section

noncomputable section

open Bundle FiberBundle Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ContMDiffNondegenerateMetric

/-- The signature of a smooth nondegenerate metric at a point, with the positive inertia index
first and the negative inertia index second. -/
def signature (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) : ℕ × ℕ :=
  (sigPos (g x).toBilinForm.toQuadraticMap, sigNeg (g x).toBilinForm.toQuadraticMap)

/-- The first component of the metric signature is its positive inertia index. -/
@[simp]
theorem signature_fst (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    (g.signature x).1 = sigPos (g x).toBilinForm.toQuadraticMap :=
  (rfl)

/-- The second component of the metric signature is its negative inertia index. -/
@[simp]
theorem signature_snd (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    (g.signature x).2 = sigNeg (g x).toBilinForm.toQuadraticMap :=
  (rfl)

end ContMDiffNondegenerateMetric

/-- A tangent bilinear form read in a trivialization has the same positive and negative inertia
indices as the form itself, on the base set of that trivialization. -/
theorem sigPos_sigNeg_tangentBilinFormInCoordinates (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet)
    (ϕ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    (sigPos (tangentBilinFormInCoordinates a x ϕ).toBilinForm.toQuadraticMap,
      sigNeg (tangentBilinFormInCoordinates a x ϕ).toBilinForm.toQuadraticMap) =
      (sigPos ϕ.toBilinForm.toQuadraticMap, sigNeg ϕ.toBilinForm.toQuadraticMap) := by
  let e := (trivializationAt E (fun y : M ↦ TangentSpace I y) a)
    |>.continuousLinearEquivAt ℝ x hx
  have hequiv : QuadraticMap.Equivalent ϕ.toBilinForm.toQuadraticMap
      (tangentBilinFormInCoordinates a x ϕ).toBilinForm.toQuadraticMap := by
    refine ⟨{ toLinearEquiv := e.toLinearEquiv, map_app' := fun v ↦ ?_ }⟩
    rw [tangentBilinFormInCoordinates_toBilinForm a hx]
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.congr_apply]
    exact congrArg (fun w ↦ ϕ w w) (e.symm_apply_apply v)
  exact Prod.ext hequiv.sigPos_eq.symm hequiv.sigNeg_eq.symm

variable [FiniteDimensional ℝ E]

/-- The positive and negative inertia indices of a continuous family of symmetric nondegenerate
tangent bilinear forms are locally constant. The family is a continuous map from an arbitrary
topological space to the total space of the tangent bilinear-form bundle, so its base point may
vary as well as the form. -/
theorem isLocallyConstant_sigPos_sigNeg_of_continuous {X : Type*} [TopologicalSpace X]
    {q : X → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hq : Continuous q) (hsymm : ∀ y, (q y).snd.toBilinForm.IsSymm)
    (hnd : ∀ y, (q y).snd.toBilinForm.Nondegenerate) :
    IsLocallyConstant fun y ↦
      (sigPos (q y).snd.toBilinForm.toQuadraticMap,
        sigNeg (q y).snd.toBilinForm.toQuadraticMap) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  let a := (q y₀).proj
  let e := trivializationAt E (fun y : M ↦ TangentSpace I y) a
  let V : X → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦ tangentBilinFormInCoordinates a (q y).proj (q y).snd
  have ha : a ∈ e.baseSet := mem_baseSet_trivializationAt E _ a
  have he : ∀ᶠ y in nhds y₀, (q y).proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj _ _ |>.comp hq).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds ha)
  have hV : ContinuousAt V y₀ := by
    have hcoord := ((FiberBundle.continuousAt_totalSpace (E →L[ℝ] E →L[ℝ] ℝ) q).mp
      (hq.continuousAt (x := y₀))).2
    simpa only [V, tangentBilinFormInCoordinates, hom_trivializationAt_apply] using hcoord
  have hsymmV : ∀ᶠ y in nhds y₀, (V y).toBilinForm.IsSymm := by
    filter_upwards [he] with y hy
    exact isSymm_tangentBilinFormInCoordinates a hy (hsymm y)
  have hndV : (V y₀).toBilinForm.Nondegenerate :=
    nondegenerate_tangentBilinFormInCoordinates a ha (hnd y₀)
  have hneg : ∀ᶠ y in nhds y₀,
      sigNeg (V y).toBilinForm.toQuadraticMap =
        sigNeg (V y₀).toBilinForm.toQuadraticMap :=
    ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt hsymmV hV hndV
  have hpos : ∀ᶠ y in nhds y₀,
      sigPos (V y).toBilinForm.toQuadraticMap =
        sigPos (V y₀).toBilinForm.toQuadraticMap := by
    filter_upwards [he, hneg] with y hy hny
    have hsum {z : X} (hz : (q z).proj ∈ e.baseSet) :=
      QuadraticForm.sigPos_add_sigNeg_of_nondegenerate (V z).toBilinForm.toQuadraticMap
        ((nondegenerate_tangentBilinFormInCoordinates a hz (hnd z)).toQuadraticMap
          (LinearMap.BilinForm.isSymm_iff_flip.mp
            (isSymm_tangentBilinFormInCoordinates a hz (hsymm z))))
    have hsumy := hsum hy
    have hsumx := hsum ha
    omega
  filter_upwards [he, hpos, hneg] with y hy hpy hny
  rw [← sigPos_sigNeg_tangentBilinFormInCoordinates a hy,
    ← sigPos_sigNeg_tangentBilinFormInCoordinates a ha]
  exact Prod.ext hpy hny

namespace ContMDiffNondegenerateMetric

/-- The signature of a smooth nondegenerate metric is locally constant. -/
theorem isLocallyConstant_signature
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) :
    IsLocallyConstant g.signature :=
  isLocallyConstant_sigPos_sigNeg_of_continuous
    (q := fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x)) g.contMDiff.continuous
    (fun x ↦ g.symm x) (fun x ↦ g.nondegenerate x)

/-- The metric signature is constant on each connected component. -/
theorem signature_eq_of_mem_connectedComponent
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) {x y : M}
    (hy : y ∈ connectedComponent x) : g.signature y = g.signature x :=
  g.isLocallyConstant_signature.apply_eq_of_isPreconnected isPreconnected_connectedComponent hy
    mem_connectedComponent

/-- On a preconnected manifold, a smooth nondegenerate metric has one fixed signature. -/
theorem signature_eq [PreconnectedSpace M]
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x y : M) :
    g.signature x = g.signature y :=
  g.isLocallyConstant_signature.apply_eq_of_preconnectedSpace x y

end ContMDiffNondegenerateMetric

end TauCeti.Manifold

end
