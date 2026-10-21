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

The positive and negative inertia indices of a smooth field of symmetric nondegenerate bilinear
forms are locally constant.  The proof reads the metric in a tangent-bundle trivialization and
applies stability of the signature for continuous families of forms on the fixed model space.
The coordinate form is isometric to the original form, so its inertia indices are intrinsic.

Thus a smooth nondegenerate metric has one fixed signature on each connected component.  This is
the topological input for treating a nondegenerate metric of fixed signature as a
pseudo-Riemannian metric.

## Main results

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

private abbrev inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (fun y : M ↦ TangentSpace I y)
    (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) a x a x (g x)

private theorem continuousAt_inCoordinates_self
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) :
    ContinuousAt (g.inCoordinates a) a := by
  have hg := g.contMDiff.continuous.continuousAt (x := a)
  have hcoord := (FiberBundle.continuousAt_section
    (E →L[ℝ] E →L[ℝ] ℝ) a).mp hg
  simpa only [hom_trivializationAt_apply] using hcoord

private theorem inCoordinates_apply
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) (v w : E) :
    g.inCoordinates a x v w =
      g x ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).symm x v)
        ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).symm x w) := by
  simpa only [inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq] using
    (inCoordinates_apply_eq₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun y : M ↦ TangentSpace I y) (E₂ := fun y : M ↦ TangentSpace I y)
      (E₃ := Bundle.Trivial M ℝ) (x₀ := a) (x := x)
      (ϕ := g x) hx hx (by simp) (v := v) (w := w))

private theorem inCoordinates_toBilinForm
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm =
      LinearMap.BilinForm.congr
        ((trivializationAt E (fun y : M ↦ TangentSpace I y) a).continuousLinearEquivAt ℝ x hx
          |>.toLinearEquiv) (g x).toBilinForm := by
  ext v w
  rw [ContinuousLinearMap.toBilinForm_apply, LinearMap.BilinForm.congr_apply,
    inCoordinates_apply g a hx]
  rfl

private theorem isSymm_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm.IsSymm := by
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply, inCoordinates_apply g a hx]
  exact g.apply_comm x _ _

private theorem nondegenerate_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (g.inCoordinates a x).toBilinForm.Nondegenerate := by
  rw [inCoordinates_toBilinForm g a hx]
  exact (g.nondegenerate x).congr _

private theorem signature_inCoordinates
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (a : M) {x : M}
    (hx : x ∈ (trivializationAt E (fun y : M ↦ TangentSpace I y) a).baseSet) :
    (sigPos (g.inCoordinates a x).toBilinForm.toQuadraticMap,
      sigNeg (g.inCoordinates a x).toBilinForm.toQuadraticMap) = g.signature x := by
  let e := (trivializationAt E (fun y : M ↦ TangentSpace I y) a)
    |>.continuousLinearEquivAt ℝ x hx
  have hequiv : QuadraticMap.Equivalent (g x).toBilinForm.toQuadraticMap
      (g.inCoordinates a x).toBilinForm.toQuadraticMap := by
    refine ⟨{ toLinearEquiv := e.toLinearEquiv, map_app' := fun v ↦ ?_ }⟩
    rw [inCoordinates_toBilinForm g a hx]
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.congr_apply]
    exact congrArg (fun w ↦ g x w w) (e.symm_apply_apply v)
  exact Prod.ext hequiv.sigPos_eq.symm hequiv.sigNeg_eq.symm

variable [FiniteDimensional ℝ E]

/-- The signature of a smooth nondegenerate metric is locally constant. -/
theorem isLocallyConstant_signature
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) :
    IsLocallyConstant g.signature := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := trivializationAt E (fun y : M ↦ TangentSpace I y) x
  let V := g.inCoordinates x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E _ x
  have he : e.baseSet ∈ nhds x := e.open_baseSet.mem_nhds hx
  have hV : ContinuousAt V x := g.continuousAt_inCoordinates_self x
  have hsymm : ∀ᶠ y in nhds x, (V y).toBilinForm.IsSymm := by
    filter_upwards [he] with y hy
    exact g.isSymm_inCoordinates x hy
  have hnd : (V x).toBilinForm.Nondegenerate := g.nondegenerate_inCoordinates x hx
  have hneg : ∀ᶠ y in nhds x,
      sigNeg (V y).toBilinForm.toQuadraticMap =
        sigNeg (V x).toBilinForm.toQuadraticMap :=
    ContinuousLinearMap.eventually_sigNeg_toBilinForm_eq_of_continuousAt hsymm hV hnd
  have hpos : ∀ᶠ y in nhds x,
      sigPos (V y).toBilinForm.toQuadraticMap =
        sigPos (V x).toBilinForm.toQuadraticMap := by
    filter_upwards [he, hneg] with y hy hny
    have hQy : (V y).toBilinForm.toQuadraticMap.Nondegenerate :=
      (g.nondegenerate_inCoordinates x hy).toQuadraticMap
        (LinearMap.BilinForm.isSymm_iff_flip.mp (g.isSymm_inCoordinates x hy))
    have hQx : (V x).toBilinForm.toQuadraticMap.Nondegenerate :=
      hnd.toQuadraticMap
        (LinearMap.BilinForm.isSymm_iff_flip.mp (g.isSymm_inCoordinates x hx))
    have hsumy := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate
      (V y).toBilinForm.toQuadraticMap hQy
    have hsumx := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate
      (V x).toBilinForm.toQuadraticMap hQx
    omega
  filter_upwards [he, hpos, hneg] with y hy hpy hny
  rw [← g.signature_inCoordinates x hy, ← g.signature_inCoordinates x hx]
  exact Prod.ext hpy hny

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
