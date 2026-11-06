/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic

/-!
# Metric duals of real one-forms

The metric dual `α.metricDual` represents a real one-form by the Riemannian inner product.
It vanishes exactly at the zeros of the form and agrees with the gradient of every local
primitive. A `Cⁿ` form has a `Cⁿ` dual for a `Cⁿ` metric. In particular, the negative dual of
a smooth closed one-form is a smooth vector field even when no global potential exists.

The construction uses the fibrewise Riesz equivalence and the degree-one alternating-map
identification. The potential comparison fixes the sign for descending trajectories:
`df(-α.metricDual) = -‖α.metricDual‖²` wherever `df = α`.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 1.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002), §1.
-/

public noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

open Riemannian.Tensor

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace RoughForm

/-- The metric dual of a real one-form, using the Riemannian metric on each tangent fibre. -/
def metricDual (α : RoughForm I M ℝ 1) (x : M) : TangentSpace I x :=
  rieszDual x ((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := TangentSpace I x) (F := ℝ) (ι := Fin 1) 0).symm (α x))

/-- The metric dual is the Riesz representative of the degree-one form. -/
theorem metricDual_def (α : RoughForm I M ℝ 1) (x : M) :
    α.metricDual x = rieszDual x
      ((ContinuousAlternatingMap.ofSubsingletonLIE
        (𝕜 := ℝ) (E := TangentSpace I x) (F := ℝ) (ι := Fin 1) 0).symm (α x)) :=
  (rfl)

variable {α : RoughForm I M ℝ 1} {x : M}

/-- Pairing the metric dual with a vector evaluates the one-form on that vector. -/
@[simp]
theorem inner_metricDual (v : TangentSpace I x) :
    inner ℝ (α.metricDual x) v = α x ![v] := by
  simp [metricDual_def, ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply,
    Matrix.vec_single_eq_const]

/-- The metric dual is uniquely determined by its pairing with tangent vectors. -/
theorem eq_metricDual_iff {w : TangentSpace I x} :
    w = α.metricDual x ↔ ∀ v, inner ℝ w v = α x ![v] := by
  exact ⟨fun h v ↦ h ▸ inner_metricDual v, fun h ↦
    ext_inner_right ℝ fun v ↦ (h v).trans (inner_metricDual v).symm⟩

/-- The metric dual vanishes precisely at the zeros of the form. -/
@[simp]
theorem metricDual_eq_zero_iff : α.metricDual x = 0 ↔ α x = 0 := by
  simp only [metricDual_def, LinearIsometryEquiv.map_eq_zero_iff]

/-- The zero one-form has zero metric dual. -/
@[simp]
theorem metricDual_zero : (0 : RoughForm I M ℝ 1).metricDual = 0 := by
  funext x
  simp

/-- Metric duality is additive. -/
@[simp]
theorem metricDual_add (α β : RoughForm I M ℝ 1) :
    (α + β).metricDual = α.metricDual + β.metricDual := by
  funext x
  simp only [metricDual_def, Pi.add_apply, LinearIsometryEquiv.map_add]

/-- Metric duality commutes with real scalar multiplication. -/
@[simp]
theorem metricDual_smul (c : ℝ) (α : RoughForm I M ℝ 1) :
    (c • α).metricDual = c • α.metricDual := by
  funext x
  simp [metricDual_def]

/-- Negating the form reverses its metric dual. -/
@[simp]
theorem metricDual_neg (α : RoughForm I M ℝ 1) : (-α).metricDual = -α.metricDual := by
  funext x
  simp only [metricDual_def, Pi.neg_apply, map_neg]
  exact (rieszDual (I := I) x).toLinearEquiv.map_neg _

/-- Evaluating a form on its dual gives the squared length of the dual. -/
theorem apply_metricDual : α x ![α.metricDual x] = ‖α.metricDual x‖ ^ 2 := by
  rw [← inner_metricDual, real_inner_self_eq_norm_sq]

/-- The negative dual decreases a local potential at the squared speed. -/
theorem apply_neg_metricDual : α x ![-α.metricDual x] = -‖α.metricDual x‖ ^ 2 := by
  have h := inner_metricDual (α := α) (-α.metricDual x)
  simpa only [inner_neg_right, real_inner_self_eq_norm_sq] using h.symm

/-- The dual of the differential of a function is its Riemannian gradient. -/
@[simp]
theorem metricDual_mextDeriv_ofFunction (f : M → ℝ) :
    (mextDeriv (RoughForm.ofFunction I f)).metricDual = Manifold.mgradient I f := by
  funext x
  rw [metricDual_def, Manifold.mgradient_def, mextDeriv_ofFunction]
  simp

end RoughForm

/-- On the domain of a local primitive, metric duality is the ordinary gradient. -/
theorem IsPrimitiveOn.metricDual_eq_mgradient {α : RoughForm I M ℝ 1}
    {f : M → ℝ} {U : Set M} (hf : IsPrimitiveOn α f U) {x : M} (hx : x ∈ U) :
    α.metricDual x = Manifold.mgradient I f x := by
  rw [← RoughForm.metricDual_mextDeriv_ofFunction]
  simp only [RoughForm.metricDual_def, hf.mextDeriv_eq x hx]

/-- A local primitive decreases in the negative metric-dual direction at the squared speed. -/
theorem IsPrimitiveOn.mvfderiv_neg_metricDual {α : RoughForm I M ℝ 1}
    {f : M → ℝ} {U : Set M} (hf : IsPrimitiveOn α f U) {x : M} (hx : x ∈ U) :
    mvfderiv I f x (-α.metricDual x) = -‖α.metricDual x‖ ^ 2 := by
  rw [hf.metricDual_eq_mgradient hx, map_neg, Manifold.mvfderiv_apply_mgradient,
    real_inner_self_eq_norm_sq]

/-- For a `Cⁿ` metric a `Cⁿ` real one-form has a `Cⁿ` metric-dual vector field. -/
theorem IsSmoothForm.contMDiff_metricDual {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    {α : RoughForm I M ℝ 1} (hα : IsSmoothForm I n α) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, α.metricDual x⟩ : TangentBundle I M)) := by
  let Φ := fun x ↦ (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := TangentSpace I x) (F := ℝ) (ι := Fin 1) 0).symm (α x)
  have hΦ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (Φ x)) :=
    isSmoothForm_ofSubsingleton_iff.mp (by simpa [Φ] using hα)
  intro x
  simp only [RoughForm.metricDual_def]
  refine contMDiffAt_rieszDual x (mem_chart_source H x) fun j ↦ ?_
  have hframe := (contMDiffOn_chartLocalFrame (I := I) (n := n) x j).contMDiffAt
    (by simpa only [TangentBundle.trivializationAt_baseSet] using chart_source_mem_nhds H x)
  have h := (hΦ x).clm_bundle_apply hframe
  rw [contMDiffAt_section] at h
  simpa only [Trivial.eq_trivialization M ℝ, Trivial.trivialization_apply] using h

/-- The negative metric dual has the same regularity as the form and metric. -/
theorem IsSmoothForm.contMDiff_neg_metricDual {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    {α : RoughForm I M ℝ 1} (hα : IsSmoothForm I n α) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, -α.metricDual x⟩ : TangentBundle I M)) := by
  simpa only [RoughForm.metricDual_neg, Pi.neg_apply] using hα.neg.contMDiff_metricDual

end TauCeti
