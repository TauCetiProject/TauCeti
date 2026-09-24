/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Lagrangian graphs in a cotangent space

The graph of a linear map from a vector space to its dual is Lagrangian for the canonical
cotangent symplectic form precisely when the induced bilinear pairing is symmetric. The same
criterion holds for the continuous dual of a normed space. In particular, the graph of the
Hessian of a twice continuously differentiable real function is Lagrangian. The derivative of
the differential graph has this Hessian graph as its range, and the Liouville form pulls back
to the differential of the function.

The Hessian graph is the tangent-space model of the graph of the differential of a function,
the basic exact Lagrangian in a cotangent bundle. The sign convention is that of
`TauCeti.cotangentSymplecticForm` and `TauCeti.strongDualCotangentSymplecticForm`.

The geometric criterion is standard; see McDuff--Salamon, *Introduction to Symplectic
Topology*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

section AlgebraicDual

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {A : V →ₗ[ℝ] Module.Dual ℝ V}

/-- A graph in the algebraic cotangent space is Lagrangian exactly when its defining map gives a
symmetric bilinear pairing. No finite-dimensionality hypothesis is needed. -/
theorem isLagrangian_cotangent_graph_iff :
    (cotangentSymplecticForm (V := V)).IsLagrangian A.graph ↔
      ∀ v w, A v w = A w v := by
  exact SymplecticForm.isLagrangian_graph_iff_of_pairing cotangentSymplecticForm
    (fun a v ↦ a v) (by simp) (fun _ _ h ↦ LinearMap.ext h) A

end AlgebraicDual

section ContinuousDual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {A : V →L[ℝ] StrongDual ℝ V}

/-- The graph of a continuous linear map to the continuous dual is Lagrangian precisely when
its pairing is symmetric. This applies in infinite-dimensional normed spaces as well. -/
theorem isLagrangian_strongDualCotangent_graph_iff :
    (strongDualCotangentSymplecticForm (V := V)).IsLagrangian A.toLinearMap.graph ↔
      ∀ v w, A v w = A w v := by
  exact SymplecticForm.isLagrangian_graph_iff_of_pairing strongDualCotangentSymplecticForm
    (fun a v ↦ a v) (by simp) (fun _ _ h ↦ ContinuousLinearMap.ext h) A.toLinearMap

/-- The graph of a symmetric second derivative is Lagrangian. The Hessian here is the derivative
of the differential, taking values in the continuous dual. -/
theorem isLagrangian_hessian_graph {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) :
    (strongDualCotangentSymplecticForm (V := V)).IsLagrangian
      (fderiv ℝ (fderiv ℝ f) x).toLinearMap.graph := by
  apply isLagrangian_strongDualCotangent_graph_iff.mpr
  exact hf.isSymmSndFDerivAt (by norm_num)

/-- The derivative of the graph map of `df` is the graph map of the Hessian. -/
@[simp] theorem fderiv_cotangent_differential_graph {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    fderiv ℝ (fun y : V ↦ (y, fderiv ℝ f y)) x =
      (ContinuousLinearMap.id ℝ V).prod (fderiv ℝ (fderiv ℝ f) x) := by
  simpa using (differentiableAt_id.fderiv_prodMk hf)

/-- The Liouville form pulls back along the graph of `df` to `df` itself: on a tangent vector
`v`, its value is the directional derivative `dfₓ(v)`. -/
theorem cotangentLiouvilleForm_differential_graph_apply
    {f : V → ℝ} {x : V} (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : V) :
    cotangentLiouvilleForm (x, fderiv ℝ f x)
      (fun _ ↦ fderiv ℝ (fun y : V ↦ (y, fderiv ℝ f y)) x v) =
        fderiv ℝ f x v := by
  rw [fderiv_cotangent_differential_graph hf]
  simp

/-- The tangent image to the graph of a differential is Lagrangian in the linear cotangent
space. This is the pointwise Lagrangian condition for an exact graph. -/
theorem isLagrangian_range_fderiv_cotangent_differential_graph
    {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ 2 f x) :
    (strongDualCotangentSymplecticForm (V := V)).IsLagrangian
      (LinearMap.range (fderiv ℝ (fun y : V ↦ (y, fderiv ℝ f y)) x).toLinearMap) := by
  rw [fderiv_cotangent_differential_graph
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  have hid : (ContinuousLinearMap.id ℝ V).toLinearMap = (LinearMap.id : V →ₗ[ℝ] V) := rfl
  simpa only [ContinuousLinearMap.coe_prod, hid, LinearMap.graph_eq_range_prod] using
    (isLagrangian_hessian_graph hf)

end ContinuousDual

end TauCeti

end
