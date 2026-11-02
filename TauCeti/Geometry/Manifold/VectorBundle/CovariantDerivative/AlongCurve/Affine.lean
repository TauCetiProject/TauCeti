/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic

/-!
# Covariant derivatives of affine fields along constant curves

For any connection, the affine field `t ↦ u + (t - a) • v` along a constant curve
has covariant derivative `v`. This gives explicit initial data for Jacobi fields
along constant geodesics, including derivatives within closed parameter intervals.
The computation takes place in a fixed bundle chart and requires no metric.
-/

public section

open Bundle
open scoped Manifold

noncomputable section

namespace CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- Along a constant curve, an affine tangent field has constant covariant velocity,
independently of the connection. The derivative may be taken within a parameter set. -/
@[simp]
theorem alongCurveWithin_const_add_smul
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {s : Set 𝕜} {t : 𝕜} {x : M} (hs : UniqueDiffWithinAt 𝕜 s t)
    (u v : TangentSpace I x) (a : 𝕜) :
    alongCurveWithin cov (fun _ ↦ x) (fun r ↦ u + (r - a) • v) s t = v := by
  let _ : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let _ : NormedSpace 𝕜 (TangentSpace I x) := inferInstanceAs (NormedSpace 𝕜 E)
  refine alongCurveWithin_const_of_hasDerivWithinAt cov x ?_ hs
  simpa only [id_eq, one_smul] using! ((((hasDerivAt_id t).sub_const a).smul_const v).const_add u)
    |>.hasDerivWithinAt (s := s)

end CovariantDerivative
