/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

/-!
# Metric duality of smooth one-forms on Riemannian manifolds

On a Riemannian manifold `(M, g)`, a smooth real one-form `a : SmoothForm I M ℝ 1` defines at each
point `x : M` a continuous linear functional
`SmoothForm.degreeOneEquiv a x : TangentSpace I x →L[ℝ] ℝ` whose Riesz-dual tangent vector is
`Riemannian.Tensor.rieszDual x (SmoothForm.degreeOneEquiv a x)`. This file bridges that musical
identification with `TauCeti.alternatingFormEquiv` in degree `1`.

## Main results

* `TauCeti.SmoothForm.alternatingFormEquiv_rieszDual_degreeOneEquiv`: under
  `TauCeti.alternatingFormEquiv`, the `1`-vector `ιMulti ℝ 1 ![(a_x)♯]` maps to `a.1 x`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer, 2018, Chapter 2.
-/

public section

noncomputable section

open Bundle exteriorPower
open scoped Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Under `alternatingFormEquiv`, a smooth one-form at `x` corresponds to the tangent vector given
by the Riesz dual of `SmoothForm.degreeOneEquiv`. -/
theorem alternatingFormEquiv_rieszDual_degreeOneEquiv (a : SmoothForm I M ℝ 1) (x : M) :
    (letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
     alternatingFormEquiv (TangentSpace I x) 1
      (ιMulti ℝ 1 ![Riemannian.Tensor.rieszDual (I := I) x (degreeOneEquiv a x)])) =
      a.1 x := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  ext w
  have hw : ![w 0] = w := funext fun i ↦ by fin_cases i; rfl
  rw [alternatingFormEquiv_ιMulti_apply, Matrix.det_fin_one]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one, Riemannian.Tensor.inner_rieszDual,
    degreeOneEquiv_apply_apply_vec, hw]

end TauCeti.SmoothForm
