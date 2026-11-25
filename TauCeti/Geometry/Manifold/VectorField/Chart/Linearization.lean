/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The linearization of a vector field is its chart derivative

Let `V` be a vector field on a boundaryless manifold `M` modelled on `E`. Read as a section of the
tangent bundle, `V` has a linearization `T_p M → T_p M` at every point
(`TauCeti.sectionLinearization`, along the identity of `M`). It is the chart derivative
`TauCeti.vectorFieldChartDerivative I V p`, the derivative of the coordinate field of `V` in the
chart at `p` (`TauCeti.sectionLinearization_eq_vectorFieldChartDerivative`): both are read in the
tangent-bundle trivialization at `p`, which is the identity on the fibre over `p`. This holds at
every point, whether or not `V` vanishes or is differentiable there.

In positive finite dimension, a chart derivative of nonzero determinant is not the junk value `0`,
so the field is differentiable there
(`TauCeti.mdifferentiableAt_of_det_vectorFieldChartDerivative_ne_zero`).

## Main results

* `TauCeti.sectionLinearization_eq_vectorFieldChartDerivative`: the linearization of a vector
  field is its chart derivative; `TauCeti.sectionLinearization_apply_eq_vectorFieldChartDerivative`
  is the pointwise form.
* `TauCeti.mdifferentiableAt_of_det_vectorFieldChartDerivative_ne_zero`: a vector field whose chart
  derivative has nonzero determinant is differentiable there.
-/

public section

open Bundle Module Set
open scoped Manifold

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- **The linearization of a vector field is its chart derivative**, pointwise. On a boundaryless
manifold, the linearization `T_p M → T_p M` of a vector field `V`, read as a section of the tangent
bundle, sends `v` to the derivative at `v` of the coordinate field of `V` in the chart at `p`. -/
theorem sectionLinearization_apply_eq_vectorFieldChartDerivative
    (V : (x : M) → TangentSpace I x) (p : M) (v : TangentSpace I p) :
    sectionLinearization (F := E) I id V p v = vectorFieldChartDerivative I V p v := by
  have hp : p ∈ (chartAt H p).source := mem_chart_source H p
  -- The fibre coordinate of `V` in the trivialization at `p` is, near the chart image of `p`, the
  -- coordinate field of `V` in the chart at `p`.
  have h := VectorField.trivializationAt_snd_eventuallyEq_mpullbackWithin_extChartAt_symm V p
  rw [I.range_eq_univ, nhdsWithin_univ, VectorField.mpullbackWithin_univ] at h
  -- The trivialization at `p` reads the fibre over `p` by the identity.
  rw [sectionLinearization_def, id, ContinuousLinearMap.comp_apply,
    TangentBundle.symmL_trivializationAt_eq_core hp]
  refine ((tangentBundleCore I M).coordChange_self (achart H p) p hp _).trans ?_
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm, vectorFieldChartDerivative_def, ← h.fderiv_eq,
    ContinuousLinearMap.coe_coe]
  -- The two functions differentiated are equal by `Function.comp` and by the coercion of a point
  -- of the tangent space to the total space of the tangent bundle.
  rfl

/-- **The linearization of a vector field is its chart derivative.** On a boundaryless manifold,
the linearization `T_p M → T_p M` of a vector field `V`, read as a section of the tangent bundle,
is the derivative of the coordinate field of `V` in the chart at `p`. Both are computed in the
tangent-bundle trivialization at `p`, which reads the fibre over `p` by the identity. -/
theorem sectionLinearization_eq_vectorFieldChartDerivative (V : (x : M) → TangentSpace I x)
    (p : M) :
    (sectionLinearization (F := E) I id V p).toLinearMap = vectorFieldChartDerivative I V p :=
  LinearMap.ext (sectionLinearization_apply_eq_vectorFieldChartDerivative V p)

/-- **Nondegenerate chart derivatives come from differentiable fields.** In positive finite
dimension, a vector field whose chart derivative at `p` has nonzero determinant is differentiable
at `p` as a section of the tangent bundle: otherwise the chart derivative is `0`, whose
determinant vanishes. -/
theorem mdifferentiableAt_of_det_vectorFieldChartDerivative_ne_zero [FiniteDimensional 𝕜 E]
    [Nontrivial E] {V : (x : M) → TangentSpace I x} {p : M}
    (hdet : LinearMap.det (vectorFieldChartDerivative I V p) ≠ 0) :
    MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) p := by
  refine mdifferentiableAt_section_iff_differentiableAt_mpullbackWithin_extChartAt_symm.2 ?_
  rw [I.range_eq_univ, VectorField.mpullbackWithin_univ]
  by_contra hd
  rw [vectorFieldChartDerivative_def, fderiv_zero_of_not_differentiableAt hd,
    ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero,
    zero_pow finrank_pos.ne'] at hdet
  exact hdet rfl

end TauCeti
